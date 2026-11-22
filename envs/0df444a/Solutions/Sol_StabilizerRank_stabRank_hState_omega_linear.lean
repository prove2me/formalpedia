-- Prove2me | solution 1 for StabilizerRank.stabRank_hState_omega_linear
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T23:40:12.763993+00:00
-- url     : https://prove2.me/submissions/6befa9cd-8bc6-4fd9-8a68-b50434b48755

import Definitions.Def_StabilizerRank


section

/- Complete frozen bridge body copied from ImpactStabilizerBridge.lean.
   Original byte hash and verification receipt are recorded in manifest.json. -/
namespace StabilizerRank

variable {n : ℕ}

/-- Translation on the canonical Boolean index set. -/
def bitTranslate (a x : Bits n) : Bits n := fun i => xor (a i) (x i)

@[simp] theorem bitTranslate_twice (a x : Bits n) :
    bitTranslate a (bitTranslate a x) = x := by
  funext i
  simp [bitTranslate]

@[simp] theorem bitTranslate_zero (x : Bits n) : bitTranslate (fun _ => false) x = x := by
  funext i
  exact Bool.false_xor (x i)

theorem bitTranslate_injective (a : Bits n) : Function.Injective (bitTranslate a) :=
  Function.LeftInverse.injective (bitTranslate_twice a)

/-- The column convention of the canonical Pauli matrix determines this recurrence. -/
theorem pauli_mulVec_translate (a b x : Bits n) (ψ : QState n) :
    (pauliMatrix a b).mulVec ψ (bitTranslate a x) =
      (-1 : ℂ) ^ (Finset.univ.filter (fun i => b i && x i)).card * ψ x := by
  classical
  simp only [Matrix.mulVec, dotProduct, pauliMatrix, Matrix.of_apply]
  have h (y : Bits n) :
      (bitTranslate a x = fun i => xor (a i) (y i)) ↔ y = x := by
    change bitTranslate a x = bitTranslate a y ↔ y = x
    exact ⟨fun h => ((bitTranslate_injective a) h).symm,
      fun h => congrArg (bitTranslate a) h.symm⟩
  simp_rw [h, ite_mul, zero_mul]
  simp

/-- Every diagonal Z operator fixes the canonical zero state. -/
theorem pauli_zero_mulVec_zeroState (b : Bits n) :
    (pauliMatrix (fun _ => false) b).mulVec (zeroState n) = zeroState n := by
  funext x
  have h := pauli_mulVec_translate (fun _ => false) b x (zeroState n)
  rw [bitTranslate_zero] at h
  rw [h]
  by_cases hx : x = fun _ => false
  · subst x
    simp [zeroState]
  · simp [zeroState, hx]

theorem pauli_mem_group (a b : Bits n) : pauliMatrix a b ∈ pauliGroupSet n := by
  exact ⟨0, a, b, by simp⟩

/-- Conjugation transports actual fixed vectors, using both canonical matrix conventions. -/
theorem clifford_conjugate_fixes (U : Matrix (Bits n) (Bits n) ℂ)
    (hU : IsCliffordUnitary U) (b : Bits n) :
    (U * pauliMatrix (fun _ => false) b * star U).mulVec
      (U.mulVec (zeroState n)) = U.mulVec (zeroState n) := by
  have hstar : star U * U = 1 := hU.1.1
  rw [Matrix.mulVec_mulVec, mul_assoc, hstar, mul_one,
    ← Matrix.mulVec_mulVec, pauli_zero_mulVec_zeroState]

/-- A canonical stabilizer state has the Pauli amplitude recurrence for every conjugated Z. -/
theorem stabilizer_pauli_recurrence (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∃ U : Matrix (Bits n) (Bits n) ℂ, IsCliffordUnitary U ∧
      ψ = U.mulVec (zeroState n) ∧
      ∀ b : Bits n, ∃ (c : Fin 4) (a d : Bits n),
        U * pauliMatrix (fun _ => false) b * star U =
          Complex.I ^ (c : ℕ) • pauliMatrix a d ∧
        ∀ x : Bits n, ψ (bitTranslate a x) =
          Complex.I ^ (c : ℕ) *
            ((-1 : ℂ) ^ (Finset.univ.filter (fun i => d i && x i)).card * ψ x) := by
  obtain ⟨U, hU, rfl⟩ := hψ
  refine ⟨U, hU, rfl, fun b => ?_⟩
  obtain ⟨c, a, d, hP⟩ := hU.2 _ (pauli_mem_group (fun _ => false) b)
  refine ⟨c, a, d, hP, fun x => ?_⟩
  have hfix := clifford_conjugate_fixes U hU b
  rw [hP, Matrix.smul_mulVec] at hfix
  have hx := congrFun hfix (bitTranslate a x)
  simpa only [Pi.smul_apply, smul_eq_mul, pauli_mulVec_translate] using hx.symm

/-- Unitarity rules out the zero vector, including the zero-qubit case. -/
theorem stabilizer_ne_zero (ψ : QState n) (hψ : IsStabilizerState ψ) : ψ ≠ 0 := by
  obtain ⟨U, hU, rfl⟩ := hψ
  intro h
  have hv := congrArg (fun v => (star U).mulVec v) h
  rw [Matrix.mulVec_mulVec, hU.1.1, Matrix.one_mulVec, Matrix.mulVec_zero] at hv
  have hzero := congrFun hv (fun _ => false)
  simp [zeroState] at hzero

/-- The common fixed space of all diagonal Paulis is exactly the zero-state line. -/
theorem diagonal_common_fixed_iff (v : QState n) :
    (∀ b : Bits n, (pauliMatrix (fun _ => false) b).mulVec v = v) ↔
      ∃ t : ℂ, v = t • zeroState n := by
  classical
  constructor
  · intro hv
    refine ⟨v (fun _ => false), ?_⟩
    funext x
    by_cases hx : x = fun _ => false
    · subst x
      simp [zeroState]
    · have hex : ∃ i, x i = true := by
        by_contra! h
        apply hx
        funext i
        cases hi : x i with
        | false => rfl
        | true => exact False.elim (h i hi)
      obtain ⟨i, hi⟩ := hex
      let b : Bits n := fun j => decide (j = i)
      have hfilter : Finset.univ.filter (fun j => b j && x j) = {i} := by
        ext j
        by_cases hj : j = i
        · subst j
          simp [b, hi]
        · simp [b, hj]
      have he := congrFun (hv b) x
      have hp := pauli_mulVec_translate (fun _ => false) b x v
      rw [bitTranslate_zero] at hp
      rw [hp, hfilter] at he
      simp only [Finset.card_singleton, pow_one] at he
      have hz : v x = 0 := by linear_combination -he / 2
      simp [zeroState, hx, hz]
  · rintro ⟨t, rfl⟩ b
    rw [Matrix.mulVec_smul, pauli_zero_mulVec_zeroState]

/-- Unitary transport identifies the entire common fixed space, not only one fixed vector. -/
theorem clifford_common_fixed_iff (U : Matrix (Bits n) (Bits n) ℂ)
    (hU : IsCliffordUnitary U) (v : QState n) :
    (∀ b : Bits n,
      (U * pauliMatrix (fun _ => false) b * star U).mulVec v = v) ↔
      ∃ t : ℂ, v = t • U.mulVec (zeroState n) := by
  constructor
  · intro hv
    have hw : ∀ b : Bits n,
        (pauliMatrix (fun _ => false) b).mulVec ((star U).mulVec v) =
          (star U).mulVec v := by
      intro b
      have he := congrArg (fun w => (star U).mulVec w) (hv b)
      simp only [Matrix.mulVec_mulVec] at he ⊢
      simpa only [← mul_assoc, hU.1.1, one_mul] using he
    obtain ⟨t, ht⟩ := (diagonal_common_fixed_iff _).1 hw
    refine ⟨t, ?_⟩
    have he := congrArg (fun w => U.mulVec w) ht
    simpa only [Matrix.mulVec_mulVec, hU.1.2, Matrix.one_mulVec,
      Matrix.mulVec_smul] using he
  · rintro ⟨t, rfl⟩ b
    rw [Matrix.mulVec_smul, clifford_conjugate_fixes U hU]

@[simp] theorem bitTranslate_self (a : Bits n) :
    bitTranslate a a = fun _ => false := by
  funext i
  simp [bitTranslate]

theorem bitTranslate_comm (a b : Bits n) : bitTranslate a b = bitTranslate b a := by
  funext i
  exact Bool.xor_comm _ _

theorem bitTranslate_assoc (a b c : Bits n) :
    bitTranslate a (bitTranslate b c) = bitTranslate (bitTranslate a b) c := by
  funext i
  exact (Bool.xor_assoc _ _ _).symm

/-- Finite sums of the extracted Pauli translations; no amplitude normal form is assumed. -/
inductive ShiftSpan {ι : Type*} (a : ι → Bits n) : Bits n → Prop
  | zero : ShiftSpan a (fun _ => false)
  | step (i : ι) {x : Bits n} : ShiftSpan a x → ShiftSpan a (bitTranslate (a i) x)

theorem shiftSpan_add {ι : Type*} (a : ι → Bits n) {x y : Bits n}
    (hx : ShiftSpan a x) (hy : ShiftSpan a y) : ShiftSpan a (bitTranslate x y) := by
  induction hx with
  | zero => simpa using hy
  | step i hx ih =>
      rw [← bitTranslate_assoc]
      exact ShiftSpan.step i ih

theorem shiftSpan_generator_iff {ι : Type*} (a : ι → Bits n) (i : ι) (x : Bits n) :
    ShiftSpan a (bitTranslate (a i) x) ↔ ShiftSpan a x := by
  constructor
  · intro h
    simpa using ShiftSpan.step i h
  · exact ShiftSpan.step i

/-- The fixed-vector equation and its coordinate recurrence are equivalent. -/
theorem pauli_fixed_iff (c : ℂ) (a b : Bits n) (v : QState n) :
    (c • pauliMatrix a b).mulVec v = v ↔
      ∀ x, v (bitTranslate a x) =
        c * ((-1 : ℂ) ^ (Finset.univ.filter (fun i => b i && x i)).card * v x) := by
  rw [Matrix.smul_mulVec]
  constructor
  · intro h x
    have he := congrFun h (bitTranslate a x)
    simpa only [Pi.smul_apply, smul_eq_mul, pauli_mulVec_translate] using he.symm
  · intro h
    funext y
    have he := h (bitTranslate a y)
    rw [bitTranslate_twice] at he
    have hp := pauli_mulVec_translate a b (bitTranslate a y) v
    rw [bitTranslate_twice] at hp
    simpa only [Pi.smul_apply, smul_eq_mul, hp] using he.symm

/-- The parity character in the canonical Pauli definition. -/
def pauliSign (b x : Bits n) : ℂ :=
  (-1 : ℂ) ^ (Finset.univ.filter (fun i => b i && x i)).card

theorem pauliSign_eq_prod (b x : Bits n) :
    pauliSign b x = ∏ i, (if b i && x i then (-1 : ℂ) else 1) := by
  simp [pauliSign, Finset.prod_ite]

theorem pauliSign_translate (b x y : Bits n) :
    pauliSign b (bitTranslate x y) = pauliSign b x * pauliSign b y := by
  simp only [pauliSign_eq_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  dsimp [bitTranslate]
  have hbool : ∀ (u v w : Bool),
      (if u && xor v w then (-1 : ℂ) else 1) =
        (if u && v then (-1 : ℂ) else 1) * (if u && w then (-1 : ℂ) else 1) := by
    intro u v w
    cases u <;> cases v <;> cases w <;> norm_num
  exact hbool (b i) (x i) (y i)

theorem pauliSign_comm (b x : Bits n) : pauliSign b x = pauliSign x b := by
  unfold pauliSign
  congr 2
  ext i
  simp [Bool.and_comm]

theorem pauliSign_translate_left (b d x : Bits n) :
    pauliSign (bitTranslate b d) x = pauliSign b x * pauliSign d x := by
  rw [pauliSign_comm, pauliSign_translate, pauliSign_comm x b, pauliSign_comm x d]

@[simp] theorem pauliSign_zero (x : Bits n) : pauliSign (fun _ => false) x = 1 := by
  simp [pauliSign]

@[simp] theorem pauliSign_four (b x : Bits n) : pauliSign b x ^ 4 = 1 := by
  unfold pauliSign
  rw [← pow_mul, Nat.mul_comm _ 4, pow_mul]
  norm_num

/-- Composing extracted Pauli recurrences gives one character for every support direction. -/
theorem shiftSpan_phase {ι : Type*} (ψ : QState n) (a d : ι → Bits n) (c : ι → Fin 4)
    (hphase : ∀ i x, ψ (bitTranslate (a i) x) =
      Complex.I ^ (c i : ℕ) * (pauliSign (d i) x * ψ x))
    (z : Bits n) (hz : ShiftSpan a z) :
    ∃ (t : ℂ) (b : Bits n), t ^ 4 = 1 ∧
      ∀ x, ψ (bitTranslate z x) = t * (pauliSign b x * ψ x) := by
  induction hz with
  | zero => exact ⟨1, fun _ => false, by norm_num, by intro x; simp⟩
  | @step i z hz ih =>
      obtain ⟨t, b, ht, he⟩ := ih
      refine ⟨Complex.I ^ (c i : ℕ) * pauliSign (d i) z * t,
        bitTranslate (d i) b, ?_, ?_⟩
      · rw [mul_pow, mul_pow, ht, pauliSign_four]
        have hi : (Complex.I ^ (c i : ℕ)) ^ 4 = 1 := by
          rw [← pow_mul, Nat.mul_comm _ 4, pow_mul, Complex.I_pow_four, one_pow]
        rw [hi]
        norm_num
      · intro x
        rw [← bitTranslate_assoc, hphase, he, pauliSign_translate,
          pauliSign_translate_left]
        ring

/-- A canonical stabilizer has support equal to one affine Boolean subspace.
The statement uses explicit XOR closure to preserve the canonical `Bits` type. -/
theorem stabilizer_support_affine (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∃ (x₀ : Bits n) (L : Set (Bits n)),
      ψ x₀ ≠ 0 ∧ (fun _ => false) ∈ L ∧
      (∀ x ∈ L, ∀ y ∈ L, bitTranslate x y ∈ L) ∧
      (∀ x, ψ x ≠ 0 ↔ bitTranslate x₀ x ∈ L) ∧
      ∀ z ∈ L, ∃ (t : ℂ) (b : Bits n), t ^ 4 = 1 ∧
        ∀ x, ψ (bitTranslate z x) = t * (pauliSign b x * ψ x) := by
  classical
  obtain ⟨U, hU, hψU, hrec⟩ := stabilizer_pauli_recurrence ψ hψ
  choose c a d hP hphase using hrec
  have hex : ∃ x₀, ψ x₀ ≠ 0 := by
    by_contra! h
    exact stabilizer_ne_zero ψ hψ (funext h)
  obtain ⟨x₀, hx₀⟩ := hex
  let L : Set (Bits n) := {x | ShiftSpan a x}
  have hshift (b : Bits n) (x : Bits n) :
      ψ (bitTranslate (a b) x) ≠ 0 ↔ ψ x ≠ 0 := by
    rw [hphase]
    simp [Complex.I_ne_zero]
  have hspan (z : Bits n) (hz : ShiftSpan a z) :
      ∀ x, ψ (bitTranslate z x) ≠ 0 ↔ ψ x ≠ 0 := by
    induction hz with
    | zero => intro x; simp
    | step b hz ih =>
        intro x
        rw [← bitTranslate_assoc, hshift, ih]
  have hinv (b : Bits n) (x : Bits n) :
      ShiftSpan a (bitTranslate x₀ (bitTranslate (a b) x)) ↔
        ShiftSpan a (bitTranslate x₀ x) := by
    have he : bitTranslate x₀ (bitTranslate (a b) x) =
        bitTranslate (a b) (bitTranslate x₀ x) := by
      rw [bitTranslate_assoc, bitTranslate_comm x₀ (a b), ← bitTranslate_assoc]
    rw [he, shiftSpan_generator_iff]
  let v : QState n := fun x => if ShiftSpan a (bitTranslate x₀ x) then ψ x else 0
  have hv : ∀ b : Bits n,
      (U * pauliMatrix (fun _ => false) b * star U).mulVec v = v := by
    intro b
    rw [hP, pauli_fixed_iff]
    intro x
    dsimp [v]
    rw [hinv]
    by_cases hx : ShiftSpan a (bitTranslate x₀ x)
    · simp only [hx, if_true]
      exact hphase b x
    · simp [hx]
  obtain ⟨t, ht⟩ := (clifford_common_fixed_iff U hU v).1 hv
  rw [← hψU] at ht
  have ht1 : t = 1 := by
    have he := congrFun ht x₀
    have hmem : ShiftSpan a (bitTranslate x₀ x₀) := by
      rw [bitTranslate_self]
      exact ShiftSpan.zero
    change (if ShiftSpan a (bitTranslate x₀ x₀) then ψ x₀ else 0) = t * ψ x₀ at he
    rw [if_pos hmem] at he
    exact (mul_right_cancel₀ hx₀ (by simpa using he.symm : t * ψ x₀ = 1 * ψ x₀))
  have hvψ : v = ψ := by simpa [ht1] using ht
  refine ⟨x₀, L, hx₀, ShiftSpan.zero, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact shiftSpan_add a hx hy
  · intro x
    constructor
    · intro hx
      by_contra hn
      have he := congrFun hvψ x
      change (if ShiftSpan a (bitTranslate x₀ x) then ψ x else 0) = ψ x at he
      change ¬ ShiftSpan a (bitTranslate x₀ x) at hn
      rw [if_neg hn] at he
      exact hx he.symm
    · intro hx
      have he := (hspan (bitTranslate x₀ x) hx x₀).2 hx₀
      have heq : bitTranslate (bitTranslate x₀ x) x₀ = x := by
        rw [bitTranslate_comm (bitTranslate x₀ x) x₀, bitTranslate_twice]
      rwa [heq] at he

  · intro z hz
    exact shiftSpan_phase ψ a d c hphase z hz

/-- Four roots, with no choice of global phase imposed on the state. -/
theorem fourth_root_cases (t : ℂ) (ht : t ^ 4 = 1) :
    t = 1 ∨ t = -1 ∨ t = Complex.I ∨ t = -Complex.I := by
  have h : (t - 1) * (t + 1) * (t - Complex.I) * (t + Complex.I) = 0 := by
    linear_combination ht - (t ^ 2 - 1) * Complex.I_sq
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h)))

/-- All nonzero amplitudes differ from a fixed nonzero amplitude by a fourth root. -/
theorem stabilizer_four_phase (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ x : Bits n,
      ψ x = 0 ∨ ψ x = C ∨ ψ x = -C ∨ ψ x = Complex.I * C ∨ ψ x = -Complex.I * C := by
  obtain ⟨x₀, L, hx₀, _, _, hsupp, hderiv⟩ := stabilizer_support_affine ψ hψ
  refine ⟨ψ x₀, hx₀, fun x => ?_⟩
  by_cases hx : ψ x = 0
  · exact Or.inl hx
  · obtain ⟨t, b, ht, he⟩ := hderiv (bitTranslate x₀ x) ((hsupp x).1 hx)
    have heq : bitTranslate (bitTranslate x₀ x) x₀ = x := by
      rw [bitTranslate_comm (bitTranslate x₀ x) x₀, bitTranslate_twice]
    have hv := he x₀
    rw [heq] at hv
    have hroot : (t * pauliSign b x₀) ^ 4 = 1 := by
      rw [mul_pow, ht, pauliSign_four, one_mul]
    rcases fourth_root_cases _ hroot with h | h | h | h
    · exact Or.inr (Or.inl (by simpa [← mul_assoc, h] using hv))
    · exact Or.inr (Or.inr (Or.inl (by simpa [← mul_assoc, h] using hv)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [← mul_assoc, h] using hv))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa [← mul_assoc, h] using hv))))

/-- Once one collision exists, every further collision is one parity equation on the support. -/
theorem phase_collision_iff (ψ : QState n) (z b x₀ x : Bits n) (t : ℂ)
    (ht : t ^ 4 = 1)
    (hrec : ∀ y, ψ (bitTranslate z y) = t * (pauliSign b y * ψ y))
    (hzero : ψ x₀ ≠ 0) (hx : ψ x ≠ 0)
    (hcollision : ψ (bitTranslate z x₀) = ψ x₀) :
    ψ (bitTranslate z x) = ψ x ↔ pauliSign b x = pauliSign b x₀ := by
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht
  have hbase : t * pauliSign b x₀ = 1 := by
    rw [hrec, ← mul_assoc] at hcollision
    exact mul_right_cancel₀ hzero (by simpa using hcollision)
  rw [hrec, ← mul_assoc]
  constructor
  · intro he
    have hcurrent : t * pauliSign b x = 1 :=
      mul_right_cancel₀ hx (by simpa using he)
    exact mul_left_cancel₀ ht0 (hcurrent.trans hbase.symm)
  · intro he
    rw [he, hbase, one_mul]

/-- A parity level set is an affine Boolean subspace, expressed by ternary closure. -/
theorem pauliSign_fiber_affine (b x y z : Bits n)
    (hxy : pauliSign b x = pauliSign b y) (hxz : pauliSign b x = pauliSign b z) :
    pauliSign b (bitTranslate x (bitTranslate y z)) = pauliSign b x := by
  have hsquare : pauliSign b x * pauliSign b x = 1 := by
    rw [← pauliSign_translate, bitTranslate_self, pauliSign_comm, pauliSign_zero]
  rw [pauliSign_translate, pauliSign_translate, ← hxy, ← hxz, hsquare, mul_one]

end StabilizerRank

namespace StabilizerRank

/-- Three Boolean coordinates suffice to encode each stabilizer amplitude. -/
theorem stabilizer_family_coloring {n r : ℕ} (φ : Fin r → QState n)
    (hφ : ∀ j, IsStabilizerState (φ j)) :
    ∃ F : Bits n → Bits (3 * r),
      ∀ a b, F a = F b → ∀ j, φ j a = φ j b := by
  classical
  choose C hC hvalues using fun j => stabilizer_four_phase (φ j) (hφ j)
  let value : Fin r → Fin 8 → ℂ := fun j k =>
    if k = 0 then 0 else if k = 1 then C j else if k = 2 then -C j
    else if k = 3 then Complex.I * C j else -Complex.I * C j
  have hex (j : Fin r) (x : Bits n) : ∃ k : Fin 8, φ j x = value j k := by
    rcases hvalues j x with h | h | h | h | h
    · exact ⟨0, by simpa [value] using h⟩
    · exact ⟨1, by simpa [value] using h⟩
    · exact ⟨2, by simpa [value] using h⟩
    · exact ⟨3, by simpa [value] using h⟩
    · exact ⟨4, by simpa [value] using h⟩
  choose code hcode using hex
  have hcard : Fintype.card (Fin r → Fin 8) = Fintype.card (Bits (3 * r)) := by
    simp only [Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    rw [pow_mul]
    norm_num
  let e := Fintype.equivOfCardEq hcard
  refine ⟨fun x => e (fun j => code j x), ?_⟩
  intro a b hab j
  have he := congrFun (e.injective hab) j
  exact (hcode j a).trans ((congrArg (value j) he).trans (hcode j b).symm)

/-- Every canonical parity character has exactly two possible values. -/
theorem pauliSign_eq_one_or_neg_one {n : ℕ} (d x : Bits n) :
    pauliSign d x = 1 ∨ pauliSign d x = -1 := by
  have hs : pauliSign d x * pauliSign d x = 1 := by
    rw [← pauliSign_translate, bitTranslate_self, pauliSign_comm, pauliSign_zero]
  have hp : (pauliSign d x - 1) * (pauliSign d x + 1) = 0 := by
    linear_combination hs
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- On a ternary-closed set, the parity fiber through any chosen point has density
at least `2⁻ʳ`. Translation identifies every occupied fiber with this fiber. -/
theorem pauliSign_common_fiber {n r : ℕ} (d : Fin r → Bits n)
    (U : Finset (Bits n)) (a : Bits n) (ha : a ∈ U)
    (hU : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      bitTranslate x (bitTranslate y z) ∈ U) :
    ∃ V : Finset (Bits n), V ⊆ U ∧ a ∈ V ∧
      (∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, bitTranslate x (bitTranslate y z) ∈ V) ∧
      U.card ≤ 2 ^ r * V.card ∧
      ∀ x ∈ V, ∀ j, pauliSign (d j) x = pauliSign (d j) a := by
  classical
  let V := U.filter (fun x => ∀ j, pauliSign (d j) x = pauliSign (d j) a)
  have memV (x : Bits n) : x ∈ V ↔ x ∈ U ∧ ∀ j,
      pauliSign (d j) x = pauliSign (d j) a := by simp [V]
  have haV : a ∈ V := (memV a).2 ⟨ha, fun _ => rfl⟩
  let pattern : Bits n → Bits r := fun x j => decide (pauliSign (d j) x = 1)
  have pattern_iff (x y : Bits n) : pattern x = pattern y ↔
      ∀ j, pauliSign (d j) x = pauliSign (d j) y := by
    constructor
    · intro h j
      have he : (pauliSign (d j) x = 1) ↔ (pauliSign (d j) y = 1) := by
        have hj := congrFun h j
        simpa only [pattern, decide_eq_decide] using hj
      rcases pauliSign_eq_one_or_neg_one (d j) x with hx | hx
      · exact hx.trans (he.mp hx).symm
      · rcases pauliSign_eq_one_or_neg_one (d j) y with hy | hy
        · exact (he.mpr hy).trans hy.symm
        · exact hx.trans hy.symm
    · intro h
      funext j
      simp only [pattern, h j]
  have representatives (p : Bits r) :
      ∃ y : Bits n, y ∈ U ∧ ( (∃ x ∈ U, pattern x = p) → pattern y = p) := by
    by_cases hp : ∃ x ∈ U, pattern x = p
    · obtain ⟨x, hx, he⟩ := hp
      exact ⟨x, hx, fun _ => he⟩
    · exact ⟨a, ha, fun h => False.elim (hp h)⟩
  choose representative hrep using representatives
  have translate_mem (x : Bits n) (hx : x ∈ U) :
      bitTranslate x (bitTranslate (representative (pattern x)) a) ∈ V := by
    refine (memV _).2 ⟨hU x hx _ (hrep _).1 a ha, ?_⟩
    intro j
    have he := (pattern_iff x (representative (pattern x))).1
      ((hrep (pattern x)).2 ⟨x, hx, rfl⟩).symm j
    have hs : pauliSign (d j) x * pauliSign (d j) x = 1 := by
      rw [← pauliSign_translate, bitTranslate_self, pauliSign_comm, pauliSign_zero]
    rw [pauliSign_translate, pauliSign_translate, ← he, ← mul_assoc, hs, one_mul]
  let encode : U → Bits r × V := fun x =>
    ⟨pattern x, ⟨bitTranslate x (bitTranslate (representative (pattern x)) a),
      translate_mem x x.property⟩⟩
  have hinj : Function.Injective encode := by
    intro x y h
    have hp : pattern x = pattern y := congrArg Prod.fst h
    have hv : bitTranslate x (bitTranslate (representative (pattern x)) a) =
        bitTranslate y (bitTranslate (representative (pattern y)) a) :=
      congrArg (fun z : Bits r × V => (z.2 : Bits n)) h
    rw [hp] at hv
    apply Subtype.ext
    rw [bitTranslate_comm (x : Bits n), bitTranslate_comm (y : Bits n)] at hv
    exact bitTranslate_injective _ hv
  refine ⟨V, fun x hx => ((memV x).1 hx).1, haV, ?_, ?_, ?_⟩
  · intro x hx y hy z hz
    obtain ⟨hxU, hxS⟩ := (memV x).1 hx
    obtain ⟨hyU, hyS⟩ := (memV y).1 hy
    obtain ⟨hzU, hzS⟩ := (memV z).1 hz
    refine (memV _).2 ⟨hU x hxU y hyU z hzU, fun j => ?_⟩
    exact (pauliSign_fiber_affine (d j) x y z
      ((hxS j).trans (hyS j).symm) ((hxS j).trans (hzS j).symm)).trans (hxS j)
  · have hc := Fintype.card_le_of_injective encode hinj
    simpa only [Fintype.card_prod, Fintype.card_coe, Bits, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin] using hc
  · intro x hx
    exact ((memV x).1 hx).2

end StabilizerRank


namespace StabilizerRank

/-- A family collision cuts a constant-support affine region by at most one parity
per stabilizer. The resulting region preserves every amplitude along the collision direction.
Membership of `a` already witnesses that the input region is nonempty. -/
theorem stabilizer_phase_cut {n r : ℕ} (φ : Fin r → QState n)
    (hφ : ∀ j, IsStabilizerState (φ j)) (U : Finset (Bits n))
    (hU : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      bitTranslate x (bitTranslate y z) ∈ U)
    (hsupport : ∀ j, (∀ x ∈ U, φ j x = 0) ∨ (∀ x ∈ U, φ j x ≠ 0))
    (a b : Bits n) (ha : a ∈ U) (hb : b ∈ U)
    (hab : ∀ j, φ j a = φ j b) :
    ∃ V : Finset (Bits n), V ⊆ U ∧ a ∈ V ∧
      (∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, bitTranslate x (bitTranslate y z) ∈ V) ∧
      U.card ≤ 2 ^ r * V.card ∧
      ∀ x ∈ V, ∀ j, φ j (bitTranslate (bitTranslate a b) x) = φ j x := by
  classical
  have directions (j : Fin r) : ∃ d : Bits n, ∀ x ∈ U,
      pauliSign d x = pauliSign d a →
      φ j (bitTranslate (bitTranslate a b) x) = φ j x := by
    rcases hsupport j with hinactive | hactive
    · refine ⟨fun _ => false, fun x hx _ => ?_⟩
      have htranslated : bitTranslate (bitTranslate a b) x ∈ U := by
        rw [← bitTranslate_assoc]
        exact hU a ha b hb x hx
      rw [hinactive _ htranslated, hinactive x hx]
    · obtain ⟨x₀, L, _, _, hclosed, hmem, hrec⟩ :=
        stabilizer_support_affine (φ j) (hφ j)
      have hv : bitTranslate a b ∈ L := by
        have he : bitTranslate (bitTranslate x₀ a) (bitTranslate x₀ b) =
            bitTranslate a b := by
          funext i
          dsimp only [bitTranslate]
          cases x₀ i <;> cases a i <;> cases b i <;> rfl
        rw [← he]
        exact hclosed _ ((hmem a).1 (hactive a ha)) _ ((hmem b).1 (hactive b hb))
      obtain ⟨t, d, ht, hphase⟩ := hrec _ hv
      have hbase : φ j (bitTranslate (bitTranslate a b) a) = φ j a := by
        have he : bitTranslate (bitTranslate a b) a = b := by
          rw [bitTranslate_comm (bitTranslate a b) a, bitTranslate_twice]
        rw [he]
        exact (hab j).symm
      refine ⟨d, fun x hx he => ?_⟩
      exact (phase_collision_iff (φ j) (bitTranslate a b) d a x t ht hphase
        (hactive a ha) (hactive x hx) hbase).2 he
  choose d hd using directions
  obtain ⟨V, hVU, haV, hV, hcard, hparity⟩ := pauliSign_common_fiber d U a ha hU
  exact ⟨V, hVU, haV, hV, hcard, fun x hx j => hd j x (hVU hx) (hparity x hx j)⟩

end StabilizerRank

end


section

namespace StabilizerAffine

open StabilizerRank

abbrev Vec (n : ℕ) := Fin n → ZMod 2

def translate {n : ℕ} (x y : Bits n) : Bits n := fun i => xor (x i) (y i)

def IsAffine {n : ℕ} (S : Set (Bits n)) : Prop :=
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, translate (translate x y) z ∈ S

def VecClosed {n : ℕ} (S : Set (Vec n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + y + z ∈ S

private theorem two_values (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
  exact h a

private theorem vec_self {n : ℕ} (x : Vec n) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem cancel_pair {n : ℕ} (x y : Vec n) : x + y + y = x := by
  rw [add_assoc, vec_self, add_zero]

/-- Translating a ternary-closed set through a member gives a subspace. -/
def direction {n : ℕ} (S : Set (Vec n)) (hS : VecClosed S)
    (a : Vec n) (ha : a ∈ S) : Submodule (ZMod 2) (Vec n) where
  carrier := {v | v + a ∈ S}
  zero_mem' := by simpa using ha
  add_mem' := by
    intro x y hx hy
    have h := hS (x + a) hx (y + a) hy a ha
    change x + y + a ∈ S
    have he : x + a + (y + a) + a = (x + y + a) + (a + a) := by abel
    simpa only [he, vec_self, add_zero] using h
  smul_mem' := by
    intro c x hx
    rcases two_values c with rfl | rfl
    · simpa using ha
    · simpa using hx

/-- An affine set and an exterior point are separated by an affine binary level. -/
theorem separate {n : ℕ} (S : Set (Vec n)) (hS : VecClosed S)
    (hne : S.Nonempty) (x : Vec n) (hx : x ∉ S) :
    ∃ (f : Vec n →ₗ[ZMod 2] ZMod 2) (c : ZMod 2),
      (∀ y ∈ S, f y = c) ∧ f x ≠ c := by
  obtain ⟨a, ha⟩ := hne
  have hout : x + a ∉ direction S hS a ha := by
    simpa [direction, cancel_pair] using hx
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hout
  refine ⟨f, f a, ?_, ?_⟩
  · intro y hy
    have hm : y + a ∈ direction S hS a ha := by
      simpa [direction, cancel_pair] using hy
    have he : f y + f a = 0 := by simpa using hker hm
    have hself := CharTwo.add_self_eq_zero (f a)
    exact add_right_cancel (he.trans hself.symm)
  · intro he
    apply hf
    simp [map_add, he, CharTwo.add_self_eq_zero]

private theorem binary_eq_of_ne {a b c : ZMod 2} (hb : b ≠ a) (hc : c ≠ a) : b = c := by
  rcases two_values a with rfl | rfl <;>
    rcases two_values b with rfl | rfl <;>
    rcases two_values c with rfl | rfl <;> simp_all

/-- Every nonempty linear level in an affine region retains at least half its points. -/
theorem level_cut {n : ℕ} (U : Finset (Vec n))
    (hU : VecClosed (U : Set (Vec n)))
    (a : Vec n) (ha : a ∈ U) (f : Vec n →ₗ[ZMod 2] ZMod 2) :
    ∃ V : Finset (Vec n), V ⊆ U ∧ a ∈ V ∧
      VecClosed (V : Set (Vec n)) ∧ U.card ≤ 2 * V.card ∧
      ∀ y ∈ V, f y = f a := by
  classical
  let V := U.filter (fun y => f y = f a)
  have hVa : a ∈ V := by simp [V, ha]
  refine ⟨V, Finset.filter_subset _ _, hVa, ?_, ?_, ?_⟩
  · intro x hx y hy z hz
    simp only [Finset.mem_coe, V, Finset.mem_filter] at hx hy hz ⊢
    refine ⟨hU x hx.1 y hy.1 z hz.1, ?_⟩
    simp [map_add, hx.2, hy.2, hz.2, CharTwo.add_self_eq_zero]
  · by_cases hex : ∃ b ∈ U, f b ≠ f a
    · obtain ⟨b, hb, hfb⟩ := hex
      have hcard : (U.filter (fun y => ¬ f y = f a)).card ≤ V.card := by
        apply Finset.card_le_card_of_injOn (fun y => a + b + y)
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_filter] at hy
          simp only [Finset.mem_coe, V, Finset.mem_filter]
          refine ⟨hU a ha b hb y hy.1, ?_⟩
          have he : f b = f y := binary_eq_of_ne hfb hy.2
          simp [map_add, he, add_assoc, CharTwo.add_self_eq_zero]
        · intro x hx y hy he
          exact add_left_cancel he
      have hsum := U.card_filter_add_card_filter_not (fun y => f y = f a)
      dsimp [V] at *
      omega
    · have he : V = U := by
        apply Finset.filter_eq_self.mpr
        simpa only [not_exists, not_and, not_not] using hex
      rw [he]
      omega
  · intro y hy
    exact (Finset.mem_filter.mp hy).2

/-- A single affine support can be made constant with a loss of at most two. -/
theorem support_cut {n : ℕ} (U : Finset (Vec n)) (hne : U.Nonempty)
    (hU : VecClosed (U : Set (Vec n))) (S : Set (Vec n)) (hS : VecClosed S) :
    ∃ V : Finset (Vec n), V ⊆ U ∧ V.Nonempty ∧
      VecClosed (V : Set (Vec n)) ∧ U.card ≤ 2 * V.card ∧
      ((∀ y ∈ V, y ∈ S) ∨ (∀ y ∈ V, y ∉ S)) := by
  classical
  by_cases hin : ∀ y ∈ U, y ∈ S
  · exact ⟨U, Finset.Subset.refl _, hne, hU, by omega, Or.inl hin⟩
  push Not at hin
  obtain ⟨a, ha, has⟩ := hin
  by_cases hsne : S.Nonempty
  · obtain ⟨f, c, hfc, hfa⟩ := separate S hS hsne a has
    obtain ⟨V, hvu, hav, hv, hc, hf⟩ := level_cut U hU a ha f
    refine ⟨V, hvu, ⟨a, hav⟩, hv, hc, Or.inr ?_⟩
    intro y hy hys
    exact hfa ((hf y hy).symm.trans (hfc y hys))
  · refine ⟨U, Finset.Subset.refl _, hne, hU, by omega, Or.inr ?_⟩
    intro y hy hys
    exact hsne ⟨y, hys⟩

/-- Iterated support cutting, with a cardinality loss of at most two per support. -/
theorem constant_region_vec {n r : ℕ} (U : Finset (Vec n)) (hne : U.Nonempty)
    (hU : VecClosed (U : Set (Vec n)))
    (S : Fin r → Set (Vec n)) (hS : ∀ j, VecClosed (S j)) :
    ∃ V : Finset (Vec n), V ⊆ U ∧ V.Nonempty ∧
      VecClosed (V : Set (Vec n)) ∧ U.card ≤ 2 ^ r * V.card ∧
      ∀ j, (∀ y ∈ V, y ∈ S j) ∨ (∀ y ∈ V, y ∉ S j) := by
  induction r with
  | zero =>
    refine ⟨U, Finset.Subset.refl _, hne, hU, by simp, ?_⟩
    exact fun j => Fin.elim0 j
  | succ r ih =>
    obtain ⟨W, hWU, hWne, hW, hcardW, hconstW⟩ :=
      ih (fun j => S j.succ) (fun j => hS j.succ)
    obtain ⟨V, hVW, hVne, hV, hcardV, hconstV⟩ :=
      support_cut W hWne hW (S 0) (hS 0)
    refine ⟨V, hVW.trans hWU, hVne, hV, ?_, ?_⟩
    · calc
        U.card ≤ 2 ^ r * W.card := hcardW
        _ ≤ 2 ^ r * (2 * V.card) := Nat.mul_le_mul_left _ hcardV
        _ = 2 ^ (r + 1) * V.card := by ring
    · intro j
      refine Fin.cases hconstV (fun k => ?_) j
      rcases hconstW k with hin | hout
      · exact Or.inl (fun y hy => hin y (hVW hy))
      · exact Or.inr (fun y hy => hout y (hVW hy))

def encode {n : ℕ} (x : Bits n) : Vec n := fun i => if x i then 1 else 0

def decode {n : ℕ} (v : Vec n) : Bits n := fun i => decide (v i = 1)

@[simp] theorem decode_encode {n : ℕ} (x : Bits n) : decode (encode x) = x := by
  funext i
  cases h : x i <;> simp [decode, encode, h]

@[simp] theorem encode_decode {n : ℕ} (v : Vec n) : encode (decode v) = v := by
  funext i
  rcases two_values (v i) with h | h <;> simp [encode, decode, h]

def bitsEquiv (n : ℕ) : Bits n ≃ Vec n where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

@[simp] theorem encode_translate {n : ℕ} (x y : Bits n) :
    encode (translate x y) = encode x + encode y := by
  funext i
  cases hx : x i <;> cases hy : y i <;>
    simp [encode, translate, hx, hy, CharTwo.add_self_eq_zero]

/-- Ternary closure of Boolean supports suffices for the vector-space argument. -/
theorem image_closed {n : ℕ} (S : Set (Bits n))
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, translate (translate x y) z ∈ S) :
    VecClosed (bitsEquiv n '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  refine ⟨translate (translate x y) z, hS x hx y hy z hz, ?_⟩
  exact (encode_translate (translate x y) z).trans (by rw [encode_translate]; rfl)

/-- A Boolean affine region of density at least `2⁻ʳ` makes all support indicators constant. -/
theorem constant_region {n r : ℕ} (S : Fin r → Set (Bits n))
    (hS : ∀ j, S j = ∅ ∨ IsAffine (S j)) :
    ∃ U : Finset (Bits n), IsAffine (U : Set (Bits n)) ∧
      2 ^ n ≤ 2 ^ r * U.card ∧
      ∀ j, (∀ x ∈ U, x ∈ S j) ∨ (∀ x ∈ U, x ∉ S j) := by
  classical
  have hclosed (j : Fin r) : VecClosed (bitsEquiv n '' S j) := by
    apply image_closed
    intro x hx y hy z hz
    rcases hS j with he | hs
    · rw [he] at hx
      exact False.elim hx
    · exact hs.2 x hx y hy z hz
  obtain ⟨V, _, hVne, hV, hcard, hconst⟩ :=
    constant_region_vec (Finset.univ : Finset (Vec n))
      Finset.univ_nonempty (by intro x hx y hy z hz; simp)
      (fun j => bitsEquiv n '' S j) hclosed
  let U := V.map (bitsEquiv n).symm.toEmbedding
  have hmem (x : Bits n) : x ∈ U ↔ encode x ∈ V := by
    simp [U, bitsEquiv]
  have hcardU : U.card = V.card := Finset.card_map _
  have hne : (U : Set (Bits n)).Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    exact ⟨decode v, (hmem _).mpr (by simpa using hv)⟩
  refine ⟨U, ⟨hne, ?_⟩, ?_, ?_⟩
  · intro x hx y hy z hz
    apply (hmem _).mpr
    simpa only [encode_translate, Finset.mem_coe] using hV _ ((hmem x).mp hx)
      _ ((hmem y).mp hy) _ ((hmem z).mp hz)
  · rw [hcardU]
    simpa [Vec, Fintype.card_fun] using hcard
  · intro j
    rcases hconst j with hin | hout
    · left
      intro x hx
      have he := hin (encode x) ((hmem x).mp hx)
      exact (bitsEquiv n).injective.mem_set_image.mp he
    · right
      intro x hx hxs
      apply hout (encode x) ((hmem x).mp hx)
      exact ⟨x, hxs, rfl⟩

/-- Adapter for support descriptions by a translated XOR-closed direction set. -/
theorem isAffine_of_direction {n : ℕ} (S : Set (Bits n)) (a : Bits n)
    (L : Set (Bits n)) (hzero : (fun _ => false) ∈ L)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, translate x y ∈ L)
    (hS : ∀ x, x ∈ S ↔ translate a x ∈ L) : IsAffine S := by
  have haa : translate a a = fun _ => false := by
    funext i
    simp [translate]
  refine ⟨⟨a, (hS a).mpr (haa ▸ hzero)⟩, ?_⟩
  intro x hx y hy z hz
  apply (hS _).mpr
  have hm := hadd _ (hadd _ ((hS x).mp hx) _ ((hS y).mp hy)) _ ((hS z).mp hz)
  have he : translate (translate (translate a x) (translate a y)) (translate a z) =
      translate a (translate (translate x y) z) := by
    funext i
    simp only [translate]
    cases a i <;> cases x i <;> cases y i <;> cases z i <;> rfl
  rwa [he] at hm

/-- Several linear levels through a prescribed point retain at least a `2⁻ʳ` fraction. -/
theorem equation_region_vec {n r : ℕ} (U : Finset (Vec n))
    (hU : VecClosed (U : Set (Vec n))) (a : Vec n) (ha : a ∈ U)
    (f : Fin r → (Vec n →ₗ[ZMod 2] ZMod 2)) :
    ∃ V : Finset (Vec n), V ⊆ U ∧ a ∈ V ∧
      VecClosed (V : Set (Vec n)) ∧ U.card ≤ 2 ^ r * V.card ∧
      ∀ j, ∀ x ∈ V, f j x = f j a := by
  induction r with
  | zero =>
    exact ⟨U, Finset.Subset.refl _, ha, hU, by simp, fun j => Fin.elim0 j⟩
  | succ r ih =>
    obtain ⟨W, hWU, haW, hW, hcW, hfW⟩ := ih (fun j => f j.succ)
    obtain ⟨V, hVW, haV, hV, hcV, hfV⟩ := level_cut W hW a haW (f 0)
    refine ⟨V, hVW.trans hWU, haV, hV, ?_, ?_⟩
    · calc
        U.card ≤ 2 ^ r * W.card := hcW
        _ ≤ 2 ^ r * (2 * V.card) := Nat.mul_le_mul_left _ hcV
        _ = 2 ^ (r + 1) * V.card := by ring
    · intro j
      exact Fin.cases hfV (fun k x hx => hfW k x (hVW hx)) j

/-- The homogeneous parity functional with mask `b`, valued in the binary field. -/
def parityLinear {n : ℕ} (b : Bits n) : Vec n →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i, encode b i * v i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

def parity {n : ℕ} (b x : Bits n) : ZMod 2 := parityLinear b (encode x)

/-- Imposing homogeneous parity levels through a point preserves a large affine subregion. -/
theorem parity_region {n r : ℕ} (U : Finset (Bits n))
    (hU : IsAffine (U : Set (Bits n))) (a : Bits n) (ha : a ∈ U)
    (b : Fin r → Bits n) :
    ∃ V : Finset (Bits n), V ⊆ U ∧ a ∈ V ∧ IsAffine (V : Set (Bits n)) ∧
      U.card ≤ 2 ^ r * V.card ∧ ∀ j, ∀ x ∈ V, parity (b j) x = parity (b j) a := by
  classical
  let W := U.map (bitsEquiv n).toEmbedding
  have hWmem (v : Vec n) : v ∈ W ↔ decode v ∈ U := by simp [W, bitsEquiv]
  have hWset : (W : Set (Vec n)) = bitsEquiv n '' (U : Set (Bits n)) := by
    ext v
    simp [W]
  have hW : VecClosed (W : Set (Vec n)) := by
    rw [hWset]
    exact image_closed _ hU.2
  obtain ⟨T, hTW, haT, hT, hc, hf⟩ := equation_region_vec W hW (encode a)
    ((hWmem _).mpr (by simpa using ha)) (fun j => parityLinear (b j))
  let V := T.map (bitsEquiv n).symm.toEmbedding
  have hVmem (x : Bits n) : x ∈ V ↔ encode x ∈ T := by simp [V, bitsEquiv]
  have haV : a ∈ V := (hVmem _).mpr haT
  refine ⟨V, ?_, haV, ⟨⟨a, haV⟩, ?_⟩, ?_, ?_⟩
  · intro x hx
    have hm := (hWmem _).mp (hTW ((hVmem x).mp hx))
    simpa using hm
  · intro x hx y hy z hz
    apply (hVmem _).mpr
    simpa only [encode_translate, Finset.mem_coe] using
      hT _ ((hVmem x).mp hx) _ ((hVmem y).mp hy) _ ((hVmem z).mp hz)
  · simpa only [W, V, Finset.card_map] using hc
  · intro j x hx
    exact hf j _ ((hVmem x).mp hx)

end StabilizerAffine
end


section
namespace StabilizerAffineIntegration
open StabilizerRank StabilizerAffine

theorem stabilizer_indicator_region {n r : ℕ} (ψ : Fin r → QState n)
    (hψ : ∀ j, IsStabilizerState (ψ j)) :
    ∃ U : Finset (Bits n), StabilizerAffine.IsAffine (U : Set (Bits n)) ∧
      2 ^ n ≤ 2 ^ r * U.card ∧
      ∀ j, (∀ x ∈ U, ψ j x ≠ 0) ∨ (∀ x ∈ U, ψ j x = 0) := by
  obtain ⟨U, hU, hc, hm⟩ := StabilizerAffine.constant_region
    (fun j => {x | ψ j x ≠ 0}) (fun j => Or.inr (by
      obtain ⟨a, L, _, hz, hadd, hs, _⟩ := stabilizer_support_affine (ψ j) (hψ j)
      exact isAffine_of_direction _ a L hz hadd hs))
  refine ⟨U, hU, hc, ?_⟩
  intro j
  simpa only [Set.mem_ofPred_eq, not_not] using hm j

end StabilizerAffineIntegration
end


section

open scoped BigOperators

namespace StabilizerRank.Counting

/-- Number of true coordinates, using the canonical Boolean cube. -/
def weight {n : ℕ} (x : Bits n) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

/-- Translation in the Boolean cube. -/
def translate {n : ℕ} (a x : Bits n) : Bits n := fun i => xor (a i) (x i)

theorem weight_le {n : ℕ} (x : Bits n) : weight x ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem weighted_product {n : ℕ} (x : Bits n) :
    (∏ i, if x i = true then (1 : ℕ) else 2) = 2 ^ (n - weight x) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold weight
  omega

/-- The weighted mass of the cube factors coordinate by coordinate. -/
theorem cube_mass (n : ℕ) :
    (∑ x : Bits n, 2 ^ (n - weight x)) = 3 ^ n := by
  simp_rw [← weighted_product]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b = true then (1 : ℕ) else 2)]
  simp

theorem translate_involutive {n : ℕ} (a : Bits n) :
    Function.Involutive (translate a) := by
  intro x
  funext i
  simp [translate]

/-- Translation preserves the total weighted mass. -/
theorem translated_mass {n : ℕ} (a : Bits n) :
    (∑ x : Bits n, 2 ^ (n - weight (translate a x))) = 3 ^ n := by
  rw [(translate_involutive a).bijective.sum_comp (fun x => 2 ^ (n - weight x))]
  exact cube_mass n

/-- Any finite subset of a radius-k ball satisfies an integral volume bound. -/
theorem ball_bound {n k : ℕ} (a : Bits n) (s : Finset (Bits n))
    (h : ∀ x ∈ s, weight (translate a x) ≤ k) :
    s.card * 2 ^ n ≤ 2 ^ k * 3 ^ n := by
  classical
  calc
    s.card * 2 ^ n = ∑ _x ∈ s, 2 ^ n := by simp
    _ ≤ ∑ x ∈ s, 2 ^ k * 2 ^ (n - weight (translate a x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      have := weight_le (translate a x)
      have := h x hx
      omega
    _ = 2 ^ k * ∑ x ∈ s, 2 ^ (n - weight (translate a x)) := by
      rw [Finset.mul_sum]
    _ ≤ 2 ^ k * ∑ x : Bits n, 2 ^ (n - weight (translate a x)) := by
      apply Nat.mul_le_mul_left
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    _ = 2 ^ k * 3 ^ n := by rw [translated_mass]


/-- A map with small-diameter fibers has bounded domain size. -/
theorem fiber_bound {n r k : ℕ} (s : Finset (Bits n)) (f : Bits n → Bits r)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y → weight (translate x y) ≤ k) :
    s.card * 2 ^ n ≤ 2 ^ (r + k) * 3 ^ n := by
  classical
  have hf (b : Bits r) :
      (s.filter fun x => f x = b).card * 2 ^ n ≤ 2 ^ k * 3 ^ n := by
    by_cases hb : (s.filter fun x => f x = b).Nonempty
    · obtain ⟨a, ha⟩ := hb
      apply ball_bound a
      intro x hx
      exact h a (Finset.mem_filter.mp ha).1 x (Finset.mem_filter.mp hx).1
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hx).2.symm)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hb]
  calc
    s.card * 2 ^ n = (∑ b : Bits r, (s.filter fun x => f x = b).card) * 2 ^ n := by
      congr 1
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ = ∑ b : Bits r, (s.filter fun x => f x = b).card * 2 ^ n := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _b : Bits r, 2 ^ k * 3 ^ n := Finset.sum_le_sum (fun b _ => hf b)
    _ = 2 ^ (r + k) * 3 ^ n := by
      simp [Bits, pow_add, mul_assoc]

/-- Integral exponential comparison behind the explicit constant 48. -/
theorem exponent_bound {n r : ℕ}
    (h : 2 ^ (2 * n) ≤ 2 ^ (12 * r) * 3 ^ n) : n ≤ 48 * r := by
  have hfour := Nat.pow_le_pow_left h 4
  have hthree : (3 : ℕ) ^ (4 * n) ≤ 2 ^ (7 * n) := by
    have hb : (3 : ℕ) ^ 4 ≤ 2 ^ 7 := by norm_num
    simpa [pow_mul] using Nat.pow_le_pow_left hb n
  have hfinal : (2 : ℕ) ^ (8 * n) ≤ 2 ^ (48 * r + 7 * n) := by
    calc
      2 ^ (8 * n) = (2 ^ (2 * n)) ^ 4 := by rw [← pow_mul]; congr 1; omega
      _ ≤ (2 ^ (12 * r) * 3 ^ n) ^ 4 := hfour
      _ = 2 ^ (48 * r) * 3 ^ (4 * n) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 1 <;> congr 1 <;> omega
      _ ≤ 2 ^ (48 * r) * 2 ^ (7 * n) := Nat.mul_le_mul_left _ hthree
      _ = 2 ^ (48 * r + 7 * n) := (pow_add _ _ _).symm
  have he := (Nat.pow_le_pow_iff_right (by decide : (1 : ℕ) < 2)).mp hfinal
  omega

/-- Dense Boolean cubes contain a same-label pair separated by more than 8r. -/
theorem collision {n r : ℕ} (hn : 48 * r < n) (s : Finset (Bits n))
    (hd : 2 ^ n ≤ 2 ^ (3 * r) * s.card) (f : Bits n → (Fin r → Bool)) :
    ∃ x ∈ s, ∃ y ∈ s, f x = f y ∧ 8 * r < weight (translate x y) := by
  classical
  by_contra h
  have hdiam : ∀ x ∈ s, ∀ y ∈ s, f x = f y → weight (translate x y) ≤ 8 * r := by
    intro x hx y hy he
    by_contra hw
    exact h ⟨x, hx, y, hy, he, by omega⟩
  have hf := fiber_bound s f hdiam
  have hcompare : 2 ^ (2 * n) ≤ 2 ^ (12 * r) * 3 ^ n := by
    calc
      2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [← pow_add]; congr 1; omega
      _ ≤ (2 ^ (3 * r) * s.card) * 2 ^ n := Nat.mul_le_mul_right _ hd
      _ = 2 ^ (3 * r) * (s.card * 2 ^ n) := by ac_rfl
      _ ≤ 2 ^ (3 * r) * (2 ^ (r + 8 * r) * 3 ^ n) := Nat.mul_le_mul_left _ hf
      _ = 2 ^ (12 * r) * 3 ^ n := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega
  exact (Nat.not_le_of_gt hn) (exponent_bound hcompare)

/-- The two density formulations agree when the exponent is not truncated. -/
theorem density_iff {n r : ℕ} (h : 3 * r ≤ n) (s : Finset (Bits n)) :
    2 ^ (n - 3 * r) ≤ s.card ↔ 2 ^ n ≤ 2 ^ (3 * r) * s.card := by
  have he : 2 ^ n = 2 ^ (3 * r) * 2 ^ (n - 3 * r) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  rw [he]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < (2 : ℕ) ^ (3 * r))).symm

/-- The collision conclusion with the original power-of-two density hypothesis. -/
theorem collision_of_card {n r : ℕ} (hn : 48 * r < n) (s : Finset (Bits n))
    (hd : 2 ^ (n - 3 * r) ≤ s.card) (f : Bits n → (Fin r → Bool)) :
    ∃ x ∈ s, ∃ y ∈ s, f x = f y ∧ 8 * r < weight (translate x y) := by
  exact collision hn s ((density_iff (by omega) s).mp hd) f

end StabilizerRank.Counting


end


section

namespace ImpactStabilizerLowWeight

open StabilizerRank

/-- The coordinates where a bit string is true. -/
def support {n : ℕ} (x : Bits n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

/-- Hamming weight, expressed as a finite cardinality. -/
def weight {n : ℕ} (x : Bits n) : ℕ := (support x).card

@[simp] theorem mem_support {n : ℕ} (x : Bits n) (i : Fin n) :
    i ∈ support x ↔ x i = true := by simp [support]

/-- A minimum-weight point makes restriction to its zero coordinates injective. -/
theorem restriction_injective {n : ℕ} (U : Finset (Bits n)) (x : Bits n)
    (hx : x ∈ U)
    (hclosed : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U,
      (fun i => xor (a i) (xor (b i) (c i))) ∈ U)
    (hmin : ∀ y ∈ U, weight x ≤ weight y) :
    Function.Injective (fun y : U => fun i : {i : Fin n // i ∉ support x} =>
      y.val i.val) := by
  classical
  intro y z heq
  let w : Bits n := fun i => xor (x i) (xor (y.val i) (z.val i))
  have hw : w ∈ U := hclosed x hx y.val y.property z.val z.property
  have hout (i : Fin n) (hi : i ∉ support x) : y.val i = z.val i :=
    congrFun heq ⟨i, hi⟩
  have hsub : support w ⊆ support x := by
    intro i hi
    by_contra hnot
    have he := hout i hnot
    have hfalse : x i = false := by simpa using hnot
    simp [mem_support, w, hfalse, he] at hi
  have hs : support w = support x :=
    Finset.eq_of_subset_of_card_le hsub (hmin w hw)
  have hwx : w = x := by
    funext i
    have hh : w i = true ↔ x i = true := by
      simpa only [mem_support] using (show i ∈ support w ↔ i ∈ support x by rw [hs])
    cases hw' : w i <;> cases hx' : x i <;> simp_all
  apply Subtype.ext
  funext i
  have hh := congrFun hwx i
  change xor (x i) (xor (y.val i) (z.val i)) = x i at hh
  cases hxbit : x i <;> cases hybit : y.val i <;> cases hzbit : z.val i <;> simp_all

/-- The size of a ternary-xor-closed set is bounded by the zero coordinates
of any minimum-weight point. -/
theorem card_le_two_pow_complement {n : ℕ} (U : Finset (Bits n)) (x : Bits n)
    (hx : x ∈ U)
    (hclosed : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U,
      (fun i => xor (a i) (xor (b i) (c i))) ∈ U)
    (hmin : ∀ y ∈ U, weight x ≤ weight y) :
    U.card ≤ 2 ^ (n - weight x) := by
  classical
  have h := Fintype.card_le_of_injective _ (restriction_injective U x hx hclosed hmin)
  rw [Fintype.card_fun, Fintype.card_subtype_compl] at h
  simpa only [Fintype.card_coe, Fintype.card_bool, Fintype.card_fin, weight] using h

/-- A nonempty ternary-xor-closed set of density at least `2^(-k)` contains
 a point of Hamming weight at most `k`. The statement uses only natural numbers. -/
theorem exists_weight_le {n k : ℕ} (U : Finset (Bits n))
    (hne : U.Nonempty)
    (hclosed : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      (fun i => xor (x i) (xor (y i) (z i))) ∈ U)
    (hdensity : 2 ^ n ≤ 2 ^ k * U.card) :
    ∃ x ∈ U, weight x ≤ k := by
  classical
  obtain ⟨x, hx, hmin⟩ := U.exists_min_image weight hne
  refine ⟨x, hx, ?_⟩
  have hcard := card_le_two_pow_complement U x hx hclosed hmin
  have hweight : weight x ≤ n := by
    simpa [weight] using (Finset.card_le_univ (support x))
  have hp : 2 ^ n ≤ 2 ^ (k + (n - weight x)) := by
    rw [pow_add]
    exact hdensity.trans (Nat.mul_le_mul_left _ hcard)
  have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hp
  omega

/-- Hamming weight is subadditive under coordinatewise xor. -/
theorem weight_xor_le {n : ℕ} (x y : Bits n) :
    weight (fun i => xor (x i) (y i)) ≤ weight x + weight y := by
  classical
  have hsub : support (fun i => xor (x i) (y i)) ⊆ support x ∪ support y := by
    intro i hi
    simp only [mem_support, Finset.mem_union] at *
    cases hx : x i <;> cases hy : y i <;> simp_all
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Distance greater than twice the first weight rules out equal weights. -/
theorem weight_ne_of_two_mul_lt_xor {n : ℕ} (x y : Bits n)
    (h : 2 * weight x < weight (fun i => xor (x i) (y i))) :
    weight x ≠ weight y := by
  have htriangle := weight_xor_le x y
  omega

/-- The main result with the weight expanded, for use without local helpers. -/
theorem exists_card_filter_le {n k : ℕ} (U : Finset (Bits n))
    (hne : U.Nonempty)
    (hclosed : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      (fun i => xor (x i) (xor (y i) (z i))) ∈ U)
    (hdensity : 2 ^ n ≤ 2 ^ k * U.card) :
    ∃ x ∈ U, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ k :=
  exists_weight_le U hne hclosed hdensity

end ImpactStabilizerLowWeight


end


section

namespace ImpactStabilizerAmplitude

open StabilizerRank

def weight {n : ℕ} (x : Bits n) : ℕ :=
  (Finset.univ.filter (fun i => x i)).card

theorem angle_bounds :
    0 < Real.sin (Real.pi / 8) ∧
    Real.sin (Real.pi / 8) < Real.cos (Real.pi / 8) ∧
    0 < Real.cos (Real.pi / 8) := by
  have hp := Real.pi_pos
  have hs : 0 < Real.sin (Real.pi / 8) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsc : Real.sin (Real.pi / 8) < Real.cos (Real.pi / 8) := by
    rw [← Real.sin_pi_div_two_sub]
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith
  exact ⟨hs, hsc, hs.trans hsc⟩

theorem amplitude_formula {n : ℕ} (x : Bits n) :
    hState n x =
      ((Real.cos (Real.pi / 8) ^ n *
        (Real.sin (Real.pi / 8) / Real.cos (Real.pi / 8)) ^ weight x : ℝ) : ℂ) := by
  classical
  have hc := ne_of_gt angle_bounds.2.2
  have hprod : hState n x =
      ∏ i : Fin n, ((Real.cos (Real.pi / 8) : ℂ) *
        if x i then ((Real.sin (Real.pi / 8) / Real.cos (Real.pi / 8) : ℝ) : ℂ)
        else 1) := by
    unfold hState
    apply Finset.prod_congr rfl
    intro i hi
    cases x i
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    · simp only [↓reduceIte, ← Complex.ofReal_mul]
      congr 1
      exact (mul_div_cancel₀ _ hc).symm
  rw [hprod, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_ite, Finset.prod_const, one_pow, mul_one,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, weight]

theorem amplitude_eq_iff_weight_eq {n : ℕ} (x y : Bits n) :
    hState n x = hState n y ↔ weight x = weight y := by
  obtain ⟨hs, hsc, hc⟩ := angle_bounds
  have hr0 : 0 < Real.sin (Real.pi / 8) / Real.cos (Real.pi / 8) :=
    div_pos hs hc
  have hr1 : Real.sin (Real.pi / 8) / Real.cos (Real.pi / 8) < 1 :=
    (div_lt_one hc).2 hsc
  rw [amplitude_formula, amplitude_formula, Complex.ofReal_inj,
    mul_right_inj' (ne_of_gt (pow_pos hc n)),
    pow_right_inj₀ hr0 (ne_of_lt hr1)]

end ImpactStabilizerAmplitude

end


section

/- The computational-basis construction below is reused from Zehao Jin, accepted
submission cd113c75-bb06-4170-9fc9-a29a19671a9b. The final statements expose
the decomposition witness and attainment needed for the lower-bound proof. -/

/-!
# The stabilizer rank of any `n`-qubit state is at most `2^n`

Every computational basis state `|y⟩` is a stabilizer state: it is the image of `|0…0⟩` under
the Pauli `X`-string `X^y`, which is a Clifford unitary (it is a self-adjoint involution and
conjugates `i^c X^a Z^b` to `i^c (-1)^{b·y} X^a Z^b`).  Expanding `ψ = ∑_y ψ(y) |y⟩` over the
`2^n` basis states therefore exhibits `ψ` as a linear combination of `2^n` stabilizer states.
-/

namespace ImpactStabilizerRankWitness

open StabilizerRank

variable {n : ℕ}

/-! ### Bit-string arithmetic -/

theorem xor_xor_self (a x : Bits n) : (fun i => xor (a i) (xor (a i) (x i))) = x := by
  funext i
  cases a i <;> cases x i <;> rfl

theorem xor_eq_iff (a x y : Bits n) :
    (y = fun i => xor (a i) (x i)) ↔ (x = fun i => xor (a i) (y i)) := by
  constructor
  · rintro rfl
    exact (xor_xor_self a x).symm
  · rintro rfl
    exact (xor_xor_self a y).symm

theorem xor_inj (a x y : Bits n) :
    ((fun i => xor (a i) (x i)) = fun i => xor (a i) (y i)) ↔ x = y := by
  simp [funext_iff]

/-! ### The sign `(-1)^(b·x)` and its multiplicativity in `x` -/

/-- The sign `(-1)^{b·x}` appearing in the action of `Z^b`. -/
noncomputable def sgn (b x : Bits n) : ℂ :=
  (-1 : ℂ) ^ (Finset.univ.filter (fun i => b i && x i)).card

theorem neg_one_pow_card_filter (p : Fin n → Prop) [DecidablePred p] :
    (-1 : ℂ) ^ (Finset.univ.filter p).card = ∏ i, (if p i then (-1 : ℂ) else 1) := by
  rw [← Finset.prod_const, Finset.prod_filter]

theorem sgn_xor (b a x : Bits n) : sgn b (fun i => xor (a i) (x i)) = sgn b a * sgn b x := by
  unfold sgn
  rw [neg_one_pow_card_filter, neg_one_pow_card_filter, neg_one_pow_card_filter,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rcases Bool.eq_false_or_eq_true (b i) with hb | hb <;>
  rcases Bool.eq_false_or_eq_true (a i) with ha | ha <;>
  rcases Bool.eq_false_or_eq_true (x i) with hx | hx <;>
  simp [hb, ha, hx]

/-! ### Entries of Pauli matrices -/

theorem pauliMatrix_apply (a b y x : Bits n) :
    pauliMatrix a b y x = if y = (fun i => xor (a i) (x i)) then sgn b x else 0 := rfl

theorem pauliX_apply (a y x : Bits n) :
    pauliMatrix a 0 y x = if y = (fun i => xor (a i) (x i)) then 1 else 0 := by
  show pauliMatrix a (fun _ => false) y x = _
  simp [pauliMatrix]

theorem star_pauliX (a : Bits n) : star (pauliMatrix a 0) = pauliMatrix a 0 := by
  ext y x
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, pauliX_apply, pauliX_apply]
  by_cases h : y = fun i => xor (a i) (x i)
  · rw [if_pos ((xor_eq_iff a x y).mp h), if_pos h, star_one]
  · rw [if_neg (fun h' => h ((xor_eq_iff a x y).mpr h')), if_neg h, star_zero]

theorem pauliX_mul_pauliX (a : Bits n) : pauliMatrix a 0 * pauliMatrix a 0 = 1 := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single (fun i => xor (a i) (y i))]
  · rw [pauliX_apply, pauliX_apply, Matrix.one_apply, if_pos (xor_xor_self a y).symm, one_mul]
    simp only [xor_inj]
  · intro z _ hz
    rw [pauliX_apply, if_neg, zero_mul]
    intro h
    exact hz ((xor_eq_iff a z y).mp h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pauliX_unitary (a : Bits n) : pauliMatrix a 0 ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_pauliX, pauliX_mul_pauliX]

/-! ### Conjugation by an `X`-string -/

theorem pauliX_mul_apply (y : Bits n) (M : Matrix (Bits n) (Bits n) ℂ) (u z : Bits n) :
    (pauliMatrix y 0 * M) u z = M (fun i => xor (y i) (u i)) z := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (fun i => xor (y i) (u i))]
  · rw [pauliX_apply, if_pos (xor_xor_self y u).symm, one_mul]
  · intro w _ hw
    rw [pauliX_apply, if_neg, zero_mul]
    intro h
    exact hw ((xor_eq_iff y w u).mp h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_pauliX_apply (y : Bits n) (M : Matrix (Bits n) (Bits n) ℂ) (u x : Bits n) :
    (M * pauliMatrix y 0) u x = M u (fun i => xor (y i) (x i)) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (fun i => xor (y i) (x i))]
  · rw [pauliX_apply, if_pos rfl, mul_one]
  · intro w _ hw
    rw [pauliX_apply, if_neg hw, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem xor_conj_eq (y a x : Bits n) :
    (fun i => xor (y i) (xor (a i) (xor (y i) (x i)))) = fun i => xor (a i) (x i) := by
  funext i
  cases y i <;> cases a i <;> cases x i <;> rfl

theorem pauliX_conj (y a b : Bits n) :
    pauliMatrix y 0 * pauliMatrix a b * pauliMatrix y 0 = sgn b y • pauliMatrix a b := by
  ext u x
  rw [mul_pauliX_apply, pauliX_mul_apply, Matrix.smul_apply, pauliMatrix_apply,
    pauliMatrix_apply, smul_eq_mul, sgn_xor]
  have hc : ((fun i => xor (y i) (u i)) = fun i => xor (a i) (xor (y i) (x i))) ↔
      (u = fun i => xor (a i) (x i)) := by
    rw [eq_comm, xor_eq_iff, xor_conj_eq]
  by_cases h : u = fun i => xor (a i) (x i)
  · rw [if_pos (hc.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, mul_zero]

theorem pauliX_clifford (y : Bits n) : IsCliffordUnitary (pauliMatrix y 0) := by
  refine ⟨pauliX_unitary y, ?_⟩
  intro P hP
  obtain ⟨c, a, b, rfl⟩ := hP
  rw [star_pauliX, Matrix.mul_smul, Matrix.smul_mul, pauliX_conj, smul_smul]
  refine ⟨⟨((c : ℕ) + 2 * (Finset.univ.filter (fun i => b i && y i)).card) % 4,
    Nat.mod_lt _ (by norm_num)⟩, a, b, ?_⟩
  congr 1
  rw [Fin.val_mk, ← Complex.I_pow_eq_pow_mod, pow_add, pow_mul, Complex.I_sq]
  rfl

/-! ### Computational basis states are stabilizer states -/

theorem pauliX_mulVec_zeroState (y : Bits n) :
    (pauliMatrix y 0).mulVec (zeroState n) = fun x => if x = y then 1 else 0 := by
  funext x
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp only [zeroState, pauliX_apply, if_true, mul_one]
    simp
  · intro z _ hz
    simp only [zeroState]
    rw [if_neg hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem basis_isStabilizerState (y : Bits n) :
    IsStabilizerState (fun x => if x = y then (1 : ℂ) else 0) :=
  ⟨pauliMatrix y 0, pauliX_clifford y, (pauliX_mulVec_zeroState y).symm⟩

theorem card_bits : Fintype.card (Bits n) = 2 ^ n := by
  simp [Bits, Fintype.card_bool, Fintype.card_fin]



theorem decomposition_exists (n : ℕ) (ψ : QState n) :
    ∃ (c : Fin (2 ^ n) → ℂ) (φ : Fin (2 ^ n) → QState n),
      (∀ j, IsStabilizerState (φ j)) ∧ ∀ x, ψ x = ∑ j, c j * φ j x := by
  let e : Fin (2 ^ n) ≃ Bits n := (Fintype.equivFinOfCardEq card_bits).symm
  refine ⟨fun j => ψ (e j), fun j x => if x = e j then 1 else 0,
    fun j => basis_isStabilizerState (e j), ?_⟩
  intro x
  rw [Finset.sum_eq_single (e.symm x)]
  · simp
  · intro j _ hj
    dsimp only
    rw [if_neg, mul_zero]
    intro h
    apply hj
    rw [h, Equiv.symm_apply_apply]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem rank_attained (n : ℕ) (ψ : QState n) :
    ∃ (c : Fin (stabRank ψ) → ℂ) (φ : Fin (stabRank ψ) → QState n),
      (∀ j, IsStabilizerState (φ j)) ∧ ∀ x, ψ x = ∑ j, c j * φ j x := by
  let S : Set ℕ := {r | ∃ (c : Fin r → ℂ) (φ : Fin r → QState n),
    (∀ j, IsStabilizerState (φ j)) ∧ ∀ x, ψ x = ∑ j, c j * φ j x}
  have hS : S.Nonempty := ⟨2 ^ n, decomposition_exists n ψ⟩
  exact Nat.sInf_mem hS

end ImpactStabilizerRankWitness

end


section
namespace ImpactStabilizerFinal

open StabilizerRank

/-- The collision property isolates the finite geometry from rank attainment. -/
def FamilyCollision : Prop :=
  ∀ (n r : ℕ), 200 * r < n → ∀ (φ : Fin r → QState n),
    (∀ j, IsStabilizerState (φ j)) →
    ∃ x y : Bits n, ImpactStabilizerAmplitude.weight x ≠
      ImpactStabilizerAmplitude.weight y ∧ ∀ j, φ j x = φ j y

theorem linear_bound_of_collision (hcollision : FamilyCollision) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ≤ (stabRank (hState n) : ℝ) := by
  refine ⟨1 / 200, by norm_num, 1, ?_⟩
  intro n hn
  have hnat : n ≤ 200 * stabRank (hState n) := by
    by_contra h
    have hlt : 200 * stabRank (hState n) < n := by omega
    obtain ⟨c, φ, hφ, hrepr⟩ :=
      ImpactStabilizerRankWitness.rank_attained n (hState n)
    obtain ⟨x, y, hweight, hsame⟩ := hcollision n _ hlt φ hφ
    apply hweight
    apply (ImpactStabilizerAmplitude.amplitude_eq_iff_weight_eq x y).1
    rw [hrepr x, hrepr y]
    exact Finset.sum_congr rfl (fun j _ => congrArg (c j * ·) (hsame j))
  have hreal : (n : ℝ) ≤ 200 * (stabRank (hState n) : ℝ) := by
    exact_mod_cast hnat
  linarith

end ImpactStabilizerFinal

end


section
namespace ImpactStabilizerFinal

open StabilizerRank

theorem family_collision : FamilyCollision := by
  classical
  intro n r hn φ hφ
  obtain ⟨U, hUa, hUd, hUs⟩ :=
    StabilizerAffineIntegration.stabilizer_indicator_region φ hφ
  have hU : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      bitTranslate x (bitTranslate y z) ∈ U := by
    intro x hx y hy z hz
    have h := hUa.2 x hx y hy z hz
    change bitTranslate (bitTranslate x y) z ∈ U at h
    rwa [← bitTranslate_assoc] at h
  obtain ⟨F, hF⟩ := stabilizer_family_coloring φ hφ
  have hd : 2 ^ n ≤ 2 ^ (3 * (3 * r)) * U.card := by
    exact hUd.trans (Nat.mul_le_mul_right U.card
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))
  obtain ⟨a, ha, b, hb, hab, hfar⟩ :=
    Counting.collision (r := 3 * r) (by omega) U hd F
  obtain ⟨V, hVU, haV, hV, hcard, hsame⟩ :=
    stabilizer_phase_cut φ hφ U hU (fun j => (hUs j).symm)
      a b ha hb (hF a b hab)
  have hVd : 2 ^ n ≤ 2 ^ (2 * r) * V.card := by
    calc
      2 ^ n ≤ 2 ^ r * U.card := hUd
      _ ≤ 2 ^ r * (2 ^ r * V.card) := Nat.mul_le_mul_left _ hcard
      _ = 2 ^ (2 * r) * V.card := by rw [← mul_assoc, ← pow_add]; congr 2; omega
  obtain ⟨x, hx, hw⟩ := ImpactStabilizerLowWeight.exists_weight_le V
    ⟨a, haV⟩ hV hVd
  let y := bitTranslate (bitTranslate a b) x
  have hxy : bitTranslate x y = bitTranslate a b := by
    funext i
    dsimp only [y, bitTranslate]
    cases a i <;> cases b i <;> cases x i <;> rfl
  have hfar' : 8 * (3 * r) <
      ImpactStabilizerLowWeight.weight (bitTranslate a b) := hfar
  have hdist : 2 * ImpactStabilizerLowWeight.weight x <
      ImpactStabilizerLowWeight.weight (bitTranslate x y) := by
    rw [hxy]
    omega
  have hne := ImpactStabilizerLowWeight.weight_ne_of_two_mul_lt_xor x y hdist
  refine ⟨x, y, hne, fun j => (hsame x hx j).symm⟩

end ImpactStabilizerFinal

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ≤ (StabilizerRank.stabRank (StabilizerRank.hState n) : ℝ) :=
  ImpactStabilizerFinal.linear_bound_of_collision ImpactStabilizerFinal.family_collision
end
