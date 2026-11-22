-- Prove2me | solution 1 for StabilizerRank.stabRank_hState_six_le_seven
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-08T02:50:21.916318+00:00
-- url     : https://prove2.me/submissions/0bd59054-e0ff-43e6-97a7-ac2d1a57a996

import Definitions.Def_StabilizerRank

open scoped BigOperators

namespace StabilizerRank

private noncomputable def zPhase {n : ℕ} (b x : Bits n) : ℂ :=
  (-1 : ℂ) ^ (Finset.univ.filter (fun i => b i && x i)).card

private theorem pauliMatrix_mulVec {n : ℕ} (a b : Bits n) (v : QState n) (y : Bits n) :
    (pauliMatrix a b).mulVec v y =
      zPhase b (fun i => xor (a i) (y i)) * v (fun i => xor (a i) (y i)) := by
  classical
  simp only [pauliMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (fun i => xor (a i) (y i))]
  · simp [zPhase]
  · intro x _ hx
    have hne : y ≠ (fun i => xor (a i) (x i)) := by
      intro h
      apply hx
      funext i
      have hi := congr_fun h i
      cases hai : a i <;> cases hyi : y i <;> cases hxi : x i <;> simp_all
    simp [hne]
  · simp

private theorem isCliffordUnitary_one {n : ℕ} :
    IsCliffordUnitary (1 : Matrix (Bits n) (Bits n) ℂ) := by
  constructor
  · exact Submonoid.one_mem _
  · intro P hP
    simpa using hP

private theorem IsCliffordUnitary.mul {n : ℕ}
    {U V : Matrix (Bits n) (Bits n) ℂ}
    (hU : IsCliffordUnitary U) (hV : IsCliffordUnitary V) :
    IsCliffordUnitary (U * V) := by
  constructor
  · exact (Matrix.unitaryGroup (Bits n) ℂ).mul_mem hU.1 hV.1
  · intro P hP
    rw [star_mul]
    simpa only [Matrix.mul_assoc] using hU.2 (V * P * star V) (hV.2 P hP)

private theorem zeroState_isStabilizerState (n : ℕ) :
    IsStabilizerState (zeroState n) := by
  refine ⟨1, isCliffordUnitary_one, ?_⟩
  simpa using (Matrix.one_mulVec (zeroState n))

private theorem IsCliffordUnitary.isStabilizerState_mulVec {n : ℕ}
    {U : Matrix (Bits n) (Bits n) ℂ} (hU : IsCliffordUnitary U)
    {ψ : QState n} (hψ : IsStabilizerState ψ) :
    IsStabilizerState (U.mulVec ψ) := by
  rcases hψ with ⟨V, hV, rfl⟩
  refine ⟨U * V, hU.mul hV, ?_⟩
  exact Matrix.mulVec_mulVec (zeroState n) U V

private theorem permutationMatrix_isCliffordUnitary {n : ℕ}
    (σ : Equiv.Perm (Bits n)) (mapA mapB : Bits n → Bits n)
    (htranslate :
      ∀ a x, σ (fun i => xor ((mapA a) i) (x i)) = fun i => xor (a i) ((σ x) i))
    (hphase : ∀ b x, zPhase b (σ x) = zPhase (mapB b) x) :
    IsCliffordUnitary (σ.permMatrix ℂ) := by
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix]
    rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  · rintro P ⟨c, a, b, rfl⟩
    refine ⟨c, mapA a, mapB b, ?_⟩
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    funext y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [Matrix.permMatrix_mulVec, Function.comp_apply, pauliMatrix_mulVec]
    rw [← htranslate, hphase]
    simp

private def dotCount {n : ℕ} (b x : Bits n) : ℕ :=
  (Finset.univ.filter (fun i => b i && x i)).card

private noncomputable def signValue {n : ℕ} (q : Bits n → Bool) (x : Bits n) : ℂ :=
  if q x then -1 else 1

private noncomputable def signMatrix {n : ℕ} (q : Bits n → Bool) :
    Matrix (Bits n) (Bits n) ℂ :=
  Matrix.diagonal (signValue q)

private theorem zPhase_eq_I_pow {n : ℕ} (b x : Bits n) :
    zPhase b x = Complex.I ^ (2 * (dotCount b x % 2)) := by
  change (-1 : ℂ) ^ dotCount b x = Complex.I ^ (2 * (dotCount b x % 2))
  rw [neg_one_pow_eq_pow_mod_two]
  have hmod : dotCount b x % 2 = 0 ∨ dotCount b x % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · simp [hmod]
  · simp [hmod, Complex.I_sq]

private theorem signValue_eq_I_pow {n : ℕ} (q : Bits n → Bool) (x : Bits n) :
    signValue q x = Complex.I ^ (2 * (q x).toNat) := by
  cases hqx : q x <;> simp [signValue, hqx, Complex.I_sq]

private theorem I_pow_eq_of_mod_four {m k : ℕ} (h : m % 4 = k % 4) :
    Complex.I ^ m = Complex.I ^ k := by
  calc
    Complex.I ^ m = Complex.I ^ (m % 4) := Complex.I_pow_eq_pow_mod m
    _ = Complex.I ^ (k % 4) := congrArg (Complex.I ^ ·) h
    _ = Complex.I ^ k := (Complex.I_pow_eq_pow_mod k).symm

private theorem signMatrix_mulVec {n : ℕ} (q : Bits n → Bool)
    (v : QState n) (x : Bits n) :
    (signMatrix q).mulVec v x = signValue q x * v x := by
  classical
  exact Matrix.mulVec_diagonal (signValue q) v x

private theorem signMatrix_isCliffordUnitary {n : ℕ}
    (q : Bits n → Bool)
    (mapC : Fin 4 → Bits n → Bits n → Fin 4)
    (mapB : Bits n → Bits n → Bits n)
    (hphase :
      ∀ c a b y,
        (c.val + 2 * (q y).toNat + 2 * (dotCount b (fun i => xor (a i) (y i)) % 2) +
          2 * (q (fun i => xor (a i) (y i))).toNat) % 4 =
        ((mapC c a b).val +
          2 * (dotCount (mapB a b) (fun i => xor (a i) (y i)) % 2)) % 4) :
    IsCliffordUnitary (signMatrix q) := by
  classical
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext y x
    by_cases hyx : y = x
    · subst x
      cases hqy : q y <;> simp [signMatrix, signValue, hqy]
    · simp [signMatrix, hyx]
  · rintro P ⟨c, a, b, rfl⟩
    refine ⟨mapC c a b, a, mapB a b, ?_⟩
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    funext y
    rw [Matrix.star_eq_conjTranspose]
    have hstar : Matrix.conjTranspose (signMatrix q) = signMatrix q := by
      ext x z
      by_cases hxz : x = z
      · subst z
        cases hqx : q x <;> simp [signMatrix, signValue, hqx]
      · simp [signMatrix, hxz, Ne.symm hxz]
    rw [hstar, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [Matrix.smul_mulVec, Pi.smul_apply, signMatrix_mulVec,
      pauliMatrix_mulVec, smul_eq_mul]
    rw [signValue_eq_I_pow, signValue_eq_I_pow, zPhase_eq_I_pow,
      zPhase_eq_I_pow]
    have hpow := I_pow_eq_of_mod_four (hphase c a b y)
    calc
      _ = Complex.I ^
            (c.val + 2 * (q y).toNat +
              2 * (dotCount b (fun i => xor (a i) (y i)) % 2) +
              2 * (q (fun i => xor (a i) (y i))).toNat) *
            v (fun i => xor (a i) (y i)) := by
          simp only [pow_add]
          ring
      _ = Complex.I ^
            ((mapC c a b).val +
              2 * (dotCount (mapB a b) (fun i => xor (a i) (y i)) % 2)) *
            v (fun i => xor (a i) (y i)) := by rw [hpow]
      _ = _ := by
        simp only [pow_add]
        ring

private def addTwoIf (c : Fin 4) (p : Bool) : Fin 4 :=
  ⟨(c.val + 2 * p.toNat) % 4, Nat.mod_lt _ (by omega)⟩

private theorem addTwoIf_addTwoIf (c : Fin 4) (p q : Bool) :
    addTwoIf (addTwoIf c p) q = addTwoIf c (p + q) := by
  decide +revert

private theorem phase_three_val (c : Fin 4) (p q r : Bool) :
    (c.val + 2 * p.toNat + 2 * q.toNat + 2 * r.toNat) % 4 =
      (addTwoIf (addTwoIf (addTwoIf c p) q) r).val := by
  decide +revert

private theorem bool_z_phase_identity (a y d : Bool) :
    y + (d + (a + y)) = a + d := by
  decide +revert

private theorem bool_cz_phase_identity (ai aj yi yj d : Bool) :
    yi * yj + (d + (ai + yi) * (aj + yj)) =
      ai * aj + (d + aj * (ai + yi) + ai * (aj + yj)) := by
  decide +revert

private def dotBool (b x : Bits 6) : Bool :=
  ∑ i, b i * x i

private def bitsAdd (x y : Bits 6) : Bits 6 :=
  fun i => x i + y i

private theorem bool_sum_toNat_eq_filter_card_mod_two
    {α : Type} (s : Finset α) (f : α → Bool) :
    Bool.toNat (s.sum f) =
      (s.filter (fun i => f i = true)).card % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Bool.zero_eq_false]
  | @insert a s ha ih =>
      cases hfa : f a <;>
        cases hsum : s.sum f <;>
        simp [Finset.sum_insert, Finset.filter_insert, ha, hfa, hsum,
          Bool.zero_eq_false, Bool.one_eq_true, Bool.add_eq_xor] at ih ⊢ <;>
        omega

private theorem dotCount_mod_two_eq_dotBool :
    ∀ b x : Bits 6, dotCount b x % 2 = (dotBool b x).toNat := by
  intro b x
  unfold dotCount dotBool
  simpa [Bool.mul_eq_and] using
    (bool_sum_toNat_eq_filter_card_mod_two
      (Finset.univ : Finset (Fin 6)) (fun i => b i * x i)).symm

private theorem signMatrixSix_isCliffordUnitary
    (q : Bits 6 → Bool)
    (mapC : Fin 4 → Bits 6 → Bits 6 → Fin 4)
    (mapB : Bits 6 → Bits 6 → Bits 6)
    (hphase :
      ∀ c a b y,
        addTwoIf
            (addTwoIf (addTwoIf c (q y))
              (dotBool b (fun i => xor (a i) (y i))))
            (q (fun i => xor (a i) (y i))) =
          addTwoIf (mapC c a b)
            (dotBool (mapB a b) (fun i => xor (a i) (y i)))) :
    IsCliffordUnitary (signMatrix q) := by
  apply signMatrix_isCliffordUnitary (mapC := mapC) (mapB := mapB)
  intro c a b y
  rw [dotCount_mod_two_eq_dotBool b (fun i => xor (a i) (y i)),
    dotCount_mod_two_eq_dotBool (mapB a b) (fun i => xor (a i) (y i))]
  calc
    (c.val + 2 * (q y).toNat +
        2 * (dotBool b (fun i => xor (a i) (y i))).toNat +
        2 * (q (fun i => xor (a i) (y i))).toNat) % 4 =
      (addTwoIf
          (addTwoIf (addTwoIf c (q y))
            (dotBool b (fun i => xor (a i) (y i))))
          (q (fun i => xor (a i) (y i)))).val :=
        phase_three_val _ _ _ _
    _ = (addTwoIf (mapC c a b)
          (dotBool (mapB a b) (fun i => xor (a i) (y i)))).val :=
      congrArg Fin.val (hphase c a b y)
    _ = ((mapC c a b).val +
          2 * (dotBool (mapB a b) (fun i => xor (a i) (y i))).toNat) % 4 := rfl

private theorem dotBool_add (b d x : Bits 6) :
    dotBool (fun i => b i + d i) x = dotBool b x + dotBool d x := by
  simp [dotBool, add_mul, Finset.sum_add_distrib]

private theorem dotBool_bitsAdd_left (b d x : Bits 6) :
    dotBool (bitsAdd b d) x = dotBool b x + dotBool d x := by
  exact dotBool_add b d x

private theorem dotBool_bitsAdd_right (b x y : Bits 6) :
    dotBool b (bitsAdd x y) = dotBool b x + dotBool b y := by
  simp [dotBool, bitsAdd, mul_add, Finset.sum_add_distrib]

private def singleBit (i : Fin 6) (p : Bool) : Bits 6 :=
  fun k => if k = i then p else false

private theorem dotBool_singleBit (i : Fin 6) (p : Bool) (x : Bits 6) :
    dotBool (singleBit i p) x = p * x i := by
  classical
  unfold dotBool
  rw [Finset.sum_eq_single i]
  · simp [singleBit]
  · intro k _ hki
    simpa only [singleBit, if_neg hki, Bool.zero_eq_false] using
      (zero_mul (x k) : (0 : Bool) * x k = 0)
  · simp

private theorem zPhase_eq_if_dotBool (b x : Bits 6) :
    zPhase b x = if dotBool b x then -1 else 1 := by
  rw [zPhase_eq_I_pow, dotCount_mod_two_eq_dotBool]
  cases h : dotBool b x <;> simp [h, Complex.I_sq]

private theorem if_neg_one_mul_if_neg_one (p q : Bool) :
    (if p then (-1 : ℂ) else 1) * (if q then -1 else 1) =
      if p + q then -1 else 1 := by
  cases p <;> cases q <;> simp [Bool.add_eq_xor]

private theorem bool_mul_two_eq_zero (p : Bool) :
    p * 2 = 0 := by
  decide +revert

private theorem zPhase_pauli_mul_identity
    (a b d e y : Bits 6) :
    zPhase b (bitsAdd a y) * zPhase e (bitsAdd d (bitsAdd a y)) =
      zPhase b d * zPhase (bitsAdd b e) (bitsAdd d (bitsAdd a y)) := by
  have hparity :
      dotBool b (bitsAdd a y) +
          dotBool e (bitsAdd d (bitsAdd a y)) =
        dotBool b d +
          dotBool (bitsAdd b e) (bitsAdd d (bitsAdd a y)) := by
    simp only [dotBool_bitsAdd_left, dotBool_bitsAdd_right]
    ring_nf
    rw [bool_mul_two_eq_zero, add_zero]
  rw [zPhase_eq_if_dotBool, zPhase_eq_if_dotBool,
    zPhase_eq_if_dotBool, zPhase_eq_if_dotBool,
    if_neg_one_mul_if_neg_one, if_neg_one_mul_if_neg_one, hparity]

private theorem pauliMatrix_mul_six (a b d e : Bits 6) :
    pauliMatrix a b * pauliMatrix d e =
      zPhase b d • pauliMatrix (bitsAdd a d) (bitsAdd b e) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext y
  rw [← Matrix.mulVec_mulVec, pauliMatrix_mulVec, pauliMatrix_mulVec,
    Matrix.smul_mulVec, Pi.smul_apply, pauliMatrix_mulVec]
  simp only [← Bool.add_eq_xor]
  change
    zPhase b (bitsAdd a y) *
        (zPhase e (bitsAdd d (bitsAdd a y)) *
          v (bitsAdd d (bitsAdd a y))) =
      zPhase b d *
        (zPhase (bitsAdd b e) (bitsAdd (bitsAdd a d) y) *
          v (bitsAdd (bitsAdd a d) y))
  have harg :
      bitsAdd d (bitsAdd a y) = bitsAdd (bitsAdd a d) y := by
    funext k
    simp [bitsAdd, add_assoc, add_comm, add_left_comm]
  have hphase := zPhase_pauli_mul_identity a b d e y
  rw [harg] at hphase ⊢
  calc
    _ = (zPhase b (bitsAdd a y) *
          zPhase e (bitsAdd (bitsAdd a d) y)) *
          v (bitsAdd (bitsAdd a d) y) := by ring
    _ = (zPhase b d *
          zPhase (bitsAdd b e) (bitsAdd (bitsAdd a d) y)) *
          v (bitsAdd (bitsAdd a d) y) := by rw [hphase]
    _ = _ := by ring

private def zGatePhase (i : Fin 6) (x : Bits 6) : Bool :=
  x i

private theorem zGate_isCliffordUnitary (i : Fin 6) :
    IsCliffordUnitary (signMatrix (zGatePhase i)) := by
  apply signMatrixSix_isCliffordUnitary
      (mapC := fun c a _ => addTwoIf c (a i))
      (mapB := fun _ b => b)
  intro c a b y
  rw [addTwoIf_addTwoIf, addTwoIf_addTwoIf, addTwoIf_addTwoIf]
  congr 1
  simp only [zGatePhase, ← Bool.add_eq_xor]
  exact bool_z_phase_identity _ _ _

private def czGatePhase (i j : Fin 6) (x : Bits 6) : Bool :=
  x i && x j

private def czMapB (i j : Fin 6) (a b : Bits 6) : Bits 6 :=
  fun k => b k + singleBit i (a j) k + singleBit j (a i) k

private theorem dotBool_czMapB (i j : Fin 6) (a b x : Bits 6) :
    dotBool (czMapB i j a b) x =
      dotBool b x + a j * x i + a i * x j := by
  change dotBool
      (fun k => (b k + singleBit i (a j) k) + singleBit j (a i) k) x = _
  rw [dotBool_add, dotBool_add, dotBool_singleBit, dotBool_singleBit]

private theorem czGate_isCliffordUnitary (i j : Fin 6) (hij : i ≠ j) :
    IsCliffordUnitary (signMatrix (czGatePhase i j)) := by
  apply signMatrixSix_isCliffordUnitary
      (mapC := fun c a _ => addTwoIf c (a i && a j))
      (mapB := czMapB i j)
  intro c a b y
  rw [addTwoIf_addTwoIf, addTwoIf_addTwoIf, addTwoIf_addTwoIf]
  congr 1
  rw [dotBool_czMapB]
  simp only [czGatePhase, ← Bool.add_eq_xor, ← Bool.mul_eq_and]
  exact bool_cz_phase_identity _ _ _ _ _

private theorem signMatrix_conjTranspose (q : Bits 6 → Bool) :
    Matrix.conjTranspose (signMatrix q) = signMatrix q := by
  ext x y
  by_cases hxy : x = y
  · subst y
    cases hqx : q x <;> simp [signMatrix, signValue, hqx]
  · simp [signMatrix, hxy, Ne.symm hxy]

private def zeroBits : Bits 6 :=
  fun _ => false

private def toggleBits (i : Fin 6) (x : Bits 6) : Bits 6 :=
  fun k => xor (singleBit i true k) (x k)

private theorem toggleBits_involutive (i : Fin 6) :
    Function.Involutive (toggleBits i) := by
  intro x
  funext k
  by_cases hki : k = i
  · subst k
    simp [toggleBits, singleBit]
  · simp [toggleBits, singleBit, hki]

private def togglePerm (i : Fin 6) : Equiv.Perm (Bits 6) :=
  { toFun := toggleBits i
    invFun := toggleBits i
    left_inv := toggleBits_involutive i
    right_inv := toggleBits_involutive i }

private theorem togglePerm_apply_at (i : Fin 6) (x : Bits 6) :
    togglePerm i x i = !x i := by
  change toggleBits i x i = !x i
  simp [toggleBits, singleBit]

private theorem togglePerm_apply (i k : Fin 6) (x : Bits 6) :
    togglePerm i x k = if k = i then !x k else x k := by
  change toggleBits i x k = if k = i then !x k else x k
  by_cases hki : k = i
  · subst k
    simp [toggleBits, singleBit]
  · simp [toggleBits, singleBit, hki]

private theorem xPauli_eq_permMatrix (i : Fin 6) :
    pauliMatrix (singleBit i true) zeroBits = (togglePerm i).permMatrix ℂ := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext y
  rw [pauliMatrix_mulVec, Matrix.permMatrix_mulVec]
  change zPhase zeroBits (toggleBits i y) * v (toggleBits i y) =
    v (toggleBits i y)
  simp [zPhase, zeroBits]

private theorem zPhase_singleBit (i : Fin 6) (x : Bits 6) :
    zPhase (singleBit i true) x = signValue (zGatePhase i) x := by
  rw [zPhase_eq_I_pow, dotCount_mod_two_eq_dotBool,
    dotBool_singleBit]
  cases hxi : x i <;>
    simp [signValue, zGatePhase, hxi, Bool.mul_eq_and, Complex.I_sq]

private theorem zPauli_eq_signMatrix (i : Fin 6) :
    pauliMatrix zeroBits (singleBit i true) = signMatrix (zGatePhase i) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext y
  rw [pauliMatrix_mulVec, signMatrix_mulVec, zPhase_singleBit]
  simp [zeroBits]

private noncomputable def invSqrtTwo : ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ)

private theorem invSqrtTwo_mul_self :
    invSqrtTwo * invSqrtTwo = (2 : ℂ)⁻¹ := by
  change (↑((Real.sqrt 2)⁻¹) : ℂ) * ↑((Real.sqrt 2)⁻¹) = (2 : ℂ)⁻¹
  rw [← Complex.ofReal_mul, TsirelsonInequality.sqrt_two_inv_mul_self]
  norm_num

private theorem invSqrtTwo_self_add :
    invSqrtTwo * invSqrtTwo + invSqrtTwo * invSqrtTwo = 1 := by
  rw [invSqrtTwo_mul_self]
  norm_num

private theorem invSqrtTwo_sq_mul_two :
    invSqrtTwo ^ 2 * 2 = 1 := by
  calc
    invSqrtTwo ^ 2 * 2 =
        invSqrtTwo * invSqrtTwo + invSqrtTwo * invSqrtTwo := by ring
    _ = 1 := invSqrtTwo_self_add

private noncomputable def hadamardMatrix (i : Fin 6) :
    Matrix (Bits 6) (Bits 6) ℂ :=
  invSqrtTwo •
    (pauliMatrix (singleBit i true) zeroBits +
      pauliMatrix zeroBits (singleBit i true))

private theorem hadamardMatrix_mulVec (i : Fin 6) (v : QState 6) (y : Bits 6) :
    (hadamardMatrix i).mulVec v y =
      invSqrtTwo *
        (v (togglePerm i y) + signValue (zGatePhase i) y * v y) := by
  rw [hadamardMatrix, Matrix.smul_mulVec, Pi.smul_apply, Matrix.add_mulVec,
    Pi.add_apply, xPauli_eq_permMatrix, Matrix.permMatrix_mulVec,
    zPauli_eq_signMatrix, signMatrix_mulVec]
  rfl

private theorem togglePerm_involutive (i : Fin 6) :
    Function.Involutive (togglePerm i) :=
  toggleBits_involutive i

private theorem xPauli_conjTranspose (i : Fin 6) :
    Matrix.conjTranspose (pauliMatrix (singleBit i true) zeroBits) =
      pauliMatrix (singleBit i true) zeroBits := by
  rw [xPauli_eq_permMatrix, Matrix.conjTranspose_permMatrix]
  have hinv : (togglePerm i)⁻¹ = togglePerm i :=
    Function.Involutive.symm_eq_self_of_involutive
      (togglePerm i) (togglePerm_involutive i)
  rw [hinv]

private theorem star_invSqrtTwo :
    star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

private theorem hadamardMatrix_conjTranspose (i : Fin 6) :
    Matrix.conjTranspose (hadamardMatrix i) = hadamardMatrix i := by
  rw [hadamardMatrix, Matrix.conjTranspose_smul, star_invSqrtTwo,
    Matrix.conjTranspose_add, xPauli_conjTranspose, zPauli_eq_signMatrix,
    signMatrix_conjTranspose]

private theorem hadamardMatrix_mul_self (i : Fin 6) :
    hadamardMatrix i * hadamardMatrix i = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec]
  funext y
  rw [hadamardMatrix_mulVec, hadamardMatrix_mulVec,
    hadamardMatrix_mulVec]
  have htoggle : togglePerm i (togglePerm i y) = y :=
    togglePerm_involutive i y
  have hbit : togglePerm i y i = !y i :=
    togglePerm_apply_at i y
  rw [htoggle]
  cases hyi : y i <;>
    simp [signValue, zGatePhase, hyi, hbit]
  all_goals
    calc
      _ = (invSqrtTwo * invSqrtTwo + invSqrtTwo * invSqrtTwo) * v y := by
        ring
      _ = v y := by rw [invSqrtTwo_self_add, one_mul]

private theorem dotBool_comm (b x : Bits 6) :
    dotBool b x = dotBool x b := by
  simp [dotBool, mul_comm]

private theorem dotBool_singleBit_right
    (i : Fin 6) (p : Bool) (b : Bits 6) :
    dotBool b (singleBit i p) = p * b i := by
  rw [dotBool_comm, dotBool_singleBit]

private theorem zPhase_zeroBits (x : Bits 6) :
    zPhase zeroBits x = 1 := by
  simp [zPhase, zeroBits]

private theorem zPhase_at_zeroBits (b : Bits 6) :
    zPhase b zeroBits = 1 := by
  simp [zPhase, zeroBits]

private theorem zPhase_singleBit_right (i : Fin 6) (b : Bits 6) :
    zPhase b (singleBit i true) = if b i then -1 else 1 := by
  rw [zPhase_eq_if_dotBool, dotBool_singleBit_right]
  cases hbi : b i <;> simp [hbi, Bool.mul_eq_and]

private theorem bitsAdd_comm (x y : Bits 6) :
    bitsAdd x y = bitsAdd y x := by
  funext k
  exact add_comm _ _

private theorem bitsAdd_zero_right (x : Bits 6) :
    bitsAdd x zeroBits = x := by
  funext k
  simp [bitsAdd, zeroBits, Bool.add_eq_xor]

private theorem bitsAdd_zero_left (x : Bits 6) :
    bitsAdd zeroBits x = x := by
  rw [bitsAdd_comm, bitsAdd_zero_right]

private theorem bitsAdd_singleBit_cancel (i : Fin 6) (x : Bits 6) :
    bitsAdd (bitsAdd (singleBit i true) x) (singleBit i true) = x := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [bitsAdd, singleBit, Bool.add_eq_xor]
  · simp [bitsAdd, singleBit, hki, Bool.add_eq_xor]

private theorem xPauli_conj_pauli (i : Fin 6) (a b : Bits 6) :
    pauliMatrix (singleBit i true) zeroBits *
          pauliMatrix a b *
          pauliMatrix (singleBit i true) zeroBits =
      (if b i then (-1 : ℂ) else 1) • pauliMatrix a b := by
  rw [pauliMatrix_mul_six, Matrix.smul_mul, pauliMatrix_mul_six,
    zPhase_zeroBits, one_smul, bitsAdd_zero_left,
    zPhase_singleBit_right, bitsAdd_singleBit_cancel,
    bitsAdd_zero_right]

private theorem zPauli_conj_pauli (i : Fin 6) (a b : Bits 6) :
    pauliMatrix zeroBits (singleBit i true) *
          pauliMatrix a b *
          pauliMatrix zeroBits (singleBit i true) =
      (if a i then (-1 : ℂ) else 1) • pauliMatrix a b := by
  rw [pauliMatrix_mul_six, Matrix.smul_mul, pauliMatrix_mul_six,
    zPhase_singleBit, zPhase_at_zeroBits, one_smul,
    bitsAdd_zero_left, bitsAdd_zero_right, bitsAdd_singleBit_cancel]
  cases hai : a i <;> simp [signValue, zGatePhase, hai]

private theorem xPauli_pauli_zPauli (i : Fin 6) (a b : Bits 6) :
    pauliMatrix (singleBit i true) zeroBits *
          pauliMatrix a b *
          pauliMatrix zeroBits (singleBit i true) =
      pauliMatrix (bitsAdd a (singleBit i true))
        (bitsAdd b (singleBit i true)) := by
  rw [pauliMatrix_mul_six, Matrix.smul_mul, pauliMatrix_mul_six,
    zPhase_zeroBits, one_smul, zPhase_at_zeroBits, one_smul,
    bitsAdd_zero_right, bitsAdd_zero_left]
  rw [bitsAdd_comm (singleBit i true) a]

private theorem zPauli_pauli_xPauli (i : Fin 6) (a b : Bits 6) :
    pauliMatrix zeroBits (singleBit i true) *
          pauliMatrix a b *
          pauliMatrix (singleBit i true) zeroBits =
      (if a i = b i then (-1 : ℂ) else 1) •
        pauliMatrix (bitsAdd a (singleBit i true))
          (bitsAdd b (singleBit i true)) := by
  rw [pauliMatrix_mul_six, Matrix.smul_mul, pauliMatrix_mul_six,
    zPhase_singleBit, bitsAdd_zero_left, bitsAdd_zero_right,
    zPhase_singleBit_right]
  rw [bitsAdd_comm (singleBit i true) b]
  cases hai : a i <;> cases hbi : b i <;>
    simp [signValue, zGatePhase, bitsAdd, singleBit, hai, hbi,
      Bool.add_eq_xor]

private theorem hadamardMatrix_conj_expand (i : Fin 6) (P : Matrix (Bits 6) (Bits 6) ℂ) :
    hadamardMatrix i * P * hadamardMatrix i =
      (invSqrtTwo * invSqrtTwo) •
        (pauliMatrix (singleBit i true) zeroBits * P *
            pauliMatrix (singleBit i true) zeroBits +
          pauliMatrix (singleBit i true) zeroBits * P *
            pauliMatrix zeroBits (singleBit i true) +
          pauliMatrix zeroBits (singleBit i true) * P *
            pauliMatrix (singleBit i true) zeroBits +
          pauliMatrix zeroBits (singleBit i true) * P *
            pauliMatrix zeroBits (singleBit i true)) := by
  rw [hadamardMatrix]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_mul, mul_add]
  module

private theorem singleBit_false (i : Fin 6) :
    singleBit i false = zeroBits := by
  funext k
  simp [singleBit, zeroBits]

private theorem bitsAdd_singleBit_false (i : Fin 6) (x : Bits 6) :
    bitsAdd x (singleBit i false) = x := by
  rw [singleBit_false, bitsAdd_zero_right]

private theorem invSqrtTwo_double_smul
    (M : Matrix (Bits 6) (Bits 6) ℂ) :
    (invSqrtTwo * invSqrtTwo) • M +
        (invSqrtTwo * invSqrtTwo) • M = M := by
  rw [← add_smul, invSqrtTwo_self_add, one_smul]

private def hadamardMapA (i : Fin 6) (a b : Bits 6) : Bits 6 :=
  bitsAdd a (singleBit i (a i + b i))

private def hadamardMapB (i : Fin 6) (a b : Bits 6) : Bits 6 :=
  bitsAdd b (singleBit i (a i + b i))

private theorem hadamardMatrix_conj_pauli (i : Fin 6) (a b : Bits 6) :
    hadamardMatrix i * pauliMatrix a b * hadamardMatrix i =
      (if a i && b i then (-1 : ℂ) else 1) •
        pauliMatrix (hadamardMapA i a b) (hadamardMapB i a b) := by
  rw [hadamardMatrix_conj_expand, xPauli_conj_pauli,
    xPauli_pauli_zPauli, zPauli_pauli_xPauli,
    zPauli_conj_pauli]
  cases hai : a i <;> cases hbi : b i
  all_goals
    simp [hadamardMapA, hadamardMapB, hai, hbi, bitsAdd, singleBit,
      bitsAdd_singleBit_false, Bool.add_eq_xor]
  · exact invSqrtTwo_double_smul _
  · calc
      _ = (invSqrtTwo * invSqrtTwo) •
            pauliMatrix (bitsAdd a (singleBit i true))
              (bitsAdd b (singleBit i true)) +
          (invSqrtTwo * invSqrtTwo) •
            pauliMatrix (bitsAdd a (singleBit i true))
              (bitsAdd b (singleBit i true)) := by abel
      _ = _ := invSqrtTwo_double_smul _
  · calc
      _ = (invSqrtTwo * invSqrtTwo) •
            pauliMatrix (bitsAdd a (singleBit i true))
              (bitsAdd b (singleBit i true)) +
          (invSqrtTwo * invSqrtTwo) •
            pauliMatrix (bitsAdd a (singleBit i true))
              (bitsAdd b (singleBit i true)) := by abel
      _ = _ := invSqrtTwo_double_smul _
  · calc
      _ = -((invSqrtTwo * invSqrtTwo) • pauliMatrix a b +
          (invSqrtTwo * invSqrtTwo) • pauliMatrix a b) := by abel
      _ = _ := congrArg Neg.neg (invSqrtTwo_double_smul (pauliMatrix a b))

private theorem I_pow_mul_if_neg_one (c : Fin 4) (p : Bool) :
    Complex.I ^ c.val * (if p then (-1 : ℂ) else 1) =
      Complex.I ^ (addTwoIf c p).val := by
  have hsign :
      (if p then (-1 : ℂ) else 1) = Complex.I ^ (2 * p.toNat) := by
    cases p <;> simp [Complex.I_sq]
  rw [hsign, ← pow_add]
  apply I_pow_eq_of_mod_four
  simp [addTwoIf]

private theorem hadamardMatrix_isCliffordUnitary (i : Fin 6) :
    IsCliffordUnitary (hadamardMatrix i) := by
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      hadamardMatrix_conjTranspose, hadamardMatrix_mul_self]
  · rintro P ⟨c, a, b, rfl⟩
    refine ⟨addTwoIf c (a i && b i), hadamardMapA i a b,
      hadamardMapB i a b, ?_⟩
    rw [Matrix.star_eq_conjTranspose, hadamardMatrix_conjTranspose]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [hadamardMatrix_conj_pauli, smul_smul,
      I_pow_mul_if_neg_one]

private def cnotBits (control target : Fin 6) (x : Bits 6) : Bits 6 :=
  fun k => if k = target then x k + x control else x k

private theorem cnotBits_involutive (control target : Fin 6)
    (hct : control ≠ target) :
    Function.Involutive (cnotBits control target) := by
  intro x
  funext k
  by_cases hkt : k = target
  · subst k
    simp [cnotBits, hct, Bool.add_eq_xor]
  · simp [cnotBits, hkt]

private def cnotPerm (control target : Fin 6) (hct : control ≠ target) :
    Equiv.Perm (Bits 6) :=
  { toFun := cnotBits control target
    invFun := cnotBits control target
    left_inv := cnotBits_involutive control target hct
    right_inv := cnotBits_involutive control target hct }

private def cnotMapB (control target : Fin 6) (b : Bits 6) : Bits 6 :=
  bitsAdd b (singleBit control (b target))

private theorem bool_cnot_translate_identity
    (aTarget aControl xTarget xControl : Bool) :
    ((aTarget + aControl) + xTarget) + (aControl + xControl) =
      aTarget + (xTarget + xControl) := by
  decide +revert

private theorem cnot_translate (control target : Fin 6)
    (hct : control ≠ target) (a x : Bits 6) :
    cnotPerm control target hct
        (fun i => xor ((cnotBits control target a) i) (x i)) =
      fun i => xor (a i) ((cnotPerm control target hct x) i) := by
  change cnotBits control target
      (bitsAdd (cnotBits control target a) x) =
    bitsAdd a (cnotBits control target x)
  funext k
  by_cases hkt : k = target
  · subst k
    simpa [cnotBits, bitsAdd, hct, Bool.add_eq_xor] using
      bool_cnot_translate_identity
        (a target) (a control) (x target) (x control)
  · simp [cnotBits, bitsAdd, hkt, Bool.add_eq_xor]

private theorem cnotBits_eq_bitsAdd (control target : Fin 6) (x : Bits 6) :
    cnotBits control target x =
      bitsAdd x (singleBit target (x control)) := by
  funext k
  by_cases hkt : k = target
  · subst k
    simp [cnotBits, bitsAdd, singleBit]
  · simp [cnotBits, bitsAdd, singleBit, hkt, Bool.add_eq_xor]

private theorem dotBool_cnot (control target : Fin 6) (b x : Bits 6) :
    dotBool b (cnotBits control target x) =
      dotBool (cnotMapB control target b) x := by
  rw [cnotBits_eq_bitsAdd, dotBool_bitsAdd_right,
    dotBool_singleBit_right]
  change dotBool b x + x control * b target =
    dotBool (bitsAdd b (singleBit control (b target))) x
  rw [dotBool_bitsAdd_left, dotBool_singleBit]
  rw [mul_comm (x control) (b target)]

private theorem cnot_phase (control target : Fin 6)
    (hct : control ≠ target) (b x : Bits 6) :
    zPhase b (cnotPerm control target hct x) =
      zPhase (cnotMapB control target b) x := by
  change zPhase b (cnotBits control target x) =
    zPhase (cnotMapB control target b) x
  rw [zPhase_eq_if_dotBool, zPhase_eq_if_dotBool,
    dotBool_cnot]

private theorem cnotMatrix_isCliffordUnitary
    (control target : Fin 6) (hct : control ≠ target) :
    IsCliffordUnitary ((cnotPerm control target hct).permMatrix ℂ) := by
  apply permutationMatrix_isCliffordUnitary
      (mapA := cnotBits control target)
      (mapB := cnotMapB control target)
  · exact cnot_translate control target hct
  · exact cnot_phase control target hct

private theorem xPauli_isCliffordUnitary (i : Fin 6) :
    IsCliffordUnitary (pauliMatrix (singleBit i true) zeroBits) := by
  constructor
  · rw [xPauli_eq_permMatrix, Matrix.mem_unitaryGroup_iff,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    have hinv : (togglePerm i)⁻¹ = togglePerm i :=
      Function.Involutive.symm_eq_self_of_involutive
        (togglePerm i) (togglePerm_involutive i)
    rw [hinv, ← Matrix.permMatrix_mul]
    have hsq : togglePerm i * togglePerm i = 1 := by
      apply Equiv.ext
      intro x
      exact togglePerm_involutive i x
    rw [hsq, Matrix.permMatrix_one]
  · rintro P ⟨c, a, b, rfl⟩
    refine ⟨addTwoIf c (b i), a, b, ?_⟩
    rw [Matrix.star_eq_conjTranspose, xPauli_conjTranspose]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [xPauli_conj_pauli, smul_smul,
      I_pow_mul_if_neg_one]

private noncomputable def tensorState6
    (f0 f1 f2 f3 f4 f5 : Bool → ℂ) : QState 6 :=
  fun x =>
    f0 (x 0) * f1 (x 1) * f2 (x 2) *
      f3 (x 3) * f4 (x 4) * f5 (x 5)

private noncomputable def bitHadamard (f : Bool → ℂ) : Bool → ℂ :=
  fun b =>
    invSqrtTwo *
      (f (!b) + (if b then (-1 : ℂ) else 1) * f b)

private theorem hadamard_zero_tensorState6
    (f0 f1 f2 f3 f4 f5 : Bool → ℂ) :
    (hadamardMatrix 0).mulVec (tensorState6 f0 f1 f2 f3 f4 f5) =
      tensorState6 (bitHadamard f0) f1 f2 f3 f4 f5 := by
  funext y
  rw [hadamardMatrix_mulVec]
  cases hy : y 0 <;>
    simp [tensorState6, bitHadamard, togglePerm_apply,
    signValue, zGatePhase, hy] <;>
    ring

private theorem hadamard_one_tensorState6
    (f0 f1 f2 f3 f4 f5 : Bool → ℂ) :
    (hadamardMatrix 1).mulVec (tensorState6 f0 f1 f2 f3 f4 f5) =
      tensorState6 f0 (bitHadamard f1) f2 f3 f4 f5 := by
  funext y
  rw [hadamardMatrix_mulVec]
  cases hy : y 1 <;>
    simp [tensorState6, bitHadamard, togglePerm_apply,
      signValue, zGatePhase, hy] <;>
    ring

private theorem hadamard_two_tensorState6
    (f0 f1 f2 f3 f4 f5 : Bool → ℂ) :
    (hadamardMatrix 2).mulVec (tensorState6 f0 f1 f2 f3 f4 f5) =
      tensorState6 f0 f1 (bitHadamard f2) f3 f4 f5 := by
  funext y
  rw [hadamardMatrix_mulVec]
  cases hy : y 2 <;>
    simp [tensorState6, bitHadamard, togglePerm_apply,
      signValue, zGatePhase, hy] <;>
    ring

private theorem hadamard_three_tensorState6
    (f0 f1 f2 f3 f4 f5 : Bool → ℂ) :
    (hadamardMatrix 3).mulVec (tensorState6 f0 f1 f2 f3 f4 f5) =
      tensorState6 f0 f1 f2 (bitHadamard f3) f4 f5 := by
  funext y
  rw [hadamardMatrix_mulVec]
  cases hy : y 3 <;>
    simp [tensorState6, bitHadamard, togglePerm_apply,
      signValue, zGatePhase, hy] <;>
    ring

private theorem hadamard_four_tensorState6
    (f0 f1 f2 f3 f4 f5 : Bool → ℂ) :
    (hadamardMatrix 4).mulVec (tensorState6 f0 f1 f2 f3 f4 f5) =
      tensorState6 f0 f1 f2 f3 (bitHadamard f4) f5 := by
  funext y
  rw [hadamardMatrix_mulVec]
  cases hy : y 4 <;>
    simp [tensorState6, bitHadamard, togglePerm_apply,
      signValue, zGatePhase, hy] <;>
    ring

private theorem hadamard_five_tensorState6
    (f0 f1 f2 f3 f4 f5 : Bool → ℂ) :
    (hadamardMatrix 5).mulVec (tensorState6 f0 f1 f2 f3 f4 f5) =
      tensorState6 f0 f1 f2 f3 f4 (bitHadamard f5) := by
  funext y
  rw [hadamardMatrix_mulVec]
  cases hy : y 5 <;>
    simp [tensorState6, bitHadamard, togglePerm_apply,
    signValue, zGatePhase, hy] <;>
    ring

private noncomputable def ketZeroBit : Bool → ℂ :=
  fun b => if b then 0 else 1

private noncomputable def ketOneBit : Bool → ℂ :=
  fun b => if b then 1 else 0

private noncomputable def plusBit : Bool → ℂ :=
  fun _ => invSqrtTwo

private noncomputable def minusBit : Bool → ℂ :=
  fun b => if b then -invSqrtTwo else invSqrtTwo

private theorem bitHadamard_ketZero :
    bitHadamard ketZeroBit = plusBit := by
  funext b
  cases b <;> simp [bitHadamard, ketZeroBit, plusBit] <;> ring

private theorem bitHadamard_ketOne :
    bitHadamard ketOneBit = minusBit := by
  funext b
  cases b <;> simp [bitHadamard, ketOneBit, minusBit] <;> ring

private noncomputable def allHadamardMatrix :
    Matrix (Bits 6) (Bits 6) ℂ :=
  hadamardMatrix 5 * hadamardMatrix 4 * hadamardMatrix 3 *
    hadamardMatrix 2 * hadamardMatrix 1 * hadamardMatrix 0

private theorem allHadamardMatrix_isCliffordUnitary :
    IsCliffordUnitary allHadamardMatrix := by
  exact (((((hadamardMatrix_isCliffordUnitary 5).mul
    (hadamardMatrix_isCliffordUnitary 4)).mul
      (hadamardMatrix_isCliffordUnitary 3)).mul
        (hadamardMatrix_isCliffordUnitary 2)).mul
          (hadamardMatrix_isCliffordUnitary 1)).mul
            (hadamardMatrix_isCliffordUnitary 0)

private theorem allHadamardMatrix_mulVec_tensorState6
    (f0 f1 f2 f3 f4 f5 : Bool → ℂ) :
    allHadamardMatrix.mulVec (tensorState6 f0 f1 f2 f3 f4 f5) =
      tensorState6 (bitHadamard f0) (bitHadamard f1)
        (bitHadamard f2) (bitHadamard f3)
        (bitHadamard f4) (bitHadamard f5) := by
  rw [allHadamardMatrix, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hadamard_zero_tensorState6, hadamard_one_tensorState6,
    hadamard_two_tensorState6, hadamard_three_tensorState6,
    hadamard_four_tensorState6, hadamard_five_tensorState6]

private theorem allHadamardMatrix_mulVec_ketZero :
    allHadamardMatrix.mulVec
        (tensorState6 ketZeroBit ketZeroBit ketZeroBit
          ketZeroBit ketZeroBit ketZeroBit) =
      tensorState6 plusBit plusBit plusBit plusBit plusBit plusBit := by
  rw [allHadamardMatrix_mulVec_tensorState6, bitHadamard_ketZero]

private theorem allHadamardMatrix_mulVec_ketOne :
    allHadamardMatrix.mulVec
        (tensorState6 ketOneBit ketOneBit ketOneBit
          ketOneBit ketOneBit ketOneBit) =
      tensorState6 minusBit minusBit minusBit minusBit minusBit minusBit := by
  rw [allHadamardMatrix_mulVec_tensorState6, bitHadamard_ketOne]

private def oneBits : Bits 6 :=
  fun _ => true

private theorem bits_eq_zeroBits_iff (x : Bits 6) :
    x = zeroBits ↔
      x 0 = false ∧ x 1 = false ∧ x 2 = false ∧
        x 3 = false ∧ x 4 = false ∧ x 5 = false := by
  decide +revert

private theorem bits_eq_oneBits_iff (x : Bits 6) :
    x = oneBits ↔
      x 0 = true ∧ x 1 = true ∧ x 2 = true ∧
        x 3 = true ∧ x 4 = true ∧ x 5 = true := by
  decide +revert

private theorem ketZero_product_eq_indicator
    (b0 b1 b2 b3 b4 b5 : Bool) :
    ketZeroBit b0 * ketZeroBit b1 * ketZeroBit b2 *
        ketZeroBit b3 * ketZeroBit b4 * ketZeroBit b5 =
      if b0 = false ∧ b1 = false ∧ b2 = false ∧
          b3 = false ∧ b4 = false ∧ b5 = false then
        1
      else 0 := by
  cases b0 <;> cases b1 <;> cases b2 <;>
    cases b3 <;> cases b4 <;> cases b5 <;>
    norm_num [ketZeroBit]

private theorem ketOne_product_eq_indicator
    (b0 b1 b2 b3 b4 b5 : Bool) :
    ketOneBit b0 * ketOneBit b1 * ketOneBit b2 *
        ketOneBit b3 * ketOneBit b4 * ketOneBit b5 =
      if b0 = true ∧ b1 = true ∧ b2 = true ∧
          b3 = true ∧ b4 = true ∧ b5 = true then
        1
      else 0 := by
  cases b0 <;> cases b1 <;> cases b2 <;>
    cases b3 <;> cases b4 <;> cases b5 <;>
    norm_num [ketOneBit]

private theorem tensorState6_ketZero_eq_zeroState :
    tensorState6 ketZeroBit ketZeroBit ketZeroBit
        ketZeroBit ketZeroBit ketZeroBit =
      zeroState 6 := by
  funext x
  rw [tensorState6, ketZero_product_eq_indicator]
  change (if
      x 0 = false ∧ x 1 = false ∧ x 2 = false ∧
        x 3 = false ∧ x 4 = false ∧ x 5 = false
    then 1 else 0) =
      if x = zeroBits then 1 else 0
  simp only [bits_eq_zeroBits_iff]

private noncomputable def basisOneState : QState 6 :=
  tensorState6 ketOneBit ketOneBit ketOneBit
    ketOneBit ketOneBit ketOneBit

private theorem basisOneState_apply (x : Bits 6) :
    basisOneState x = if x = oneBits then 1 else 0 := by
  rw [basisOneState, tensorState6, ketOne_product_eq_indicator]
  change (if
      x 0 = true ∧ x 1 = true ∧ x 2 = true ∧
        x 3 = true ∧ x 4 = true ∧ x 5 = true
    then 1 else 0) =
      if x = oneBits then 1 else 0
  simp only [bits_eq_oneBits_iff]

private noncomputable def allXMatrix :
    Matrix (Bits 6) (Bits 6) ℂ :=
  pauliMatrix (singleBit 5 true) zeroBits *
    pauliMatrix (singleBit 4 true) zeroBits *
    pauliMatrix (singleBit 3 true) zeroBits *
    pauliMatrix (singleBit 2 true) zeroBits *
    pauliMatrix (singleBit 1 true) zeroBits *
    pauliMatrix (singleBit 0 true) zeroBits

private theorem allXMatrix_isCliffordUnitary :
    IsCliffordUnitary allXMatrix := by
  exact (((((xPauli_isCliffordUnitary 5).mul
    (xPauli_isCliffordUnitary 4)).mul
      (xPauli_isCliffordUnitary 3)).mul
        (xPauli_isCliffordUnitary 2)).mul
          (xPauli_isCliffordUnitary 1)).mul
            (xPauli_isCliffordUnitary 0)

private theorem xPauli_mulVec (i : Fin 6) (v : QState 6) (y : Bits 6) :
    (pauliMatrix (singleBit i true) zeroBits).mulVec v y =
      v (togglePerm i y) := by
  rw [pauliMatrix_mulVec, zPhase_zeroBits, one_mul]
  rfl

private def notBits (x : Bits 6) : Bits 6 :=
  fun i => !x i

private theorem all_toggles_eq_notBits (x : Bits 6) :
    togglePerm 0
        (togglePerm 1
          (togglePerm 2
            (togglePerm 3
              (togglePerm 4 (togglePerm 5 x))))) =
      notBits x := by
  decide +revert

private theorem notBits_eq_zeroBits_iff (x : Bits 6) :
    notBits x = zeroBits ↔ x = oneBits := by
  decide +revert

private theorem allXMatrix_mulVec_zeroState :
    allXMatrix.mulVec (zeroState 6) = basisOneState := by
  funext y
  rw [allXMatrix, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    xPauli_mulVec, xPauli_mulVec, xPauli_mulVec,
    xPauli_mulVec, xPauli_mulVec, xPauli_mulVec,
    all_toggles_eq_notBits, basisOneState_apply]
  change (if notBits y = zeroBits then 1 else 0) =
    if y = oneBits then 1 else 0
  simp only [notBits_eq_zeroBits_iff]

private theorem basisOneState_isStabilizerState :
    IsStabilizerState basisOneState := by
  refine ⟨allXMatrix, allXMatrix_isCliffordUnitary, ?_⟩
  exact allXMatrix_mulVec_zeroState.symm

private noncomputable def uniformState : QState 6 :=
  tensorState6 plusBit plusBit plusBit plusBit plusBit plusBit

private theorem invSqrtTwo_pow_six :
    invSqrtTwo ^ 6 = (1 / 8 : ℂ) := by
  calc
    invSqrtTwo ^ 6 =
        (invSqrtTwo * invSqrtTwo) *
          (invSqrtTwo * invSqrtTwo) *
            (invSqrtTwo * invSqrtTwo) := by ring
    _ = (1 / 8 : ℂ) := by rw [invSqrtTwo_mul_self]; norm_num

private theorem uniformState_apply (x : Bits 6) :
    uniformState x = (1 / 8 : ℂ) := by
  rw [uniformState, tensorState6]
  simp only [plusBit]
  rw [show
      invSqrtTwo * invSqrtTwo * invSqrtTwo *
          invSqrtTwo * invSqrtTwo * invSqrtTwo =
        invSqrtTwo ^ 6 by ring,
    invSqrtTwo_pow_six]

private theorem allHadamardMatrix_mulVec_zeroState :
    allHadamardMatrix.mulVec (zeroState 6) = uniformState := by
  rw [← tensorState6_ketZero_eq_zeroState,
    allHadamardMatrix_mulVec_ketZero]
  rfl

private theorem uniformState_isStabilizerState :
    IsStabilizerState uniformState := by
  refine ⟨allHadamardMatrix, allHadamardMatrix_isCliffordUnitary, ?_⟩
  exact allHadamardMatrix_mulVec_zeroState.symm

private noncomputable def cnotMatrix
    (control target : Fin 6) (hct : control ≠ target) :
    Matrix (Bits 6) (Bits 6) ℂ :=
  (cnotPerm control target hct).permMatrix ℂ

private theorem cnotMatrix_mulVec
    (control target : Fin 6) (hct : control ≠ target)
    (v : QState 6) (y : Bits 6) :
    (cnotMatrix control target hct).mulVec v y =
      v (cnotBits control target y) := by
  rw [cnotMatrix, Matrix.permMatrix_mulVec]
  rfl

private noncomputable def fanoutMatrix :
    Matrix (Bits 6) (Bits 6) ℂ :=
  cnotMatrix 0 5 (by decide) *
    cnotMatrix 0 4 (by decide) *
    cnotMatrix 0 3 (by decide) *
    cnotMatrix 0 2 (by decide) *
    cnotMatrix 0 1 (by decide)

private theorem fanoutMatrix_isCliffordUnitary :
    IsCliffordUnitary fanoutMatrix := by
  exact ((((cnotMatrix_isCliffordUnitary 0 5 (by decide)).mul
    (cnotMatrix_isCliffordUnitary 0 4 (by decide))).mul
      (cnotMatrix_isCliffordUnitary 0 3 (by decide))).mul
        (cnotMatrix_isCliffordUnitary 0 2 (by decide))).mul
          (cnotMatrix_isCliffordUnitary 0 1 (by decide))

private def fanoutBits (x : Bits 6) : Bits 6 :=
  fun k => if k = 0 then x 0 else x k + x 0

private theorem cnot_chain_eq_fanoutBits (x : Bits 6) :
    cnotBits 0 1
        (cnotBits 0 2
          (cnotBits 0 3
            (cnotBits 0 4 (cnotBits 0 5 x)))) =
      fanoutBits x := by
  decide +revert

private noncomputable def ghzSeedState : QState 6 :=
  tensorState6 plusBit ketZeroBit ketZeroBit
    ketZeroBit ketZeroBit ketZeroBit

private theorem ketZero_five_product_eq_indicator
    (b1 b2 b3 b4 b5 : Bool) :
    ketZeroBit b1 * ketZeroBit b2 * ketZeroBit b3 *
        ketZeroBit b4 * ketZeroBit b5 =
      if b1 = false ∧ b2 = false ∧ b3 = false ∧
          b4 = false ∧ b5 = false then
        1
      else 0 := by
  cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;>
    norm_num [ketZeroBit]

private theorem ghzSeedState_apply (x : Bits 6) :
    ghzSeedState x =
      if x 1 = false ∧ x 2 = false ∧ x 3 = false ∧
          x 4 = false ∧ x 5 = false then
        invSqrtTwo
      else 0 := by
  rw [ghzSeedState, tensorState6]
  simp only [plusBit]
  have hproduct := ketZero_five_product_eq_indicator
    (x 1) (x 2) (x 3) (x 4) (x 5)
  calc
    invSqrtTwo * ketZeroBit (x 1) * ketZeroBit (x 2) *
          ketZeroBit (x 3) * ketZeroBit (x 4) * ketZeroBit (x 5) =
        invSqrtTwo *
          (ketZeroBit (x 1) * ketZeroBit (x 2) *
            ketZeroBit (x 3) * ketZeroBit (x 4) * ketZeroBit (x 5)) := by
      ring
    _ = invSqrtTwo *
        (if x 1 = false ∧ x 2 = false ∧ x 3 = false ∧
            x 4 = false ∧ x 5 = false then 1 else 0) := by
      rw [hproduct]
    _ = _ := by split_ifs <;> ring

private noncomputable def ghzPlusState : QState 6 :=
  fun x =>
    if x = zeroBits ∨ x = oneBits then invSqrtTwo else 0

private theorem fanout_condition_iff (x : Bits 6) :
    fanoutBits x 1 = false ∧ fanoutBits x 2 = false ∧
        fanoutBits x 3 = false ∧ fanoutBits x 4 = false ∧
        fanoutBits x 5 = false ↔
      x = zeroBits ∨ x = oneBits := by
  decide +revert

private theorem fanoutMatrix_mulVec_ghzSeedState :
    fanoutMatrix.mulVec ghzSeedState = ghzPlusState := by
  funext y
  rw [fanoutMatrix, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, cnotMatrix_mulVec,
    cnotMatrix_mulVec, cnotMatrix_mulVec,
    cnotMatrix_mulVec, cnotMatrix_mulVec,
    cnot_chain_eq_fanoutBits, ghzSeedState_apply]
  change (if
      fanoutBits y 1 = false ∧ fanoutBits y 2 = false ∧
        fanoutBits y 3 = false ∧ fanoutBits y 4 = false ∧
        fanoutBits y 5 = false
    then invSqrtTwo else 0) =
      ghzPlusState y
  rw [ghzPlusState]
  simp only [fanout_condition_iff]

private theorem hadamard_zero_mulVec_zeroState :
    (hadamardMatrix 0).mulVec (zeroState 6) = ghzSeedState := by
  rw [← tensorState6_ketZero_eq_zeroState,
    hadamard_zero_tensorState6, bitHadamard_ketZero]
  rfl

private noncomputable def ghzPrepMatrix :
    Matrix (Bits 6) (Bits 6) ℂ :=
  fanoutMatrix * hadamardMatrix 0

private theorem ghzPrepMatrix_isCliffordUnitary :
    IsCliffordUnitary ghzPrepMatrix :=
  fanoutMatrix_isCliffordUnitary.mul
    (hadamardMatrix_isCliffordUnitary 0)

private theorem ghzPrepMatrix_mulVec_zeroState :
    ghzPrepMatrix.mulVec (zeroState 6) = ghzPlusState := by
  rw [ghzPrepMatrix, ← Matrix.mulVec_mulVec,
    hadamard_zero_mulVec_zeroState,
    fanoutMatrix_mulVec_ghzSeedState]

private theorem ghzPlusState_isStabilizerState :
    IsStabilizerState ghzPlusState := by
  refine ⟨ghzPrepMatrix, ghzPrepMatrix_isCliffordUnitary, ?_⟩
  exact ghzPrepMatrix_mulVec_zeroState.symm

private noncomputable def ghzMinusState : QState 6 :=
  (signMatrix (zGatePhase 0)).mulVec ghzPlusState

private theorem zeroBits_ne_oneBits :
    zeroBits ≠ oneBits := by
  decide

private theorem oneBits_ne_zeroBits :
    oneBits ≠ zeroBits :=
  Ne.symm zeroBits_ne_oneBits

private theorem ghzMinusState_apply (x : Bits 6) :
    ghzMinusState x =
      if x = zeroBits then invSqrtTwo
      else if x = oneBits then -invSqrtTwo
      else 0 := by
  rw [ghzMinusState, signMatrix_mulVec]
  by_cases hx0 : x = zeroBits
  · subst x
    simp [ghzPlusState, signValue, zGatePhase, zeroBits,
      zeroBits_ne_oneBits]
  · by_cases hx1 : x = oneBits
    · subst x
      simp [ghzPlusState, signValue, zGatePhase, oneBits,
        zeroBits_ne_oneBits, oneBits_ne_zeroBits]
    · simp [ghzPlusState, signValue, zGatePhase, hx0, hx1]

private theorem ghzMinusState_isStabilizerState :
    IsStabilizerState ghzMinusState := by
  exact (zGate_isCliffordUnitary 0).isStabilizerState_mulVec
    ghzPlusState_isStabilizerState

private theorem tensorState6_ketZero_apply (x : Bits 6) :
    tensorState6 ketZeroBit ketZeroBit ketZeroBit
        ketZeroBit ketZeroBit ketZeroBit x =
      if x = zeroBits then 1 else 0 := by
  rw [tensorState6_ketZero_eq_zeroState]
  rfl

private theorem ghzPlusState_eq_tensor_sum :
    ghzPlusState =
      invSqrtTwo •
        (tensorState6 ketZeroBit ketZeroBit ketZeroBit
            ketZeroBit ketZeroBit ketZeroBit +
          tensorState6 ketOneBit ketOneBit ketOneBit
            ketOneBit ketOneBit ketOneBit) := by
  funext x
  rw [Pi.smul_apply, Pi.add_apply, tensorState6_ketZero_apply]
  change ghzPlusState x =
    invSqrtTwo * ((if x = zeroBits then 1 else 0) +
      basisOneState x)
  rw [basisOneState_apply, ghzPlusState]
  by_cases hx0 : x = zeroBits
  · subst x
    simp [zeroBits_ne_oneBits]
  · by_cases hx1 : x = oneBits
    · subst x
      simp [zeroBits_ne_oneBits, oneBits_ne_zeroBits]
    · simp [hx0, hx1]

private theorem ghzMinusState_eq_tensor_sub :
    ghzMinusState =
      invSqrtTwo •
        (tensorState6 ketZeroBit ketZeroBit ketZeroBit
            ketZeroBit ketZeroBit ketZeroBit -
          tensorState6 ketOneBit ketOneBit ketOneBit
            ketOneBit ketOneBit ketOneBit) := by
  funext x
  rw [Pi.smul_apply, Pi.sub_apply, tensorState6_ketZero_apply]
  change ghzMinusState x =
    invSqrtTwo * ((if x = zeroBits then 1 else 0) -
      basisOneState x)
  rw [basisOneState_apply, ghzMinusState_apply]
  by_cases hx0 : x = zeroBits
  · subst x
    simp [zeroBits_ne_oneBits]
  · by_cases hx1 : x = oneBits
    · subst x
      simp [zeroBits_ne_oneBits, oneBits_ne_zeroBits]
    · simp [hx0, hx1]

private def parity6 (x : Bits 6) : Bool :=
  xor (x 0) (xor (x 1) (xor (x 2)
    (xor (x 3) (xor (x 4) (x 5)))))

private theorem tensorState6_minus_apply (x : Bits 6) :
    tensorState6 minusBit minusBit minusBit
        minusBit minusBit minusBit x =
      signValue parity6 x * (1 / 8 : ℂ) := by
  rw [← invSqrtTwo_pow_six]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    cases h2 : x 2 <;> cases h3 : x 3 <;>
    cases h4 : x 4 <;> cases h5 : x 5 <;>
    simp [tensorState6, minusBit, signValue, parity6,
      h0, h1, h2, h3, h4, h5] <;>
    ring

private noncomputable def evenState : QState 6 :=
  fun x => if parity6 x then 0 else invSqrtTwo / 4

private noncomputable def oddState : QState 6 :=
  fun x => if parity6 x then invSqrtTwo / 4 else 0

private theorem allHadamardMatrix_mulVec_ghzPlusState :
    allHadamardMatrix.mulVec ghzPlusState = evenState := by
  rw [ghzPlusState_eq_tensor_sum, Matrix.mulVec_smul,
    Matrix.mulVec_add, allHadamardMatrix_mulVec_ketZero,
    allHadamardMatrix_mulVec_ketOne]
  funext x
  rw [Pi.smul_apply, Pi.add_apply, tensorState6_minus_apply]
  change invSqrtTwo *
      (uniformState x + signValue parity6 x * (1 / 8 : ℂ)) =
    evenState x
  rw [uniformState_apply]
  cases hp : parity6 x <;>
    simp [evenState, signValue, hp] <;>
    ring

private theorem allHadamardMatrix_mulVec_ghzMinusState :
    allHadamardMatrix.mulVec ghzMinusState = oddState := by
  rw [ghzMinusState_eq_tensor_sub, Matrix.mulVec_smul,
    Matrix.mulVec_sub, allHadamardMatrix_mulVec_ketZero,
    allHadamardMatrix_mulVec_ketOne]
  funext x
  rw [Pi.smul_apply, Pi.sub_apply, tensorState6_minus_apply]
  change invSqrtTwo *
      (uniformState x - signValue parity6 x * (1 / 8 : ℂ)) =
    oddState x
  rw [uniformState_apply]
  cases hp : parity6 x <;>
    simp [oddState, signValue, hp] <;>
    ring

private theorem evenState_isStabilizerState :
    IsStabilizerState evenState := by
  rw [← allHadamardMatrix_mulVec_ghzPlusState]
  exact allHadamardMatrix_isCliffordUnitary.isStabilizerState_mulVec
    ghzPlusState_isStabilizerState

private theorem oddState_isStabilizerState :
    IsStabilizerState oddState := by
  rw [← allHadamardMatrix_mulVec_ghzMinusState]
  exact allHadamardMatrix_isCliffordUnitary.isStabilizerState_mulVec
    ghzMinusState_isStabilizerState

private inductive DiagonalGate where
  | z (i : Fin 6)
  | cz (i j : Fin 6) (hij : i ≠ j)

private def DiagonalGate.phase : DiagonalGate → Bits 6 → Bool
  | .z i => zGatePhase i
  | .cz i j _ => czGatePhase i j

private theorem DiagonalGate.isCliffordUnitary (g : DiagonalGate) :
    IsCliffordUnitary (signMatrix g.phase) := by
  cases g with
  | z i => exact zGate_isCliffordUnitary i
  | cz i j hij => exact czGate_isCliffordUnitary i j hij

private def diagonalPhase : List DiagonalGate → Bits 6 → Bool
  | [], _ => false
  | g :: gates, x => xor (g.phase x) (diagonalPhase gates x)

private noncomputable def applyDiagonalGates :
    List DiagonalGate → QState 6 → QState 6
  | [], ψ => ψ
  | g :: gates, ψ =>
      (signMatrix g.phase).mulVec (applyDiagonalGates gates ψ)

private theorem signValue_xor
    (q r : Bits 6 → Bool) (x : Bits 6) :
    signValue q x * signValue r x =
      signValue (fun y => xor (q y) (r y)) x := by
  cases hq : q x <;> cases hr : r x <;>
    simp [signValue, hq, hr]

private theorem applyDiagonalGates_apply
    (gates : List DiagonalGate) (ψ : QState 6) (x : Bits 6) :
    applyDiagonalGates gates ψ x =
      signValue (diagonalPhase gates) x * ψ x := by
  induction gates with
  | nil =>
      simp [applyDiagonalGates, diagonalPhase, signValue]
  | cons g gates ih =>
      rw [applyDiagonalGates, signMatrix_mulVec, ih]
      calc
        signValue g.phase x *
            (signValue (diagonalPhase gates) x * ψ x) =
          (signValue g.phase x *
              signValue (diagonalPhase gates) x) * ψ x := by
            rw [mul_assoc]
        _ = signValue
              (fun y => xor (g.phase y) (diagonalPhase gates y)) x *
              ψ x := by
            rw [signValue_xor]
        _ = signValue (diagonalPhase (g :: gates)) x * ψ x := rfl

private theorem applyDiagonalGates_isStabilizerState
    (gates : List DiagonalGate) {ψ : QState 6}
    (hψ : IsStabilizerState ψ) :
    IsStabilizerState (applyDiagonalGates gates ψ) := by
  induction gates with
  | nil => exact hψ
  | cons g gates ih =>
      exact g.isCliffordUnitary.isStabilizerState_mulVec ih

private def completeGraphGates : List DiagonalGate :=
  [ .cz 0 1 (by decide), .cz 0 2 (by decide),
    .cz 0 3 (by decide), .cz 0 4 (by decide),
    .cz 0 5 (by decide), .cz 1 2 (by decide),
    .cz 1 3 (by decide), .cz 1 4 (by decide),
    .cz 1 5 (by decide), .cz 2 3 (by decide),
    .cz 2 4 (by decide), .cz 2 5 (by decide),
    .cz 3 4 (by decide), .cz 3 5 (by decide),
    .cz 4 5 (by decide) ]

private def zKGraphGates : List DiagonalGate :=
  [ .z 0, .z 1, .z 2, .z 3, .z 4, .z 5 ] ++
    completeGraphGates

private def primeGraphGates : List DiagonalGate :=
  [ .cz 4 0 (by decide), .cz 0 1 (by decide),
    .cz 1 2 (by decide), .cz 2 3 (by decide),
    .cz 3 4 (by decide), .cz 5 0 (by decide),
    .cz 5 1 (by decide), .cz 5 2 (by decide),
    .cz 5 3 (by decide), .cz 5 4 (by decide) ]

private def doublePrimeGraphGates : List DiagonalGate :=
  [ .cz 5 0 (by decide), .cz 0 1 (by decide),
    .cz 1 3 (by decide), .cz 3 4 (by decide),
    .cz 4 5 (by decide), .cz 2 0 (by decide),
    .cz 2 1 (by decide), .cz 2 3 (by decide),
    .cz 2 4 (by decide), .cz 2 5 (by decide) ]

private noncomputable def zKState : QState 6 :=
  applyDiagonalGates zKGraphGates uniformState

private noncomputable def phiPrimeState : QState 6 :=
  applyDiagonalGates primeGraphGates oddState

private noncomputable def phiDoublePrimeState : QState 6 :=
  applyDiagonalGates doublePrimeGraphGates oddState

private theorem zKState_apply (x : Bits 6) :
    zKState x =
      signValue (diagonalPhase zKGraphGates) x * (1 / 8 : ℂ) := by
  rw [zKState, applyDiagonalGates_apply, uniformState_apply]

private theorem phiPrimeState_apply (x : Bits 6) :
    phiPrimeState x =
      signValue (diagonalPhase primeGraphGates) x *
        (if parity6 x then invSqrtTwo / 4 else 0) := by
  rw [phiPrimeState, applyDiagonalGates_apply, oddState]

private theorem phiDoublePrimeState_apply (x : Bits 6) :
    phiDoublePrimeState x =
      signValue (diagonalPhase doublePrimeGraphGates) x *
        (if parity6 x then invSqrtTwo / 4 else 0) := by
  rw [phiDoublePrimeState, applyDiagonalGates_apply, oddState]

private theorem zKState_isStabilizerState :
    IsStabilizerState zKState :=
  applyDiagonalGates_isStabilizerState zKGraphGates
    uniformState_isStabilizerState

private theorem phiPrimeState_isStabilizerState :
    IsStabilizerState phiPrimeState :=
  applyDiagonalGates_isStabilizerState primeGraphGates
    oddState_isStabilizerState

private theorem phiDoublePrimeState_isStabilizerState :
    IsStabilizerState phiDoublePrimeState :=
  applyDiagonalGates_isStabilizerState doublePrimeGraphGates
    oddState_isStabilizerState

private noncomputable def hCos : ℂ :=
  (Real.cos (Real.pi / 8) : ℝ)

private noncomputable def hSin : ℂ :=
  (Real.sin (Real.pi / 8) : ℝ)

private theorem invSqrtTwo_eq_sqrt_two_div_two :
    invSqrtTwo = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  change (↑((Real.sqrt 2)⁻¹) : ℂ) =
    ↑(Real.sqrt 2 / 2 : ℝ)
  norm_cast
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem hState_six_apply (x : Bits 6) :
    hState 6 x =
      (if x 0 then hSin else hCos) *
      (if x 1 then hSin else hCos) *
      (if x 2 then hSin else hCos) *
      (if x 3 then hSin else hCos) *
      (if x 4 then hSin else hCos) *
      (if x 5 then hSin else hCos) := by
  change (∏ i : Fin 6, if x i then hSin else hCos) = _
  rw [Fin.prod_univ_six]

private theorem real_sin_pi_div_eight_eq :
    Real.sin (Real.pi / 8) =
      (Real.sqrt 2 - 1) * Real.cos (Real.pi / 8) := by
  have hsub : 0 ≤ 2 - Real.sqrt 2 := by
    linarith [Real.sqrt_two_lt_three_halves]
  rw [Real.sin_pi_div_eight, Real.cos_pi_div_eight]
  rw [← sq_eq_sq₀ (by positivity)
    (mul_nonneg (sub_nonneg.mpr Real.one_lt_sqrt_two.le)
      (by positivity))]
  rw [div_pow, mul_pow, div_pow,
    Real.sq_sqrt hsub,
    Real.sq_sqrt (by positivity : 0 ≤ 2 + Real.sqrt 2)]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem hSin_eq :
    hSin = (2 * invSqrtTwo - 1) * hCos := by
  rw [hSin, hCos, invSqrtTwo_eq_sqrt_two_div_two]
  norm_cast
  convert real_sin_pi_div_eight_eq using 1 <;> ring

private theorem hCos_sq :
    hCos ^ 2 = (1 + invSqrtTwo) / 2 := by
  rw [hCos, Real.cos_pi_div_eight,
    invSqrtTwo_eq_sqrt_two_div_two]
  norm_cast
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 + Real.sqrt 2)]
  ring

private theorem invSqrtTwo_sq :
    invSqrtTwo ^ 2 = (1 / 2 : ℂ) := by
  rw [pow_two, invSqrtTwo_mul_self]
  norm_num

private theorem hCos_pow_six :
    hCos ^ 6 = (10 + 14 * invSqrtTwo) / 32 := by
  calc
    hCos ^ 6 = (hCos ^ 2) ^ 3 := by ring
    _ = ((1 + invSqrtTwo) / 2) ^ 3 := by rw [hCos_sq]
    _ = (1 + 3 * invSqrtTwo + 3 * invSqrtTwo ^ 2 +
          invSqrtTwo ^ 3) / 8 := by ring
    _ = (10 + 14 * invSqrtTwo) / 32 := by
      rw [show invSqrtTwo ^ 3 = invSqrtTwo / 2 by
        calc
          invSqrtTwo ^ 3 =
              invSqrtTwo * invSqrtTwo ^ 2 := by ring
          _ = invSqrtTwo / 2 := by rw [invSqrtTwo_sq]; ring]
      rw [invSqrtTwo_sq]
      ring

private theorem invSqrtTwo_pow_three :
    invSqrtTwo ^ 3 = invSqrtTwo / 2 := by
  calc
    invSqrtTwo ^ 3 = invSqrtTwo * invSqrtTwo ^ 2 := by ring
    _ = invSqrtTwo / 2 := by rw [invSqrtTwo_sq]; ring

private theorem invSqrtTwo_pow_four :
    invSqrtTwo ^ 4 = (1 / 4 : ℂ) := by
  calc
    invSqrtTwo ^ 4 = (invSqrtTwo ^ 2) ^ 2 := by ring
    _ = (1 / 4 : ℂ) := by rw [invSqrtTwo_sq]; norm_num

private theorem invSqrtTwo_pow_five :
    invSqrtTwo ^ 5 = invSqrtTwo / 4 := by
  calc
    invSqrtTwo ^ 5 = invSqrtTwo * invSqrtTwo ^ 4 := by ring
    _ = invSqrtTwo / 4 := by rw [invSqrtTwo_pow_four]; ring

private theorem invSqrtTwo_pow_seven :
    invSqrtTwo ^ 7 = invSqrtTwo / 8 := by
  calc
    invSqrtTwo ^ 7 = invSqrtTwo * invSqrtTwo ^ 6 := by ring
    _ = invSqrtTwo / 8 := by rw [invSqrtTwo_pow_six]; ring

private theorem zeroState_six_apply (x : Bits 6) :
    zeroState 6 x = if x = zeroBits then 1 else 0 := by
  rfl

private theorem hState_decomposition_apply (x : Bits 6) :
    hState 6 x =
      ((1 + 2 * invSqrtTwo) / 4) * zeroState 6 x +
      ((1 - 2 * invSqrtTwo) / 4) * basisOneState x +
      (invSqrtTwo / 2) * evenState x +
      (1 / 2) * oddState x +
      (-invSqrtTwo / 2) * zKState x +
      (invSqrtTwo / 2) * phiPrimeState x +
      (invSqrtTwo / 2) * phiDoublePrimeState x := by
  rw [hState_six_apply, hSin_eq, zeroState_six_apply,
    basisOneState_apply, zKState_apply, phiPrimeState_apply,
    phiDoublePrimeState_apply]
  change
    (if x 0 then (2 * invSqrtTwo - 1) * hCos else hCos) *
      (if x 1 then (2 * invSqrtTwo - 1) * hCos else hCos) *
      (if x 2 then (2 * invSqrtTwo - 1) * hCos else hCos) *
      (if x 3 then (2 * invSqrtTwo - 1) * hCos else hCos) *
      (if x 4 then (2 * invSqrtTwo - 1) * hCos else hCos) *
      (if x 5 then (2 * invSqrtTwo - 1) * hCos else hCos) =
    ((1 + 2 * invSqrtTwo) / 4) *
        (if x = zeroBits then 1 else 0) +
      ((1 - 2 * invSqrtTwo) / 4) *
        (if x = oneBits then 1 else 0) +
      (invSqrtTwo / 2) *
        (if parity6 x then 0 else invSqrtTwo / 4) +
      (1 / 2) *
        (if parity6 x then invSqrtTwo / 4 else 0) +
      (-invSqrtTwo / 2) *
        (signValue (diagonalPhase zKGraphGates) x * (1 / 8)) +
      (invSqrtTwo / 2) *
        (signValue (diagonalPhase primeGraphGates) x *
          (if parity6 x then invSqrtTwo / 4 else 0)) +
      (invSqrtTwo / 2) *
        (signValue (diagonalPhase doublePrimeGraphGates) x *
          (if parity6 x then invSqrtTwo / 4 else 0))
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    cases h2 : x 2 <;> cases h3 : x 3 <;>
    cases h4 : x 4 <;> cases h5 : x 5 <;>
    simp [h0, h1, h2, h3, h4, h5,
      bits_eq_zeroBits_iff, bits_eq_oneBits_iff,
      parity6, signValue, diagonalPhase, DiagonalGate.phase,
      zKGraphGates, completeGraphGates, primeGraphGates,
      doublePrimeGraphGates, zGatePhase, czGatePhase] <;>
    ring_nf
  all_goals
    rw [hCos_pow_six]
    ring_nf
    simp only [invSqrtTwo_pow_seven, invSqrtTwo_pow_six,
      invSqrtTwo_pow_five, invSqrtTwo_pow_four,
      invSqrtTwo_pow_three, invSqrtTwo_sq]
    ring

private noncomputable def decompositionCoeff : Fin 7 → ℂ :=
  ![(1 + 2 * invSqrtTwo) / 4,
    (1 - 2 * invSqrtTwo) / 4,
    invSqrtTwo / 2,
    1 / 2,
    -invSqrtTwo / 2,
    invSqrtTwo / 2,
    invSqrtTwo / 2]

private noncomputable def decompositionState : Fin 7 → QState 6 :=
  ![zeroState 6, basisOneState, evenState, oddState,
    zKState, phiPrimeState, phiDoublePrimeState]

private theorem decompositionState_isStabilizer (j : Fin 7) :
    IsStabilizerState (decompositionState j) := by
  fin_cases j
  · exact zeroState_isStabilizerState 6
  · exact basisOneState_isStabilizerState
  · exact evenState_isStabilizerState
  · exact oddState_isStabilizerState
  · exact zKState_isStabilizerState
  · exact phiPrimeState_isStabilizerState
  · exact phiDoublePrimeState_isStabilizerState

private theorem hState_decomposition (x : Bits 6) :
    hState 6 x =
      ∑ j, decompositionCoeff j * decompositionState j x := by
  rw [Fin.sum_univ_seven]
  simpa [decompositionCoeff, decompositionState] using
    hState_decomposition_apply x

theorem stabRank_hState_six_le_seven : stabRank (hState 6) ≤ 7 := by
  rw [stabRank]
  apply Nat.sInf_le
  exact ⟨decompositionCoeff, decompositionState,
    decompositionState_isStabilizer, hState_decomposition⟩

end StabilizerRank

open StabilizerRank in
theorem solution : stabRank (hState 6) ≤ 7 :=
  stabRank_hState_six_le_seven
