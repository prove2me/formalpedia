-- Prove2me | solution 1 for QAlgorithms.Childs.compressedPhaseOracle_containsZero_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:45:17.945983+00:00
-- url     : https://prove2.me/submissions/e9a234e6-b088-43b3-9895-732ac9699d7e

import Theorems.Thm_QAlgorithms_Childs_compressedPhaseOracle_local_action

open QAlgorithms Matrix
open scoped ComplexConjugate

namespace CompressedBound

private noncomputable def c (m : ℕ) : ℝ := (Real.sqrt 2)⁻¹ ^ m
private def sig (b : Bool) : ℂ := if b then -1 else 1
private def phase (m : ℕ) (z : Qubits m) : Matrix (Option (Qubits m)) (Option (Qubits m)) ℂ :=
  Matrix.diagonal fun t => match t with | none => 1 | some v => sig (dotBits z v)
private noncomputable def loc (m : ℕ) (z : Qubits m) :=
  compressionUnitary m * phase m z * compressionUnitary m

private lemma cnorm (m : ℕ) : c m ^ 2 * (2 : ℝ) ^ m = 1 := by
  have h : ((Real.sqrt 2)⁻¹)^2 * 2 = (1 : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)).ne'
    field_simp
    nlinarith
  unfold c
  rw [← pow_mul, Nat.mul_comm m 2, pow_mul, ← mul_pow, h, one_pow]

private lemma sig_add (a b : Bool) : sig (a + b) = sig a * sig b := by
  cases a <;> cases b <;> norm_num [sig, Bool.add_eq_xor, Bool.zero_eq_false]

private lemma sig_sum {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    sig (∑ i ∈ s, f i) = ∏ i ∈ s, sig (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sig, Bool.zero_eq_false]
  | @insert a s ha ih => simp [ha, sig_add, ih]

private lemma char_sum (m : ℕ) (z : Qubits m) :
    (∑ v : Qubits m, sig (dotBits z v)) = if z = 0 then (2 : ℂ)^m else 0 := by
  classical
  simp_rw [dotBits, sig_sum]
  rw [← Fintype.prod_sum (fun k v => sig (z k && v))]
  have h (k : Fin m) : (∑ v : Bool, sig (z k && v)) = if z k = false then (2 : ℂ) else 0 := by
    cases z k <;> norm_num [sig]
  simp_rw [h]
  by_cases hz : z = 0
  · subst z; simp [Bool.zero_eq_false]
  · rw [if_neg hz]
    have ⟨k,hk⟩ := Function.ne_iff.mp hz
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (by simpa [Bool.zero_eq_false] using hk))

private lemma Cstar (m : ℕ) : (compressionUnitary m)ᴴ = compressionUnitary m := by
  ext a b
  cases a <;> cases b <;> simp [compressionUnitary, eq_comm]

private lemma Centry (m : ℕ) (a b : Option (Qubits m)) :
    compressionUnitary m a b = match a,b with
      | none,none => 0
      | none,some _ => (c m : ℂ)
      | some _,none => (c m : ℂ)
      | some v,some w => (if v = w then 1 else 0) - (c m : ℂ)^2 := by
  cases a <;> cases b <;> simp [compressionUnitary,c]

private lemma Csq (m : ℕ) : compressionUnitary m * compressionUnitary m = 1 := by
  classical
  have hc : ((c m : ℂ)^2 * (2 : ℂ)^m) = 1 := by exact_mod_cast cnorm m
  have hc2 : (2 : ℂ)^m * (c m : ℂ)^2 = 1 := by linear_combination hc
  have hc4 : (c m : ℂ)^4 * (2 : ℂ)^m = (c m : ℂ)^2 := by
    calc _ = (c m : ℂ)^2 * ((c m : ℂ)^2 * (2 : ℂ)^m) := by ring
         _ = _ := by rw [hc]; ring
  ext a b
  cases a with
  | none => cases b <;> simp [Matrix.mul_apply, Fintype.sum_option, Centry,
       Fintype.card_fun, ← Finset.mul_sum, ← Finset.sum_mul, ← pow_two, hc2]
  | some a =>
    cases b with
    | none => simp [Matrix.mul_apply, Fintype.sum_option, Centry,
        Fintype.card_fun, ← Finset.mul_sum, ← Finset.sum_mul, ← pow_two, hc2]
    | some b =>
      simp only [Matrix.mul_apply, Fintype.sum_option, Centry]
      change (c m : ℂ) * c m + ∑ v : Qubits m,
        ((if a = v then 1 else 0) - (c m : ℂ)^2) *
        ((if v = b then 1 else 0) - (c m : ℂ)^2) = _
      simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
      simp [← Finset.mul_sum, ← Finset.sum_mul, Fintype.card_fun, hc4,
        ← pow_two, hc, Matrix.one_apply, eq_comm]
      split_ifs <;> linear_combination -hc4

private lemma loc_unitary (m : ℕ) (z : Qubits m) : (loc m z)ᴴ * loc m z = 1 := by
  have hp : (phase m z)ᴴ * phase m z = 1 := by
    ext a b
    cases a <;> cases b <;> simp [phase, Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose, sig, Matrix.one_apply]
    split_ifs <;> simp_all
  unfold loc
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Cstar]
  calc _ = compressionUnitary m * ((phase m z)ᴴ *
      (compressionUnitary m * compressionUnitary m) * phase m z) * compressionUnitary m := by
          simp only [Matrix.mul_assoc]
       _ = 1 := by rw [Csq, Matrix.mul_one, hp, Matrix.mul_one, Csq]

private lemma norm_act {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : Aᴴ * A = 1) (v : EuclideanSpace ℂ ι) : ‖act A v‖ = ‖v‖ := by
  have h : inner ℂ (act A v) (act A v) = inner ℂ v v := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, act, WithLp.ofLp_toLp]
    rw [dotProduct_comm, star_mulVec, dotProduct_mulVec, vecMul_vecMul, hA, vecMul_one, dotProduct_comm]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), h, ← norm_eq_sqrt_re_inner (𝕜 := ℂ)]

private lemma row_zero (m : ℕ) (z : Qubits m) (hz : z ≠ 0) (o : Option (Qubits m)) :
    loc m z (some 0) o = match o with
      | none => (c m : ℂ)
      | some v => (if v = 0 then 1 else 0) - (sig (dotBits z v)) * (c m : ℂ)^2 := by
  classical
  have hs := char_sum m z
  rw [if_neg hz] at hs
  have hzero : dotBits z 0 = false := by simp only [dotBits, Pi.zero_apply, Bool.zero_eq_false, Bool.and_false]; change (∑ _ : Fin m, (0 : Bool)) = 0; simp
  unfold loc
  rw [Matrix.mul_apply]
  simp_rw [phase, Matrix.mul_diagonal]
  simp only [Fintype.sum_option, Centry]
  cases o with
  | none =>
    dsimp only
    simp only [mul_zero]
    change (0 : ℂ) + ∑ v : Qubits m,
      ((if (0 : Qubits m) = v then 1 else 0) - (c m : ℂ)^2) *
        sig (dotBits z v) * (c m : ℂ) = _
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero, zero_add]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hs, mul_zero, zero_mul, sub_zero, hzero]
    norm_num [sig]
  | some v =>
    dsimp only
    simp only [mul_one, ← pow_two]
    change (c m : ℂ)^2 + ∑ u : Qubits m,
      (((if (0 : Qubits m) = u then 1 else 0) - (c m : ℂ)^2) * sig (dotBits z u)) *
        ((if u = v then 1 else 0) - (c m : ℂ)^2) = _
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
    simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero, zero_add]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hs, mul_zero, zero_mul, sub_zero, hzero]
    by_cases hv : v = 0
    · subst v
      simp only [hzero, if_pos rfl, sig, Bool.false_eq_true, if_false]
      ring
    · simp only [hv, Ne.symm hv, if_false, show sig false = (1:ℂ) from rfl]
      ring

private lemma loc_zero (m : ℕ) : loc m 0 = 1 := by
  have h : phase m 0 = 1 := by
    have hz (v : Qubits m) : dotBits 0 v = false := by
      simp only [dotBits, Pi.zero_apply, Bool.zero_eq_false, Bool.false_and]
      change (∑ _ : Fin m, (0 : Bool)) = 0; simp
    ext a b
    cases a <;> cases b <;> simp [phase, hz, sig, Matrix.one_apply, Matrix.diagonal_apply]
  simp only [loc, h, Matrix.mul_one, Csq]

private lemma row_bound (m : ℕ) (z : Qubits m) (v : EuclideanSpace ℂ (Option (Qubits m)))
    (hv : v (some 0) = 0) : ‖act (loc m z) v (some 0)‖^2 ≤ (2 * c m^2) * ‖v‖^2 := by
  classical
  by_cases hz : z = 0
  · subst z
    simp only [loc_zero, act, Matrix.one_mulVec, PiLp.toLp_apply, hv, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    positivity
  let r : Option (Qubits m) → ℂ := fun o => if o = some 0 then 0 else loc m z (some 0) o
  have he : act (loc m z) v (some 0) = ∑ o, r o * v o := by
    simp only [act, Matrix.mulVec, dotProduct, PiLp.toLp_apply]
    apply Finset.sum_congr rfl
    intro o _; by_cases ho : o = some 0 <;> simp [r, ho, hv]
  have hr : ∑ o, ‖r o‖^2 ≤ 2*c m^2 := by
    have hn : ‖(c m : ℂ)‖^2 = c m^2 := by simp
    have hsg (v : Qubits m) : ‖sig (dotBits z v)‖ = 1 := by simp [sig]; split_ifs <;> norm_num
    have hc4 : (2 : ℝ)^m * c m^4 = c m^2 := by nlinarith [cnorm m, sq_nonneg (c m)]
    simp only [Fintype.sum_option, r, row_zero m z hz]
    simp only [Option.noConfusion, ↓reduceIte, Option.some.injEq]
    have hsum : ∑ v : Qubits m, ‖if v = 0 then (0 : ℂ) else
        (if v = 0 then 1 else 0) - sig (dotBits z v) * (c m : ℂ)^2‖^2 ≤
        ∑ _v : Qubits m, c m^4 := by
      apply Finset.sum_le_sum
      intro u _
      by_cases hu : u = 0
      · simpa [hu] using (show (0:ℝ) ≤ c m^4 by positivity)
      · simp [hu, norm_mul, norm_pow, hsg, Complex.norm_real, Real.norm_eq_abs, ← pow_mul]
    have hcard : (Fintype.card (Qubits m) : ℝ) = (2 : ℝ)^m := by simp [Fintype.card_fun]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, hc4] at hsum
    simp only [reduceCtorEq, if_false, hn]
    linarith
  rw [he]
  have htri := norm_sum_le (Finset.univ : Finset (Option (Qubits m))) (fun o => r o * v o)
  simp only [norm_mul] at htri
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Option (Qubits m)))
    (fun o => ‖r o‖) (fun o => ‖v o‖)
  have hnorm : ∑ o, ‖v o‖^2 = ‖v‖^2 := (EuclideanSpace.norm_sq_eq v).symm
  have h1 : ‖∑ o, r o*v o‖^2 ≤ (∑ o, ‖r o‖*‖v o‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  rw [hnorm] at hcs
  exact h1.trans (hcs.trans (mul_le_mul_of_nonneg_right hr (sq_nonneg _)))


private noncomputable def proj {ι : Type*} (P : ι → Prop) (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι := by
  classical
  exact WithLp.toLp 2 fun i => if P i then v i else 0

private lemma proj_norm_le {ι : Type*} [Fintype ι] (P : ι → Prop) (v : EuclideanSpace ℂ ι) :
    ‖proj P v‖ ≤ ‖v‖ := by
  classical
  have h : ‖proj P v‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : P i <;> simp [proj, hi, sq_nonneg]
  nlinarith [norm_nonneg (proj P v), norm_nonneg v]

private abbrev Reg (n m : ℕ) (W : Type*) :=
  (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
private abbrev Rest {n : ℕ} (m : ℕ) (x : Fin n) := {i : Fin n // i ≠ x} → Option (Qubits m)

private noncomputable def join {n m : ℕ} (x : Fin n) (o : Option (Qubits m)) (r : Rest m x) :
    Fin n → Option (Qubits m) := (Equiv.funSplitAt x _).symm (o,r)

private lemma join_self {n m : ℕ} (x : Fin n) (o : Option (Qubits m)) (r : Rest m x) :
    join x o r x = o := by simp [join, Equiv.funSplitAt, Equiv.piSplitAt]

private lemma join_ne {n m : ℕ} (x : Fin n) (o : Option (Qubits m)) (r : Rest m x)
    (i : Fin n) (hi : i ≠ x) : join x o r i = r ⟨i,hi⟩ := by
  simp [join, Equiv.funSplitAt, Equiv.piSplitAt, hi]

private lemma join_update {n m : ℕ} (x : Fin n) (o t : Option (Qubits m)) (r : Rest m x) :
    Function.update (join x t r) x o = join x o r := by
  classical
  ext i
  by_cases hi : i = x
  · subst i; simp [join_self]
  · simp [Function.update_of_ne hi, join_ne x _ r i hi]

private noncomputable def slice {n m : ℕ} {W : Type*} (v : EuclideanSpace ℂ (Reg n m W))
    (a : (Fin n × Qubits m) × W) (r : Rest m a.1.1) : EuclideanSpace ℂ (Option (Qubits m)) :=
  WithLp.toLp 2 fun o => v (a, join a.1.1 o r)

private lemma sum_split {n m : ℕ} {W : Type*} [Fintype W] (f : Reg n m W → ℝ) :
    ∑ p, f p = ∑ a : (Fin n × Qubits m) × W, ∑ r : Rest m a.1.1,
      ∑ o : Option (Qubits m), f (a, join a.1.1 o r) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← (Equiv.funSplitAt a.1.1 (Option (Qubits m))).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

private lemma norm_split {n m : ℕ} {W : Type*} [Fintype W] (v : EuclideanSpace ℂ (Reg n m W)) :
    ‖v‖^2 = ∑ a : (Fin n × Qubits m) × W, ∑ r : Rest m a.1.1, ‖slice v a r‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, sum_split]
  congr 1
  ext a
  congr 1
  ext r
  simp only [EuclideanSpace.norm_sq_eq, slice, PiLp.toLp_apply]

private lemma slice_action {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (v : EuclideanSpace ℂ (Reg n m W)) (a : (Fin n × Qubits m) × W) (r : Rest m a.1.1) :
    slice (act (compressedPhaseOracle n m W) v) a r = act (loc m a.1.2) (slice v a r) := by
  ext t
  change act (compressedPhaseOracle n m W) v (a,join a.1.1 t r) = _
  rw [QAlgorithms.Childs.compressedPhaseOracle_local_action]
  simp only [join_self, join_update]
  rfl

private lemma oracle_norm {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (v : EuclideanSpace ℂ (Reg n m W)) : ‖act (compressedPhaseOracle n m W) v‖ = ‖v‖ := by
  have h : ‖act (compressedPhaseOracle n m W) v‖^2 = ‖v‖^2 := by
    rw [norm_split, norm_split]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro r _
    rw [slice_action, norm_act _ (loc_unitary _ _)]
  nlinarith [norm_nonneg v, norm_nonneg (act (compressedPhaseOracle n m W) v)]

private def zeroIn {n m : ℕ} {W : Type*} (p : Reg n m W) : Prop := ∃ i, p.2 i = some 0

private lemma zero_join {n m : ℕ} {W : Type*} (a : (Fin n × Qubits m) × W)
    (r : Rest m a.1.1) (o : Option (Qubits m)) :
    zeroIn (a,join a.1.1 o r) ↔ o = some 0 ∨ ∃ i, r i = some 0 := by
  constructor
  · rintro ⟨i,hi⟩
    by_cases hx : i = a.1.1
    · subst i; exact Or.inl ((join_self _ _ _).symm.trans hi)
    · exact Or.inr ⟨⟨i,hx⟩,(join_ne _ _ _ _ hx).symm.trans hi⟩
  · rintro (ho|⟨i,hi⟩)
    · exact ⟨a.1.1,(join_self _ _ _).trans ho⟩
    · exact ⟨i.val,(join_ne _ _ _ _ i.property).trans hi⟩

private lemma oracle_leak {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (v : EuclideanSpace ℂ (Reg n m W)) (hv : ∀ p, zeroIn p → v p = 0) :
    ‖proj zeroIn (act (compressedPhaseOracle n m W) v)‖^2 ≤ (2*c m^2)*‖v‖^2 := by
  classical
  rw [norm_split, norm_split, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : ∃ i, r i = some 0
  · have hs : slice v a r = 0 := by
      ext o
      exact hv _ ((zero_join _ _ _).mpr (Or.inr hr))
    have ht : slice (proj zeroIn (act (compressedPhaseOracle n m W) v)) a r =
        slice (act (compressedPhaseOracle n m W) v) a r := by
      ext o
      simp [slice, proj, (zero_join _ _ _).mpr (Or.inr hr)]
    rw [ht, slice_action, hs]
    simp [act]
  · have ht : slice (proj zeroIn (act (compressedPhaseOracle n m W) v)) a r =
        EuclideanSpace.single (some 0) (act (loc m a.1.2) (slice v a r) (some 0)) := by
      have hs := slice_action v a r
      ext o
      have he := congrArg (fun t : EuclideanSpace ℂ (Option (Qubits m)) => t o) hs
      simp only [slice, PiLp.toLp_apply] at he
      simp only [slice, proj, PiLp.toLp_apply, zero_join, hr, or_false,
        PiLp.single_apply]
      by_cases ho : o = some 0
      · subst o; simpa using he
      · simp [ho, Ne.symm ho]
    rw [ht, PiLp.norm_single]
    apply row_bound
    exact hv _ ((zero_join _ _ _).mpr (Or.inl rfl))

private lemma projection_action {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (v : EuclideanSpace ℂ (Reg n m W)) : act (containsZeroProj n m W) v = proj zeroIn v := by
  classical
  ext p
  simp only [containsZeroProj, act, Matrix.mulVec_diagonal, proj, PiLp.toLp_apply]
  by_cases hp : zeroIn p <;> simp [zeroIn] at hp ⊢ <;> simp_all

end CompressedBound

open CompressedBound

theorem solution {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (ψ : EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))))
    (hψ : IsState ψ) :
    ‖act (containsZeroProj n m W) (act (compressedPhaseOracle n m W) ψ)‖ ≤
      ‖act (containsZeroProj n m W) ψ‖ + Real.sqrt (2 / 2 ^ m) := by
  classical
  let u := proj zeroIn ψ
  let v := proj (fun p => ¬zeroIn p) ψ
  have hsum : ψ = u + v := by
    ext p
    by_cases hp : zeroIn p <;> simp [u,v,proj,hp]
  have hv : ∀ p, zeroIn p → v p = 0 := by
    intro p hp; simp [v,proj,hp]
  have hadd : proj zeroIn (act (compressedPhaseOracle n m W) ψ) =
      proj zeroIn (act (compressedPhaseOracle n m W) u) +
        proj zeroIn (act (compressedPhaseOracle n m W) v) := by
    conv_lhs => rw [hsum]
    ext p
    simp only [act, Matrix.mulVec_add, WithLp.toLp_add, PiLp.add_apply, proj, PiLp.toLp_apply]
    split_ifs <;> simp [Matrix.mulVec_add]
  have hu := (proj_norm_le zeroIn (act (compressedPhaseOracle n m W) u)).trans_eq (oracle_norm u)
  have hvnorm : ‖v‖ ≤ 1 := by simpa [IsState] using (proj_norm_le (fun p => ¬zeroIn p) ψ).trans_eq hψ
  have hleak := oracle_leak v hv
  have hc : 2*c m^2 = 2/(2:ℝ)^m := by
    have hn : (2:ℝ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
    apply (eq_div_iff hn).mpr
    nlinarith [cnorm m]
  rw [hc] at hleak
  have hsmall : ‖proj zeroIn (act (compressedPhaseOracle n m W) v)‖ ≤ Real.sqrt (2/2^m) := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2/2^m by positivity)
    have hb : ‖v‖^2 ≤ 1 := by nlinarith [norm_nonneg v]
    have he := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ 2/2^m by positivity)
    nlinarith [Real.sqrt_nonneg (2/2^m), norm_nonneg (proj zeroIn (act (compressedPhaseOracle n m W) v))]
  rw [projection_action, projection_action, hadd]
  exact (norm_add_le _ _).trans (add_le_add hu hsmall)
