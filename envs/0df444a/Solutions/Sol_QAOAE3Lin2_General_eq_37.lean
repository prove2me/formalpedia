-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_37
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:24:26.844637+00:00
-- url     : https://prove2.me/submissions/d35f5856-0ba1-4eb8-9fdc-53ec58a0b9be

import Definitions.Def_QAOAE3Lin2_General_Setting

open QAlgorithms
open QAOAE3Lin2.General

section MixerFormula

private noncomputable def Xop (n : ℕ) (q : Fin n) : Matrix (Qubits n) (Qubits n) ℂ :=
  Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli q Stabilizer.Pauli.X)

private lemma Xop_apply (n : ℕ) (q : Fin n) (x y : Qubits n) :
    Xop n q x y = if y = Function.update x q (!(x q)) then 1 else 0 := by
  unfold Xop
  dsimp only [Stabilizer.CliffordOp.mat]
  unfold embedOp
  simp only [Matrix.of_apply]
  by_cases h2 : y = Function.update x q (!(x q))
  · subst h2; rw [if_pos rfl]
    rw [if_pos (fun a ha => (Function.update_of_ne (fun h => ha ⟨(0 : Fin 1), h.symm⟩) _ _).symm)]
    simp only [Gate.ofMatrix1, Function.comp_apply, Stabilizer.Pauli.mat, pauliX,
      Matrix.submatrix_apply, Matrix.of_apply]
    change (if x q = Function.update x q (!(x q)) q then (0 : ℂ) else 1) = 1
    rw [Function.update_self]
    cases x q <;> rfl
  · rw [if_neg h2]
    split_ifs with h1
    · simp only [Gate.ofMatrix1, Function.comp_apply, Stabilizer.wire1, Stabilizer.Pauli.mat, pauliX,
        Matrix.submatrix_apply]
      have hyq : y q ≠ !(x q) := by
        intro h; apply h2; ext r
        by_cases hr : r = q
        · rw [hr, Function.update_self]; exact h
        · rw [Function.update_of_ne hr]; exact (h1 r fun ⟨_, hz⟩ => hr hz.symm).symm
      cases hx : x q <;> cases hy : y q <;> simp_all
    · rfl

private lemma Xop_mul_self (n : ℕ) (q : Fin n) : Xop n q * Xop n q = 1 := by
  ext x y
  simp only [Matrix.mul_apply, Xop_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Function.update x q (!(x q)))]
  · have hup : Function.update (Function.update x q (!(x q))) q
        (!(Function.update x q (!(x q)) q)) = x := by
      ext r; by_cases hr : r = q
      · subst hr; simp
      · simp [Function.update_of_ne hr]
    simp only [↓reduceIte, one_mul, hup, eq_comm]
  · intro z _ hz
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma Xop_comm (n : ℕ) (p q : Fin n) : Commute (Xop n p) (Xop n q) := by
  by_cases hpq : p = q
  · subst hpq; rfl
  · ext x y
    simp only [Matrix.mul_apply, Xop_apply]
    rw [Finset.sum_eq_single (Function.update x p (!(x p)))]
    · rw [Finset.sum_eq_single (Function.update x q (!(x q)))]
      · rw [Function.update_of_ne (Ne.symm hpq), Function.update_of_ne hpq,
          Function.update_comm hpq]
        simp only [↓reduceIte, mul_one, one_mul]
      · intro z _ hz; simp [hz]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro z _ hz; simp [hz]
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma matrix_exp_eq_linfty {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    NormedSpace.exp M =
      (letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
      NormedSpace.exp M) := by
  have ha :
      (letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
      HasSum (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) (NormedSpace.exp M)) := by
    letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
    have hpow_norm : ∀ k : ℕ, ‖M ^ (k + 1)‖ ≤ ‖M‖ ^ (k + 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, pow_succ]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
    have hs : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) := by
      rw [← summable_nat_add_iff 1]
      refine Summable.of_norm_bounded
        ((Real.summable_pow_div_factorial ‖M‖).comp_injective Nat.succ_injective) fun k => ?_
      simp only [Function.comp_apply, norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
      gcongr
      exact hpow_norm k
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
    exact hs.hasSum
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]

private lemma matrix_exp_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    HasSum (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) (NormedSpace.exp M) := by
  rw [matrix_exp_eq_linfty M]
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  have hpow_norm : ∀ k : ℕ, ‖M ^ (k + 1)‖ ≤ ‖M‖ ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
  have hs : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial ‖M‖).comp_injective Nat.succ_injective) fun k => ?_
    simp only [Function.comp_apply, norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    gcongr
    exact hpow_norm k
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  exact hs.hasSum

private lemma matrix_exp_add_of_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : Commute A B) :
    NormedSpace.exp (A + B) = NormedSpace.exp A * NormedSpace.exp B := by
  rw [matrix_exp_eq_linfty (A + B), matrix_exp_eq_linfty A, matrix_exp_eq_linfty B]
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_add_of_commute h

private lemma exp_smul_idem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M * M = M) (a : ℂ) :
    NormedSpace.exp (a • M) = 1 + (Complex.exp a - 1) • M := by
  have hpow : ∀ k : ℕ, (a • M) ^ (k + 1) = a ^ (k + 1) • M := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, smul_mul_smul_comm, hM, ← pow_succ]
  have hs : Summable (fun k : ℕ => (k.factorial : ℂ)⁻¹ * a ^ k) := by
    have := NormedSpace.expSeries_summable (𝕂 := ℂ) a
    simpa [NormedSpace.expSeries, smul_eq_mul] using this
  have hsum : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * a ^ k) (Complex.exp a) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
    simpa [NormedSpace.expSeries, smul_eq_mul] using hs.hasSum
  have hsum_tail : HasSum (fun k : ℕ => ((k + 1).factorial : ℂ)⁻¹ * a ^ (k + 1))
      (Complex.exp a - 1) := by
    have := (hasSum_nat_add_iff' (f := fun k : ℕ => (k.factorial : ℂ)⁻¹ * a ^ k) 1).2 hsum
    simpa [Finset.sum_range_one] using this
  have hsum_M : HasSum (fun k : ℕ => (((k + 1).factorial : ℂ)⁻¹ * a ^ (k + 1)) • M)
      ((Complex.exp a - 1) • M) :=
    hsum_tail.smul_const M
  have hsum_all : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ • (a • M) ^ k)
      (1 + (Complex.exp a - 1) • M) :=
    (hasSum_nat_add_iff' 1).1 (by
      rw [Finset.sum_range_one]
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
        add_sub_cancel_left]
      exact hsum_M.congr_fun fun k => by rw [hpow, smul_smul])
  exact (matrix_exp_hasSum (a • M)).unique hsum_all

private lemma exp_neg_I_mul_sq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A * A = 1) (θ : ℝ) :
    NormedSpace.exp (-(Complex.I * (θ : ℂ)) • A) =
      (Real.cos θ : ℂ) • 1 - (Complex.I * (Real.sin θ : ℂ)) • A := by
  let P : Matrix ι ι ℂ := (1 / 2 : ℂ) • (1 + A)
  let Q : Matrix ι ι ℂ := (1 / 2 : ℂ) • (1 - A)
  have hPP : P * P = P := by
    dsimp [P]; rw [smul_mul_smul_comm, mul_add, add_mul, add_mul, one_mul, mul_one, hA]
    ext i j; simp; by_cases hij : i = j <;> simp [hij] <;> ring
  have hQQ : Q * Q = Q := by
    dsimp [Q]; rw [smul_mul_smul_comm, mul_sub, sub_mul, sub_mul, one_mul, mul_one, hA]
    ext i j; simp; by_cases hij : i = j <;> simp [hij] <;> ring
  have hPQ : P * Q = 0 := by
    dsimp [P, Q]; rw [smul_mul_smul_comm, mul_sub, add_mul, add_mul, one_mul, mul_one, hA]
    ext i j; simp; ring
  have hQP : Q * P = 0 := by
    dsimp [P, Q]; rw [smul_mul_smul_comm, mul_add, sub_mul, sub_mul, one_mul, mul_one, hA]
    ext i j; simp
  have hPaddQ : P + Q = 1 := by
    dsimp [P, Q]; ext i j; simp; by_cases hij : i = j <;> simp [hij] <;> ring
  have hPsubQ : P - Q = A := by
    dsimp [P, Q]; ext i j; simp; by_cases hij : i = j <;> simp [hij] <;> ring
  have hdecomp : -(Complex.I * (θ : ℂ)) • A =
      (-(Complex.I * (θ : ℂ))) • P + (Complex.I * (θ : ℂ)) • Q := by
    rw [← hPsubQ]; ext i j; simp; ring
  have hcomm : Commute ((-(Complex.I * (θ : ℂ))) • P) ((Complex.I * (θ : ℂ)) • Q) := by
    simp only [Commute, SemiconjBy, Matrix.smul_mul, Matrix.mul_smul, hPQ, hQP, smul_zero]
  rw [hdecomp, matrix_exp_add_of_commute hcomm, exp_smul_idem P hPP,
    exp_smul_idem Q hQQ]
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, smul_mul_smul_comm, hPQ, smul_zero, add_zero,
    one_mul]
  have h1 : 1 + (Complex.exp (-(Complex.I * (θ : ℂ))) - 1) • P +
      (Complex.exp (Complex.I * (θ : ℂ)) - 1) • Q =
      Complex.exp (-(Complex.I * (θ : ℂ))) • P + Complex.exp (Complex.I * (θ : ℂ)) • Q := by
    rw [← hPaddQ]; ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have h2 : 1 + (Complex.exp (Complex.I * (θ : ℂ)) - 1) • Q +
      (Complex.exp (-(Complex.I * (θ : ℂ))) - 1) • P =
      1 + (Complex.exp (-(Complex.I * (θ : ℂ))) - 1) • P +
      (Complex.exp (Complex.I * (θ : ℂ)) - 1) • Q := by
    ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  rw [h2, h1]
  have hexp1 : Complex.exp (-(Complex.I * (θ : ℂ))) = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
    rw [show -(Complex.I * (θ : ℂ)) = (-θ : ℝ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have hexp2 : Complex.exp (Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
    rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring, Complex.exp_mul_I]
    push_cast; ring
  rw [hexp1, hexp2]
  dsimp [P, Q]
  ext i j
  simp
  by_cases hij : i = j <;> simp [hij] <;> ring

private noncomputable def Mop (n : ℕ) (q : Fin n) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (1 - Complex.I • Xop n q)

private lemma Mop_apply (n : ℕ) (q : Fin n) (x y : Qubits n) :
    Mop n q x y = if ∀ r ≠ q, x r = y r then
      (Real.sqrt 2 : ℂ)⁻¹ * (if x q = y q then 1 else -Complex.I) else 0 := by
  unfold Mop
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Xop_apply, smul_eq_mul]
  by_cases hother : ∀ r ≠ q, x r = y r
  · rw [if_pos hother]
    by_cases hq : x q = y q
    · have hxy : x = y := funext fun r => if hr : r = q then hr ▸ hq else hother r hr
      have hupd : y ≠ Function.update x q (!(x q)) := by
        intro h; have := congr_fun h q; simp [hq] at this
      simp [hxy, hupd, hq]
    · have hxy : x ≠ y := fun h => hq (congr_fun h q)
      have hupd : y = Function.update x q (!(x q)) := by
        ext r; by_cases hr : r = q
        · rw [hr]; cases hx : x q <;> cases hy : y q <;> simp_all
        · simp [Function.update_of_ne hr, (hother r hr).symm]
      simp [hxy, hupd, hq]
  · have hxy : x ≠ y := fun h => hother fun r _ => congr_fun h r
    have hupd : y ≠ Function.update x q (!(x q)) := by
      intro h; apply hother; intro r hr; rw [h, Function.update_of_ne hr]
    simp [hother, hxy, hupd]

private lemma exp_mixer_pi_div_4 (n : ℕ) :
    NormedSpace.exp (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • qaoaMixer n) =
      ((List.finRange n).map (Mop n)).prod := by
  have hsum : -(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • qaoaMixer n =
      ∑ q ∈ (List.finRange n).toFinset, (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • Xop n q) := by
    unfold qaoaMixer Xop
    rw [Finset.smul_sum]
    congr 1
    ext q
    simp
  rw [hsum]
  have hprod : ∀ l : List (Fin n), l.Nodup →
      NormedSpace.exp (∑ q ∈ l.toFinset, (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • Xop n q)) =
        (l.map (Mop n)).prod := by
    intro l hl
    induction l with
    | nil => simp
    | cons q l ih =>
      simp only [List.nodup_cons] at hl
      have hqs : q ∉ l.toFinset := by simpa [List.mem_toFinset] using hl.1
      rw [List.toFinset_cons, Finset.sum_insert hqs, List.map_cons, List.prod_cons]
      have hcomm : Commute (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • Xop n q)
          (∑ p ∈ l.toFinset, (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • Xop n p)) := by
        refine Commute.sum_right _ _ _ fun p _ => ?_
        exact (Xop_comm n q p).smul_left _ |>.smul_right _
      rw [matrix_exp_add_of_commute hcomm, ih hl.2]
      congr 1
      rw [exp_neg_I_mul_sq_one _ (Xop_mul_self n q) (Real.pi / 4)]
      rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
      have hsq : (Real.sqrt 2 / 2 : ℂ) = (Real.sqrt 2 : ℂ)⁻¹ := by
        have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_cast; positivity
        field_simp
        norm_cast
        exact Real.sq_sqrt (by norm_num)
      unfold Mop
      push_cast
      rw [hsq]
      ext x y
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      ring
  exact hprod (List.finRange n) (List.nodup_finRange n)

private lemma prod_Mop_apply (n : ℕ) (l : List (Fin n)) (hl : l.Nodup) (x y : Qubits n) :
    ((l.map (Mop n)).prod) x y = if ∀ r ∉ l, x r = y r then
      ∏ q ∈ l.toFinset, ((Real.sqrt 2 : ℂ)⁻¹ * (if x q = y q then 1 else -Complex.I)) else 0 := by
  induction l generalizing x y with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.one_apply, List.not_mem_nil,
      not_false_eq_true, forall_true_left, List.toFinset_nil, Finset.prod_empty]
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy]
      by_contra h; push_neg at h; exact hxy (funext h)
  | cons q l ih =>
    simp only [List.nodup_cons] at hl
    have hqs : q ∉ l.toFinset := by simpa [List.mem_toFinset] using hl.1
    rw [List.map_cons, List.prod_cons, Matrix.mul_apply, List.toFinset_cons, Finset.prod_insert hqs]
    rw [Finset.sum_eq_single (Function.update x q (y q))]
    · rw [Mop_apply, ih hl.2]
      by_cases hother : ∀ r ∉ q :: l, x r = y r
      · have h1 : ∀ r ≠ q, x r = Function.update x q (y q) r := by
          intro r hr; simp [Function.update_of_ne hr]
        have h2 : ∀ r ∉ l, Function.update x q (y q) r = y r := by
          intro r hr
          by_cases hrq : r = q
          · subst hrq; simp [Function.update_self]
          · rw [Function.update_of_ne hrq]
            exact hother r (by simp [List.mem_cons, hrq, hr])
        rw [if_pos h1, if_pos h2, if_pos hother, Function.update_self]
        refine congr_arg₂ (· * ·) rfl (Finset.prod_congr rfl fun r hr => ?_)
        have hrq : r ≠ q := fun h => hqs (h ▸ hr)
        simp [Function.update_of_ne hrq]
      · simp only [hother, ↓reduceIte]
        by_cases h1 : ∀ r ≠ q, x r = Function.update x q (y q) r
        · have h2 : ¬ ∀ r ∉ l, Function.update x q (y q) r = y r := by
            intro h2; apply hother; intro r hr
            simp only [List.mem_cons, not_or] at hr
            have := h2 r hr.2
            rwa [Function.update_of_ne hr.1] at this
          simp [h2]
        · simp [h1]
    · intro z _ hz
      rw [Mop_apply]
      by_cases h1 : ∀ r ≠ q, x r = z r
      · simp only [h1, ↓reduceIte, ih hl.2]
        by_cases h2 : ∀ r ∉ l, z r = y r
        · exfalso; apply hz; ext r
          by_cases hr : r = q
          · subst hr; rw [Function.update_self]; exact h2 r hl.1
          · rw [Function.update_of_ne hr]; exact (h1 r hr).symm
        · simp [h2]
      · simp [h1]
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma exp_mixer_pi_div_4_apply (n : ℕ) (x y : Qubits n) :
    NormedSpace.exp (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • qaoaMixer n) x y =
      ∏ q : Fin n, ((Real.sqrt 2 : ℂ)⁻¹ * (if x q = y q then 1 else -Complex.I)) := by
  rw [exp_mixer_pi_div_4, prod_Mop_apply n (List.finRange n) (List.nodup_finRange n) x y]
  have hmem : ∀ r : Fin n, r ∈ List.finRange n := List.mem_finRange
  have hto : (List.finRange n).toFinset = Finset.univ := by ext r; simp [hmem]
  simp [hmem, hto]

end MixerFormula

section CorrClauseSin

private def flip3 {n : ℕ} (a b c : Fin n) (y : Qubits n) : Qubits n :=
  fun q => if q = a ∨ q = b ∨ q = c then !(y q) else y q

private def flipMask {n : ℕ} (a b c : Fin n) (p q r : Bool) (y : Qubits n) : Qubits n :=
  fun v => if v = a then xor (y a) p else if v = b then xor (y b) q else if v = c then xor (y c) r else y v

private lemma flipMask_involutive {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p q r : Bool) : Function.Involutive (flipMask a b c p q r) := by
  intro y; ext v
  unfold flipMask
  by_cases hva : v = a
  · subst hva; simp [Bool.xor_assoc]
  · by_cases hvb : v = b
    · subst hvb; simp [hva, Bool.xor_assoc]
    · by_cases hvc : v = c
      · subst hvc; simp [hva, hvb, Bool.xor_assoc]
      · simp [hva, hvb, hvc]

private lemma exp_diagonal_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (d : ι → ℂ) :
    NormedSpace.exp (c • Matrix.diagonal d) = Matrix.diagonal (fun x => Complex.exp (c * d x)) := by
  have hpow : ∀ k : ℕ, (c • Matrix.diagonal d) ^ k = Matrix.diagonal (fun x => (c * d x) ^ k) := by
    intro k
    induction k with
    | zero => simp [Matrix.diagonal_one]
    | succ k ih =>
      rw [pow_succ, ih, ← Matrix.diagonal_smul, Matrix.diagonal_mul_diagonal]
      congr 1
  let diagLM : (ι → ℂ) →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := Matrix.diagonal
      map_add' := fun f g => by ext i j; by_cases h : i = j <;> simp [h]
      map_smul' := fun a f => by ext i j; by_cases h : i = j <;> simp [h] }
  let diagCLM : (ι → ℂ) →L[ℂ] Matrix ι ι ℂ := diagLM.toContinuousLinearMap
  have hsum : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ • (fun x => (c * d x) ^ k))
      (fun x => Complex.exp (c * d x)) := by
    refine Pi.hasSum.mpr fun x => ?_
    have hs : Summable (fun k : ℕ => (k.factorial : ℂ)⁻¹ * (c * d x) ^ k) := by
      have := NormedSpace.expSeries_summable (𝕂 := ℂ) (c * d x)
      simpa [NormedSpace.expSeries, smul_eq_mul] using this
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
    simpa [NormedSpace.expSeries, smul_eq_mul] using hs.hasSum
  have hmap := diagCLM.hasSum hsum
  have hterm : ∀ k : ℕ, (diagCLM ((k.factorial : ℂ)⁻¹ • fun x => (c * d x) ^ k)) =
      (k.factorial : ℂ)⁻¹ • (c • Matrix.diagonal d) ^ k := by
    intro k; rw [hpow]; simp [diagCLM, diagLM, Matrix.diagonal_smul]
  have hsum' : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ • (c • Matrix.diagonal d) ^ k)
      (Matrix.diagonal fun x => Complex.exp (c * d x)) := by
    change HasSum _ (diagCLM fun x => Complex.exp (c * d x))
    simpa only [hterm] using hmap
  exact (matrix_exp_hasSum (c • Matrix.diagonal d)).unique hsum'

private lemma sqrt_two_pow (n : ℕ) : Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

private lemma qaoaState1_pi_div_4 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (γ : ℝ) (x : Qubits n) :
    qaoaState1 tri rhs (-γ) (Real.pi / 4) x =
      ((2 : ℂ) ^ n)⁻¹ * ∑ y : Qubits n,
        (∏ q : Fin n, (if x q = y q then (1 : ℂ) else -Complex.I)) *
          Complex.exp (Complex.I * (γ : ℂ) * (satCount tri rhs y : ℂ)) := by
  unfold qaoaState1 qaoaUnitary
  have hord : orderedProd (fun _ : Fin 1 =>
      NormedSpace.exp (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • qaoaMixer n) *
        NormedSpace.exp (-(Complex.I * ((-γ : ℝ) : ℂ)) • problemHamiltonian (satCount tri rhs))) =
      NormedSpace.exp (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • qaoaMixer n) *
        NormedSpace.exp (-(Complex.I * ((-γ : ℝ) : ℂ)) • problemHamiltonian (satCount tri rhs)) := by
    simp [orderedProd]
  rw [hord]
  have hdiag : NormedSpace.exp (-(Complex.I * ((-γ : ℝ) : ℂ)) • problemHamiltonian (satCount tri rhs)) =
      Matrix.diagonal (fun y => Complex.exp (Complex.I * (γ : ℂ) * (satCount tri rhs y : ℂ))) := by
    unfold problemHamiltonian
    rw [exp_diagonal_smul]
    congr 1; ext y; congr 1; push_cast; ring
  rw [hdiag]
  simp only [act, Matrix.mul_diagonal, Matrix.mulVec, dotProduct, uniformState,
    exp_mixer_pi_div_4_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hcard : (Fintype.card (Qubits n) : ℝ) = (2 : ℝ) ^ n := by
    simp [Qubits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hcard]
  have hsq : ((Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹ ^ n) = ((2 : ℂ) ^ n)⁻¹ := by
    rw [sqrt_two_pow n]
    push_cast
    rw [← inv_pow, ← mul_pow, ← mul_inv]
    have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      norm_cast; exact Real.mul_self_sqrt (by norm_num)
    rw [h2, inv_pow]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  calc ((Real.sqrt 2 : ℂ)⁻¹ ^ n * ∏ q : Fin n, if x q = y q then (1 : ℂ) else -Complex.I) *
        Complex.exp (Complex.I * (γ : ℂ) * (satCount tri rhs y : ℂ)) *
        ((Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹)
      = (((Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹ ^ n)) *
          ((∏ q : Fin n, if x q = y q then (1 : ℂ) else -Complex.I) *
            Complex.exp (Complex.I * (γ : ℂ) * (satCount tri rhs y : ℂ))) := by ring
    _ = ((2 : ℂ) ^ n)⁻¹ * ((∏ q : Fin n, if x q = y q then (1 : ℂ) else -Complex.I) *
          Complex.exp (Complex.I * (γ : ℂ) * (satCount tri rhs y : ℂ))) := by rw [hsq]

private lemma prob_qaoaState1_pi_div_4 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (γ : ℝ) (x : Qubits n) :
    prob (qaoaState1 tri rhs (-γ) (Real.pi / 4)) x =
      ((2 : ℝ) ^ (2 * n))⁻¹ *
        (∑ y : Qubits n, ∑ z : Qubits n,
          Complex.exp (Complex.I * (γ : ℂ) * ((satCount tri rhs y : ℂ) - (satCount tri rhs z : ℂ))) *
            ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
              (if x q = z q then (1 : ℂ) else Complex.I))).re := by
  have hprob : prob (qaoaState1 tri rhs (-γ) (Real.pi / 4)) x =
      (qaoaState1 tri rhs (-γ) (Real.pi / 4) x *
        star (qaoaState1 tri rhs (-γ) (Real.pi / 4) x)).re := by
    have hinner : inner ℂ (ket x) (qaoaState1 tri rhs (-γ) (Real.pi / 4)) =
        qaoaState1 tri rhs (-γ) (Real.pi / 4) x := by
      simp [ket, EuclideanSpace.inner_single_left]
    rw [prob, hinner, ← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _),
      ← Complex.mul_conj]
    rfl
  rw [hprob, qaoaState1_pi_div_4]
  simp only [star_mul, star_inv₀, star_pow, Complex.star_def, Complex.conj_ofNat, map_sum,
    map_mul]
  have hstar_if : ∀ (q : Fin n) (z : Qubits n),
      (starRingEnd ℂ) (if x q = z q then (1 : ℂ) else -Complex.I) =
        if x q = z q then (1 : ℂ) else Complex.I := by
    intro q z; split_ifs <;> simp
  have hstar_exp : ∀ z : Qubits n,
      (starRingEnd ℂ) (Complex.exp (Complex.I * (γ : ℂ) * (satCount tri rhs z : ℂ))) =
        Complex.exp (-(Complex.I * (γ : ℂ) * (satCount tri rhs z : ℂ))) := by
    intro z
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  have hprod_conj : ∀ z : Qubits n,
      (starRingEnd ℂ) (∏ q : Fin n, if x q = z q then (1 : ℂ) else -Complex.I) =
        ∏ q : Fin n, if x q = z q then (1 : ℂ) else Complex.I := by
    intro z; rw [map_prod]; refine Finset.prod_congr rfl fun q _ => hstar_if q z
  simp only [hprod_conj, hstar_exp]
  have h2n : (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) = (((2 : ℝ) ^ (2 * n) : ℝ) : ℂ)⁻¹ := by
    push_cast; rw [← mul_inv, ← pow_add, two_mul]
  have hmul : (((2 : ℂ) ^ n)⁻¹ * ∑ y : Qubits n,
        (∏ q : Fin n, if x q = y q then (1 : ℂ) else -Complex.I) *
          Complex.exp (Complex.I * ↑γ * ↑(satCount tri rhs y))) *
      ∑ z : Qubits n,
        (∏ q : Fin n, if x q = z q then (1 : ℂ) else Complex.I) *
          Complex.exp (-(Complex.I * ↑γ * ↑(satCount tri rhs z))) * ((2 : ℂ) ^ n)⁻¹ =
      (((2 : ℝ) ^ (2 * n) : ℝ) : ℂ)⁻¹ * ∑ y : Qubits n, ∑ z : Qubits n,
        Complex.exp (Complex.I * ↑γ * (↑(satCount tri rhs y) - ↑(satCount tri rhs z))) *
          ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
            (if x q = z q then (1 : ℂ) else Complex.I)) := by
    rw [← Finset.sum_mul]
    have : ∀ y : Qubits n,
        (∏ q : Fin n, if x q = y q then (1 : ℂ) else -Complex.I) *
          Complex.exp (Complex.I * ↑γ * ↑(satCount tri rhs y)) *
          ∑ z : Qubits n, (∏ q : Fin n, if x q = z q then (1 : ℂ) else Complex.I) *
            Complex.exp (-(Complex.I * ↑γ * ↑(satCount tri rhs z))) =
        ∑ z : Qubits n, Complex.exp (Complex.I * ↑γ * (↑(satCount tri rhs y) - ↑(satCount tri rhs z))) *
          ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
            (if x q = z q then (1 : ℂ) else Complex.I)) := by
      intro y; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.prod_mul_distrib, mul_sub, Complex.exp_sub, div_eq_mul_inv, ← Complex.exp_neg]
      ring
    calc ((2 : ℂ) ^ n)⁻¹ * (∑ y : Qubits n, (∏ q : Fin n, if x q = y q then (1 : ℂ) else -Complex.I) *
            Complex.exp (Complex.I * ↑γ * ↑(satCount tri rhs y))) *
          ((∑ z : Qubits n, (∏ q : Fin n, if x q = z q then (1 : ℂ) else Complex.I) *
            Complex.exp (-(Complex.I * ↑γ * ↑(satCount tri rhs z)))) * ((2 : ℂ) ^ n)⁻¹)
        = (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) *
            ((∑ y : Qubits n, (∏ q : Fin n, if x q = y q then (1 : ℂ) else -Complex.I) *
              Complex.exp (Complex.I * ↑γ * ↑(satCount tri rhs y))) *
            (∑ z : Qubits n, (∏ q : Fin n, if x q = z q then (1 : ℂ) else Complex.I) *
              Complex.exp (-(Complex.I * ↑γ * ↑(satCount tri rhs z))))) := by ring
      _ = (((2 : ℝ) ^ (2 * n) : ℝ) : ℂ)⁻¹ *
            ∑ y : Qubits n, ∑ z : Qubits n,
              Complex.exp (Complex.I * ↑γ * (↑(satCount tri rhs y) - ↑(satCount tri rhs z))) *
                ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
                  (if x q = z q then (1 : ℂ) else Complex.I)) := by
          rw [← h2n, Finset.sum_mul]; congr 1; exact Finset.sum_congr rfl fun y _ => this y
  rw [← Finset.sum_mul] at *
  rw [hmul]
  have hre : (((((2 : ℝ) ^ (2 * n) : ℝ) : ℂ)⁻¹) *
        ∑ y : Qubits n, ∑ z : Qubits n,
          Complex.exp (Complex.I * ↑γ * (↑(satCount tri rhs y) - ↑(satCount tri rhs z))) *
            ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
              (if x q = z q then (1 : ℂ) else Complex.I))).re =
      ((2 : ℝ) ^ (2 * n))⁻¹ *
        (∑ y : Qubits n, ∑ z : Qubits n,
          Complex.exp (Complex.I * ↑γ * (↑(satCount tri rhs y) - ↑(satCount tri rhs z))) *
            ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
              (if x q = z q then (1 : ℂ) else Complex.I))).re := by
    rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]
  exact hre

private lemma sum_x_spin3_prod {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (y z : Qubits n) :
    ∑ x : Qubits n, ((spin x a * spin x b * spin x c : ℝ) : ℂ) *
        ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
          (if x q = z q then (1 : ℂ) else Complex.I)) =
      if z = flip3 a b c y then
        (2 : ℂ) ^ n * (-Complex.I * ((spin y a * spin y b * spin y c : ℝ) : ℂ))
      else 0 := by
  let w (q : Fin n) (bx : Bool) : ℂ :=
    if q = a ∨ q = b ∨ q = c then (if bx then (-1 : ℂ) else 1) else 1
  have hw_prod : ∀ x : Qubits n,
      ∏ q : Fin n, w q (x q) = ((spin x a * spin x b * spin x c : ℝ) : ℂ) := by
    intro x
    have ha : a ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have hb : b ∈ (Finset.univ.erase a : Finset (Fin n)) := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
    have hc : c ∈ ((Finset.univ.erase a).erase b : Finset (Fin n)) :=
      Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_univ _⟩⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun q => w q (x q)) ha]
    rw [← Finset.mul_prod_erase (Finset.univ.erase a) (fun q => w q (x q)) hb]
    rw [← Finset.mul_prod_erase ((Finset.univ.erase a).erase b) (fun q => w q (x q)) hc]
    have hrest : ∏ q ∈ ((Finset.univ.erase a).erase b).erase c, w q (x q) = 1 := by
      refine Finset.prod_eq_one fun q hq => ?_
      simp only [Finset.mem_erase, ne_eq] at hq
      have hqc : q ≠ c := hq.1
      have hqb : q ≠ b := hq.2.1
      have hqa : q ≠ a := hq.2.2.1
      simp [w, hqa, hqb, hqc]
    rw [hrest, mul_one]
    simp only [w, spin, true_or, or_true, ↓reduceIte]
    cases x a <;> cases x b <;> cases x c <;> simp <;> ring
  have hsum_prod : (∑ x : Qubits n, ((spin x a * spin x b * spin x c : ℝ) : ℂ) *
        ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
          (if x q = z q then (1 : ℂ) else Complex.I))) =
      ∏ q : Fin n, ∑ bx : Bool, w q bx *
        ((if bx = y q then (1 : ℂ) else -Complex.I) * (if bx = z q then (1 : ℂ) else Complex.I)) := by
    calc ∑ x : Qubits n, ((spin x a * spin x b * spin x c : ℝ) : ℂ) *
          ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
            (if x q = z q then (1 : ℂ) else Complex.I))
        = ∑ x : Qubits n, ∏ q : Fin n, (w q (x q) *
            ((if x q = y q then (1 : ℂ) else -Complex.I) *
              (if x q = z q then (1 : ℂ) else Complex.I))) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← hw_prod x, ← Finset.prod_mul_distrib]
      _ = ∏ q : Fin n, ∑ bx : Bool, w q bx *
            ((if bx = y q then (1 : ℂ) else -Complex.I) *
              (if bx = z q then (1 : ℂ) else Complex.I)) := by
          exact (Fintype.prod_sum (fun q bx => w q bx *
            ((if bx = y q then (1 : ℂ) else -Complex.I) *
              (if bx = z q then (1 : ℂ) else Complex.I)))).symm
  rw [hsum_prod]
  have hterm : ∀ q : Fin n, (∑ bx : Bool, w q bx *
        ((if bx = y q then (1 : ℂ) else -Complex.I) *
          (if bx = z q then (1 : ℂ) else Complex.I))) =
      if z q = flip3 a b c y q then
        2 * (if q = a ∨ q = b ∨ q = c then Complex.I * (spin y q : ℂ) else 1)
      else 0 := by
    intro q
    rw [Fintype.sum_bool]
    unfold flip3 w spin
    by_cases hq : q = a ∨ q = b ∨ q = c
    · simp only [hq, ↓reduceIte]
      cases hy : y q <;> cases hz : z q <;> simp <;> ring
    · simp only [hq, ↓reduceIte]
      cases hy : y q <;> cases hz : z q <;> simp <;> ring
  simp_rw [hterm]
  by_cases hzf : z = flip3 a b c y
  · subst hzf
    simp only [↓reduceIte]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    have ha : a ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have hb : b ∈ (Finset.univ.erase a : Finset (Fin n)) := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
    have hc : c ∈ ((Finset.univ.erase a).erase b : Finset (Fin n)) :=
      Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_univ _⟩⟩
    rw [← Finset.mul_prod_erase Finset.univ _ ha]
    rw [← Finset.mul_prod_erase (Finset.univ.erase a) _ hb]
    rw [← Finset.mul_prod_erase ((Finset.univ.erase a).erase b) _ hc]
    have hrest : ∏ q ∈ ((Finset.univ.erase a).erase b).erase c,
        (if q = a ∨ q = b ∨ q = c then Complex.I * (spin y q : ℂ) else 1) = 1 := by
      refine Finset.prod_eq_one fun q hq => ?_
      simp only [Finset.mem_erase, ne_eq] at hq
      simp [hq.1, hq.2.1, hq.2.2.1]
    rw [hrest, mul_one]
    simp only [true_or, or_true, ↓reduceIte]
    have hI3 : Complex.I * (spin y a : ℂ) * (Complex.I * (spin y b : ℂ) * (Complex.I * (spin y c : ℂ))) =
        -Complex.I * ((spin y a * spin y b * spin y c : ℝ) : ℂ) := by
      push_cast
      calc Complex.I * (spin y a : ℂ) * (Complex.I * (spin y b : ℂ) * (Complex.I * (spin y c : ℂ)))
          = (Complex.I * Complex.I) * Complex.I * ((spin y a : ℂ) * (spin y b : ℂ) * (spin y c : ℂ)) := by ring
        _ = (-1) * Complex.I * ((spin y a : ℂ) * (spin y b : ℂ) * (spin y c : ℂ)) := by rw [Complex.I_mul_I]
        _ = -Complex.I * ((spin y a : ℂ) * (spin y b : ℂ) * (spin y c : ℂ)) := by ring
    exact hI3
  · simp only [hzf, ↓reduceIte]
    have hex : ∃ q : Fin n, z q ≠ flip3 a b c y q := by
      by_contra h; push_neg at h; exact hzf (funext h)
    rcases hex with ⟨q, hq⟩
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])

private lemma spin_sq {n : ℕ} (x : Qubits n) (v : Fin n) : spin x v * spin x v = 1 := by
  unfold spin; cases x v <;> norm_num

private lemma sgn_sq {m : ℕ} (rhs : Fin m → Bool) (i : Fin m) : sgn rhs i * sgn rhs i = 1 := by
  unfold sgn; cases rhs i <;> norm_num

private lemma spin_flip3 {n : ℕ} (a b c : Fin n) (y : Qubits n) (v : Fin n) :
    spin (flip3 a b c y) v = (if v = a ∨ v = b ∨ v = c then (-1 : ℝ) else 1) * spin y v := by
  unfold spin flip3
  by_cases hv : v = a ∨ v = b ∨ v = c
  · simp only [hv, ↓reduceIte]; cases y v <;> norm_num
  · simp only [hv, ↓reduceIte, one_mul]

private lemma satCount_eq_sum_spin {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (x : Qubits n) :
    satCount tri rhs x =
      ∑ j : Fin m, (1 + sgn rhs j * (spin x (tri j).1 * spin x (tri j).2.1 * spin x (tri j).2.2)) / 2 := by
  unfold satCount
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases h1 : x (tri j).1 <;> cases h2 : x (tri j).2.1 <;> cases h3 : x (tri j).2.2 <;>
    cases hr : rhs j <;> simp [spin, sgn, h1, h2, h3, hr] <;> norm_num

private lemma satCount_sub_flip3 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : IsTripleFamily tri) (i : Fin m) (y : Qubits n) :
    satCount tri rhs y - satCount tri rhs (flip3 (tri i).1 (tri i).2.1 (tri i).2.2 y) =
      sgn rhs i * (spin y (tri i).1 * spin y (tri i).2.1 * spin y (tri i).2.2) +
        spin y (tri i).1 * cPoly tri rhs i 0 y +
        spin y (tri i).2.1 * cPoly tri rhs i 1 y +
        spin y (tri i).2.2 * cPoly tri rhs i 2 y := by
  set a := (tri i).1
  set b := (tri i).2.1
  set c := (tri i).2.2
  have hab : a < b := (htri.1 i).1
  have hbc : b < c := (htri.1 i).2
  have hac : a < c := lt_trans hab hbc
  rw [satCount_eq_sum_spin, satCount_eq_sum_spin, ← Finset.sum_sub_distrib]
  have hterm : ∀ j : Fin m,
      (1 + sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2)) / 2 -
        (1 + sgn rhs j * (spin (flip3 a b c y) (tri j).1 * spin (flip3 a b c y) (tri j).2.1 *
          spin (flip3 a b c y) (tri j).2.2)) / 2 =
      (if j = i then sgn rhs i * (spin y a * spin y b * spin y c) else 0) +
        (if sharesOnly tri i j 0 then
          spin y a * (sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y a))
        else 0) +
        (if sharesOnly tri i j 1 then
          spin y b * (sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y b))
        else 0) +
        (if sharesOnly tri i j 2 then
          spin y c * (sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y c))
        else 0) := by
    intro j
    rw [spin_flip3, spin_flip3, spin_flip3]
    by_cases hji : j = i
    · subst hji
      have h0 : ¬ sharesOnly tri j j 0 := fun h => h.1 rfl
      have h1 : ¬ sharesOnly tri j j 1 := fun h => h.1 rfl
      have h2 : ¬ sharesOnly tri j j 2 := fun h => h.1 rfl
      simp only [h0, h1, h2, ↓reduceIte, add_zero]
      have ha1 : a = a ∨ a = b ∨ a = c := Or.inl rfl
      have hb1 : b = a ∨ b = b ∨ b = c := Or.inr (Or.inl rfl)
      have hc1 : c = a ∨ c = b ∨ c = c := Or.inr (Or.inr rfl)
      simp only [a, b, c] at ha1 hb1 hc1 ⊢
      simp only [ha1, hb1, hc1, ↓reduceIte]
      ring
    · have htri_ne : tri j ≠ tri i := fun h => hji (htri.2 h)
      have hja := (htri.1 j).1
      have hjb := (htri.1 j).2
      have hjc := lt_trans hja hjb
      have hnot3 : ¬ (((tri j).1 = a ∨ (tri j).1 = b ∨ (tri j).1 = c) ∧
          ((tri j).2.1 = a ∨ (tri j).2.1 = b ∨ (tri j).2.1 = c) ∧
          ((tri j).2.2 = a ∨ (tri j).2.2 = b ∨ (tri j).2.2 = c)) := by
        rintro ⟨h1, h2, h3⟩
        apply htri_ne
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
            rcases h3 with h3 | h3 | h3 <;> omega
        · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
            rcases h3 with h3 | h3 | h3 <;> omega
        · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
            rcases h3 with h3 | h3 | h3 <;> omega
      have hsh0 : sharesOnly tri i j 0 ↔
          (onTriple (tri j) a ∧ ¬ onTriple (tri j) b ∧ ¬ onTriple (tri j) c) := by
        simp only [sharesOnly, hji, ne_eq, not_false_eq_true, true_and, roleBit]
        constructor
        · intro ⟨ha, h⟩; exact ⟨ha, h 1 (by decide), h 2 (by decide)⟩
        · intro ⟨ha, hb, hc⟩; refine ⟨ha, fun r hr => ?_⟩
          fin_cases r <;> simp_all [a, b, c]
      have hsh1 : sharesOnly tri i j 1 ↔
          (¬ onTriple (tri j) a ∧ onTriple (tri j) b ∧ ¬ onTriple (tri j) c) := by
        simp only [sharesOnly, hji, ne_eq, not_false_eq_true, true_and, roleBit]
        constructor
        · intro ⟨hb, h⟩; exact ⟨h 0 (by decide), hb, h 2 (by decide)⟩
        · intro ⟨ha, hb, hc⟩; refine ⟨hb, fun r hr => ?_⟩
          fin_cases r <;> simp_all [a, b, c]
      have hsh2 : sharesOnly tri i j 2 ↔
          (¬ onTriple (tri j) a ∧ ¬ onTriple (tri j) b ∧ onTriple (tri j) c) := by
        simp only [sharesOnly, hji, ne_eq, not_false_eq_true, true_and, roleBit]
        constructor
        · intro ⟨hc, h⟩; exact ⟨h 0 (by decide), h 1 (by decide), hc⟩
        · intro ⟨ha, hb, hc⟩; refine ⟨hc, fun r hr => ?_⟩
          fin_cases r <;> simp_all [a, b, c]
      have ha_spin : spin y a * (sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y a)) =
          sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) := by
        calc spin y a * (sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y a))
            = sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) * (spin y a * spin y a) := by ring
          _ = sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) := by rw [spin_sq, mul_one]
      have hb_spin : spin y b * (sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y b)) =
          sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) := by
        calc spin y b * (sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y b))
            = sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) * (spin y b * spin y b) := by ring
          _ = sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) := by rw [spin_sq, mul_one]
      have hc_spin : spin y c * (sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y c)) =
          sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) := by
        calc spin y c * (sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y c))
            = sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) * (spin y c * spin y c) := by ring
          _ = sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) := by rw [spin_sq, mul_one]
      simp only [if_neg hji, zero_add, hsh0, hsh1, hsh2, ha_spin, hb_spin, hc_spin]
      -- Helper: if two of (tri j).1, (tri j).2.1, (tri j).2.2 are in {a, b, c}, no single roleBit is unique
      have huniq : ∀ x y : Fin n, x ≠ y →
          (x = a ∨ x = b ∨ x = c) → (y = a ∨ y = b ∨ y = c) →
          onTriple (tri j) x → onTriple (tri j) y →
          ¬ (onTriple (tri j) a ∧ ¬ onTriple (tri j) b ∧ ¬ onTriple (tri j) c) ∧
          ¬ (¬ onTriple (tri j) a ∧ onTriple (tri j) b ∧ ¬ onTriple (tri j) c) ∧
          ¬ (¬ onTriple (tri j) a ∧ ¬ onTriple (tri j) b ∧ onTriple (tri j) c) := by
        intro x y hxy hx hy htx hty
        refine ⟨fun ⟨_, hb, hc⟩ => ?_, fun ⟨ha, _, hc⟩ => ?_, fun ⟨ha, hb, _⟩ => ?_⟩
        · rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
            first | exact hxy rfl | exact hb htx | exact hb hty | exact hc htx | exact hc hty
        · rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
            first | exact hxy rfl | exact ha htx | exact ha hty | exact hc htx | exact hc hty
        · rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
            first | exact hxy rfl | exact ha htx | exact ha hty | exact hb htx | exact hb hty
      -- Helper: if only one of (tri j).1, (tri j).2.1, (tri j).2.2 is in {a, b, c}, it's unique!
      have hone : ∀ v : Fin n, onTriple (tri j) v →
          (∀ u : Fin n, onTriple (tri j) u → u ≠ v → u ≠ a ∧ u ≠ b ∧ u ≠ c) →
          (v = a ∨ v = b ∨ v = c) →
          ((if onTriple (tri j) a ∧ ¬ onTriple (tri j) b ∧ ¬ onTriple (tri j) c then
              sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) else 0) +
            (if ¬ onTriple (tri j) a ∧ onTriple (tri j) b ∧ ¬ onTriple (tri j) c then
              sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) else 0) +
            (if ¬ onTriple (tri j) a ∧ ¬ onTriple (tri j) b ∧ onTriple (tri j) c then
              sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) else 0)) =
          sgn rhs j * (spin y (tri j).1 * spin y (tri j).2.1 * spin y (tri j).2.2) := by
        intro v hv hrest hvc
        have hother_not : ∀ w : Fin n, w ≠ v → (w = a ∨ w = b ∨ w = c) → ¬ onTriple (tri j) w := by
          intro w hwv _ htw
          have := hrest w htw hwv
          rcases ‹w = a ∨ w = b ∨ w = c› with rfl | rfl | rfl <;> simp_all
        rcases hvc with rfl | rfl | rfl
        · have hb := hother_not b hab.ne.symm (Or.inr (Or.inl rfl))
          have hc := hother_not c hac.ne.symm (Or.inr (Or.inr rfl))
          rw [if_pos ⟨hv, hb, hc⟩, if_neg (fun h => hb h.2.1), if_neg (fun h => hc h.2.2)]; ring
        · have ha := hother_not a hab.ne (Or.inl rfl)
          have hc := hother_not c hbc.ne.symm (Or.inr (Or.inr rfl))
          rw [if_neg (fun h => ha h.1), if_pos ⟨ha, hv, hc⟩, if_neg (fun h => hc h.2.2)]; ring
        · have ha := hother_not a hac.ne (Or.inl rfl)
          have hb := hother_not b hbc.ne (Or.inr (Or.inl rfl))
          rw [if_neg (fun h => ha h.1), if_neg (fun h => hb h.2.1), if_pos ⟨ha, hb, hv⟩]; ring
      by_cases h1 : (tri j).1 = a ∨ (tri j).1 = b ∨ (tri j).1 = c <;>
      by_cases h2 : (tri j).2.1 = a ∨ (tri j).2.1 = b ∨ (tri j).2.1 = c <;>
      by_cases h3 : (tri j).2.2 = a ∨ (tri j).2.2 = b ∨ (tri j).2.2 = c
      · exact absurd ⟨h1, h2, h3⟩ hnot3
      · have hu := huniq _ _ hja.ne h1 h2 (Or.inl rfl) (Or.inr (Or.inl rfl))
        rw [if_pos h1, if_pos h2, if_neg h3, if_neg hu.1, if_neg hu.2.1, if_neg hu.2.2]; ring
      · have hu := huniq _ _ hjc.ne h1 h3 (Or.inl rfl) (Or.inr (Or.inr rfl))
        rw [if_pos h1, if_neg h2, if_pos h3, if_neg hu.1, if_neg hu.2.1, if_neg hu.2.2]; ring
      · rw [if_pos h1, if_neg h2, if_neg h3]
        have hrest : ∀ u : Fin n, onTriple (tri j) u → u ≠ (tri j).1 → u ≠ a ∧ u ≠ b ∧ u ≠ c := by
          intro u hu hun
          rcases hu with rfl | rfl | rfl
          · exact absurd rfl hun
          · exact ⟨fun h => h2 (Or.inl h), fun h => h2 (Or.inr (Or.inl h)), fun h => h2 (Or.inr (Or.inr h))⟩
          · exact ⟨fun h => h3 (Or.inl h), fun h => h3 (Or.inr (Or.inl h)), fun h => h3 (Or.inr (Or.inr h))⟩
        rw [hone (tri j).1 (Or.inl rfl) hrest h1]; ring
      · have hu := huniq _ _ hjb.ne h2 h3 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
        rw [if_neg h1, if_pos h2, if_pos h3, if_neg hu.1, if_neg hu.2.1, if_neg hu.2.2]; ring
      · rw [if_neg h1, if_pos h2, if_neg h3]
        have hrest : ∀ u : Fin n, onTriple (tri j) u → u ≠ (tri j).2.1 → u ≠ a ∧ u ≠ b ∧ u ≠ c := by
          intro u hu hun
          rcases hu with rfl | rfl | rfl
          · exact ⟨fun h => h1 (Or.inl h), fun h => h1 (Or.inr (Or.inl h)), fun h => h1 (Or.inr (Or.inr h))⟩
          · exact absurd rfl hun
          · exact ⟨fun h => h3 (Or.inl h), fun h => h3 (Or.inr (Or.inl h)), fun h => h3 (Or.inr (Or.inr h))⟩
        rw [hone (tri j).2.1 (Or.inr (Or.inl rfl)) hrest h2]; ring
      · rw [if_neg h1, if_neg h2, if_pos h3]
        have hrest : ∀ u : Fin n, onTriple (tri j) u → u ≠ (tri j).2.2 → u ≠ a ∧ u ≠ b ∧ u ≠ c := by
          intro u hu hun
          rcases hu with rfl | rfl | rfl
          · exact ⟨fun h => h1 (Or.inl h), fun h => h1 (Or.inr (Or.inl h)), fun h => h1 (Or.inr (Or.inr h))⟩
          · exact ⟨fun h => h2 (Or.inl h), fun h => h2 (Or.inr (Or.inl h)), fun h => h2 (Or.inr (Or.inr h))⟩
          · exact absurd rfl hun
        rw [hone (tri j).2.2 (Or.inr (Or.inr rfl)) hrest h3]; ring
      · rw [if_neg h1, if_neg h2, if_neg h3]
        have ha : ¬ onTriple (tri j) a := fun h => by
          rcases h with h | h | h
          · exact h1 (Or.inl h.symm)
          · exact h2 (Or.inl h.symm)
          · exact h3 (Or.inl h.symm)
        have hb : ¬ onTriple (tri j) b := fun h => by
          rcases h with h | h | h
          · exact h1 (Or.inr (Or.inl h.symm))
          · exact h2 (Or.inr (Or.inl h.symm))
          · exact h3 (Or.inr (Or.inl h.symm))
        have hc : ¬ onTriple (tri j) c := fun h => by
          rcases h with h | h | h
          · exact h1 (Or.inr (Or.inr h.symm))
          · exact h2 (Or.inr (Or.inr h.symm))
          · exact h3 (Or.inr (Or.inr h.symm))
        rw [if_neg (fun h => ha h.1), if_neg (fun h => hb h.2.1), if_neg (fun h => hc h.2.2)]; ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold cPoly
  simp only [roleBit, Finset.mul_sum, mul_ite, mul_zero]
  rfl

private lemma corr_pi_div_4 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : IsTripleFamily tri) (i : Fin m) (γ : ℝ) :
    corr tri rhs i (-γ) (Real.pi / 4) =
      (2 ^ n : ℝ)⁻¹ * ∑ y : Qubits n,
        (spin y (tri i).1 * spin y (tri i).2.1 * spin y (tri i).2.2) *
          Real.sin (γ * (satCount tri rhs y -
            satCount tri rhs (flip3 (tri i).1 (tri i).2.1 (tri i).2.2 y))) := by
  set a := (tri i).1
  set b := (tri i).2.1
  set c := (tri i).2.2
  have hab : a ≠ b := ne_of_lt (htri.1 i).1
  have hbc : b ≠ c := ne_of_lt (htri.1 i).2
  have hac : a ≠ c := ne_of_lt (lt_trans (htri.1 i).1 (htri.1 i).2)
  unfold corr
  simp_rw [prob_qaoaState1_pi_div_4]
  have h1 : (∑ x : Qubits n,
        ((2 : ℝ) ^ (2 * n))⁻¹ *
          (∑ y : Qubits n, ∑ z : Qubits n,
            Complex.exp (Complex.I * (γ : ℂ) * ((satCount tri rhs y : ℂ) - (satCount tri rhs z : ℂ))) *
              ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
                (if x q = z q then (1 : ℂ) else Complex.I))).re *
          (spin x a * spin x b * spin x c)) =
      ((2 : ℝ) ^ (2 * n))⁻¹ *
        (∑ x : Qubits n,
          ∑ y : Qubits n, ∑ z : Qubits n,
            Complex.exp (Complex.I * (γ : ℂ) * ((satCount tri rhs y : ℂ) - (satCount tri rhs z : ℂ))) *
              (((spin x a * spin x b * spin x c : ℝ) : ℂ) *
                ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
                  (if x q = z q then (1 : ℂ) else Complex.I)))).re := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Complex.re_mul_ofReal, Finset.sum_mul]
    congr 1; refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun z _ => ?_; ring
  rw [h1]
  have hswap : (∑ x : Qubits n, ∑ y : Qubits n, ∑ z : Qubits n,
        Complex.exp (Complex.I * (γ : ℂ) * ((satCount tri rhs y : ℂ) - (satCount tri rhs z : ℂ))) *
          (((spin x a * spin x b * spin x c : ℝ) : ℂ) *
            ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
              (if x q = z q then (1 : ℂ) else Complex.I)))) =
      ∑ y : Qubits n, ∑ z : Qubits n,
        Complex.exp (Complex.I * (γ : ℂ) * ((satCount tri rhs y : ℂ) - (satCount tri rhs z : ℂ))) *
          ∑ x : Qubits n, (((spin x a * spin x b * spin x c : ℝ) : ℂ) *
            ∏ q : Fin n, ((if x q = y q then (1 : ℂ) else -Complex.I) *
              (if x q = z q then (1 : ℂ) else Complex.I))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  simp_rw [sum_x_spin3_prod a b c hab hac hbc]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Complex.re_sum]
  have hterm : ∀ y : Qubits n,
      (Complex.exp (Complex.I * (γ : ℂ) * ((satCount tri rhs y : ℂ) - (satCount tri rhs (flip3 a b c y) : ℂ))) *
        ((2 : ℂ) ^ n * (-Complex.I * ((spin y a * spin y b * spin y c : ℝ) : ℂ)))).re =
      (2 : ℝ) ^ n * ((spin y a * spin y b * spin y c) *
        Real.sin (γ * (satCount tri rhs y - satCount tri rhs (flip3 a b c y)))) := by
    intro y
    let θ : ℝ := γ * (satCount tri rhs y - satCount tri rhs (flip3 a b c y))
    have hθ : Complex.I * (γ : ℂ) * ((satCount tri rhs y : ℂ) - (satCount tri rhs (flip3 a b c y) : ℂ)) =
        (θ : ℂ) * Complex.I := by
      dsimp [θ]; push_cast; ring
    rw [hθ, Complex.exp_mul_I]
    have hprod : ((Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) *
        ((2 : ℂ) ^ n * (-Complex.I * ((spin y a * spin y b * spin y c : ℝ) : ℂ)))) =
        (((2 : ℝ) ^ n * (spin y a * spin y b * spin y c) * Real.sin θ : ℝ) : ℂ) -
        (((2 : ℝ) ^ n * (spin y a * spin y b * spin y c) * Real.cos θ : ℝ) : ℂ) * Complex.I := by
      have hcos : Complex.cos (θ : ℂ) = (Real.cos θ : ℂ) := (Complex.ofReal_cos θ).symm
      have hsin : Complex.sin (θ : ℂ) = (Real.sin θ : ℂ) := (Complex.ofReal_sin θ).symm
      rw [hcos, hsin]
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
      calc (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I) *
            ((2 : ℂ) ^ n * (-Complex.I * (↑(spin y a) * ↑(spin y b) * ↑(spin y c))))
          = (2 : ℂ) ^ n * (↑(spin y a) * ↑(spin y b) * ↑(spin y c)) * ↑(Real.sin θ) * (-(Complex.I * Complex.I)) -
            (2 : ℂ) ^ n * (↑(spin y a) * ↑(spin y b) * ↑(spin y c)) * ↑(Real.cos θ) * Complex.I := by ring
        _ = (2 : ℂ) ^ n * (↑(spin y a) * ↑(spin y b) * ↑(spin y c)) * ↑(Real.sin θ) -
            (2 : ℂ) ^ n * (↑(spin y a) * ↑(spin y b) * ↑(spin y c)) * ↑(Real.cos θ) * Complex.I := by
            rw [Complex.I_mul_I]; ring
    rw [hprod]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, Complex.ofReal_im, mul_one, sub_zero]
    simp [θ, mul_assoc]
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← mul_assoc]
  congr 1
  rw [two_mul, pow_add]
  field_simp

private lemma cPoly_flipMask {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : IsTripleFamily tri) (i : Fin m) (r : Fin 3)
    (p q s : Bool) (y : Qubits n) :
    cPoly tri rhs i r (flipMask (tri i).1 (tri i).2.1 (tri i).2.2 p q s y) = cPoly tri rhs i r y := by
  unfold cPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · congr 1
    set a := (tri i).1
    set b := (tri i).2.1
    set c := (tri i).2.2
    have hneq : ∀ v : Fin n, onTriple (tri j) v → v ≠ roleBit (tri i) r →
        v ≠ a ∧ v ≠ b ∧ v ≠ c := by
      intro v hv hvr
      refine ⟨?_, ?_, ?_⟩
      · intro h; subst h; exact hvr (by
          by_cases hr : r = 0
          · subst hr; rfl
          · exact absurd hv (hj.2.2 0 (Ne.symm hr)))
      · intro h; subst h; exact hvr (by
          by_cases hr : r = 1
          · subst hr; rfl
          · exact absurd hv (hj.2.2 1 (Ne.symm hr)))
      · intro h; subst h; exact hvr (by
          by_cases hr : r = 2
          · subst hr; rfl
          · exact absurd hv (hj.2.2 2 (Ne.symm hr)))
    have hspin_eq : ∀ v : Fin n, v ≠ a → v ≠ b → v ≠ c →
        spin (flipMask a b c p q s y) v = spin y v := by
      intro v h1 h2 h3; simp [spin, flipMask, h1, h2, h3]
    have hprod_eq : ∀ v : Fin n, onTriple (tri j) v →
        (if v = roleBit (tri i) r then 1 else spin (flipMask a b c p q s y) v) =
        (if v = roleBit (tri i) r then 1 else spin y v) := by
      intro v hv; split_ifs with hvr
      · rfl
      · have := hneq v hv hvr; exact hspin_eq v this.1 this.2.1 this.2.2
    have h1 := hprod_eq (tri j).1 (Or.inl rfl)
    have h2 := hprod_eq (tri j).2.1 (Or.inr (Or.inl rfl))
    have h3 := hprod_eq (tri j).2.2 (Or.inr (Or.inr rfl))
    have hj_dis : (tri j).1 ≠ (tri j).2.1 ∧ (tri j).1 ≠ (tri j).2.2 ∧ (tri j).2.1 ≠ (tri j).2.2 :=
      ⟨ne_of_lt (htri.1 j).1, ne_of_lt (lt_trans (htri.1 j).1 (htri.1 j).2), ne_of_lt (htri.1 j).2⟩
    have hon := hj.2.1
    simp only [onTriple] at hon
    rcases hon with h | h | h
    · have h12 : (tri j).2.1 ≠ roleBit (tri i) r := h ▸ hj_dis.1.symm
      have h13 : (tri j).2.2 ≠ roleBit (tri i) r := h ▸ hj_dis.2.1.symm
      simp only [if_neg h12] at h2; simp only [if_neg h13] at h3
      rw [← h]
      calc spin (flipMask a b c p q s y) (roleBit (tri i) r) *
            spin (flipMask a b c p q s y) (tri j).2.1 *
            spin (flipMask a b c p q s y) (tri j).2.2 *
            spin (flipMask a b c p q s y) (roleBit (tri i) r)
          = (spin (flipMask a b c p q s y) (roleBit (tri i) r) *
              spin (flipMask a b c p q s y) (roleBit (tri i) r)) *
              (spin (flipMask a b c p q s y) (tri j).2.1 * spin (flipMask a b c p q s y) (tri j).2.2) := by ring
        _ = 1 * (spin y (tri j).2.1 * spin y (tri j).2.2) := by rw [spin_sq, h2, h3]
        _ = spin y (roleBit (tri i) r) * spin y (tri j).2.1 * spin y (tri j).2.2 * spin y (roleBit (tri i) r) := by
            calc 1 * (spin y (tri j).2.1 * spin y (tri j).2.2)
                = (spin y (roleBit (tri i) r) * spin y (roleBit (tri i) r)) *
                    (spin y (tri j).2.1 * spin y (tri j).2.2) := by rw [spin_sq]
              _ = _ := by ring
    · have h12 : (tri j).1 ≠ roleBit (tri i) r := h ▸ hj_dis.1
      have h23 : (tri j).2.2 ≠ roleBit (tri i) r := h ▸ hj_dis.2.2.symm
      simp only [if_neg h12] at h1; simp only [if_neg h23] at h3
      rw [← h]
      calc spin (flipMask a b c p q s y) (tri j).1 *
            spin (flipMask a b c p q s y) (roleBit (tri i) r) *
            spin (flipMask a b c p q s y) (tri j).2.2 *
            spin (flipMask a b c p q s y) (roleBit (tri i) r)
          = (spin (flipMask a b c p q s y) (roleBit (tri i) r) *
              spin (flipMask a b c p q s y) (roleBit (tri i) r)) *
              (spin (flipMask a b c p q s y) (tri j).1 * spin (flipMask a b c p q s y) (tri j).2.2) := by ring
        _ = 1 * (spin y (tri j).1 * spin y (tri j).2.2) := by rw [spin_sq, h1, h3]
        _ = spin y (tri j).1 * spin y (roleBit (tri i) r) * spin y (tri j).2.2 * spin y (roleBit (tri i) r) := by
            calc 1 * (spin y (tri j).1 * spin y (tri j).2.2)
                = (spin y (roleBit (tri i) r) * spin y (roleBit (tri i) r)) *
                    (spin y (tri j).1 * spin y (tri j).2.2) := by rw [spin_sq]
              _ = _ := by ring
    · have h13 : (tri j).1 ≠ roleBit (tri i) r := h ▸ hj_dis.2.1
      have h23 : (tri j).2.1 ≠ roleBit (tri i) r := h ▸ hj_dis.2.2
      simp only [if_neg h13] at h1; simp only [if_neg h23] at h2
      rw [← h]
      calc spin (flipMask a b c p q s y) (tri j).1 *
            spin (flipMask a b c p q s y) (tri j).2.1 *
            spin (flipMask a b c p q s y) (roleBit (tri i) r) *
            spin (flipMask a b c p q s y) (roleBit (tri i) r)
          = (spin (flipMask a b c p q s y) (roleBit (tri i) r) *
              spin (flipMask a b c p q s y) (roleBit (tri i) r)) *
              (spin (flipMask a b c p q s y) (tri j).1 * spin (flipMask a b c p q s y) (tri j).2.1) := by ring
        _ = 1 * (spin y (tri j).1 * spin y (tri j).2.1) := by rw [spin_sq, h1, h2]
        _ = spin y (tri j).1 * spin y (tri j).2.1 * spin y (roleBit (tri i) r) * spin y (roleBit (tri i) r) := by
            calc 1 * (spin y (tri j).1 * spin y (tri j).2.1)
                = (spin y (roleBit (tri i) r) * spin y (roleBit (tri i) r)) *
                    (spin y (tri j).1 * spin y (tri j).2.1) := by rw [spin_sq]
              _ = _ := by ring
  · rfl

private lemma half_sgn_corr_eq_clauseSin {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : IsTripleFamily tri) (i : Fin m) (γ : ℝ) :
    (1 / 2 : ℝ) * sgn rhs i * corr tri rhs i (-γ) (Real.pi / 4) = clauseSin tri rhs i γ := by
  set a := (tri i).1
  set b := (tri i).2.1
  set c := (tri i).2.2
  have hab : a ≠ b := ne_of_lt (htri.1 i).1
  have hbc : b ≠ c := ne_of_lt (htri.1 i).2
  have hac : a ≠ c := ne_of_lt (lt_trans (htri.1 i).1 (htri.1 i).2)
  rw [corr_pi_div_4 tri rhs htri i γ]
  simp_rw [satCount_sub_flip3 tri rhs htri i]
  let f : Qubits n → ℝ := fun y =>
    (spin y a * spin y b * spin y c) *
      Real.sin (γ * (sgn rhs i * (spin y a * spin y b * spin y c) +
        spin y a * cPoly tri rhs i 0 y +
        spin y b * cPoly tri rhs i 1 y +
        spin y c * cPoly tri rhs i 2 y))
  have hf_eq : ∀ y : Qubits n,
      f y = Real.sin (γ * (sgn rhs i +
        (spin y b * spin y c) * cPoly tri rhs i 0 y +
        (spin y a * spin y c) * cPoly tri rhs i 1 y +
        (spin y a * spin y b) * cPoly tri rhs i 2 y)) := by
    intro y
    dsimp [f]
    have hpm : spin y a * spin y b * spin y c = 1 ∨ spin y a * spin y b * spin y c = -1 := by
      unfold spin; cases y a <;> cases y b <;> cases y c <;> norm_num
    have harg : (spin y a * spin y b * spin y c) *
          (sgn rhs i +
            (spin y b * spin y c) * cPoly tri rhs i 0 y +
            (spin y a * spin y c) * cPoly tri rhs i 1 y +
            (spin y a * spin y b) * cPoly tri rhs i 2 y) =
        sgn rhs i * (spin y a * spin y b * spin y c) +
          spin y a * cPoly tri rhs i 0 y +
          spin y b * cPoly tri rhs i 1 y +
          spin y c * cPoly tri rhs i 2 y := by
      have ha2 := spin_sq y a
      have hb2 := spin_sq y b
      have hc2 := spin_sq y c
      calc (spin y a * spin y b * spin y c) *
            (sgn rhs i + (spin y b * spin y c) * cPoly tri rhs i 0 y +
              (spin y a * spin y c) * cPoly tri rhs i 1 y +
              (spin y a * spin y b) * cPoly tri rhs i 2 y)
          = sgn rhs i * (spin y a * spin y b * spin y c) +
              spin y a * (spin y b * spin y b) * (spin y c * spin y c) * cPoly tri rhs i 0 y +
              spin y b * (spin y a * spin y a) * (spin y c * spin y c) * cPoly tri rhs i 1 y +
              spin y c * (spin y a * spin y a) * (spin y b * spin y b) * cPoly tri rhs i 2 y := by ring
        _ = _ := by rw [ha2, hb2, hc2]; ring
    rw [← harg]
    rcases hpm with h | h
    · rw [h, one_mul, one_mul]
    · rw [h, neg_one_mul, neg_one_mul, mul_neg, Real.sin_neg, neg_neg]
  have havg : (∑ y : Qubits n, f y) =
      (1 / 8 : ℝ) * ∑ y : Qubits n, ∑ p : Bool, ∑ q : Bool, ∑ s : Bool,
        f (flipMask a b c p q s y) := by
    have hbij : ∀ p q s : Bool, ∑ y : Qubits n, f (flipMask a b c p q s y) = ∑ y : Qubits n, f y := by
      intro p q s
      exact (flipMask_involutive a b c hab hac hbc p q s).bijective.sum_comp f
    have h8 : ∑ p : Bool, ∑ q : Bool, ∑ s : Bool, ∑ y : Qubits n, f (flipMask a b c p q s y) =
        8 * ∑ y : Qubits n, f y := by
      simp only [hbij, Fintype.sum_bool]
      ring
    have hswap : (∑ p : Bool, ∑ q : Bool, ∑ s : Bool, ∑ y : Qubits n, f (flipMask a b c p q s y)) =
        ∑ y : Qubits n, ∑ p : Bool, ∑ q : Bool, ∑ s : Bool, f (flipMask a b c p q s y) := by
      simp only [Fintype.sum_bool]
      simp only [← Finset.sum_add_distrib]
    rw [← hswap, h8]
    ring
  have hinner : ∀ y : Qubits n,
      (∑ p : Bool, ∑ q : Bool, ∑ s : Bool, f (flipMask a b c p q s y)) =
        2 * (Real.sin (γ * (sgn rhs i + cPoly tri rhs i 0 y + cPoly tri rhs i 1 y + cPoly tri rhs i 2 y)) +
          Real.sin (γ * (sgn rhs i + cPoly tri rhs i 0 y - cPoly tri rhs i 1 y - cPoly tri rhs i 2 y)) +
          Real.sin (γ * (sgn rhs i - cPoly tri rhs i 0 y + cPoly tri rhs i 1 y - cPoly tri rhs i 2 y)) +
          Real.sin (γ * (sgn rhs i - cPoly tri rhs i 0 y - cPoly tri rhs i 1 y + cPoly tri rhs i 2 y))) := by
    intro y
    have hc0 : ∀ p q s, cPoly tri rhs i 0 (flipMask a b c p q s y) = cPoly tri rhs i 0 y :=
      fun p q s => cPoly_flipMask tri rhs htri i 0 p q s y
    have hc1 : ∀ p q s, cPoly tri rhs i 1 (flipMask a b c p q s y) = cPoly tri rhs i 1 y :=
      fun p q s => cPoly_flipMask tri rhs htri i 1 p q s y
    have hc2 : ∀ p q s, cPoly tri rhs i 2 (flipMask a b c p q s y) = cPoly tri rhs i 2 y :=
      fun p q s => cPoly_flipMask tri rhs htri i 2 p q s y
    simp_rw [hf_eq, hc0, hc1, hc2]
    simp only [Fintype.sum_bool, spin, flipMask, hab.symm, hac.symm, hbc.symm, ↓reduceIte]
    cases y a <;> cases y b <;> cases y c <;>
      simp only [Bool.true_xor, Bool.false_xor, ↓reduceIte] <;> norm_num <;> ring_nf
  change (1 / 2 : ℝ) * sgn rhs i * ((2 ^ n : ℝ)⁻¹ * ∑ y : Qubits n, f y) = clauseSin tri rhs i γ
  rw [havg]
  simp_rw [hinner]
  unfold clauseSin avgZ
  have hcard : (Fintype.card (Qubits n) : ℝ) = (2 : ℝ) ^ n := by
    simp [Qubits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hcard, ← Finset.mul_sum]
  ring

end CorrClauseSin


namespace AuxEq6

open QAlgorithms
open QAOAE3Lin2.General

private def flipBits {n : ℕ} (x : Qubits n) : Qubits n := fun v => !(x v)

private lemma flipBits_involutive {n : ℕ} : Function.Involutive (@flipBits n) := by
  intro x; ext v; simp [flipBits]

private lemma satCount_flipBits {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (x : Qubits n) :
    satCount tri rhs (flipBits x) = (m : ℝ) - satCount tri rhs x := by
  unfold satCount flipBits
  have hpart : (Finset.univ.filter fun i : Fin m =>
      (xor (xor (!(x (tri i).1)) (!(x (tri i).2.1))) (!(x (tri i).2.2))) = rhs i) =
      (Finset.univ.filter fun i : Fin m =>
      ¬ ((xor (xor (x (tri i).1) (x (tri i).2.1)) (x (tri i).2.2)) = rhs i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x (tri i).1 <;> cases x (tri i).2.1 <;> cases x (tri i).2.2 <;> cases rhs i <;> decide
  rw [hpart]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m)))
    (p := fun i => (xor (xor (x (tri i).1) (x (tri i).2.1)) (x (tri i).2.2)) = rhs i)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hcast : ((Finset.univ.filter fun i : Fin m =>
      (xor (xor (x (tri i).1) (x (tri i).2.1)) (x (tri i).2.2)) = rhs i).card : ℝ) +
      ((Finset.univ.filter fun i : Fin m =>
      ¬ ((xor (xor (x (tri i).1) (x (tri i).2.1)) (x (tri i).2.2)) = rhs i)).card : ℝ) =
      (m : ℝ) := by exact_mod_cast hsum
  linarith

private noncomputable def flipMat (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  fun x y => if x = flipBits y then 1 else 0

private lemma flipMat_sq (n : ℕ) : flipMat n * flipMat n = 1 := by
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [flipMat]
  rw [Finset.sum_eq_single (flipBits y)]
  · by_cases h : x = y
    · subst h; simp [flipBits_involutive x]
    · have hne : x ≠ flipBits (flipBits y) := by simpa [flipBits_involutive y] using h
      simp [h, hne]
  · intro z _ hz
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma flipMat_conj (n : ℕ) (A : Matrix (Qubits n) (Qubits n) ℂ) (x y : Qubits n) :
    (flipMat n * A * flipMat n) x y = A (flipBits x) (flipBits y) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rw [Finset.sum_eq_single (flipBits x)]
  · simp only [flipMat, flipBits_involutive x, ↓reduceIte, one_mul]
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (flipBits y)]
    · simp [flipMat, flipBits_involutive y]
    · intro z _ hz
      simp [flipMat, hz]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro z _ hz
    have hne : x ≠ flipBits z := fun h => hz (by rw [h, flipBits_involutive z])
    simp [flipMat, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma flipMat_pauliX (n : ℕ) (q : Fin n) (x y : Qubits n) :
    Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli q Stabilizer.Pauli.X)
      (flipBits x) (flipBits y) =
    Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli q Stabilizer.Pauli.X) x y := by
  dsimp only [Stabilizer.CliffordOp.mat]
  unfold embedOp
  simp only [Matrix.of_apply]
  split_ifs
  · simp only [Gate.ofMatrix1, Function.comp_apply, Stabilizer.wire1, Stabilizer.Pauli.mat, pauliX,
      flipBits, Matrix.submatrix_apply]
    cases x q <;> cases y q <;> simp
  · exfalso; simp_all [flipBits]
  · exfalso; simp_all [flipBits]
  · rfl

private lemma flipMat_mixer (n : ℕ) :
    flipMat n * qaoaMixer n * flipMat n = qaoaMixer n := by
  ext x y
  rw [flipMat_conj]
  simp only [qaoaMixer, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun q _ => flipMat_pauliX n q x y

private lemma flipMat_uniform (n : ℕ) :
    act (flipMat n) (uniformState (Qubits n)) = uniformState (Qubits n) := by
  ext x
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, uniformState]
  rw [Finset.sum_eq_single (flipBits x)]
  · simp [flipMat, flipBits_involutive x]
  · intro y _ hy
    have hne : x ≠ flipBits y := fun h => hy (by rw [h, flipBits_involutive y])
    simp [flipMat, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma matrix_exp_eq_linfty {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    NormedSpace.exp M =
      (letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
      NormedSpace.exp M) := by
  have ha :
      (letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
      HasSum (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) (NormedSpace.exp M)) := by
    letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
    have hpow_norm : ∀ k : ℕ, ‖M ^ (k + 1)‖ ≤ ‖M‖ ^ (k + 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, pow_succ]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
    have hs : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) := by
      rw [← summable_nat_add_iff 1]
      refine Summable.of_norm_bounded
        ((Real.summable_pow_div_factorial ‖M‖).comp_injective Nat.succ_injective) fun k => ?_
      simp only [Function.comp_apply, norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
      gcongr
      exact hpow_norm k
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
    exact hs.hasSum
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]

private lemma matrix_exp_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    HasSum (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) (NormedSpace.exp M) := by
  rw [matrix_exp_eq_linfty M]
  refine (Pi.hasSum (f := fun k (i j : ι) => ((Nat.factorial k : ℂ)⁻¹ • M ^ k) i j)).mpr fun i => ?_
  refine (Pi.hasSum (f := fun k (j : ι) => ((Nat.factorial k : ℂ)⁻¹ • M ^ k) i j)).mpr fun j => ?_
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  have hpow_norm : ∀ k : ℕ, ‖M ^ (k + 1)‖ ≤ ‖M‖ ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
  have hs : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial ‖M‖).comp_injective Nat.succ_injective) fun k => ?_
    simp only [Function.comp_apply, norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    gcongr
    exact hpow_norm k
  let evalIJ : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => X i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcont : Continuous evalIJ := LinearMap.continuous_of_finiteDimensional evalIJ
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  exact hs.hasSum.map evalIJ.toAddMonoidHom hcont

private lemma exp_conj_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U * U = 1) (A : Matrix ι ι ℂ) :
    U * NormedSpace.exp A * U = NormedSpace.exp (U * A * U) := by
  have hpow : ∀ k : ℕ, (U * A * U) ^ k = U * A ^ k * U := by
    intro k
    induction k with
    | zero => simp [hU]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      congr 1; congr 1
      rw [← Matrix.mul_assoc U U, hU, one_mul]
  let mulLR : Matrix ι ι ℂ →+ Matrix ι ι ℂ :=
    { toFun := fun X => U * X * U
      map_zero' := by simp
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hcont : Continuous mulLR :=
    (continuous_const.mul continuous_id).mul continuous_const
  have h1 := (matrix_exp_hasSum A).map mulLR hcont
  change HasSum (fun k => mulLR ((Nat.factorial k : ℂ)⁻¹ • A ^ k)) (mulLR (NormedSpace.exp A)) at h1
  have hterm : (fun k : ℕ => mulLR ((Nat.factorial k : ℂ)⁻¹ • A ^ k)) =
      (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • (U * A * U) ^ k) := by
    ext k
    simp only [mulLR, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hpow k, Matrix.smul_mul, Matrix.mul_smul]
  rw [hterm] at h1
  exact h1.unique (matrix_exp_hasSum (U * A * U))

private lemma matrix_exp_add_of_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : Commute A B) :
    NormedSpace.exp (A + B) = NormedSpace.exp A * NormedSpace.exp B := by
  rw [matrix_exp_eq_linfty (A + B), matrix_exp_eq_linfty A, matrix_exp_eq_linfty B]
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_add_of_commute h

private lemma exp_skew_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Matrix.conjTranspose A = -A) :
    NormedSpace.exp A ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hstar_exp : Matrix.conjTranspose (NormedSpace.exp A) = NormedSpace.exp (-A) := by
    have h1 := (matrix_exp_hasSum A).star
    have hterm : (fun k : ℕ => star ((Nat.factorial k : ℂ)⁻¹ • A ^ k)) =
        (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • (-A) ^ k) := by
      ext k
      rw [star_smul, star_pow, Matrix.star_eq_conjTranspose, hA, star_inv₀, star_natCast]
    rw [hterm] at h1
    rw [← Matrix.star_eq_conjTranspose]
    exact h1.unique (matrix_exp_hasSum (-A))
  rw [← Matrix.star_eq_conjTranspose] at hstar_exp
  have hexp := matrix_exp_add_of_commute (Commute.neg_left rfl : Commute (-A) A)
  rw [hstar_exp, ← hexp, neg_add_cancel, NormedSpace.exp_zero]

private lemma mixer_hermitian (n : ℕ) : Matrix.conjTranspose (qaoaMixer n) = qaoaMixer n := by
  ext x y
  dsimp only [qaoaMixer]
  simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, star_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  dsimp only [Stabilizer.CliffordOp.mat]
  unfold embedOp
  simp only [Matrix.of_apply]
  rw [apply_ite Star.star]
  simp only [star_zero]
  split_ifs
  · simp only [Gate.ofMatrix1, Function.comp_apply, Stabilizer.wire1, Stabilizer.Pauli.mat, pauliX,
      Matrix.submatrix_apply]
    cases x q <;> cases y q <;> simp
  · exfalso; simp_all [eq_comm]
  · exfalso; simp_all [eq_comm]
  · rfl

private lemma prob_sum_eq_one {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : ‖ψ‖ = 1) :
    ∑ x : Qubits n, prob ψ x = 1 := by
  have hp : ∀ x : Qubits n, prob ψ x = ‖ψ x‖ ^ 2 := by
    intro x
    simp [prob, ket, EuclideanSpace.inner_single_left]
  simp_rw [hp]
  rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]

private lemma exp_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ) :
    NormedSpace.exp (c • (1 : Matrix ι ι ℂ)) = Complex.exp c • (1 : Matrix ι ι ℂ) := by
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ) (𝔸 := Matrix ι ι ℂ), Complex.exp_eq_exp_ℂ,
      NormedSpace.exp_eq_tsum (𝕂 := ℂ) (𝔸 := ℂ)]
  have hterm : ∀ k : ℕ, (Nat.factorial k : ℂ)⁻¹ • (c • (1 : Matrix ι ι ℂ)) ^ k =
      ((Nat.factorial k : ℂ)⁻¹ • c ^ k) • (1 : Matrix ι ι ℂ) := by
    intro k
    rw [smul_pow, one_pow, smul_smul]
    rfl
  simp_rw [hterm]
  have hs : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • c ^ k) := by
    refine Summable.of_norm ?_
    simpa [smul_eq_mul, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_pow, div_eq_inv_mul]
      using Real.summable_pow_div_factorial ‖c‖
  exact (hs.hasSum.smul_const (1 : Matrix ι ι ℂ)).tsum_eq

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (γ β : ℝ) :
    expSat tri rhs γ β = (m : ℝ) / 2 + ∑ i, (1 / 2) * sgn rhs i * corr tri rhs i γ β := by
  have hunit : ‖qaoaState1 tri rhs γ β‖ = 1 := by
    unfold qaoaState1
    have hU_unit : qaoaUnitary (satCount tri rhs) 1 (fun _ => β) (fun _ => γ) ∈
        Matrix.unitaryGroup (Qubits n) ℂ := by
      simp only [qaoaUnitary, orderedProd, List.ofFn_succ, List.ofFn_zero,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
      refine Submonoid.mul_mem _ (exp_skew_unitary _ ?_) (exp_skew_unitary _ ?_)
      · rw [Matrix.conjTranspose_smul, mixer_hermitian n]
        simp [Complex.conj_I]
      · rw [Matrix.conjTranspose_smul]
        have hH : Matrix.conjTranspose (problemHamiltonian (satCount tri rhs)) =
            problemHamiltonian (satCount tri rhs) := by
          ext x y
          simp only [Matrix.conjTranspose_apply, problemHamiltonian, Matrix.diagonal_apply]
          by_cases h : x = y
          · subst h; simp
          · simp [h, Ne.symm h]
        rw [hH]
        simp [Complex.conj_I]
    rw [act_norm_of_mem_unitaryGroup hU_unit, ← Real.sqrt_sq (norm_nonneg _),
        EuclideanSpace.norm_sq_eq]
    simp [uniformState]
  have hprob1 : ∑ x : Qubits n, prob (qaoaState1 tri rhs γ β) x = 1 :=
    prob_sum_eq_one _ hunit
  have hsat : ∀ x : Qubits n, satCount tri rhs x =
      ∑ i : Fin m, ((1 / 2 : ℝ) + (1 / 2 : ℝ) * sgn rhs i *
        (spin x (tri i).1 * spin x (tri i).2.1 * spin x (tri i).2.2)) := by
    intro x
    unfold satCount
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [sgn, spin]
    cases x (tri i).1 <;> cases x (tri i).2.1 <;> cases x (tri i).2.2 <;> cases rhs i <;> norm_num
  simp_rw [expSat, hsat, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ i : Fin m,
      (∑ x : Qubits n, prob (qaoaState1 tri rhs γ β) x *
        ((1 / 2 : ℝ) + (1 / 2 : ℝ) * sgn rhs i *
          (spin x (tri i).1 * spin x (tri i).2.1 * spin x (tri i).2.2))) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * sgn rhs i * corr tri rhs i γ β := by
    intro i
    have hsplit : ∀ x : Qubits n,
        prob (qaoaState1 tri rhs γ β) x *
          ((1 / 2 : ℝ) + (1 / 2 : ℝ) * sgn rhs i *
            (spin x (tri i).1 * spin x (tri i).2.1 * spin x (tri i).2.2)) =
        (1 / 2 : ℝ) * prob (qaoaState1 tri rhs γ β) x +
          (1 / 2 : ℝ) * sgn rhs i * (prob (qaoaState1 tri rhs γ β) x *
            (spin x (tri i).1 * spin x (tri i).2.1 * spin x (tri i).2.2)) := by
      intro x; ring
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hprob1, corr]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
  ring
end AuxEq6

namespace AuxEq34

open QAOAE3Lin2.General



private lemma iteratedDeriv_sin_eq (m : ℕ) :
    iteratedDeriv m Real.sin = fun x =>
      if m % 4 = 0 then Real.sin x
      else if m % 4 = 1 then Real.cos x
      else if m % 4 = 2 then -Real.sin x
      else -Real.cos x := by
  induction m with
  | zero =>
    ext x
    simp [iteratedDeriv_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    ext x
    have h0 : deriv (fun y => Real.sin y) x = Real.cos x := by simp
    have h1 : deriv (fun y => Real.cos y) x = -Real.sin x := by simp
    have h2 : deriv (fun y => -Real.sin y) x = -Real.cos x := by simp
    have h3 : deriv (fun y => -Real.cos y) x = Real.sin x := by simp
    rcases Nat.mod_lt m (by norm_num : 0 < 4) with _
    have hm : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hm with h | h | h | h
    · have hm1 : (m + 1) % 4 = 1 := by omega
      simp [h, hm1, h0]
    · have hm1 : (m + 1) % 4 = 2 := by omega
      simp [h, hm1, h1]
    · have hm1 : (m + 1) % 4 = 3 := by omega
      simp [h, hm1, h2]
    · have hm1 : (m + 1) % 4 = 0 := by omega
      simp [h, hm1, h3]

private lemma norm_iteratedDeriv_sin_le (m : ℕ) (x : ℝ) :
    ‖iteratedDeriv m Real.sin x‖ ≤ 1 := by
  rw [iteratedDeriv_sin_eq m, Real.norm_eq_abs]
  split_ifs
  · exact Real.abs_sin_le_one x
  · exact Real.abs_cos_le_one x
  · rw [abs_neg]; exact Real.abs_sin_le_one x
  · rw [abs_neg]; exact Real.abs_cos_le_one x

private lemma iteratedDeriv_sin_zero (j : ℕ) :
    iteratedDeriv j Real.sin 0 = if Odd j then (-1 : ℝ) ^ ((j - 1) / 2) else 0 := by
  rw [iteratedDeriv_sin_eq j]
  have hj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases hj with h | h | h | h
  · have hne : ¬ Odd j := by rw [Nat.not_odd_iff_even]; exact Nat.even_iff.mpr (by omega)
    simp [h, hne]
  · have ho : Odd j := Nat.odd_iff.mpr (by omega)
    have hev : Even ((j - 1) / 2) := Nat.even_iff.mpr (by omega)
    simp [h, ho, hev.neg_one_pow]
  · have hne : ¬ Odd j := by rw [Nat.not_odd_iff_even]; exact Nat.even_iff.mpr (by omega)
    simp [h, hne]
  · have ho : Odd j := Nat.odd_iff.mpr (by omega)
    have hodd : Odd ((j - 1) / 2) := Nat.odd_iff.mpr (by omega)
    simp [h, ho, hodd.neg_one_pow]

private lemma sin_taylor_bound (k : ℕ) (hk : Odd k) (t : ℝ) :
    |Real.sin t - ∑ j ∈ (Finset.range (k + 1)).filter Odd,
      t ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)| ≤
      |t| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
  by_cases ht : t = 0
  · subst ht
    have hsum0 : (∑ j ∈ (Finset.range (k + 1)).filter Odd,
        (0 : ℝ) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_odd : Odd j := (Finset.mem_filter.mp hj).2
      have hj_pos : j ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hj_odd
      simp [zero_pow hj_pos]
    simp [hsum0]
  have hne : (0 : ℝ) ≠ t := Ne.symm ht
  have hcont : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) Real.sin (Set.uIcc 0 t) :=
    Real.contDiff_sin.contDiffOn
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin (k + 1) Real.sin (Set.uIcc 0 t))
      (Set.uIoo 0 t) := by
    have hud : UniqueDiffOn ℝ (Set.uIcc 0 t) :=
      uniqueDiffOn_Icc (by rcases lt_or_gt_of_ne ht with h | h <;> simp [h])
    have heq : Set.EqOn (iteratedDerivWithin (k + 1) Real.sin (Set.uIcc 0 t))
        (iteratedDeriv (k + 1) Real.sin) (Set.uIoo 0 t) := by
      intro y hy
      exact iteratedDerivWithin_eq_iteratedDeriv hud (Real.contDiff_sin.contDiffAt)
        (Set.Ioo_subset_Icc_self hy)
    exact (((Real.contDiff_sin (n := ⊤)).differentiable_iteratedDeriv (k + 1)
      (by simp)).differentiableOn).congr heq
  -- Wait: differentiable_iteratedDeriv needs ENat order, let's check!
  obtain ⟨x', hx', hrem⟩ := taylor_mean_remainder_lagrange hne hcont hdiff
  have hud : UniqueDiffOn ℝ (Set.uIcc 0 t) :=
    uniqueDiffOn_Icc (by rcases lt_or_gt_of_ne ht with h | h <;> simp [h])
  have hwithin : ∀ j : ℕ, iteratedDerivWithin j Real.sin (Set.uIcc 0 t) 0 =
      iteratedDeriv j Real.sin 0 := fun j =>
    iteratedDerivWithin_eq_iteratedDeriv hud Real.contDiff_sin.contDiffAt
      Set.left_mem_uIcc
  have hwithin_x' : iteratedDerivWithin (k + 2) Real.sin (Set.uIcc 0 t) x' =
      iteratedDeriv (k + 2) Real.sin x' :=
    iteratedDerivWithin_eq_iteratedDeriv hud Real.contDiff_sin.contDiffAt
      (Set.Ioo_subset_Icc_self hx')
  have htay : taylorWithinEval Real.sin (k + 1) (Set.uIcc 0 t) 0 t =
      ∑ j ∈ (Finset.range (k + 1)).filter Odd,
        t ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) := by
    simp [taylorWithinEval, taylorWithin, taylorCoeffWithin, hwithin, iteratedDeriv_sin_zero]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun j _ => by ring
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    have hk_even : ¬ Odd (k + 1) := by
      rw [← Nat.not_even_iff_odd]
      simpa [Nat.even_add_one] using hk
    constructor
    · rintro ⟨hj1, hj2⟩
      have hj_ne : j ≠ k + 1 := by rintro rfl; exact hk_even hj2
      exact ⟨by omega, hj2⟩
    · rintro ⟨hj1, hj2⟩
      exact ⟨by omega, hj2⟩
  rw [← htay, hrem, hwithin_x', abs_div, abs_mul, sub_zero, abs_pow, Nat.abs_cast]
  have hbound : |iteratedDeriv (k + 2) Real.sin x'| ≤ 1 := by
    simpa [Real.norm_eq_abs] using norm_iteratedDeriv_sin_le (k + 2) x'
  have hfac_pos : (0 : ℝ) < ((k + 2).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (pow_nonneg (abs_nonneg t) _) hbound)
    hfac_pos.le

private lemma abs_avgZ_le {n : ℕ} (f : QAlgorithms.Qubits n → ℝ) :
    |avgZ f| ≤ avgZ (fun x => |f x|) := by
  simp only [avgZ, abs_mul, abs_inv, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

private lemma avgZ_const' {n : ℕ} (c : ℝ) : avgZ (fun _ : QAlgorithms.Qubits n => c) = c := by
  simp only [avgZ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private lemma avgZ_add' {n : ℕ} (f g : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => f x + g x) = avgZ f + avgZ g := by
  simp only [avgZ, Finset.sum_add_distrib, mul_add]

private lemma avgZ_smul' {n : ℕ} (c : ℝ) (f : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => c * f x) = c * avgZ f := by
  simp only [avgZ, ← Finset.mul_sum]
  ring

private lemma avgZ_sum' {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, avgZ (f j) := by
  simp only [avgZ, Finset.sum_comm (s := Finset.univ) (t := s), Finset.mul_sum]

private lemma avgZ_sub' {n : ℕ} (f g : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => f x - g x) = avgZ f - avgZ g := by
  simp only [avgZ, Finset.sum_sub_distrib, mul_sub]

private lemma avgZ_mono' {n : ℕ} {f g : QAlgorithms.Qubits n → ℝ} (h : ∀ x, f x ≤ g x) :
    avgZ f ≤ avgZ g := by
  simp only [avgZ]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

private lemma eq_28_helper {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (i : Fin m) (k : ℕ) (hk : Odd k) (γ : ℝ) :
    |Rk tri rhs i k γ| ≤ (1 / 8) * |γ| ^ (k + 2) / ((k + 2).factorial : ℝ) *
      avgZ (fun x =>
        let d := sgn rhs i
        let c₁ := cPoly tri rhs i 0 x
        let c₂ := cPoly tri rhs i 1 x
        let c₃ := cPoly tri rhs i 2 x
        |d + c₁ + c₂ + c₃| ^ (k + 2) + |d + c₁ - c₂ - c₃| ^ (k + 2) +
          |d - c₁ + c₂ - c₃| ^ (k + 2) + |d - c₁ - c₂ + c₃| ^ (k + 2)) := by
  let S : ℝ → ℝ := fun t => ∑ j ∈ (Finset.range (k + 1)).filter Odd,
    t ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)
  let u₁ : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i + cPoly tri rhs i 0 x + cPoly tri rhs i 1 x + cPoly tri rhs i 2 x
  let u₂ : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i + cPoly tri rhs i 0 x - cPoly tri rhs i 1 x - cPoly tri rhs i 2 x
  let u₃ : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i - cPoly tri rhs i 0 x + cPoly tri rhs i 1 x - cPoly tri rhs i 2 x
  let u₄ : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i - cPoly tri rhs i 0 x - cPoly tri rhs i 1 x + cPoly tri rhs i 2 x
  have hlin : (1 / 2 : ℝ) * sgn rhs i ^ 2 * γ =
      (1 / 8 : ℝ) * sgn rhs i * avgZ (fun x => γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x) := by
    have hu : ∀ x, γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x = 4 * sgn rhs i * γ := by
      intro x; simp only [u₁, u₂, u₃, u₄]; ring
    simp_rw [hu, avgZ_const']
    ring
  have hPk : (1 / 2 : ℝ) * sgn rhs i ^ 2 * γ + Pk tri rhs i k γ =
      (1 / 8 : ℝ) * sgn rhs i *
        avgZ (fun x => S (γ * u₁ x) + S (γ * u₂ x) + S (γ * u₃ x) + S (γ * u₄ x)) := by
    rw [hlin, Pk]
    have hsplit : (Finset.range (k + 1)).filter Odd =
        insert 1 ((Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      have hk1 : 1 < k + 1 := by
        have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h => Nat.not_odd_zero (h ▸ hk))
        omega
      constructor
      · rintro ⟨hj1, hj2⟩
        by_cases hj_eq : j = 1
        · exact Or.inl hj_eq
        · right
          have hj_ne0 : j ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hj2
          have hj_ne2 : j ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hj2
          exact ⟨hj1, by omega, hj2⟩
      · rintro (rfl | ⟨hj1, _, hj3⟩)
        · exact ⟨hk1, by decide⟩
        · exact ⟨hj1, hj3⟩
    have h1_not : (1 : ℕ) ∉ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j) := by
      simp
    have hS_split : ∀ t : ℝ, S t = t + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
        t ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) := by
      intro t
      dsimp only [S]
      rw [hsplit, Finset.sum_insert h1_not]
      simp
    have havg_S : avgZ (fun x => S (γ * u₁ x) + S (γ * u₂ x) + S (γ * u₃ x) + S (γ * u₄ x)) =
        avgZ (fun x => γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x) +
        ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
          γ ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) *
            avgZ (fun x => u₁ x ^ j + u₂ x ^ j + u₃ x ^ j + u₄ x ^ j) := by
      simp_rw [hS_split]
      have hre : (fun x =>
          (γ * u₁ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
            (γ * u₁ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
          (γ * u₂ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
            (γ * u₂ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
          (γ * u₃ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
            (γ * u₃ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
          (γ * u₄ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
            (γ * u₄ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ))) =
          fun x => (γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x) +
            ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) *
                (u₁ x ^ j + u₂ x ^ j + u₃ x ^ j + u₄ x ^ j) := by
        ext x
        have hrearr :
            (γ * u₁ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₁ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
            (γ * u₂ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₂ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
            (γ * u₃ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₃ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
            (γ * u₄ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₄ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) =
            (γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x) +
            ((∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₁ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
             (∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₂ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
             (∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₃ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
             (∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₄ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ))) := by ring
        rw [hrearr, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow, mul_pow, mul_pow, mul_pow]; ring
      rw [hre, avgZ_add', avgZ_sum']
      simp_rw [avgZ_smul']
    rw [havg_S, mul_add]
  have hRk : Rk tri rhs i k γ = (1 / 8 : ℝ) * sgn rhs i *
      avgZ (fun x =>
        (Real.sin (γ * u₁ x) - S (γ * u₁ x)) +
        (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
        (Real.sin (γ * u₃ x) - S (γ * u₃ x)) +
        (Real.sin (γ * u₄ x) - S (γ * u₄ x))) := by
    rw [Rk, sub_sub, hPk, clauseSin]
    have hre : (fun x =>
        (Real.sin (γ * u₁ x) - S (γ * u₁ x)) +
        (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
        (Real.sin (γ * u₃ x) - S (γ * u₃ x)) +
        (Real.sin (γ * u₄ x) - S (γ * u₄ x))) =
        fun x => (Real.sin (γ * u₁ x) + Real.sin (γ * u₂ x) + Real.sin (γ * u₃ x) +
          Real.sin (γ * u₄ x)) - (S (γ * u₁ x) + S (γ * u₂ x) + S (γ * u₃ x) + S (γ * u₄ x)) := by
      ext x; ring
    rw [hre, avgZ_sub']
    dsimp only [u₁, u₂, u₃, u₄]
    ring
  rw [hRk, abs_mul, abs_mul]
  have hsgn_abs : |sgn rhs i| = 1 := by
    simp only [sgn]; cases rhs i <;> norm_num
  rw [hsgn_abs, mul_one, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
  refine (mul_le_mul_of_nonneg_left (abs_avgZ_le _) (by norm_num)).trans ?_
  have hpt : ∀ x,
      |(Real.sin (γ * u₁ x) - S (γ * u₁ x)) +
       (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
       (Real.sin (γ * u₃ x) - S (γ * u₃ x)) +
       (Real.sin (γ * u₄ x) - S (γ * u₄ x))| ≤
      (|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
        (|u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2)) := by
    intro x
    have b1 : |Real.sin (γ * u₁ x) - S (γ * u₁ x)| ≤
        |γ| ^ (k + 2) * |u₁ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
      calc |Real.sin (γ * u₁ x) - S (γ * u₁ x)|
          ≤ |γ * u₁ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := sin_taylor_bound k hk (γ * u₁ x)
        _ = |γ| ^ (k + 2) * |u₁ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by rw [abs_mul, mul_pow]
    have b2 : |Real.sin (γ * u₂ x) - S (γ * u₂ x)| ≤
        |γ| ^ (k + 2) * |u₂ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
      calc |Real.sin (γ * u₂ x) - S (γ * u₂ x)|
          ≤ |γ * u₂ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := sin_taylor_bound k hk (γ * u₂ x)
        _ = |γ| ^ (k + 2) * |u₂ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by rw [abs_mul, mul_pow]
    have b3 : |Real.sin (γ * u₃ x) - S (γ * u₃ x)| ≤
        |γ| ^ (k + 2) * |u₃ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
      calc |Real.sin (γ * u₃ x) - S (γ * u₃ x)|
          ≤ |γ * u₃ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := sin_taylor_bound k hk (γ * u₃ x)
        _ = |γ| ^ (k + 2) * |u₃ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by rw [abs_mul, mul_pow]
    have b4 : |Real.sin (γ * u₄ x) - S (γ * u₄ x)| ≤
        |γ| ^ (k + 2) * |u₄ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
      calc |Real.sin (γ * u₄ x) - S (γ * u₄ x)|
          ≤ |γ * u₄ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := sin_taylor_bound k hk (γ * u₄ x)
        _ = |γ| ^ (k + 2) * |u₄ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by rw [abs_mul, mul_pow]
    calc |(Real.sin (γ * u₁ x) - S (γ * u₁ x)) +
           (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
           (Real.sin (γ * u₃ x) - S (γ * u₃ x)) +
           (Real.sin (γ * u₄ x) - S (γ * u₄ x))|
        ≤ |Real.sin (γ * u₁ x) - S (γ * u₁ x)| + |Real.sin (γ * u₂ x) - S (γ * u₂ x)| +
          |Real.sin (γ * u₃ x) - S (γ * u₃ x)| + |Real.sin (γ * u₄ x) - S (γ * u₄ x)| := by
          linarith [abs_add_le (Real.sin (γ * u₁ x) - S (γ * u₁ x) +
            (Real.sin (γ * u₂ x) - S (γ * u₂ x)) + (Real.sin (γ * u₃ x) - S (γ * u₃ x)))
            (Real.sin (γ * u₄ x) - S (γ * u₄ x)),
            abs_add_le (Real.sin (γ * u₁ x) - S (γ * u₁ x) +
            (Real.sin (γ * u₂ x) - S (γ * u₂ x))) (Real.sin (γ * u₃ x) - S (γ * u₃ x)),
            abs_add_le (Real.sin (γ * u₁ x) - S (γ * u₁ x)) (Real.sin (γ * u₂ x) - S (γ * u₂ x))]
      _ ≤ |γ| ^ (k + 2) * |u₁ x| ^ (k + 2) / ↑(k + 2).factorial +
          |γ| ^ (k + 2) * |u₂ x| ^ (k + 2) / ↑(k + 2).factorial +
          |γ| ^ (k + 2) * |u₃ x| ^ (k + 2) / ↑(k + 2).factorial +
          |γ| ^ (k + 2) * |u₄ x| ^ (k + 2) / ↑(k + 2).factorial := by linarith
      _ = (|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
            (|u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2)) := by ring
  have hmono := avgZ_mono' hpt
  have hsmul : avgZ (fun x => (|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
      (|u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2))) =
      (|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
        avgZ (fun x => |u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2)) := by
    simp only [avgZ, ← Finset.mul_sum]
    ring
  rw [hsmul] at hmono
  calc (1 / 8 : ℝ) * avgZ (fun x =>
        |(Real.sin (γ * u₁ x) - S (γ * u₁ x)) + (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
         (Real.sin (γ * u₃ x) - S (γ * u₃ x)) + (Real.sin (γ * u₄ x) - S (γ * u₄ x))|)
      ≤ (1 / 8 : ℝ) * ((|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
          avgZ (fun x => |u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2))) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = (1 / 8) * |γ| ^ (k + 2) / ((k + 2).factorial : ℝ) *
          avgZ (fun x => |u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2)) := by
        ring



private lemma spin_sq' {n : ℕ} (x : QAlgorithms.Qubits n) (q : Fin n) :
    spin x q * spin x q = 1 := by
  simp only [spin]
  cases x q <;> norm_num

private lemma avgZ_const'' {n : ℕ} (c : ℝ) : avgZ (fun _ : QAlgorithms.Qubits n => c) = c := by
  simp only [avgZ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private lemma avgZ_nonneg {n : ℕ} {f : QAlgorithms.Qubits n → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ avgZ f := by
  simp only [avgZ]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => hf x)

private lemma avgZ_mono'' {n : ℕ} {f g : QAlgorithms.Qubits n → ℝ} (h : ∀ x, f x ≤ g x) :
    avgZ f ≤ avgZ g := by
  simp only [avgZ]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

private lemma avgZ_split {n : ℕ} (f : QAlgorithms.Qubits (n + 1) → ℝ) :
    avgZ f = (1 / 2 : ℝ) * avgZ (fun x : QAlgorithms.Qubits n =>
      f (Fin.snoc x false) + f (Fin.snoc x true)) := by
  let e : QAlgorithms.Qubits (n + 1) ≃ QAlgorithms.Qubits n × Bool :=
    { toFun := fun x => (Fin.init x, x (Fin.last n))
      invFun := fun p => Fin.snoc p.1 p.2
      left_inv := fun x => Fin.snoc_init_self x
      right_inv := fun p => by ext <;> simp [Fin.init, Fin.snoc] }
  have hsum : ∑ x : QAlgorithms.Qubits (n + 1), f x =
      ∑ x : QAlgorithms.Qubits n, (f (Fin.snoc x false) + f (Fin.snoc x true)) := by
    rw [Fintype.sum_equiv e _ (fun p => f (Fin.snoc p.1 p.2)) (fun x => by simp [e])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [add_comm]
  have hcard : (Fintype.card (QAlgorithms.Qubits (n + 1)) : ℝ) =
      2 * (Fintype.card (QAlgorithms.Qubits n) : ℝ) := by
    simp only [QAlgorithms.Qubits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, pow_succ]
    push_cast
    ring
  simp only [avgZ, hsum, hcard]
  ring

private lemma poly_factor_id (p : ℕ) (hp : 3 ≤ p) (u : ℝ) :
    2 * ((p : ℝ) - 1) * (1 - u) * (1 + u ^ p) -
      (1 - u ^ (p - 1)) * ((1 + u) ^ 2 + ((p : ℝ) - 1) * (1 - u) ^ 2) =
    (1 - u) ^ 3 * ∑ j ∈ Finset.range (p - 1),
      (((p : ℝ) - 2) + 2 * (j : ℝ) * ((p : ℝ) - 2 - (j : ℝ))) * u ^ j := by
  let c : ℕ → ℝ := fun j => ((p : ℝ) - 2) + 2 * (j : ℝ) * ((p : ℝ) - 2 - (j : ℝ))
  have hc0 : c 0 = (p : ℝ) - 2 := by simp [c]
  have hcp : c (p - 2) = (p : ℝ) - 2 := by
    simp only [c]
    have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast]
    ring
  -- Telescope (1 - u) * ∑_{j < p - 1} c j * u^j
  have hstep1 : (1 - u) * ∑ j ∈ Finset.range (p - 1), c j * u ^ j =
      c 0 - c (p - 2) * u ^ (p - 1) +
        ∑ j ∈ Finset.Ico 1 (p - 1), (c j - c (j - 1)) * u ^ j := by
    have h1 : (∑ j ∈ Finset.range (p - 1), c j * u ^ j) -
        ∑ j ∈ Finset.range (p - 1), c j * u ^ (j + 1) =
        c 0 - c (p - 2) * u ^ (p - 1) +
          ∑ j ∈ Finset.Ico 1 (p - 1), (c j - c (j - 1)) * u ^ j := by
      have hr1 : Finset.range (p - 1) = insert 0 (Finset.Ico 1 (p - 1)) := by
        ext j; simp; omega
      have hr2 : Finset.range (p - 1) = insert (p - 2) (Finset.range (p - 2)) := by
        rw [← Finset.range_add_one]
        congr 1; omega
      nth_rw 1 [hr1]
      rw [Finset.sum_insert (by simp)]
      nth_rw 1 [hr2]
      rw [Finset.sum_insert (by simp)]
      have hshift : ∑ j ∈ Finset.range (p - 2), c j * u ^ (j + 1) =
          ∑ j ∈ Finset.Ico 1 (p - 1), c (j - 1) * u ^ j := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        refine Finset.sum_congr (by congr 1) fun j _ => by ring
      rw [hshift]
      have hsub : p - 2 + 1 = p - 1 := by omega
      rw [hsub]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      simp only [pow_zero, mul_one]
      ring
    calc (1 - u) * ∑ j ∈ Finset.range (p - 1), c j * u ^ j
        = (∑ j ∈ Finset.range (p - 1), c j * u ^ j) -
            ∑ j ∈ Finset.range (p - 1), c j * u ^ (j + 1) := by
          rw [sub_mul, one_mul, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = _ := h1
  have hdiff : ∀ j ∈ Finset.Ico 1 (p - 1),
      c j - c (j - 1) = 2 * ((p : ℝ) - 1) - 4 * (j : ℝ) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    simp only [c, Nat.cast_sub hj1, Nat.cast_one]
    ring
  have hstep2 : (1 - u) * ((p - 2 : ℝ) - (p - 2 : ℝ) * u ^ (p - 1) +
      ∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j) =
      (p - 2 : ℝ) + ((p : ℝ) - 4) * u + ((p : ℝ) - 4) * u ^ (p - 1) +
        ((p : ℝ) - 2) * u ^ p - 4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j := by
    have hmul : (1 - u) * ∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j =
        (∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j) -
        (∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ (j + 1)) := by
      rw [sub_mul, one_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    have hsum_eq : (∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j) -
        (∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ (j + 1)) =
        (2 * ((p : ℝ) - 1) - 4) * u - (2 * ((p : ℝ) - 1) - 4 * ((p - 2 : ℕ) : ℝ)) * u ^ (p - 1) -
          4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j := by
      have hIco1 : Finset.Ico 1 (p - 1) = insert 1 (Finset.Ico 2 (p - 1)) := by
        ext j; simp; omega
      have hIco2 : Finset.Ico 1 (p - 1) = insert (p - 2) (Finset.Ico 1 (p - 2)) := by
        ext j; simp; omega
      nth_rw 1 [hIco1]
      rw [Finset.sum_insert (by simp)]
      nth_rw 1 [hIco2]
      rw [Finset.sum_insert (by simp)]
      have hsh : ∑ j ∈ Finset.Ico 1 (p - 2), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ (j + 1) =
          ∑ j ∈ Finset.Ico 2 (p - 1), (2 * ((p : ℝ) - 1) - 4 * ((j : ℝ) - 1)) * u ^ j := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
        have hrg : p - 2 - 1 = p - 1 - 2 := by omega
        rw [hrg]
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast
        rw [show 1 + j + 1 = 2 + j by omega]
        ring
      rw [hsh]
      have hsub : p - 2 + 1 = p - 1 := by omega
      rw [hsub]
      have hsub_sum : (∑ j ∈ Finset.Ico 2 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j) -
          (∑ j ∈ Finset.Ico 2 (p - 1), (2 * ((p : ℝ) - 1) - 4 * ((j : ℝ) - 1)) * u ^ j) =
          -4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      simp only [Nat.cast_one, pow_one]
      linear_combination hsub_sum
    have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hp_split : u ^ p = u * u ^ (p - 1) := by
      rw [← pow_succ', show p - 1 + 1 = p by omega]
    rw [mul_add, hmul, hsum_eq, hcast, hp_split]
    ring
  have hgeom : (1 - u) * (4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j) =
      4 * u ^ 2 - 4 * u ^ (p - 1) := by
    by_cases hp3 : p = 3
    · subst hp3; simp
    · have hp4 : 4 ≤ p := by omega
      have htel : (1 - u) * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j = u ^ 2 - u ^ (p - 1) := by
        rw [sub_mul, one_mul, Finset.mul_sum]
        have hI1 : Finset.Ico 2 (p - 1) = insert 2 (Finset.Ico 3 (p - 1)) := by
          ext j; simp; omega
        have hI2 : Finset.Ico 2 (p - 1) = insert (p - 2) (Finset.Ico 2 (p - 2)) := by
          ext j; simp; omega
        nth_rw 1 [hI1]
        rw [Finset.sum_insert (by simp)]
        nth_rw 1 [hI2]
        rw [Finset.sum_insert (by simp)]
        have hsh : ∑ j ∈ Finset.Ico 2 (p - 2), u * u ^ j = ∑ j ∈ Finset.Ico 3 (p - 1), u ^ j := by
          rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
          have hrg : p - 2 - 2 = p - 1 - 3 := by omega
          rw [hrg]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show 3 + j = (2 + j) + 1 by omega, pow_succ']
        rw [hsh, ← pow_succ', show p - 2 + 1 = p - 1 by omega]
        ring
      rw [← mul_assoc, mul_comm (1 - u) 4, mul_assoc, htel]
      ring
  have hstep3 : (1 - u) * ((p - 2 : ℝ) + ((p : ℝ) - 4) * u + ((p : ℝ) - 4) * u ^ (p - 1) +
      ((p : ℝ) - 2) * u ^ p - 4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j) =
      2 * ((p : ℝ) - 1) * (1 - u) * (1 + u ^ p) -
        (1 - u ^ (p - 1)) * ((1 + u) ^ 2 + ((p : ℝ) - 1) * (1 - u) ^ 2) := by
    have hp_split : u ^ p = u * u ^ (p - 1) := by
      rw [← pow_succ', show p - 1 + 1 = p by omega]
    rw [mul_sub, hgeom, hp_split]
    ring
  rw [show (1 - u) ^ 3 * ∑ j ∈ Finset.range (p - 1), c j * u ^ j =
      (1 - u) * ((1 - u) * ((1 - u) * ∑ j ∈ Finset.range (p - 1), c j * u ^ j)) by ring]
  rw [hstep1, Finset.sum_congr rfl fun j hj => by rw [hdiff j hj], hc0, hcp, hstep2, hstep3]

private lemma two_point_bonami_unit (p : ℕ) (hp : 2 ≤ p) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 + t) ^ p + (1 - t) ^ p) / 2 ≤ (1 + ((p : ℝ) - 1) * t ^ 2) ^ ((p : ℝ) / 2) := by
  by_cases hp2 : p = 2
  · subst hp2
    norm_num
    linarith
  have hp3 : 3 ≤ p := by omega
  let f : ℝ → ℝ := fun s =>
    Real.log (((1 + s) ^ p + (1 - s) ^ p) / 2) -
      ((p : ℝ) / 2) * Real.log (1 + ((p : ℝ) - 1) * s ^ 2)
  have hpos_num : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < ((1 + s) ^ p + (1 - s) ^ p) / 2 := by
    intro s hs
    have h1 : 0 < (1 + s) ^ p := pow_pos (by linarith [hs.1]) p
    have h2 : 0 ≤ (1 - s) ^ p := pow_nonneg (by linarith [hs.2]) p
    linarith
  have hpos_den : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + ((p : ℝ) - 1) * s ^ 2 := by
    intro s _
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith
  have hf_cont : ContinuousOn f (Set.Icc 0 1) := by
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.log ?_ (fun s hs => (hpos_num s hs).ne')
      exact (((continuous_const.add continuous_id).pow p).add
        ((continuous_const.sub continuous_id).pow p)).div_const 2 |>.continuousOn
    · refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.log ?_ (fun s hs => (hpos_den s hs).ne')
      exact (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).continuousOn
  let f' : ℝ → ℝ := fun s =>
    ((p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / 2) /
      (((1 + s) ^ p + (1 - s) ^ p) / 2) -
      ((p : ℝ) / 2) * (2 * ((p : ℝ) - 1) * s / (1 + ((p : ℝ) - 1) * s ^ 2))
  have hf_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (f' s) s ∧ f' s ≤ 0 := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hs1 : s < 1 := hs.2
    have hnum_pos : 0 < ((1 + s) ^ p + (1 - s) ^ p) / 2 := hpos_num s ⟨hs0.le, hs1.le⟩
    have hden_pos : 0 < 1 + ((p : ℝ) - 1) * s ^ 2 := hpos_den s ⟨hs0.le, hs1.le⟩
    have hd1 : HasDerivAt (fun x => ((1 + x) ^ p + (1 - x) ^ p) / 2)
        ((p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / 2) s := by
      have ha : HasDerivAt (fun x => (1 + x) ^ p) ((p : ℝ) * (1 + s) ^ (p - 1) * 1) s :=
        ((hasDerivAt_id s).const_add 1).pow p
      have hb : HasDerivAt (fun x => (1 - x) ^ p) ((p : ℝ) * (1 - s) ^ (p - 1) * (-1)) s :=
        ((hasDerivAt_id s).const_sub 1).pow p
      exact ((ha.add hb).div_const 2).congr_deriv (by ring)
    have hd2 : HasDerivAt (fun x => 1 + ((p : ℝ) - 1) * x ^ 2)
        (2 * ((p : ℝ) - 1) * s) s := by
      have hx2 : HasDerivAt (fun x => x ^ 2) (2 * s) s :=
        ((hasDerivAt_id s).pow 2).congr_deriv (by simp)
      exact ((hasDerivAt_const s 1).add (hx2.const_mul ((p : ℝ) - 1))).congr_deriv (by ring)
    have hd_f : HasDerivAt f
        (((p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / 2) /
          (((1 + s) ^ p + (1 - s) ^ p) / 2) -
          ((p : ℝ) / 2) * (2 * ((p : ℝ) - 1) * s / (1 + ((p : ℝ) - 1) * s ^ 2))) s :=
      (hd1.log hnum_pos.ne').sub ((hd2.log hden_pos.ne').const_mul ((p : ℝ) / 2))
    refine ⟨hd_f, ?_⟩
    rw [sub_nonpos]
    have hsimp1 : ((p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / 2) /
        (((1 + s) ^ p + (1 - s) ^ p) / 2) =
        (p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / ((1 + s) ^ p + (1 - s) ^ p) := by
      field_simp
    have hsimp2 : ((p : ℝ) / 2) * (2 * ((p : ℝ) - 1) * s / (1 + ((p : ℝ) - 1) * s ^ 2)) =
        (p : ℝ) * (((p : ℝ) - 1) * s / (1 + ((p : ℝ) - 1) * s ^ 2)) := by
      ring
    have hsum_pos : 0 < (1 + s) ^ p + (1 - s) ^ p := by linarith
    rw [hsimp1, hsimp2, ← mul_div_assoc, div_le_div_iff₀ hsum_pos hden_pos,
      mul_assoc, mul_assoc, mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < p)]
    -- Reduce to u = (1 - s) / (1 + s) ∈ (0, 1)
    let u : ℝ := (1 - s) / (1 + s)
    have h1s_pos : 0 < 1 + s := by linarith
    have hu_pos : 0 < u := div_pos (by linarith) h1s_pos
    have hu_lt1 : u < 1 := by rw [div_lt_one h1s_pos]; linarith
    have hs_eq : s = (1 - u) / (1 + u) := by
      simp only [u]; field_simp [h1s_pos.ne']; ring
    have h1s_eq : 1 + s = 2 / (1 + u) := by
      simp only [u]; field_simp [h1s_pos.ne']; ring
    have h1ms_eq : 1 - s = 2 * u / (1 + u) := by
      simp only [u]; field_simp [h1s_pos.ne']; ring
    have hpoly := poly_factor_id p hp3 u
    have hpoly_nonneg : 0 ≤ (1 - u) ^ 3 * ∑ j ∈ Finset.range (p - 1),
        (((p : ℝ) - 2) + 2 * (j : ℝ) * ((p : ℝ) - 2 - (j : ℝ))) * u ^ j := by
      refine mul_nonneg (pow_nonneg (by linarith) 3) (Finset.sum_nonneg fun j hj => ?_)
      have hjp : j < p - 1 := Finset.mem_range.mp hj
      have hj_le : (j : ℝ) ≤ (p : ℝ) - 2 := by
        have hsub : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ p)]; norm_num
        rw [← hsub]
        exact_mod_cast (by omega : j ≤ p - 2)
      have hp2_ge : (0 : ℝ) ≤ (p : ℝ) - 2 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp
        linarith
      refine mul_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) j]) (pow_nonneg hu_pos.le j)
    rw [← hpoly] at hpoly_nonneg
    have h1u_pos : 0 < 1 + u := by linarith
    have hscale : ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) * (1 + ((p : ℝ) - 1) * s ^ 2) =
        (2 ^ (p - 1) / (1 + u) ^ (p + 1)) *
          ((1 - u ^ (p - 1)) * ((1 + u) ^ 2 + ((p : ℝ) - 1) * (1 - u) ^ 2)) := by
      rw [h1s_eq, h1ms_eq, hs_eq]
      rw [div_pow, div_pow, mul_pow]
      have hpow1 : (1 + u) ^ (p - 1) * (1 + u) ^ 2 = (1 + u) ^ (p + 1) := by
        rw [← pow_add]; congr 1; omega
      field_simp [h1u_pos.ne']
      rw [← hpow1]
      ring
    have hscale2 : ((p : ℝ) - 1) * s * ((1 + s) ^ p + (1 - s) ^ p) =
        (2 ^ (p - 1) / (1 + u) ^ (p + 1)) * (2 * ((p : ℝ) - 1) * (1 - u) * (1 + u ^ p)) := by
      rw [h1s_eq, h1ms_eq, hs_eq, div_pow, div_pow, mul_pow]
      have h2p : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by
        rw [← pow_succ', show p - 1 + 1 = p by omega]
      have h1up : (1 + u) * (1 + u) ^ p = (1 + u) ^ (p + 1) := by
        rw [← pow_succ']
      field_simp [h1u_pos.ne']
      rw [h2p, ← h1up]
      ring
    rw [hscale, hscale2]
    refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hf_anti : AntitoneOn f (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc 0 1) hf_cont ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      exact (hf_deriv s hs).1.hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hf_deriv s hs).2
  have hf_le : f t ≤ f 0 := hf_anti (Set.left_mem_Icc.mpr zero_le_one) ⟨ht0, ht1⟩ ht0
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at hf_le
  dsimp only [f] at hf_le
  have hlog_le : Real.log (((1 + t) ^ p + (1 - t) ^ p) / 2) ≤
      Real.log ((1 + ((p : ℝ) - 1) * t ^ 2) ^ ((p : ℝ) / 2)) := by
    rw [Real.log_rpow (hpos_den t ⟨ht0, ht1⟩)]
    linarith
  exact (Real.log_le_log_iff (hpos_num t ⟨ht0, ht1⟩)
    (Real.rpow_pos_of_pos (hpos_den t ⟨ht0, ht1⟩) _)).mp hlog_le

private lemma two_point_bonami (p : ℕ) (hp : 2 ≤ p) (A B : ℝ) :
    (|A + B| ^ p + |A - B| ^ p) / 2 ≤ (A ^ 2 + ((p : ℝ) - 1) * B ^ 2) ^ ((p : ℝ) / 2) := by
  wlog hAB : |B| ≤ |A|
  · push Not at hAB
    have h1 : (|B + A| ^ p + |B - A| ^ p) / 2 ≤
        (B ^ 2 + ((p : ℝ) - 1) * A ^ 2) ^ ((p : ℝ) / 2) := this p hp B A hAB.le
    have heq : |B + A| ^ p + |B - A| ^ p = |A + B| ^ p + |A - B| ^ p := by
      rw [add_comm B A, abs_sub_comm B A]
    rw [heq] at h1
    have hp1_nn : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    refine h1.trans (Real.rpow_le_rpow (by positivity) ?_ (by positivity))
    have hsq : A ^ 2 ≤ B ^ 2 := by nlinarith [abs_nonneg A, abs_nonneg B, sq_abs A, sq_abs B]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  wlog hA : 0 ≤ A
  · push Not at hA
    have h1 := this p hp (-A) (-B) (by simpa using hAB) (by linarith)
    have hneg : |(-A) + (-B)| ^ p + |(-A) - (-B)| ^ p = |A + B| ^ p + |A - B| ^ p := by
      rw [show (-A) + (-B) = -(A + B) by ring, show (-A) - (-B) = -(A - B) by ring,
        abs_neg, abs_neg]
    rw [hneg] at h1
    simpa only [neg_sq] using h1
  wlog hB : 0 ≤ B
  · push Not at hB
    have h1 := this p hp A (-B) (by simpa using hAB) hA (by linarith)
    have hneg : |A + (-B)| ^ p + |A - (-B)| ^ p = |A + B| ^ p + |A - B| ^ p := by
      rw [show A + (-B) = A - B by ring, show A - (-B) = A + B by ring, add_comm]
    rw [hneg] at h1
    simpa only [neg_sq] using h1
  by_cases hA0 : A = 0
  · subst hA0
    have hB0 : B = 0 := by
      rw [abs_zero] at hAB
      exact le_antisymm (abs_le.mp hAB).2 hB
    subst hB0
    simp [show p ≠ 0 by omega, show (p : ℝ) / 2 ≠ 0 by positivity]
  have hA_pos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  let t := B / A
  have ht0 : 0 ≤ t := div_nonneg hB hA_pos.le
  have ht1 : t ≤ 1 := by
    rw [div_le_one hA_pos]
    simpa [abs_of_nonneg hA, abs_of_nonneg hB] using hAB
  have hu := two_point_bonami_unit p hp t ht0 ht1
  have hL : (|A + B| ^ p + |A - B| ^ p) / 2 = A ^ p * (((1 + t) ^ p + (1 - t) ^ p) / 2) := by
    have h1 : |A + B| = A * (1 + t) := by
      rw [abs_of_nonneg (by linarith)]
      simp only [t]; field_simp [hA_pos.ne']
    have h2 : |A - B| = A * (1 - t) := by
      have hBA : B ≤ A := by simpa [abs_of_nonneg hA, abs_of_nonneg hB] using hAB
      rw [abs_of_nonneg (by linarith)]
      simp only [t]; field_simp [hA_pos.ne']
    rw [h1, h2, mul_pow, mul_pow]
    ring
  have hR : (A ^ 2 + ((p : ℝ) - 1) * B ^ 2) ^ ((p : ℝ) / 2) =
      A ^ p * (1 + ((p : ℝ) - 1) * t ^ 2) ^ ((p : ℝ) / 2) := by
    have hB_eq : B = A * t := by simp only [t]; field_simp [hA_pos.ne']
    rw [hB_eq, mul_pow]
    have hfac : A ^ 2 + ((p : ℝ) - 1) * (A ^ 2 * t ^ 2) =
        A ^ 2 * (1 + ((p : ℝ) - 1) * t ^ 2) := by ring
    have hp1_nn : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    rw [hfac, Real.mul_rpow (sq_nonneg A) (add_nonneg zero_le_one (mul_nonneg hp1_nn (sq_nonneg t)))]
    congr 1
    rw [← Real.rpow_natCast A p, ← Real.rpow_two A, ← Real.rpow_mul hA_pos.le]
    congr 1
    ring
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left hu (pow_nonneg hA_pos.le p)

private lemma bonami_avgZ_step {n : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (A B : QAlgorithms.Qubits n → ℝ) :
    (avgZ (fun x => (|A x + B x| ^ p + |A x - B x| ^ p) / 2)) ^ (2 / (p : ℝ)) ≤
      (avgZ (fun x => |A x| ^ p)) ^ (2 / (p : ℝ)) +
        ((p : ℝ) - 1) * (avgZ (fun x => |B x| ^ p)) ^ (2 / (p : ℝ)) := by
  have hp_pos : (0 : ℝ) < p := by positivity
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hq : 1 ≤ (p : ℝ) / 2 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hpt : ∀ x, (|A x + B x| ^ p + |A x - B x| ^ p) / 2 ≤
      (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2) :=
    fun x => two_point_bonami p hp (A x) (B x)
  have hmono : avgZ (fun x => (|A x + B x| ^ p + |A x - B x| ^ p) / 2) ≤
      avgZ (fun x => (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2)) :=
    avgZ_mono'' hpt
  have hrpow1 : (avgZ (fun x => (|A x + B x| ^ p + |A x - B x| ^ p) / 2)) ^ (2 / (p : ℝ)) ≤
      (avgZ (fun x => (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2))) ^ (2 / (p : ℝ)) :=
    Real.rpow_le_rpow (avgZ_nonneg fun x => by positivity) hmono (by positivity)
  refine hrpow1.trans ?_
  let N : ℝ := Fintype.card (QAlgorithms.Qubits n)
  have hN_pos : 0 < N := by
    simp only [N, QAlgorithms.Qubits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    positivity
  have hmink := Real.Lp_add_le (Finset.univ : Finset (QAlgorithms.Qubits n))
    (fun x => A x ^ 2) (fun x => ((p : ℝ) - 1) * B x ^ 2) hq
  have h1q : 1 / ((p : ℝ) / 2) = 2 / (p : ℝ) := by ring
  rw [h1q] at hmink
  have hA_abs : ∀ x, |A x ^ 2| ^ ((p : ℝ) / 2) = |A x| ^ p := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (A x), ← Real.rpow_natCast (|A x|) p,
      ← Real.rpow_natCast (|A x|) 2, ← Real.rpow_mul (abs_nonneg _)]
    congr 1; ring
  have hB_abs : ∀ x, |((p : ℝ) - 1) * B x ^ 2| ^ ((p : ℝ) / 2) =
      ((p : ℝ) - 1) ^ ((p : ℝ) / 2) * |B x| ^ p := by
    intro x
    rw [abs_mul, abs_of_nonneg hp1, abs_of_nonneg (sq_nonneg _),
      Real.mul_rpow hp1 (sq_nonneg _), ← sq_abs (B x), ← Real.rpow_natCast (|B x|) p,
      ← Real.rpow_natCast (|B x|) 2, ← Real.rpow_mul (abs_nonneg _)]
    congr 2; ring
  have hAB_abs : ∀ x, |A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2| ^ ((p : ℝ) / 2) =
      (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2) := by
    intro x
    rw [abs_of_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hp1 (sq_nonneg _)))]
  simp_rw [hAB_abs, hA_abs, hB_abs] at hmink
  have havg_eq : ∀ f : QAlgorithms.Qubits n → ℝ, (∀ x, 0 ≤ f x) →
      (avgZ f) ^ (2 / (p : ℝ)) = N ^ (-(2 / (p : ℝ))) * (∑ x, f x) ^ (2 / (p : ℝ)) := by
    intro f hf
    simp only [avgZ]
    rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun x _ => hf x)]
    congr 1
    rw [← Real.rpow_neg_one N, ← Real.rpow_mul hN_pos.le]
    congr 1; ring
  rw [havg_eq _ (fun x => Real.rpow_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hp1 (sq_nonneg _))) _),
    havg_eq _ (fun x => pow_nonneg (abs_nonneg _) _),
    havg_eq _ (fun x => pow_nonneg (abs_nonneg _) _)]
  have hB_factor : (∑ x, ((p : ℝ) - 1) ^ ((p : ℝ) / 2) * |B x| ^ p) ^ (2 / (p : ℝ)) =
      ((p : ℝ) - 1) * (∑ x, |B x| ^ p) ^ (2 / (p : ℝ)) := by
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg hp1 _) (Finset.sum_nonneg fun x _ => by positivity),
      ← Real.rpow_mul hp1, show ((p : ℝ) / 2) * (2 / (p : ℝ)) = 1 by field_simp [hp_pos.ne'],
      Real.rpow_one]
  rw [hB_factor] at hmink
  calc N ^ (-(2 / (p : ℝ))) * (∑ x, (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2)) ^ (2 / (p : ℝ))
      ≤ N ^ (-(2 / (p : ℝ))) * ((∑ x, |A x| ^ p) ^ (2 / (p : ℝ)) +
          ((p : ℝ) - 1) * (∑ x, |B x| ^ p) ^ (2 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hmink (by positivity)
    _ = N ^ (-(2 / (p : ℝ))) * (∑ x, |A x| ^ p) ^ (2 / (p : ℝ)) +
          ((p : ℝ) - 1) * (N ^ (-(2 / (p : ℝ))) * (∑ x, |B x| ^ p) ^ (2 / (p : ℝ))) := by
        ring

private lemma bonami_deg1 (n k : ℕ) (b₀ : ℝ) (b₁ : Fin n → ℝ) :
    (avgZ (fun x : QAlgorithms.Qubits n => |b₀ + ∑ v, b₁ v * spin x v| ^ (k + 2))) ^
        (2 / ((k + 2 : ℕ) : ℝ)) ≤
      ((k : ℝ) + 1) * avgZ (fun x : QAlgorithms.Qubits n => (b₀ + ∑ v, b₁ v * spin x v) ^ 2) := by
  induction n generalizing b₀ with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, avgZ_const'']
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    rw [← sq_abs b₀, ← Real.rpow_natCast (|b₀|) (k + 2), ← Real.rpow_mul (abs_nonneg _)]
    have hexp : ((k + 2 : ℕ) : ℝ) * (2 / ((k + 2 : ℕ) : ℝ)) = 2 := by
      have : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hexp, Real.rpow_two]
    nlinarith [sq_nonneg b₀]
  | succ n ih =>
    let A : QAlgorithms.Qubits n → ℝ := fun x => b₀ + ∑ v : Fin n, b₁ v.castSucc * spin x v
    let B : QAlgorithms.Qubits n → ℝ := fun _ => b₁ (Fin.last n)
    have hsplit_g : ∀ (x : QAlgorithms.Qubits n) (b : Bool),
        (b₀ + ∑ v : Fin (n + 1), b₁ v * spin (Fin.snoc x b) v) =
        A x + (if b = false then B x else -B x) := by
      intro x b
      rw [Fin.sum_univ_castSucc]
      have hcast : ∀ v : Fin n, spin (Fin.snoc x b) v.castSucc = spin x v := by
        intro v; simp [spin, Fin.snoc]
      have hlast : spin (Fin.snoc x b) (Fin.last n) = if b = false then 1 else -1 := by
        simp [spin, Fin.snoc]
        cases b <;> simp
      simp_rw [hcast, hlast]
      dsimp only [A, B]
      cases b <;> simp <;> ring
    have havg_p : avgZ (fun x : QAlgorithms.Qubits (n + 1) =>
        |b₀ + ∑ v, b₁ v * spin x v| ^ (k + 2)) =
        avgZ (fun x : QAlgorithms.Qubits n => (|A x + B x| ^ (k + 2) + |A x - B x| ^ (k + 2)) / 2) := by
      rw [avgZ_split]
      simp_rw [hsplit_g]
      simp only [↓reduceIte, Bool.true_eq_false, ← sub_eq_add_neg]
      simp only [avgZ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    have havg_2 : avgZ (fun x : QAlgorithms.Qubits (n + 1) =>
        (b₀ + ∑ v, b₁ v * spin x v) ^ 2) =
        avgZ (fun x : QAlgorithms.Qubits n => A x ^ 2) + b₁ (Fin.last n) ^ 2 := by
      rw [avgZ_split]
      simp_rw [hsplit_g]
      have hsq : ∀ x : QAlgorithms.Qubits n,
          (A x + B x) ^ 2 + (A x + -B x) ^ 2 = 2 * (A x ^ 2 + b₁ (Fin.last n) ^ 2) := by
        intro x; dsimp only [B]; ring
      simp only [↓reduceIte, Bool.true_eq_false]
      simp_rw [hsq]
      have hre : avgZ (fun x : QAlgorithms.Qubits n => 2 * (A x ^ 2 + b₁ (Fin.last n) ^ 2)) =
          2 * (avgZ (fun x => A x ^ 2) + b₁ (Fin.last n) ^ 2) := by
        simp only [avgZ, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum]
        have hcard : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        field_simp
      rw [hre]
      ring
    rw [havg_p, havg_2]
    have hstep := bonami_avgZ_step (k + 2) (by omega) A B
    have ihA := ih b₀ (fun v => b₁ v.castSucc)
    have hB_eq : (avgZ (fun x : QAlgorithms.Qubits n => |B x| ^ (k + 2))) ^ (2 / ((k + 2 : ℕ) : ℝ)) =
        b₁ (Fin.last n) ^ 2 := by
      simp only [B, avgZ_const'']
      rw [← Real.rpow_natCast (|b₁ (Fin.last n)|) (k + 2), ← Real.rpow_mul (abs_nonneg _)]
      have hexp : ((k + 2 : ℕ) : ℝ) * (2 / ((k + 2 : ℕ) : ℝ)) = 2 := by
        have : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [hexp, Real.rpow_two, sq_abs]
    have hk_eq : ((k + 2 : ℕ) : ℝ) - 1 = (k : ℝ) + 1 := by push_cast; ring
    rw [hk_eq] at hstep
    rw [hB_eq] at hstep
    nlinarith [ihA]

private lemma eq_29_helper (n k : ℕ) (a₀ : ℝ) (a₁ : Fin n → ℝ) (a₂ : Fin n → Fin n → ℝ) :
    let c : QAlgorithms.Qubits n → ℝ := fun x =>
      a₀ + ∑ v, a₁ v * spin x v +
        ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)
    avgZ (fun x => |c x| ^ (k + 2)) ≤
      ((k : ℝ) + 1) ^ (k + 2) * Real.sqrt (avgZ (fun x => c x ^ 2)) ^ (k + 2) := by
  intro c
  have hmain : ∀ (m : ℕ) (a₀ : ℝ) (a₁ : Fin m → ℝ) (a₂ : Fin m → Fin m → ℝ),
      (avgZ (fun x : QAlgorithms.Qubits m =>
        |a₀ + ∑ v, a₁ v * spin x v +
          ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)| ^ (k + 2))) ^
          (2 / ((k + 2 : ℕ) : ℝ)) ≤
        ((k : ℝ) + 1) ^ 2 * avgZ (fun x : QAlgorithms.Qubits m =>
          (a₀ + ∑ v, a₁ v * spin x v +
            ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)) ^ 2) := by
    intro m
    induction m with
    | zero =>
      intro a₀ a₁ a₂
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, avgZ_const'']
      rw [← Real.rpow_natCast (|a₀|) (k + 2), ← Real.rpow_mul (abs_nonneg _)]
      have hexp : ((k + 2 : ℕ) : ℝ) * (2 / ((k + 2 : ℕ) : ℝ)) = 2 := by
        have : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [hexp, Real.rpow_two, sq_abs]
      have hk1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
      nlinarith [sq_nonneg a₀]
    | succ m ih =>
      intro a₀ a₁ a₂
      let A : QAlgorithms.Qubits m → ℝ := fun x =>
        a₀ + ∑ v : Fin m, a₁ v.castSucc * spin x v +
          ∑ u : Fin m, ∑ v : Fin m,
            (if u < v then a₂ u.castSucc v.castSucc * spin x u * spin x v else 0)
      let B : QAlgorithms.Qubits m → ℝ := fun x =>
        a₁ (Fin.last m) + ∑ u : Fin m, a₂ u.castSucc (Fin.last m) * spin x u
      have hsplit_c : ∀ (x : QAlgorithms.Qubits m) (b : Bool),
          (a₀ + ∑ v : Fin (m + 1), a₁ v * spin (Fin.snoc x b) v +
            ∑ u : Fin (m + 1), ∑ v : Fin (m + 1),
              (if u < v then a₂ u v * spin (Fin.snoc x b) u * spin (Fin.snoc x b) v else 0)) =
          A x + (if b = false then B x else -B x) := by
        intro x b
        have hcast : ∀ v : Fin m, spin (Fin.snoc x b) v.castSucc = spin x v := by
          intro v; simp [spin, Fin.snoc]
        have hlast : spin (Fin.snoc x b) (Fin.last m) = if b = false then 1 else -1 := by
          simp [spin, Fin.snoc]
          cases b <;> simp
        rw [Fin.sum_univ_castSucc]
        have hdouble : (∑ u : Fin (m + 1), ∑ v : Fin (m + 1),
            (if u < v then a₂ u v * spin (Fin.snoc x b) u * spin (Fin.snoc x b) v else 0)) =
            (∑ u : Fin m, ∑ v : Fin m,
              (if u < v then a₂ u.castSucc v.castSucc * spin x u * spin x v else 0)) +
            (∑ u : Fin m, a₂ u.castSucc (Fin.last m) * spin x u) * (if b = false then 1 else -1) := by
          rw [Fin.sum_univ_castSucc]
          have hlast_u : (∑ v : Fin (m + 1),
              (if Fin.last m < v then a₂ (Fin.last m) v * spin (Fin.snoc x b) (Fin.last m) *
                spin (Fin.snoc x b) v else 0)) = 0 := by
            refine Finset.sum_eq_zero fun v _ => ?_
            have hv : ¬ Fin.last m < v := not_lt.mpr (Fin.le_last v)
            simp [hv]
          rw [hlast_u, add_zero]
          have hinner : ∀ u : Fin m,
              (∑ v : Fin (m + 1),
                (if u.castSucc < v then a₂ u.castSucc v * spin (Fin.snoc x b) u.castSucc *
                  spin (Fin.snoc x b) v else 0)) =
              (∑ v : Fin m,
                (if u < v then a₂ u.castSucc v.castSucc * spin x u * spin x v else 0)) +
              a₂ u.castSucc (Fin.last m) * spin x u * (if b = false then 1 else -1) := by
            intro u
            rw [Fin.sum_univ_castSucc]
            congr 1
            · refine Finset.sum_congr rfl fun v _ => ?_
              have hlt : (u.castSucc < v.castSucc) ↔ u < v := Iff.rfl
              simp [hlt, hcast]
            · have hlt : u.castSucc < Fin.last m := Fin.castSucc_lt_last u
              simp [hlt, hcast, hlast]
          simp_rw [hinner, Finset.sum_add_distrib, Finset.sum_mul]
        rw [hdouble]
        simp_rw [hcast, hlast]
        dsimp only [A, B]
        cases b <;> simp <;> ring
      have havg_p : avgZ (fun x : QAlgorithms.Qubits (m + 1) =>
          |a₀ + ∑ v, a₁ v * spin x v +
            ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)| ^ (k + 2)) =
          avgZ (fun x : QAlgorithms.Qubits m => (|A x + B x| ^ (k + 2) + |A x - B x| ^ (k + 2)) / 2) := by
        rw [avgZ_split]
        simp_rw [hsplit_c]
        simp only [↓reduceIte, Bool.true_eq_false, ← sub_eq_add_neg]
        simp only [avgZ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      have havg_2 : avgZ (fun x : QAlgorithms.Qubits (m + 1) =>
          (a₀ + ∑ v, a₁ v * spin x v +
            ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)) ^ 2) =
          avgZ (fun x : QAlgorithms.Qubits m => A x ^ 2) +
            avgZ (fun x : QAlgorithms.Qubits m => B x ^ 2) := by
        rw [avgZ_split]
        simp_rw [hsplit_c]
        have hsq : ∀ x : QAlgorithms.Qubits m,
            (A x + B x) ^ 2 + (A x + -B x) ^ 2 = 2 * (A x ^ 2 + B x ^ 2) := by
          intro x; ring
        simp only [↓reduceIte, Bool.true_eq_false]
        simp_rw [hsq]
        have hre : avgZ (fun x : QAlgorithms.Qubits m => 2 * (A x ^ 2 + B x ^ 2)) =
            2 * (avgZ (fun x => A x ^ 2) + avgZ (fun x => B x ^ 2)) := by
          simp only [avgZ, Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
        rw [hre]
        ring
      rw [havg_p, havg_2]
      have hstep := bonami_avgZ_step (k + 2) (by omega) A B
      have hk_eq : ((k + 2 : ℕ) : ℝ) - 1 = (k : ℝ) + 1 := by push_cast; ring
      rw [hk_eq] at hstep
      have ihA := ih a₀ (fun v => a₁ v.castSucc) (fun u v => a₂ u.castSucc v.castSucc)
      have ihB := bonami_deg1 m k (a₁ (Fin.last m)) (fun u => a₂ u.castSucc (Fin.last m))
      have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      nlinarith
  have h0 := hmain n a₀ a₁ a₂
  have hk2_pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hrpow := Real.rpow_le_rpow (Real.rpow_nonneg (avgZ_nonneg fun x => by positivity) _)
    h0 (by positivity : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) / 2)
  rw [← Real.rpow_mul (avgZ_nonneg fun x => by positivity)] at hrpow
  have hexp : (2 / ((k + 2 : ℕ) : ℝ)) * (((k + 2 : ℕ) : ℝ) / 2) = 1 := by
    field_simp [hk2_pos.ne']
  rw [hexp, Real.rpow_one] at hrpow
  refine hrpow.trans_eq ?_
  have hk1_nn : (0 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have havg2_nn : 0 ≤ avgZ (fun x => c x ^ 2) := avgZ_nonneg fun x => sq_nonneg _
  rw [Real.mul_rpow (sq_nonneg _) havg2_nn]
  have hpow1 : (((k : ℝ) + 1) ^ 2) ^ (((k + 2 : ℕ) : ℝ) / 2) = ((k : ℝ) + 1) ^ (k + 2) := by
    rw [← Real.rpow_natCast ((k : ℝ) + 1) 2, ← Real.rpow_mul hk1_nn,
      show ((2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) / 2) = ((k + 2 : ℕ) : ℝ) by norm_num; ring,
      Real.rpow_natCast]
  have hpow2 : (avgZ (fun x => c x ^ 2)) ^ (((k + 2 : ℕ) : ℝ) / 2) =
      Real.sqrt (avgZ (fun x => c x ^ 2)) ^ (k + 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ (k + 2), ← Real.rpow_mul havg2_nn]
    congr 1; ring
  rw [hpow1, hpow2]



private lemma spin_sq {n : ℕ} (x : QAlgorithms.Qubits n) (q : Fin n) : spin x q * spin x q = 1 := by
  simp only [spin]
  cases x q <;> norm_num

private lemma avgZ_const {n : ℕ} (c : ℝ) : avgZ (fun _ : QAlgorithms.Qubits n => c) = c := by
  simp only [avgZ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private lemma avgZ_add {n : ℕ} (f g : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => f x + g x) = avgZ f + avgZ g := by
  simp only [avgZ, Finset.sum_add_distrib, mul_add]

private lemma avgZ_smul {n : ℕ} (c : ℝ) (f : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => c * f x) = c * avgZ f := by
  simp only [avgZ, ← Finset.mul_sum]
  ring

private lemma avgZ_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, avgZ (f j) := by
  simp only [avgZ, Finset.sum_comm (s := Finset.univ) (t := s), Finset.mul_sum]

private lemma prod_spin_symmDiff {n : ℕ} (A B : Finset (Fin n)) (x : QAlgorithms.Qubits n) :
    (∏ q ∈ A, spin x q) * (∏ q ∈ B, spin x q) = ∏ q ∈ symmDiff A B, spin x q := by
  have hA : A = (A \ B) ∪ (A ∩ B) := by ext q; simp [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hB : B = (B \ A) ∪ (A ∩ B) := by ext q; simp [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hdA : Disjoint (A \ B) (A ∩ B) := Finset.disjoint_left.mpr fun q h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
  have hdB : Disjoint (B \ A) (A ∩ B) := Finset.disjoint_left.mpr fun q h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1
  have hAB : symmDiff A B = (A \ B) ∪ (B \ A) := by
    ext q; simp [Finset.mem_symmDiff, Finset.mem_sdiff]
  have hdAB : Disjoint (A \ B) (B \ A) := Finset.disjoint_left.mpr fun q h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
  have hAB_prod : (∏ q ∈ A, spin x q) * (∏ q ∈ B, spin x q) =
      (∏ q ∈ (A \ B) ∪ (A ∩ B), spin x q) * (∏ q ∈ (B \ A) ∪ (A ∩ B), spin x q) := by
    rw [← hA, ← hB]
  rw [hAB_prod, Finset.prod_union hdA, Finset.prod_union hdB]
  have hsq : (∏ q ∈ A ∩ B, spin x q) * (∏ q ∈ A ∩ B, spin x q) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun q _ => spin_sq x q
  calc ((∏ q ∈ A \ B, spin x q) * ∏ q ∈ A ∩ B, spin x q) *
        ((∏ q ∈ B \ A, spin x q) * ∏ q ∈ A ∩ B, spin x q)
      = (∏ q ∈ A \ B, spin x q) * (∏ q ∈ B \ A, spin x q) *
          ((∏ q ∈ A ∩ B, spin x q) * ∏ q ∈ A ∩ B, spin x q) := by ring
    _ = (∏ q ∈ A \ B, spin x q) * (∏ q ∈ B \ A, spin x q) := by rw [hsq, mul_one]
    _ = ∏ q ∈ symmDiff A B, spin x q := by rw [hAB, Finset.prod_union hdAB]

private lemma avgZ_prod_spin {n : ℕ} (T : Finset (Fin n)) :
    avgZ (fun x => ∏ q ∈ T, spin x q) = if T = ∅ then 1 else 0 := by
  by_cases hT : T = ∅
  · subst hT
    simp only [Finset.prod_empty, ↓reduceIte]
    exact avgZ_const 1
  · simp only [if_neg hT]
    obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    let flip : QAlgorithms.Qubits n → QAlgorithms.Qubits n := fun x q =>
      if q = q₀ then !(x q₀) else x q
    have hflip_inv : Function.Involutive flip := by
      intro x; ext q
      by_cases h : q = q₀ <;> simp [flip, h]
    have hflip_neg : ∀ x : QAlgorithms.Qubits n,
        (∏ q ∈ T, spin (flip x) q) = -(∏ q ∈ T, spin x q) := by
      intro x
      rw [← Finset.mul_prod_erase T _ hq₀, ← Finset.mul_prod_erase T _ hq₀]
      have h0 : spin (flip x) q₀ = -spin x q₀ := by
        simp only [spin, flip, ↓reduceIte]
        cases x q₀ <;> norm_num
      have hrest : ∏ q ∈ T.erase q₀, spin (flip x) q = ∏ q ∈ T.erase q₀, spin x q := by
        refine Finset.prod_congr rfl fun q hq => ?_
        have hne : q ≠ q₀ := (Finset.mem_erase.mp hq).1
        simp [spin, flip, hne]
      rw [h0, hrest, neg_mul]
    have hsum_eq : ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin (flip x) q) =
        ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin x q) :=
      Fintype.sum_equiv hflip_inv.toPerm _ _ fun _ => rfl
    have hsum_neg : ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin (flip x) q) =
        -∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin x q) := by
      simp_rw [hflip_neg, Finset.sum_neg_distrib]
    have hsum0 : ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin x q) = 0 := by linarith
    simp [avgZ, hsum0]

private lemma avgZ_prod_spin_mul {n : ℕ} (A B : Finset (Fin n)) :
    avgZ (fun x => (∏ q ∈ A, spin x q) * (∏ q ∈ B, spin x q)) = if A = B then 1 else 0 := by
  simp_rw [prod_spin_symmDiff, avgZ_prod_spin]
  by_cases h : A = B
  · subst h; simp
  · have hs : symmDiff A B ≠ ∅ := by
      intro heq
      exact h (Finset.symmDiff_eq_empty.mp heq)
    simp [h, hs]

private def tripleSet {n : ℕ} (t : Fin n × Fin n × Fin n) : Finset (Fin n) :=
  {t.1, t.2.1, t.2.2}

private lemma mem_tripleSet_iff {n : ℕ} (t : Fin n × Fin n × Fin n) (v : Fin n) :
    v ∈ tripleSet t ↔ onTriple t v := by
  simp [tripleSet, onTriple, Finset.mem_insert, Finset.mem_singleton]

private lemma tripleSet_inj {n : ℕ} (t₁ t₂ : Fin n × Fin n × Fin n)
    (ht₁ : t₁.1 < t₁.2.1 ∧ t₁.2.1 < t₁.2.2)
    (ht₂ : t₂.1 < t₂.2.1 ∧ t₂.2.1 < t₂.2.2)
    (heq : tripleSet t₁ = tripleSet t₂) : t₁ = t₂ := by
  have h12 : ∀ v, v ∈ tripleSet t₁ ↔ v ∈ tripleSet t₂ := fun v => by rw [heq]
  have ha1 : t₁.1 ∈ tripleSet t₂ := (h12 t₁.1).mp (by simp [tripleSet])
  have hb1 : t₂.1 ∈ tripleSet t₁ := (h12 t₂.1).mpr (by simp [tripleSet])
  have ha1_le : t₂.1 ≤ t₁.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at ha1
    rcases ha1 with h | h | h <;> omega
  have hb1_le : t₁.1 ≤ t₂.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hb1
    rcases hb1 with h | h | h <;> omega
  have hfst : t₁.1 = t₂.1 := le_antisymm hb1_le ha1_le
  have ha2 : t₁.2.1 ∈ tripleSet t₂ := (h12 t₁.2.1).mp (by simp [tripleSet])
  have hb2 : t₂.2.1 ∈ tripleSet t₁ := (h12 t₂.2.1).mpr (by simp [tripleSet])
  have ha2_le : t₂.2.1 ≤ t₁.2.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at ha2
    rcases ha2 with h | h | h <;> omega
  have hb2_le : t₁.2.1 ≤ t₂.2.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hb2
    rcases hb2 with h | h | h <;> omega
  have hsnd : t₁.2.1 = t₂.2.1 := le_antisymm hb2_le ha2_le
  have ha3 : t₁.2.2 ∈ tripleSet t₂ := (h12 t₁.2.2).mp (by simp [tripleSet])
  have hb3 : t₂.2.2 ∈ tripleSet t₁ := (h12 t₂.2.2).mpr (by simp [tripleSet])
  have ha3_eq : t₁.2.2 = t₂.2.2 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at ha3 hb3
    rcases ha3 with h | h | h <;> rcases hb3 with g | g | g <;> omega
  ext <;> simp [hfst, hsnd, ha3_eq]

private lemma prod_tripleSet_mul_spin {n : ℕ} (t : Fin n × Fin n × Fin n)
    (ht : t.1 < t.2.1 ∧ t.2.1 < t.2.2) (v : Fin n) (hv : onTriple t v) (x : QAlgorithms.Qubits n) :
    spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x v =
      ∏ q ∈ (tripleSet t).erase v, spin x q := by
  have h12 : t.1 ≠ t.2.1 := ne_of_lt ht.1
  have h13 : t.1 ≠ t.2.2 := ne_of_lt (ht.1.trans ht.2)
  have h23 : t.2.1 ≠ t.2.2 := ne_of_lt ht.2
  have hprod : ∏ q ∈ tripleSet t, spin x q = spin x t.1 * spin x t.2.1 * spin x t.2.2 := by
    rw [tripleSet, Finset.prod_insert (by simp [h12, h13]), Finset.prod_insert (by simp [h23]),
      Finset.prod_singleton]
    ring
  have hv_mem : v ∈ tripleSet t := (mem_tripleSet_iff t v).mpr hv
  rw [← hprod, ← Finset.mul_prod_erase (tripleSet t) _ hv_mem]
  calc (spin x v * ∏ q ∈ (tripleSet t).erase v, spin x q) * spin x v
      = (spin x v * spin x v) * ∏ q ∈ (tripleSet t).erase v, spin x q := by ring
    _ = ∏ q ∈ (tripleSet t).erase v, spin x q := by rw [spin_sq, one_mul]

private lemma roleBit_onTriple {n : ℕ} (t : Fin n × Fin n × Fin n) (r : Fin 3) :
    onTriple t (roleBit t r) := by
  fin_cases r <;> simp [roleBit, onTriple]

private lemma eq_31_helper {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (i : Fin m) (r : Fin 3) :
    avgZ (fun x => cPoly tri rhs i r x ^ 2) = (termCount tri i r : ℝ) ∧
      termCount tri i r ≤ D := by
  let v := roleBit (tri i) r
  let S : Finset (Fin m) := Finset.univ.filter (fun j => sharesOnly tri i j r)
  have hcard : S.card = termCount tri i r := by
    simp only [termCount, S]
  have hcPoly : ∀ x, cPoly tri rhs i r x =
      ∑ j ∈ S, sgn rhs j * ∏ q ∈ (tripleSet (tri j)).erase v, spin x q := by
    intro x
    simp only [cPoly, Finset.sum_filter, S]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [prod_tripleSet_mul_spin (tri j) (htri.1 j) v hj.2.1 x]
    · rfl
  have hpart1 : avgZ (fun x => cPoly tri rhs i r x ^ 2) = (termCount tri i r : ℝ) := by
    have hsq : ∀ x, cPoly tri rhs i r x ^ 2 =
        ∑ j₁ ∈ S, ∑ j₂ ∈ S,
          (sgn rhs j₁ * sgn rhs j₂) *
            ((∏ q ∈ (tripleSet (tri j₁)).erase v, spin x q) *
              (∏ q ∈ (tripleSet (tri j₂)).erase v, spin x q)) := by
      intro x
      rw [hcPoly x, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₂ _ => ?_
      ring
    simp_rw [hsq, avgZ_sum, avgZ_smul, avgZ_prod_spin_mul]
    rw [← hcard]
    have hdiag : ∀ j₁ ∈ S,
        (∑ j₂ ∈ S, (sgn rhs j₁ * sgn rhs j₂) *
          if (tripleSet (tri j₁)).erase v = (tripleSet (tri j₂)).erase v then (1 : ℝ) else 0) = 1 := by
      intro j₁ hj₁
      have hv₁ : v ∈ tripleSet (tri j₁) :=
        (mem_tripleSet_iff (tri j₁) v).mpr (Finset.mem_filter.mp hj₁).2.2.1
      have huniq : ∀ j₂ ∈ S,
          ((tripleSet (tri j₁)).erase v = (tripleSet (tri j₂)).erase v) ↔ j₁ = j₂ := by
        intro j₂ hj₂
        constructor
        · intro heq
          have hv₂ : v ∈ tripleSet (tri j₂) :=
            (mem_tripleSet_iff (tri j₂) v).mpr (Finset.mem_filter.mp hj₂).2.2.1
          have hset : tripleSet (tri j₁) = tripleSet (tri j₂) := by
            rw [← Finset.insert_erase hv₁, ← Finset.insert_erase hv₂, heq]
          exact htri.2 (tripleSet_inj (tri j₁) (tri j₂) (htri.1 j₁) (htri.1 j₂) hset)
        · rintro rfl; rfl
      have hterm : ∀ j₂ ∈ S,
          (sgn rhs j₁ * sgn rhs j₂) *
            (if (tripleSet (tri j₁)).erase v = (tripleSet (tri j₂)).erase v then (1 : ℝ) else 0) =
          if j₂ = j₁ then 1 else 0 := by
        intro j₂ hj₂
        simp_rw [huniq j₂ hj₂]
        by_cases heq : j₂ = j₁
        · subst heq
          simp only [↓reduceIte, mul_one]
          simp only [sgn]
          cases rhs j₂ <;> norm_num
        · have heq' : j₁ ≠ j₂ := Ne.symm heq
          simp [heq, heq']
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hj₁]
    rw [Finset.sum_congr rfl hdiag, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine ⟨hpart1, ?_⟩
  let A : Finset (Fin m) := Finset.univ.filter (fun j => onTriple (tri j) v)
  have hiA : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ i, roleBit_onTriple (tri i) r⟩
  have hsub : S ⊆ A.erase i := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_erase.mpr ⟨hj'.1, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj'.2.1⟩⟩
  have hA_le : A.card ≤ D + 1 := by
    simpa [A] using hocc v
  have hS_le : S.card ≤ A.card - 1 := by
    calc S.card ≤ (A.erase i).card := Finset.card_le_card hsub
      _ = A.card - 1 := Finset.card_erase_of_mem hiA
  rw [← hcard]
  omega

private lemma avgZ_mono {n : ℕ} {f g : QAlgorithms.Qubits n → ℝ} (h : ∀ x, f x ≤ g x) :
    avgZ f ≤ avgZ g := by
  simp only [avgZ]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

private lemma avgZ_cPoly_eq_zero {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : IsTripleFamily tri) (i : Fin m) (r : Fin 3) :
    avgZ (cPoly tri rhs i r) = 0 := by
  let v := roleBit (tri i) r
  let S : Finset (Fin m) := Finset.univ.filter (fun j => sharesOnly tri i j r)
  have hcPoly : ∀ x, cPoly tri rhs i r x =
      ∑ j ∈ S, sgn rhs j * ∏ q ∈ (tripleSet (tri j)).erase v, spin x q := by
    intro x
    simp only [cPoly, Finset.sum_filter, S]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [prod_tripleSet_mul_spin (tri j) (htri.1 j) v hj.2.1 x]
    · rfl
  have hfun : cPoly tri rhs i r = fun x =>
      ∑ j ∈ S, sgn rhs j * ∏ q ∈ (tripleSet (tri j)).erase v, spin x q := funext hcPoly
  rw [hfun, avgZ_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [avgZ_smul, avgZ_prod_spin]
  have hne : (tripleSet (tri j)).erase v ≠ ∅ := by
    have h12 : (tri j).1 ≠ (tri j).2.1 := ne_of_lt (htri.1 j).1
    have h13 : (tri j).1 ≠ (tri j).2.2 := ne_of_lt ((htri.1 j).1.trans (htri.1 j).2)
    have h23 : (tri j).2.1 ≠ (tri j).2.2 := ne_of_lt (htri.1 j).2
    have hcard3 : (tripleSet (tri j)).card = 3 := by
      rw [tripleSet, Finset.card_insert_of_notMem (by simp [h12, h13]),
        Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
    have hv : v ∈ tripleSet (tri j) :=
      (mem_tripleSet_iff (tri j) v).mpr (Finset.mem_filter.mp hj).2.2.1
    have hcard2 : ((tripleSet (tri j)).erase v).card = 2 := by
      rw [Finset.card_erase_of_mem hv, hcard3]
    intro h0
    rw [h0, Finset.card_empty] at hcard2
    omega
  simp [hne]

private lemma eq_32_helper {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (i : Fin m)
    (ε : Fin 3 → ℝ) (hε : ∀ r, ε r = 1 ∨ ε r = -1) :
    avgZ (fun x => (sgn rhs i + ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
      ε 2 * cPoly tri rhs i 2 x) ^ 2) ≤ 1 + 9 * (D : ℝ) := by
  have hpt : ∀ x,
      (sgn rhs i + ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
        ε 2 * cPoly tri rhs i 2 x) ^ 2 ≤
      sgn rhs i ^ 2 +
        2 * sgn rhs i * (ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
          ε 2 * cPoly tri rhs i 2 x) +
        3 * ((ε 0 * cPoly tri rhs i 0 x) ^ 2 + (ε 1 * cPoly tri rhs i 1 x) ^ 2 +
          (ε 2 * cPoly tri rhs i 2 x) ^ 2) := by
    intro x
    nlinarith [sq_nonneg (ε 0 * cPoly tri rhs i 0 x - ε 1 * cPoly tri rhs i 1 x),
      sq_nonneg (ε 1 * cPoly tri rhs i 1 x - ε 2 * cPoly tri rhs i 2 x),
      sq_nonneg (ε 2 * cPoly tri rhs i 2 x - ε 0 * cPoly tri rhs i 0 x)]
  refine (avgZ_mono hpt).trans ?_
  simp_rw [avgZ_add, avgZ_smul, avgZ_const]
  have hsgn_sq : sgn rhs i ^ 2 = 1 := by
    simp only [sgn]
    cases rhs i <;> norm_num
  have hε_sq : ∀ r : Fin 3, ε r ^ 2 = 1 := by
    intro r
    rcases hε r with h | h <;> rw [h] <;> norm_num
  have h0 : avgZ (cPoly tri rhs i 0) = 0 := avgZ_cPoly_eq_zero tri rhs htri i 0
  have h1 : avgZ (cPoly tri rhs i 1) = 0 := avgZ_cPoly_eq_zero tri rhs htri i 1
  have h2 : avgZ (cPoly tri rhs i 2) = 0 := avgZ_cPoly_eq_zero tri rhs htri i 2
  have hsq_eq : ∀ r : Fin 3,
      avgZ (fun x => (ε r * cPoly tri rhs i r x) ^ 2) = (termCount tri i r : ℝ) := by
    intro r
    have heq : (fun x => (ε r * cPoly tri rhs i r x) ^ 2) =
        fun x => ε r ^ 2 * (cPoly tri rhs i r x ^ 2) := by
      funext x; ring
    rw [heq, avgZ_smul, hε_sq r, one_mul]
    exact (eq_31_helper tri rhs D htri hocc i r).1
  have htc0 : (termCount tri i 0 : ℝ) ≤ D :=
    Nat.cast_le.mpr (eq_31_helper tri rhs D htri hocc i 0).2
  have htc1 : (termCount tri i 1 : ℝ) ≤ D :=
    Nat.cast_le.mpr (eq_31_helper tri rhs D htri hocc i 1).2
  have htc2 : (termCount tri i 2 : ℝ) ≤ D :=
    Nat.cast_le.mpr (eq_31_helper tri rhs D htri hocc i 2).2
  have hlin : avgZ (fun x => ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
      ε 2 * cPoly tri rhs i 2 x) = 0 := by
    rw [avgZ_add, avgZ_add, avgZ_smul, avgZ_smul, avgZ_smul, h0, h1, h2]
    ring
  have hsq_sum : avgZ (fun x => (ε 0 * cPoly tri rhs i 0 x) ^ 2 +
      (ε 1 * cPoly tri rhs i 1 x) ^ 2 + (ε 2 * cPoly tri rhs i 2 x) ^ 2) =
      (termCount tri i 0 : ℝ) + (termCount tri i 1 : ℝ) + (termCount tri i 2 : ℝ) := by
    rw [avgZ_add, avgZ_add, hsq_eq 0, hsq_eq 1, hsq_eq 2]
  rw [hsgn_sq, hlin, hsq_sum]
  linarith

private lemma pairOfTriple_eq {n : ℕ} (t : Fin n × Fin n × Fin n) (ht : t.1 < t.2.1 ∧ t.2.1 < t.2.2)
    (v : Fin n) (hv : onTriple t v) :
    ∃ p q : Fin n, p < q ∧
      ∀ x : QAlgorithms.Qubits n,
        spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x v = spin x p * spin x q := by
  rcases hv with rfl | rfl | rfl
  · refine ⟨t.2.1, t.2.2, ht.2, fun x => ?_⟩
    calc spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x t.1
        = (spin x t.1 * spin x t.1) * (spin x t.2.1 * spin x t.2.2) := by ring
      _ = spin x t.2.1 * spin x t.2.2 := by rw [spin_sq, one_mul]
  · refine ⟨t.1, t.2.2, ht.1.trans ht.2, fun x => ?_⟩
    calc spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x t.2.1
        = (spin x t.2.1 * spin x t.2.1) * (spin x t.1 * spin x t.2.2) := by ring
      _ = spin x t.1 * spin x t.2.2 := by rw [spin_sq, one_mul]
  · refine ⟨t.1, t.2.1, ht.1, fun x => ?_⟩
    calc spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x t.2.2
        = (spin x t.2.2 * spin x t.2.2) * (spin x t.1 * spin x t.2.1) := by ring
      _ = spin x t.1 * spin x t.2.1 := by rw [spin_sq, one_mul]

private lemma u_avgZ_pow_le {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (D : ℕ) (htri : IsTripleFamily tri)
    (hocc : BoundedOccurrence tri D) (hD : 1 ≤ D) (i : Fin m) (k : ℕ)
    (ε : Fin 3 → ℝ) (hε : ∀ r, ε r = 1 ∨ ε r = -1) :
    avgZ (fun x => |sgn rhs i + ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
      ε 2 * cPoly tri rhs i 2 x| ^ (k + 2)) ≤
      ((k : ℝ) + 1) ^ (k + 2) * Real.sqrt (10 * (D : ℝ)) ^ (k + 2) := by
  have hpair : ∀ (r : Fin 3) (j : Fin m),
      ∃ p q : Fin n, (sharesOnly tri i j r → p < q) ∧
        ∀ x : QAlgorithms.Qubits n,
          (if sharesOnly tri i j r then
            sgn rhs j * (spin x (tri j).1 * spin x (tri j).2.1 * spin x (tri j).2.2 *
              spin x (roleBit (tri i) r))
          else 0) =
          if sharesOnly tri i j r then sgn rhs j * spin x p * spin x q else 0 := by
    intro r j
    by_cases hj : sharesOnly tri i j r
    · obtain ⟨p, q, hpq, hspin⟩ := pairOfTriple_eq (tri j) (htri.1 j) (roleBit (tri i) r) hj.2.1
      refine ⟨p, q, fun _ => hpq, fun x => ?_⟩
      simp only [hj, ↓reduceIte, hspin x]
      ring
    · refine ⟨(tri j).1, (tri j).1, fun h => absurd h hj, fun x => ?_⟩
      simp [hj]
  choose p q hpq hterm using hpair
  let a₂ : Fin n → Fin n → ℝ := fun u v =>
    ∑ r : Fin 3, ε r * ∑ j : Fin m,
      if sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then sgn rhs j else 0
  let u_fn : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i + ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
      ε 2 * cPoly tri rhs i 2 x
  have hu_eq : ∀ x, u_fn x =
      sgn rhs i + ∑ v : Fin n, (0 : ℝ) * spin x v +
        ∑ u : Fin n, ∑ v : Fin n, (if u < v then a₂ u v * spin x u * spin x v else 0) := by
    intro x
    have hsum_uv : (∑ u : Fin n, ∑ v : Fin n,
        (if u < v then a₂ u v * spin x u * spin x v else 0)) =
        ∑ r : Fin 3, ε r * cPoly tri rhs i r x := by
      have hre : ∀ u v : Fin n,
          (if u < v then a₂ u v * spin x u * spin x v else 0) =
          ∑ r : Fin 3, ε r * ∑ j : Fin m,
            if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
              sgn rhs j * spin x u * spin x v
            else 0 := by
        intro u v
        by_cases huv : u < v
        · simp only [huv, ↓reduceIte, a₂, Finset.sum_mul, true_and]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [mul_assoc, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> ring
        · simp [huv]
      simp_rw [hre]
      calc (∑ u : Fin n, ∑ v : Fin n, ∑ r : Fin 3, ε r * ∑ j : Fin m,
            if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
              sgn rhs j * spin x u * spin x v
            else 0)
          = ∑ u : Fin n, ∑ r : Fin 3, ∑ v : Fin n, ε r * ∑ j : Fin m,
              if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                sgn rhs j * spin x u * spin x v
              else 0 := Finset.sum_congr rfl fun u _ => Finset.sum_comm
        _ = ∑ r : Fin 3, ∑ u : Fin n, ∑ v : Fin n, ε r * ∑ j : Fin m,
              if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                sgn rhs j * spin x u * spin x v
              else 0 := Finset.sum_comm
        _ = ∑ r : Fin 3, ε r * cPoly tri rhs i r x := by
            refine Finset.sum_congr rfl fun r _ => ?_
            have hpull : (∑ u : Fin n, ∑ v : Fin n, ε r * ∑ j : Fin m,
                if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                  sgn rhs j * spin x u * spin x v
                else 0) =
                ε r * ∑ u : Fin n, ∑ v : Fin n, ∑ j : Fin m,
                  if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                    sgn rhs j * spin x u * spin x v
                  else 0 := by
              simp_rw [← Finset.mul_sum]
            rw [hpull]
            congr 1
            have hswap_vj : ∀ u : Fin n,
                (∑ v : Fin n, ∑ j : Fin m,
                  if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                    sgn rhs j * spin x u * spin x v
                  else 0) =
                ∑ j : Fin m, ∑ v : Fin n,
                  if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                    sgn rhs j * spin x u * spin x v
                  else 0 := fun u => Finset.sum_comm
            simp_rw [hswap_vj]
            rw [Finset.sum_comm]
            simp only [cPoly]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hterm r j x]
            by_cases hj : sharesOnly tri i j r
            · have hpqj : p r j < q r j := hpq r j hj
              rw [if_pos hj]
              rw [Finset.sum_eq_single (p r j)]
              · rw [Finset.sum_eq_single (q r j)]
                · simp [hpqj, hj]
                · intro v _ hv; simp [Ne.symm hv]
                · intro h; exact absurd (Finset.mem_univ _) h
              · intro u _ hu
                refine Finset.sum_eq_zero fun v _ => ?_
                simp [Ne.symm hu]
              · intro h; exact absurd (Finset.mem_univ _) h
            · simp [hj]
    rw [hsum_uv]
    simp only [Fin.sum_univ_three, zero_mul, Finset.sum_const_zero, add_zero]
    dsimp only [u_fn]
    ring
  have hbon := eq_29_helper n k (sgn rhs i) (fun _ => 0) a₂
  dsimp only at hbon
  have hbon' : avgZ (fun x => |u_fn x| ^ (k + 2)) ≤
      ((k : ℝ) + 1) ^ (k + 2) * Real.sqrt (avgZ (fun x => u_fn x ^ 2)) ^ (k + 2) := by
    simpa only [← hu_eq] using hbon
  have h32 := eq_32_helper tri rhs D htri hocc i ε hε
  have hle10 : avgZ (fun x => u_fn x ^ 2) ≤ 10 * (D : ℝ) := by
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  have hsqrt_le : Real.sqrt (avgZ (fun x => u_fn x ^ 2)) ≤ Real.sqrt (10 * (D : ℝ)) :=
    Real.sqrt_le_sqrt hle10
  have hpow_le : Real.sqrt (avgZ (fun x => u_fn x ^ 2)) ^ (k + 2) ≤
      Real.sqrt (10 * (D : ℝ)) ^ (k + 2) :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le (k + 2)
  exact hbon'.trans (mul_le_mul_of_nonneg_left hpow_le (by positivity))

private lemma exp_one_lt : Real.exp 1 < 272 / 100 := by
  have hb := Real.exp_bound (x := (1 : ℝ)) (n := 4) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    Nat.factorial, Nat.cast_one, div_one, abs_one, one_pow, one_mul] at hb
  norm_num at hb
  linarith [(abs_le.mp hb).2]

private lemma coeff_bound_eq_34 (k : ℕ) :
    ((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2) ≤ 9 ^ (k + 2) := by
  have hfac_ge : ((k : ℝ) + 1) ^ (k + 1) / ((k + 1).factorial : ℝ) ≤ Real.exp ((k : ℝ) + 1) := by
    have hs := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity) (k + 2)
    have hmem : k + 1 ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
    have hsingle := Finset.single_le_sum
      (f := fun m : ℕ => ((k : ℝ) + 1) ^ m / (m.factorial : ℝ))
      (fun m _ => div_nonneg (pow_nonneg (by positivity) m) (Nat.cast_nonneg m.factorial)) hmem
    exact hsingle.trans hs
  have hratio : ((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ Real.exp 1 ^ (k + 2) := by
    have h1 : ((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) =
        (((k : ℝ) + 1) / ((k : ℝ) + 2)) * (((k : ℝ) + 1) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
      have hfac : ((k + 2).factorial : ℝ) = ((k : ℝ) + 2) * ((k + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfac, pow_succ]
      field_simp
    have h2 : (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have hexp_pow : Real.exp ((k : ℝ) + 1) = Real.exp 1 ^ (k + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hexp_le : Real.exp 1 ^ (k + 1) ≤ Real.exp 1 ^ (k + 2) := by
      have he1 : 1 ≤ Real.exp 1 := by simpa using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
      exact pow_le_pow_right₀ he1 (by omega)
    rw [h1]
    calc (((k : ℝ) + 1) / ((k : ℝ) + 2)) * (((k : ℝ) + 1) ^ (k + 1) / ((k + 1).factorial : ℝ))
        ≤ 1 * Real.exp ((k : ℝ) + 1) :=
          mul_le_mul h2 hfac_ge (by positivity) (by positivity)
      _ = Real.exp 1 ^ (k + 1) := by rw [one_mul, hexp_pow]
      _ ≤ Real.exp 1 ^ (k + 2) := hexp_le
  have hsqrt10 : Real.sqrt 10 < 317 / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hprod : Real.exp 1 * Real.sqrt 10 ≤ 9 := by
    have h1 := exp_one_lt.le
    have h2 := hsqrt10.le
    nlinarith [Real.exp_pos 1, Real.sqrt_nonneg 10]
  calc ((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)
      ≤ Real.exp 1 ^ (k + 2) * Real.sqrt 10 ^ (k + 2) :=
        mul_le_mul_of_nonneg_right hratio (pow_nonneg (Real.sqrt_nonneg 10) _)
    _ = (Real.exp 1 * Real.sqrt 10) ^ (k + 2) := (mul_pow _ _ _).symm
    _ ≤ 9 ^ (k + 2) := pow_le_pow_left₀ (by positivity) hprod _

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (hD : 1 ≤ D)
    (k : ℕ) (hk : Odd k) (i : Fin m) (γ : ℝ) :
    |Rk tri rhs i k γ| ≤ (9 * Real.sqrt D * |γ|) ^ (k + 2) := by
  have h28 := eq_28_helper tri rhs i k hk γ
  have hb1 := u_avgZ_pow_le tri rhs D htri hocc hD i k (fun | 0 => 1 | 1 => 1 | 2 => 1)
    (fun r => by fin_cases r <;> simp)
  have hb2 := u_avgZ_pow_le tri rhs D htri hocc hD i k (fun | 0 => 1 | 1 => -1 | 2 => -1)
    (fun r => by fin_cases r <;> simp)
  have hb3 := u_avgZ_pow_le tri rhs D htri hocc hD i k (fun | 0 => -1 | 1 => 1 | 2 => -1)
    (fun r => by fin_cases r <;> simp)
  have hb4 := u_avgZ_pow_le tri rhs D htri hocc hD i k (fun | 0 => -1 | 1 => -1 | 2 => 1)
    (fun r => by fin_cases r <;> simp)
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at hb1 hb2 hb3 hb4
  have havg_sum : avgZ (fun x =>
      let d := sgn rhs i
      let c₁ := cPoly tri rhs i 0 x
      let c₂ := cPoly tri rhs i 1 x
      let c₃ := cPoly tri rhs i 2 x
      |d + c₁ + c₂ + c₃| ^ (k + 2) + |d + c₁ - c₂ - c₃| ^ (k + 2) +
        |d - c₁ + c₂ - c₃| ^ (k + 2) + |d - c₁ - c₂ + c₃| ^ (k + 2)) ≤
      4 * (((k : ℝ) + 1) ^ (k + 2) * Real.sqrt (10 * (D : ℝ)) ^ (k + 2)) := by
    simp only [avgZ_add]
    linarith
  have hstep1 : |Rk tri rhs i k γ| ≤
      (1 / 2 : ℝ) * |γ| ^ (k + 2) *
        (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)) *
        Real.sqrt D ^ (k + 2) := by
    have hmul := mul_le_mul_of_nonneg_left havg_sum
      (by positivity : 0 ≤ (1 / 8 : ℝ) * |γ| ^ (k + 2) / ((k + 2).factorial : ℝ))
    have hsqrt10D : Real.sqrt (10 * (D : ℝ)) = Real.sqrt 10 * Real.sqrt D :=
      Real.sqrt_mul (by norm_num) (D : ℝ)
    rw [hsqrt10D, mul_pow] at hmul
    refine h28.trans (hmul.trans_eq ?_)
    ring
  have hstep2 : (1 / 2 : ℝ) * |γ| ^ (k + 2) *
      (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)) *
      Real.sqrt D ^ (k + 2) ≤
      (9 * Real.sqrt D * |γ|) ^ (k + 2) := by
    have hcb := coeff_bound_eq_34 k
    have hmul1 : |γ| ^ (k + 2) *
        (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)) ≤
        |γ| ^ (k + 2) * 9 ^ (k + 2) :=
      mul_le_mul_of_nonneg_left hcb (by positivity)
    have hmul2 : (1 / 2 : ℝ) * (|γ| ^ (k + 2) *
        (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2))) *
        Real.sqrt D ^ (k + 2) ≤
        9 ^ (k + 2) * |γ| ^ (k + 2) * Real.sqrt D ^ (k + 2) := by
      have ha : (1 / 2 : ℝ) * (|γ| ^ (k + 2) *
          (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2))) ≤
          1 * (|γ| ^ (k + 2) * 9 ^ (k + 2)) := by
        refine mul_le_mul (by norm_num) hmul1 (by positivity) (by norm_num)
      have hb := mul_le_mul_of_nonneg_right ha (pow_nonneg (Real.sqrt_nonneg D) (k + 2))
      linarith
    have hlin_eq : (1 / 2 : ℝ) * |γ| ^ (k + 2) *
        (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)) *
        Real.sqrt D ^ (k + 2) =
        (1 / 2 : ℝ) * (|γ| ^ (k + 2) *
          (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2))) *
        Real.sqrt D ^ (k + 2) := by ring
    rw [hlin_eq]
    exact hmul2.trans_eq (by rw [mul_pow, mul_pow]; ring)
  exact hstep1.trans hstep2
end AuxEq34

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (hD : 1 ≤ D)
    (k : ℕ) (hk : Odd k) (γ : ℝ) :
    |(m : ℝ) / 2 * γ + PkSum tri rhs k γ| - (m : ℝ) * (9 * Real.sqrt D * |γ|) ^ (k + 2) ≤
      |expSat tri rhs (-γ) (Real.pi / 4) - (m : ℝ) / 2| := by
  have h6 : expSat tri rhs (-γ) (Real.pi / 4) =
      (m : ℝ) / 2 + ∑ i, (1 / 2) * sgn rhs i * corr tri rhs i (-γ) (Real.pi / 4) :=
    AuxEq6.solution tri rhs (-γ) (Real.pi / 4)
  have hexp : expSat tri rhs (-γ) (Real.pi / 4) - (m : ℝ) / 2 =
      ∑ i, clauseSin tri rhs i γ := by
    rw [h6, add_sub_cancel_left]
    exact Finset.sum_congr rfl fun i _ => half_sgn_corr_eq_clauseSin tri rhs htri i γ
  have hsplit : ∑ i : Fin m, clauseSin tri rhs i γ =
      ((m : ℝ) / 2 * γ + PkSum tri rhs k γ) + ∑ i : Fin m, Rk tri rhs i k γ := by
    have hterm : ∀ i : Fin m, clauseSin tri rhs i γ =
        (1 / 2) * γ + Pk tri rhs i k γ + Rk tri rhs i k γ := by
      intro i
      unfold Rk
      have hsq : sgn rhs i ^ 2 = 1 := by unfold sgn; cases rhs i <;> norm_num
      rw [hsq, mul_one]
      ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    unfold PkSum
    ring
  rw [hexp, hsplit]
  have htri_ineq : |(m : ℝ) / 2 * γ + PkSum tri rhs k γ| - |∑ i : Fin m, Rk tri rhs i k γ| ≤
      |((m : ℝ) / 2 * γ + PkSum tri rhs k γ) + ∑ i : Fin m, Rk tri rhs i k γ| := by
    have h := abs_sub_abs_le_abs_sub ((m : ℝ) / 2 * γ + PkSum tri rhs k γ) (-∑ i : Fin m, Rk tri rhs i k γ)
    simpa [abs_neg, sub_neg_eq_add] using h
  have hR_bound : |∑ i : Fin m, Rk tri rhs i k γ| ≤ (m : ℝ) * (9 * Real.sqrt D * |γ|) ^ (k + 2) := by
    calc |∑ i : Fin m, Rk tri rhs i k γ|
        ≤ ∑ i : Fin m, |Rk tri rhs i k γ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, (9 * Real.sqrt D * |γ|) ^ (k + 2) :=
          Finset.sum_le_sum fun i _ => AuxEq34.solution tri rhs D htri hocc hD k hk i γ
      _ = (m : ℝ) * (9 * Real.sqrt D * |γ|) ^ (k + 2) := by
          simp [Finset.card_univ, Fintype.card_fin]
  linarith
