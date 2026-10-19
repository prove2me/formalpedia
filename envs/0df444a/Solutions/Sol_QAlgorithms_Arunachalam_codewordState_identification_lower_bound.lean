-- Prove2me | solution 1 for QAlgorithms.Arunachalam.codewordState_identification_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:05:29.519372+00:00
-- url     : https://prove2.me/submissions/97db0e1e-3bc7-4f6f-be57-b539b0597d85

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
import Mathlib.Analysis.Matrix.Order
import Theorems.Thm_QAlgorithms_pgmSuccess_uniform_real_gram
import Theorems.Thm_QAlgorithms_Arunachalam_sqrtA_diag
import Theorems.Thm_QAlgorithms_Arunachalam_fourier_weightPow_bound
import Mathlib.Analysis.Complex.Exponential
set_option autoImplicit false
open scoped BigOperators
open QAlgorithms QAlgorithms.Learning

open scoped ComplexConjugate ComplexOrder MatrixOrder
open Matrix

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) : act (A * B) x = act A (act B x) := by
  ext i
  exact congrFun (Matrix.mulVec_mulVec x A B).symm i

private lemma inner_act {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (x y : EuclideanSpace ℂ ι) :
    inner ℂ (act A x) y = inner ℂ x (act Aᴴ y) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, act]
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm]

private lemma effect_inner {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    effectProb A (pureDensity x) = (inner ℂ x (act A x)).re := by
  unfold effectProb
  congr 1
  simp only [pureDensity, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, EuclideanSpace.inner_eq_star_dotProduct, act,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change A i j * (x j * star (x i)) = (A i j * x j) * star (x i)
  ring

private lemma effect_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (u : EuclideanSpace ℂ ι) :
    0 ≤ effectProb A (pureDensity u) := by
  rw [effect_inner, EuclideanSpace.inner_eq_star_dotProduct]
  simpa only [RCLike.re_to_complex, act, WithLp.ofLp_toLp, dotProduct_comm]
    using hA.re_dotProduct_nonneg u

private lemma act_frob {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) : ‖act A x‖ ≤ frobNorm A * ‖x‖ := by
  have h := Matrix.frobenius_norm_mul A (Matrix.replicateCol Unit (⇑x))
  rw [← Matrix.replicateCol_mulVec, Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at h
  exact h

private lemma effect_frob {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    effectProb A (pureDensity x) ≤ frobNorm A * ‖x‖ ^ 2 := by
  rw [effect_inner]
  calc
    _ ≤ ‖inner ℂ x (act A x)‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖act A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (frobNorm A * ‖x‖) :=
      mul_le_mul_of_nonneg_left (act_frob A x) (norm_nonneg _)
    _ = _ := by ring

private lemma frob_sq {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    frobNorm A ^ 2 = (A * A).trace.re := by
  have hn : 0 ≤ ∑ i : ι, ∑ j : ι, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hf : frobNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    unfold frobNorm
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    simpa only [Real.rpow_two] using Real.sq_sqrt hn
  rw [hf]
  have h : (Aᴴ * A).trace.re = ∑ i, ∑ j, ‖A i j‖^2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.sq_norm, Complex.mul_re, Complex.normSq_apply]
  rw [hA.eq] at h
  exact h.symm

private lemma trace_mul_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hs : S * S = A := by simpa [S, pow_two] using CFC.sq_sqrt A hA.nonneg
  have h := (hB.conjTranspose_mul_mul_same S).trace_nonneg
  rw [hS.isHermitian.eq, Matrix.trace_mul_cycle, hs] at h
  exact h.1

private lemma sum_frob_sq {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    (A : O → Matrix ι ι ℂ) (hA : ∀ i, (A i).PosSemidef) :
    ∑ i, frobNorm (A i)^2 ≤ ((∑ i, A i) * (∑ i, A i)).trace.re := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [frob_sq _ (hA i).isHermitian]
  exact Finset.single_le_sum (fun j _ => trace_mul_nonneg _ _ (hA j) (hA i)) (Finset.mem_univ i)

private lemma density_act {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    pureDensity (act A x) = A * pureDensity x * Aᴴ := by
  ext i j
  simp only [pureDensity, act, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    map_sum, map_mul, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

private lemma pure_effect {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) :
    effectProb (pureDensity x) (pureDensity y) = ‖inner ℂ x y‖ ^ 2 := by
  rw [effect_inner]
  have h : act (pureDensity x) y = (inner ℂ x y) • x := by
    ext i
    simp [act, pureDensity, Matrix.mulVec, dotProduct,
      EuclideanSpace.inner_eq_star_dotProduct, ← Finset.mul_sum, mul_comm, mul_left_comm]
  rw [h, inner_smul_right, ← inner_conj_symm (𝕜 := ℂ) y x]
  simpa only [Complex.mul_conj, Complex.ofReal_re] using (Complex.sq_norm (inner ℂ x y)).symm

private lemma effect_add {ι : Type*} [Fintype ι] (A B ρ : Matrix ι ι ℂ) :
    effectProb (A+B) ρ = effectProb A ρ + effectProb B ρ := by
  simp [effectProb, Matrix.add_mul, Matrix.trace_add]

private lemma effect_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℂ ι) : effectProb 1 (pureDensity x) = ‖x‖^2 := by
  rw [effect_inner]
  have h : act (1 : Matrix ι ι ℂ) x = x := by ext i; simp [act]
  rw [h]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) x

private lemma effect_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) (c : ℝ) :
    effectProb A (pureDensity ((c : ℂ) • x)) = c^2 * effectProb A (pureDensity x) := by
  rw [effect_inner, effect_inner]
  have h : act A ((c : ℂ) • x) = (c : ℂ) • act A x := by
    ext i; simp [act, Matrix.mulVec_smul]
  rw [h, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re, pow_two, mul_assoc]

private def cols {O ι : Type*} (χ : O → EuclideanSpace ℂ ι) : Matrix ι O ℂ :=
  fun a i => χ i a

private lemma cols_density {O ι : Type*} [Fintype O]
    (χ : O → EuclideanSpace ℂ ι) :
    cols χ * (cols χ)ᴴ = ∑ i, pureDensity (χ i) := by
  ext a b
  simp [cols, Matrix.mul_apply, pureDensity, Matrix.sum_apply]
private lemma support_action {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    (χ : O → EuclideanSpace ℂ ι) (F : Matrix ι ι ℂ)
    (hF : (F-1) * (∑ i, pureDensity (χ i)) = 0) (i : O) :
    act F (χ i) = χ i := by
  have h := (Matrix.mul_self_mul_conjTranspose_eq_zero (cols χ) (F-1)).mp
    (by simpa only [cols_density] using hF)
  have heq : F * cols χ = cols χ := by
    simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] using h
  ext a
  exact congrArg (fun A : Matrix ι O ℂ => A a i) heq

private lemma quarter_whitening {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    (χ : O → EuclideanSpace ℂ ι) :
    let ρ := ∑ i, pureDensity (χ i)
    let S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρ
    ∃ Q R : Matrix ι ι ℂ, Q.PosSemidef ∧ R.PosSemidef ∧
      Q*Q = cfc Real.sqrt ρ ∧ R*R = S ∧
      ∀ i, act Q (act R (χ i)) = χ i := by
  classical
  dsimp only
  let ρ := ∑ i, pureDensity (χ i)
  have hρ : ρ.PosSemidef := by
    change (∑ i, pureDensity (χ i)).PosSemidef
    rw [← cols_density]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  let q : ℝ → ℝ := fun x => Real.sqrt (Real.sqrt x)
  let r : ℝ → ℝ := fun x => (q x)⁻¹
  let Q := cfc q ρ
  let R := cfc r ρ
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ ρ) :=
    ρ.finite_real_spectrum.continuousOn f
  have hQ : Q.PosSemidef := (cfc_nonneg (a := ρ) (fun x _ => Real.sqrt_nonneg _)).posSemidef
  have hR : R.PosSemidef := (cfc_nonneg (a := ρ)
    (fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg _))).posSemidef
  have hQQ : Q*Q = cfc Real.sqrt ρ := by
    rw [← cfc_mul q q ρ (hc _) (hc _)]
    exact cfc_congr (fun x _ => Real.mul_self_sqrt (Real.sqrt_nonneg x))
  have hRR : R*R = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρ := by
    rw [← cfc_mul r r ρ (hc _) (hc _)]
    apply cfc_congr
    intro x hx
    dsimp [r, q]
    rw [← mul_inv, Real.mul_self_sqrt (Real.sqrt_nonneg x)]
  refine ⟨Q,R,hQ,hR,hQQ,hRR,fun i => ?_⟩
  rw [← act_mul]
  apply support_action χ (Q*R) _ i
  have heq : (Q*R-1)*ρ = cfc (fun x : ℝ => (q x*r x-1)*x) ρ := by
    rw [cfc_mul _ _ ρ (hc _) (hc _), cfc_sub _ _ ρ (hc _) (hc _),
      cfc_mul _ _ ρ (hc _) (hc _)]
    simp only [cfc_id', cfc_const_one, hρ.isHermitian.isSelfAdjoint]
    rfl
  rw [heq, ← cfc_const_zero ℝ ρ]
  apply cfc_congr
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg hρ.nonneg hx
  by_cases h : x = 0
  · simp [h]
  · have hq : q x ≠ 0 := (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr
        (lt_of_le_of_ne hx0 (Ne.symm h)))).ne'
    simp [r, mul_inv_cancel₀ hq]

private lemma pointwise_bound {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    (χ : O → EuclideanSpace ℂ ι) (M : O → Matrix ι ι ℂ) (hM : IsPOVM M) :
    (∑ i, effectProb (M i) (pureDensity (χ i)))^2 ≤
      (∑ i, ‖χ i‖^2) *
        ∑ i, ‖inner ℂ (act (cfc (fun x : ℝ => (Real.sqrt x)⁻¹)
          (∑ j, pureDensity (χ j))) (χ i)) (χ i)‖^2 := by
  classical
  let ρ := ∑ i, pureDensity (χ i)
  let S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρ
  obtain ⟨Q,R,hQ,hR,hQQ,hRR,hQR⟩ := quarter_whitening χ
  let A : O → Matrix ι ι ℂ := fun i => Q * M i * Q
  have hA (i : O) : (A i).PosSemidef := by
    simpa only [hQ.isHermitian.eq] using (hM.1 i).conjTranspose_mul_mul_same Q
  have hsumA : ∑ i, A i = cfc Real.sqrt ρ := by
    simp only [A, ← Finset.sum_mul, ← Finset.mul_sum, hM.2, Matrix.mul_one]
    exact hQQ
  have hρ : ρ.PosSemidef := by
    change (∑ i, pureDensity (χ i)).PosSemidef
    rw [← cols_density]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hρsqrt : cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ := by
    rw [← cfc_mul Real.sqrt Real.sqrt ρ]
    calc
      _ = cfc (id : ℝ → ℝ) ρ := cfc_congr (fun x hx =>
        Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hρ.nonneg hx))
      _ = _ := cfc_id ℝ _ hρ.isHermitian
  have htrace : ρ.trace.re = ∑ i, ‖χ i‖^2 := by
    simp only [ρ, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simpa [effectProb] using effect_one (χ i)
  have hb : ∑ i, frobNorm (A i)^2 ≤ ∑ i, ‖χ i‖^2 := by
    have h := sum_frob_sq A hA
    rwa [hsumA,hρsqrt,htrace] at h
  have hRnorm (i : O) : ‖act R (χ i)‖^2 =
      ‖inner ℂ (act S (χ i)) (χ i)‖ := by
    have hi : inner ℂ (act R (χ i)) (act R (χ i)) = inner ℂ (χ i) (act S (χ i)) := by
      rw [inner_act, hR.isHermitian.eq, ← act_mul, hRR]
    rw [norm_inner_symm (act S (χ i)) (χ i), ← hi, inner_self_eq_norm_sq_to_K]
    simp
  have hpoint (i : O) : effectProb (M i) (pureDensity (χ i)) ≤
      frobNorm (A i) * ‖inner ℂ (act S (χ i)) (χ i)‖ := by
    have heq : effectProb (M i) (pureDensity (χ i)) =
        effectProb (A i) (pureDensity (act R (χ i))) := by
      rw [effect_inner,effect_inner]
      dsimp only [A]
      have hQA : ∀ u v : EuclideanSpace ℂ ι,
          inner ℂ u (act Q v) = inner ℂ (act Q u) v := by
        intro u v
        rw [inner_act, hQ.isHermitian.eq]
      rw [act_mul, act_mul, hQA, hQR]
    rw [heq, ← hRnorm]
    exact effect_frob _ _
  let P : ℝ := ∑ i, effectProb (M i) (pureDensity (χ i))
  let D : ℝ := ∑ i, ‖inner ℂ (act S (χ i)) (χ i)‖^2
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => effect_nonneg _ (hM.1 i) _
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hle : P ≤ Real.sqrt (∑ i, ‖χ i‖^2) * Real.sqrt D := by
    calc
      _ ≤ ∑ i, frobNorm (A i) * ‖inner ℂ (act S (χ i)) (χ i)‖ :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ ≤ Real.sqrt (∑ i, frobNorm (A i)^2) * Real.sqrt D :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _)
  have hc0 : 0 ≤ ∑ i, ‖χ i‖^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq := mul_self_le_mul_self hP hle
  simpa only [← pow_two, mul_pow, Real.sq_sqrt hc0, Real.sq_sqrt hD] using hsq

private lemma sqrt_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : Real.sqrt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs := Finset.sum_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hi := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hp := mul_nonneg (Real.sqrt_nonneg (f a)) (Real.sqrt_nonneg (∑ i ∈ s, f i))
    have h := Real.sq_sqrt (add_nonneg (hf a (Finset.mem_insert_self _ _)) hs)
    have h1 := Real.sq_sqrt (hf a (Finset.mem_insert_self _ _))
    have h2 := Real.sq_sqrt hs
    have hr := Real.sqrt_nonneg (f a + ∑ i ∈ s, f i)
    have h3 := Real.sqrt_nonneg (f a)
    have h4 := Real.sqrt_nonneg (∑ i ∈ s, f i)
    nlinarith

private lemma sum_weight (m : ℕ) (t : ℝ) :
    (∑ S : Fin m → ZMod 2, t ^ hammingNorm S) = (1+t)^m := by
  classical
  have point (S : Fin m → ZMod 2) :
      t ^ hammingNorm S = ∏ i, if S i ≠ 0 then t else 1 := by
    simp [Finset.prod_ite, hammingNorm]
  simp_rw [point]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (z : ZMod 2) => if z ≠ 0 then t else 1)]
  have bit : (∑ z : ZMod 2, if z ≠ 0 then t else 1) = 1+t := by
    change (∑ z : Fin 2, if (z : ZMod 2) ≠ 0 then t else 1) = _
    simp [Fin.sum_univ_succ]
  simp_rw [bit]
  simp

private lemma fiber_sqrt_le {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    (f : (Fin m → ZMod 2) → ℝ) (hf : ∀ S, 0 ≤ f S) :
    (∑ Q : Fin k → ZMod 2, Real.sqrt
      (∑ S ∈ Finset.univ.filter (fun S => M.transpose.mulVec S = Q), f S)) ≤
      ∑ S, Real.sqrt (f S) := by
  classical
  calc
    _ ≤ ∑ Q : Fin k → ZMod 2,
        ∑ S ∈ Finset.univ.filter (fun S => M.transpose.mulVec S = Q), Real.sqrt (f S) := by
      apply Finset.sum_le_sum
      intro Q _
      exact sqrt_sum_le _ _ (fun S _ => hf S)
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp

private lemma sqrt_pow (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Real.sqrt (t^n) = (Real.sqrt t)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ht _), ih, pow_succ]

private lemma diag_bound {m k T : ℕ} {β : ℝ} (hm : 10 ≤ m) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hT : 1 ≤ T) (hTm : (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β)) (hk : k ≤ m)
    (M : Matrix (Fin m) (Fin k) (ZMod 2)) (hM : M.rank = k) (x : Fin k → ZMod 2) :
    (psdSqrt (xorConvMatrix fun z => weightPowFun m β T (M.mulVec z)) x x)^2 ≤
      ((2:ℝ)^k)⁻¹ * (4*Real.exp 1*(1-β/2)^T) *
        Real.exp (22*(T:ℝ)^2*β^2/(m:ℝ) + 2*Real.sqrt ((T:ℝ)*(m:ℝ)*β)) := by
  classical
  let t := (T:ℝ)*β/(m:ℝ)
  let K := 4*Real.exp 1*(1-β/2)^T*Real.exp (22*(T:ℝ)^2*β^2/(m:ℝ))
  let U := ∑ Q : Fin k → ZMod 2, Real.sqrt
    (∑ S ∈ Finset.univ.filter (fun S : Fin m → ZMod 2 => M.transpose.mulVec S = Q),
      boolFourier (weightPowFun m β T) S)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hK : 0 ≤ K := by
    have : 0 ≤ 1-β/2 := by linarith
    dsimp [K]
    positivity
  have hb := QAlgorithms.Arunachalam.fourier_weightPow_bound hm hβ hβ1 hT hTm
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hsum : U ≤ Real.sqrt K * (1+Real.sqrt t)^m := by
    calc
      U ≤ ∑ S, Real.sqrt (boolFourier (weightPowFun m β T) S) :=
        fiber_sqrt_le M _ (fun S => (hb S).1)
      _ ≤ ∑ S : Fin m → ZMod 2, Real.sqrt K * (Real.sqrt t)^hammingNorm S := by
        apply Finset.sum_le_sum
        intro S _
        calc
          _ ≤ Real.sqrt (K*t^hammingNorm S) := Real.sqrt_le_sqrt (by
            dsimp [K,t]; nlinarith only [(hb S).2])
          _ = _ := by rw [Real.sqrt_mul hK, sqrt_pow t ht]
      _ = _ := by rw [← Finset.mul_sum, sum_weight]
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have heq : (m:ℝ)*Real.sqrt t = Real.sqrt ((T:ℝ)*(m:ℝ)*β) := by
    calc
      _ = Real.sqrt ((m:ℝ)^2) * Real.sqrt t := by rw [Real.sqrt_sq hm0.le]
      _ = Real.sqrt ((m:ℝ)^2*t) := (Real.sqrt_mul (sq_nonneg _) _).symm
      _ = _ := by congr 1; dsimp [t]; field_simp
  have he : (1+Real.sqrt t)^m ≤ Real.exp (Real.sqrt ((T:ℝ)*(m:ℝ)*β)) := by
    calc
      _ ≤ (Real.exp (Real.sqrt t))^m :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (Real.sqrt t)]) _
      _ = _ := by rw [← Real.exp_nat_mul, heq]
  have hu : U ≤ Real.sqrt K * Real.exp (Real.sqrt ((T:ℝ)*(m:ℝ)*β)) :=
    hsum.trans (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _))
  rw [QAlgorithms.Arunachalam.sqrtA_diag hm hβ hβ1 hT hTm hk M hM x]
  change ((Real.sqrt ((2:ℝ)^k))⁻¹ * U)^2 ≤ _
  have hu2 : U^2 ≤ K * Real.exp (2*Real.sqrt ((T:ℝ)*(m:ℝ)*β)) := by
    calc
      _ ≤ (Real.sqrt K * Real.exp (Real.sqrt ((T:ℝ)*(m:ℝ)*β)))^2 :=
        pow_le_pow_left₀ hU hu 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hK, ← Real.exp_nat_mul]; norm_num
  calc
    _ = ((2:ℝ)^k)⁻¹ * U^2 := by rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    _ ≤ ((2:ℝ)^k)⁻¹ * (K * Real.exp (2*Real.sqrt ((T:ℝ)*(m:ℝ)*β))) :=
      mul_le_mul_of_nonneg_left hu2 (by positivity)
    _ = _ := by dsimp [K]; rw [Real.exp_add]; ring

private lemma tensor_inner {ι : Type*} [Fintype ι] (T : ℕ)
    (u v : EuclideanSpace ℂ ι) :
    inner ℂ (tensorPow T u) (tensorPow T v) = (inner ℂ u v)^T := by
  simp only [PiLp.inner_apply, tensorPow, RCLike.inner_apply, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin T) (i : ι) => v i * (starRingEnd ℂ) (u i))]
  simp

private lemma example_inner {X : Type*} [Fintype X] (c e : X → Bool) (D : X → ℝ)
    (hD : ∀ i, 0 ≤ D i) :
    inner ℂ (exampleState c D) (exampleState e D) =
      ((∑ i, if c i = e i then D i else 0 : ℝ) : ℂ) := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  cases hc : c i <;> cases he : e i <;>
    simp [exampleState, hc, he, abs_of_nonneg (Real.sqrt_nonneg _),
      ← Complex.ofReal_pow, Real.sq_sqrt (hD i)]

private lemma bit_eq {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2))
    (x y : Fin k → ZMod 2) (i : Fin d) :
    codeConcept M x i = codeConcept M y i ↔ (M.mulVec (x+y)) i = 0 := by
  rw [Matrix.mulVec_add]
  simp only [Pi.add_apply, codeConcept, decide_eq_decide]
  have hb (a b : ZMod 2) : (a = 1 ↔ b = 1) ↔ a+b = 0 := by
    have bits (z : ZMod 2) : z = 0 ∨ z = 1 := by
      have h : z.val = 0 ∨ z.val = 1 := by have := ZMod.val_lt z; omega
      rcases h with h | h
      · exact Or.inl ((ZMod.val_eq_zero z).mp h)
      · exact Or.inr ((ZMod.val_injective 2) (by simpa only [ZMod.val_one_eq_one_mod] using h))
    rcases bits a with rfl | rfl <;> rcases bits b with rfl | rfl <;>
      simp [CharTwo.add_self_eq_zero]
  exact hb _ _

private lemma count_zero {d : ℕ} (z : Fin d → ZMod 2) :
    (∑ i, if z i = 0 then (1:ℝ) else 0) = (d:ℝ) - (hammingNorm z : ℝ) := by
  classical
  have h (i : Fin d) : (if z i = 0 then (1:ℝ) else 0) =
      1 - (if z i ≠ 0 then (1:ℝ) else 0) := by split_ifs <;> simp_all
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  rw [hammingNorm, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num


private lemma tensor_state {ι : Type*} [Fintype ι] (T : ℕ)
    (u : EuclideanSpace ℂ ι) (hu : IsState u) : IsState (tensorPow T u) := by
  have h := tensor_inner T u u
  have hu' : inner ℂ u u = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  rw [hu', one_pow] at h
  have hn : ‖tensorPow T u‖^2 = 1 := by
    calc
      _ = RCLike.re (inner ℂ (tensorPow T u) (tensorPow T u)) :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = 1 := by rw [h]; norm_num
  unfold IsState
  nlinarith [norm_nonneg (tensorPow T u)]

private lemma measurement_sq_le_pgm {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    (p : O → ℝ) (ψ : O → EuclideanSpace ℂ ι) (N : O → Matrix ι ι ℂ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hψ : ∀ i, IsState (ψ i))
    (hN : IsPOVM N) : ensembleSuccess p ψ N ^ 2 ≤ pgmSuccess p ψ := by
  classical
  let χ : O → EuclideanSpace ℂ ι := fun i => (Real.sqrt (p i) : ℂ) • ψ i
  let S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (∑ j, pureDensity (χ j))
  have hmass : ∑ i, ‖χ i‖^2 = 1 := by
    calc
      _ = ∑ i, p i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [χ, norm_smul, sq_abs, Real.sq_sqrt (hp i),
          show ‖ψ i‖ = 1 from hψ i]
      _ = _ := hsum
  have hsucc : ensembleSuccess p ψ N = ∑ i, effectProb (N i) (pureDensity (χ i)) := by
    unfold ensembleSuccess
    apply Finset.sum_congr rfl
    intro i hi
    rw [effect_smul,Real.sq_sqrt (hp i)]
  have hpgm : pgmSuccess p ψ = ∑ i, ‖inner ℂ (act S (χ i)) (χ i)‖^2 := by
    unfold pgmSuccess
    change (∑ i, p i * ‖inner ℂ (act S (χ i)) (ψ i)‖^2) = _
    apply Finset.sum_congr rfl
    intro i hi
    change _ = ‖inner ℂ (act S (χ i)) ((Real.sqrt (p i) : ℂ) • ψ i)‖^2
    rw [inner_smul_right,norm_mul,mul_pow]
    simp [Complex.norm_real,sq_abs,Real.sq_sqrt (hp i)]
  have h := pointwise_bound χ N hN
  rwa [← hsucc,hmass,one_mul,← hpgm] at h

private lemma code_gram {n k T : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin k) (ZMod 2)) (x y : Fin k → ZMod 2) :
    inner ℂ (tensorPow T (exampleState (codeConcept M x) (uniformDist (Fin n))))
      (tensorPow T (exampleState (codeConcept M y) (uniformDist (Fin n)))) =
      ((xorConvMatrix fun z => weightPowFun n 1 T (M.mulVec z)) x y : ℂ) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [tensor_inner, example_inner _ _ _ (fun _ => by unfold uniformDist; positivity)]
  simp only [xorConvMatrix, Matrix.of_apply, weightPowFun]
  rw [Complex.ofReal_pow]
  congr 2
  simp_rw [bit_eq]
  have h (i : Fin n) : (if (M.mulVec (x+y)) i = 0 then uniformDist (Fin n) i else 0) =
      (n:ℝ)⁻¹*(if (M.mulVec (x+y)) i = 0 then 1 else 0) := by
    split_ifs <;> simp [uniformDist]
  simp_rw [h]
  rw [← Finset.mul_sum,count_zero]
  field_simp

private lemma uniform_distribution {n : ℕ} (hn : 0 < n) :
    IsDistribution (uniformDist (Fin n)) := by
  constructor
  · intro i; unfold uniformDist; positivity
  · simp [uniformDist, ne_of_gt hn]

private lemma code_pgm_bound {n k T : ℕ} (hn : 10 ≤ n) (hT : 1 ≤ T)
    (hTn : (T:ℝ) ≤ (n:ℝ)/Real.exp 3)
    (M : Matrix (Fin n) (Fin k) (ZMod 2)) (hM : M.rank = k) :
    pgmSuccess (fun _ : Fin k → ZMod 2 => ((2:ℝ)^k)⁻¹)
      (fun x => tensorPow T (exampleState (codeConcept M x) (uniformDist (Fin n)))) ≤
      ((2:ℝ)^k)⁻¹ * (4*Real.exp 1*(1-(1:ℝ)/2)^T) *
        Real.exp (22*(T:ℝ)^2/(n:ℝ)+2*Real.sqrt ((T:ℝ)*(n:ℝ))) := by
  classical
  let A := xorConvMatrix fun z => weightPowFun n 1 T (M.mulVec z)
  let B := ((2:ℝ)^k)⁻¹ * (4*Real.exp 1*(1-(1:ℝ)/2)^T) *
        Real.exp (22*(T:ℝ)^2/(n:ℝ)+2*Real.sqrt ((T:ℝ)*(n:ℝ)))
  have hk : k ≤ n := by simpa [hM] using M.rank_le_height
  have hGram := QAlgorithms.pgmSuccess_uniform_real_gram
    (fun x => tensorPow T (exampleState (codeConcept M x) (uniformDist (Fin n)))) A
    (code_gram (by omega) M)
  have hcard : (Fintype.card (Fin k → ZMod 2) : ℝ) = (2:ℝ)^k := by simp
  rw [hcard] at hGram
  have hsum : (∑ x : Fin k → ZMod 2, (psdSqrt A x x)^2) ≤ (2:ℝ)^k * B := by
    calc
      _ ≤ ∑ _x : Fin k → ZMod 2, B := by
        apply Finset.sum_le_sum
        intro x _
        simpa [B] using diag_bound hn (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤1)
          hT (by simpa using hTn) hk M hM x
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  rw [hGram]
  calc
    _ ≤ ((2:ℝ)^k)⁻¹ * ((2:ℝ)^k * B) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B := by rw [inv_mul_cancel_left₀ (by positivity)]

private lemma zero_copy_success {n k : ℕ} (M : Matrix (Fin n) (Fin k) (ZMod 2))
    (N : (Fin k → ZMod 2) → Matrix (Fin 0 → Fin n × Bool) (Fin 0 → Fin n × Bool) ℂ)
    (hN : IsPOVM N) :
    ensembleSuccess (fun _ : Fin k → ZMod 2 => ((2:ℝ)^k)⁻¹)
      (fun x => tensorPow 0 (exampleState (codeConcept M x) (uniformDist (Fin n)))) N =
      ((2:ℝ)^k)⁻¹ := by
  classical
  let u : EuclideanSpace ℂ (Fin 0 → Fin n × Bool) := WithLp.toLp 2 (fun _ => 1)
  have hu (x : Fin k → ZMod 2) :
      tensorPow 0 (exampleState (codeConcept M x) (uniformDist (Fin n))) = u := by
    ext z; simp [tensorPow,u]
  simp_rw [ensembleSuccess,hu]
  rw [← Finset.mul_sum]
  have he : (∑ x, effectProb (N x) (pureDensity u)) = effectProb (∑ x,N x) (pureDensity u) := by
    simp [effectProb,Finset.sum_mul,Matrix.trace_sum,Complex.re_sum]
  rw [he,hN.2,effect_one]
  have hn : ‖u‖^2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    change (∑ _ : Fin 0 → Fin n × Bool, (1:ℂ) * star 1).re = 1
    simp
  rw [hn,mul_one]

private lemma small_copy_bound {n k T : ℕ} {c : ℝ}
    (hk : 16 ≤ (k:ℝ)) (hkn : k ≤ n) (_hc : 0 < c)
    (hrate : c*(n:ℝ) ≤ (k:ℝ))
    (hsmall : (T:ℝ) ≤ (k:ℝ)/1000) (hsmall' : (T:ℝ) ≤ c*(k:ℝ)/1024) :
    ((2:ℝ)^k)⁻¹ * (4*Real.exp 1*(1-(1:ℝ)/2)^T) *
        Real.exp (22*(T:ℝ)^2/(n:ℝ)+2*Real.sqrt ((T:ℝ)*(n:ℝ))) < 16/25 := by
  have hk0 : 0 ≤ (k:ℝ) := by positivity
  have hkn' : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hkn
  have hn0 : 0 < (n:ℝ) := by linarith
  have ht0 : 0 ≤ (T:ℝ) := by positivity
  have hquad : 22*(T:ℝ)^2/(n:ℝ) ≤ (k:ℝ)/8 := by
    rw [div_le_iff₀ hn0]
    have hs := pow_le_pow_left₀ ht0 hsmall 2
    have hm := mul_le_mul_of_nonneg_left hkn' hk0
    nlinarith
  have hroot : Real.sqrt ((T:ℝ)*(n:ℝ)) ≤ (k:ℝ)/32 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have h1 := mul_le_mul_of_nonneg_right hsmall' hn0.le
      have h2 := mul_le_mul_of_nonneg_left hrate (show 0 ≤ (k:ℝ)/1024 by positivity)
      nlinarith
  have he : 22*(T:ℝ)^2/(n:ℝ)+2*Real.sqrt ((T:ℝ)*(n:ℝ)) ≤ (k:ℝ)/4 := by
    linarith
  have hp : (1-(1:ℝ)/2)^T ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hlog : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    linarith
  have hi : ((2:ℝ)^k)⁻¹ = Real.exp (-((k:ℝ)*Real.log 2)) := by
    rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ ((2:ℝ)^k)⁻¹ * (4*Real.exp 1) *
        Real.exp (22*(T:ℝ)^2/(n:ℝ)+2*Real.sqrt ((T:ℝ)*(n:ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*Real.exp 1)
    _ ≤ ((2:ℝ)^k)⁻¹ * (4*Real.exp 1) * Real.exp ((k:ℝ)/4) := by
      gcongr
    _ = 4*Real.exp (1-(k:ℝ)*Real.log 2+(k:ℝ)/4) := by
      rw [hi,Real.exp_add,Real.exp_sub,Real.exp_neg]
      ring
    _ ≤ 4*Real.exp (-3) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hlog hk0
      linarith
    _ < 16/25 := by
      have h1 : 2 < Real.exp 1 := by
        have h := Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)
        norm_num at h
        exact h
      have h3 : 8 < Real.exp 3 := by
        have h := pow_lt_pow_left₀ h1 (by norm_num : (0:ℝ)≤2) (by norm_num : (3:ℕ)≠0)
        rw [← Real.exp_nat_mul] at h
        norm_num at h ⊢
        exact h
      rw [Real.exp_neg]
      have h0 := Real.exp_pos 3
      have h := (div_lt_iff₀ h0).mpr (show (4:ℝ) < (16/25)*Real.exp 3 by linarith)
      simpa [div_eq_mul_inv] using h

theorem solution :
    ∀ c₁ : ℝ, 0 < c₁ → ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (n k : ℕ) (M : Matrix (Fin n) (Fin k) (ZMod 2)), M.rank = k → c₁ * (n : ℝ) ≤ (k : ℝ) →
        ∀ (T : ℕ) (N : (Fin k → ZMod 2) →
            Matrix (Fin T → Fin n × Bool) (Fin T → Fin n × Bool) ℂ),
          IsPOVM N →
          ensembleSuccess (fun _ : Fin k → ZMod 2 => ((2 : ℝ) ^ k)⁻¹)
              (fun x => tensorPow T (exampleState (codeConcept M x) (uniformDist (Fin n)))) N ≥
            4 / 5 →
          c₀ * (k : ℝ) ≤ (T : ℝ) := by
  classical
  intro c hc
  let a : ℝ := min (1/1000) (min (c/1024) (Real.exp 3)⁻¹)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1/1000 := min_le_left _ _
  have ha2 : a ≤ c/1024 := (min_le_right _ _).trans (min_le_left _ _)
  have ha3 : a ≤ (Real.exp 3)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨a,ha,?_⟩
  intro n k M hM hrate T N hN hsucc
  have hkn : k ≤ n := by simpa [hM] using M.rank_le_height
  by_cases hk0 : k = 0
  · subst k; simp
  have hk : 1 ≤ k := by omega
  by_cases hT0 : T = 0
  · subst T
    rw [zero_copy_success M N hN] at hsucc
    have hp : (2:ℝ) ≤ (2:ℝ)^k := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hk
    have hi : ((2:ℝ)^k)⁻¹ ≤ 1/2 := by
      simpa using inv_anti₀ (by norm_num : (0:ℝ)<2) hp
    linarith
  have hT : 1 ≤ T := by omega
  have hn : 0 < n := by omega
  by_contra h
  have hsmall : (T:ℝ) < a*(k:ℝ) := lt_of_not_ge h
  have ht : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  have ht1 : (T:ℝ) ≤ (k:ℝ)/1000 := by
    have h := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ (k:ℝ) by positivity)
    nlinarith
  have ht2 : (T:ℝ) ≤ c*(k:ℝ)/1024 := by
    have h := mul_le_mul_of_nonneg_right ha2 (show 0 ≤ (k:ℝ) by positivity)
    nlinarith
  have hkbig : 1000 ≤ (k:ℝ) := by linarith
  have hnbig : 10 ≤ n := by
    have hkn' : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hkn
    have hn' : (10:ℝ) ≤ (n:ℝ) := by linarith
    exact_mod_cast hn'
  have hTn : (T:ℝ) ≤ (n:ℝ)/Real.exp 3 := by
    calc
      _ ≤ a*(k:ℝ) := hsmall.le
      _ ≤ (Real.exp 3)⁻¹*(k:ℝ) := mul_le_mul_of_nonneg_right ha3 (by positivity)
      _ ≤ (Real.exp 3)⁻¹*(n:ℝ) := by gcongr
      _ = _ := by ring
  have hψ : ∀ x : Fin k → ZMod 2,
      IsState (tensorPow T (exampleState (codeConcept M x) (uniformDist (Fin n)))) := by
    intro x
    exact tensor_state T _ (exampleState_norm (uniform_distribution hn) _)
  have hmass : (∑ _x : Fin k → ZMod 2, ((2:ℝ)^k)⁻¹) = 1 := by
    simp [ne_of_gt (show (0:ℝ)<2 by norm_num)]
  have hcmp := measurement_sq_le_pgm
    (fun _ : Fin k → ZMod 2 => ((2:ℝ)^k)⁻¹) _ N (fun _ => by positivity) hmass hψ hN
  have hb := code_pgm_bound hnbig hT hTn M hM
  have hnum := small_copy_bound (by linarith : 16 ≤ (k:ℝ)) hkn hc hrate ht1 ht2
  have hfinal := hcmp.trans_lt (hb.trans_lt hnum)
  nlinarith
