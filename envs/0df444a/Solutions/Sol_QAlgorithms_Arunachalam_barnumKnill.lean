-- Prove2me | solution 1 for QAlgorithms.Arunachalam.barnumKnill
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:55:52.533179+00:00
-- url     : https://prove2.me/submissions/395e1bcd-9962-4e86-b725-3fb3c05cb4f1

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
open Matrix QAlgorithms

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
private lemma pgm_completion {O ι : Type*} [Fintype O] [Nonempty O]
    [Fintype ι] [DecidableEq ι] (χ : O → EuclideanSpace ℂ ι) :
    let S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (∑ j, pureDensity (χ j))
    ∃ M : O → Matrix ι ι ℂ, IsPOVM M ∧
      ∀ i, ‖inner ℂ (act S (χ i)) (χ i)‖^2 ≤ effectProb (M i) (pureDensity (χ i)) := by
  classical
  dsimp only
  let ρ := ∑ j, pureDensity (χ j)
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  let S := cfc f ρ
  let N : O → Matrix ι ι ℂ := fun i => pureDensity (act S (χ i))
  have hρ : ρ.PosSemidef := by
    change (∑ i, pureDensity (χ i)).PosSemidef
    rw [← cols_density]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hS : S.PosSemidef := (cfc_nonneg (a := ρ)
    (fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg _))).posSemidef
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ ρ) :=
    ρ.finite_real_spectrum.continuousOn g
  have hN (i : O) : (N i).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  have hsumN : ∑ i, N i = cfc (fun x : ℝ => f x * x * f x) ρ := by
    have heq : ∑ i, N i = S*ρ*S := by
      simp only [N,density_act,hS.isHermitian.eq,← Finset.sum_mul,← Finset.mul_sum]
      rfl
    rw [heq,cfc_mul _ _ ρ (hc _) (hc _),cfc_mul _ _ ρ (hc _) (hc _)]
    simp only [cfc_id',hρ.isHermitian.isSelfAdjoint]
    rfl
  have hP : (1-∑ i, N i).PosSemidef := by
    rw [hsumN,← cfc_const_one ℝ ρ (ha := hρ.isHermitian.isSelfAdjoint),← cfc_sub _ _ ρ (hc _) (hc _)]
    apply Matrix.nonneg_iff_posSemidef.mp
    apply cfc_nonneg
    intro x hx
    have hx0 := spectrum_nonneg_of_nonneg hρ.nonneg hx
    by_cases h : x = 0
    · simp [f,h]
    · have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hx0 (Ne.symm h))).ne'
      have hs2 := Real.mul_self_sqrt hx0
      dsimp only [f]
      have he : (Real.sqrt x)⁻¹*x*(Real.sqrt x)⁻¹ = 1 := by
        field_simp
        nlinarith [Real.sq_sqrt hx0]
      rw [he]
      norm_num
  let i₀ : O := Classical.choice inferInstance
  let M : O → Matrix ι ι ℂ := fun i => N i + if i=i₀ then 1-∑ j,N j else 0
  refine ⟨M,⟨fun i => (hN i).add (by split_ifs; exact hP; exact Matrix.PosSemidef.zero), ?_⟩,?_⟩
  · simp [M,Finset.sum_add_distrib]
  · intro i
    change _ ≤ effectProb (N i + _) (pureDensity (χ i))
    rw [effect_add,show effectProb (N i) (pureDensity (χ i)) =
      ‖inner ℂ (act S (χ i)) (χ i)‖^2 from pure_effect _ _]
    have h0 : 0 ≤ effectProb (if i=i₀ then 1-∑ j,N j else 0) (pureDensity (χ i)) := by
      apply effect_nonneg
      split_ifs
      · exact hP
      · exact Matrix.PosSemidef.zero
    linarith

theorem solution {m d : ℕ} (p : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℂ (Fin d))
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hψ : ∀ i, IsState (ψ i)) :
    optSuccess p ψ ^ 2 ≤ pgmSuccess p ψ ∧ pgmSuccess p ψ ≤ optSuccess p ψ := by
  classical
  have hm : 0 < m := by
    by_contra h
    have he : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    simp at hsum
  have : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let χ : Fin m → EuclideanSpace ℂ (Fin d) := fun i => (Real.sqrt (p i) : ℂ) • ψ i
  let S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (∑ j, pureDensity (χ j))
  have hmass : ∑ i, ‖χ i‖^2 = 1 := by
    calc
      _ = ∑ i, p i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [χ, norm_smul, sq_abs, Real.sq_sqrt (hp i),
          show ‖ψ i‖ = 1 from hψ i]
      _ = _ := hsum
  have hsucc (M : Fin m → Matrix (Fin d) (Fin d) ℂ) :
      ensembleSuccess p ψ M = ∑ i, effectProb (M i) (pureDensity (χ i)) := by
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
  obtain ⟨M,hM,hbetter⟩ := pgm_completion χ
  have : Nonempty {M : Fin m → Matrix (Fin d) (Fin d) ℂ // IsPOVM M} := ⟨⟨M,hM⟩⟩
  have hbound (M : Fin m → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
      ensembleSuccess p ψ M ≤ Real.sqrt (pgmSuccess p ψ) := by
    apply Real.le_sqrt_of_sq_le
    have h := pointwise_bound χ M hM
    rwa [← hsucc,hmass,one_mul,← hpgm] at h
  have hbdd : BddAbove (Set.range fun M : {M : Fin m → Matrix (Fin d) (Fin d) ℂ // IsPOVM M} =>
      ensembleSuccess p ψ M.1) := ⟨Real.sqrt (pgmSuccess p ψ),by
        rintro _ ⟨M,rfl⟩; exact hbound M.1 M.2⟩
  have hopt : 0 ≤ optSuccess p ψ := by
    apply le_trans _ (le_ciSup hbdd (⟨M,hM⟩))
    rw [hsucc]
    exact Finset.sum_nonneg fun i _ => effect_nonneg _ (hM.1 i) _
  have hoptle : optSuccess p ψ ≤ Real.sqrt (pgmSuccess p ψ) :=
    ciSup_le fun M => hbound M.1 M.2
  have hpgm0 : 0 ≤ pgmSuccess p ψ := by
    rw [hpgm]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  constructor
  · have h := mul_self_le_mul_self hopt hoptle
    simpa only [← pow_two,Real.sq_sqrt hpgm0] using h
  · calc
      _ = ∑ i, ‖inner ℂ (act S (χ i)) (χ i)‖^2 := hpgm
      _ ≤ ∑ i, effectProb (M i) (pureDensity (χ i)) := Finset.sum_le_sum fun i _ => hbetter i
      _ = ensembleSuccess p ψ M := (hsucc M).symm
      _ ≤ _ := le_ciSup hbdd (⟨M,hM⟩)
