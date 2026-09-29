-- Prove2me | solution 1 for VectorCalculus.grad_lineIntegral_potential
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:51:18.587418+00:00
-- url     : https://prove2.me/submissions/43d44d8f-4ab4-464f-897a-4cc8aaadcc71

import Definitions.Def_VectorCalculus_lineIntegral
import Definitions.Def_VectorCalculus_grad

open VectorCalculus

namespace Ag4Aux_VCGrad

noncomputable def integrand {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (x : ℝ → (Fin n → ℝ)) (t : ℝ) : ℝ :=
  ∑ i, F (x t) i * deriv (fun s => x s i) t

theorem li_eq {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ)) (x : ℝ → (Fin n → ℝ)) (a b : ℝ) :
    lineIntegral F x a b = ∫ t in a..b, integrand F x t := rfl

theorem coord_contDiff {n : ℕ} {x : ℝ → (Fin n → ℝ)} (hx : ContDiff ℝ 1 x) (i : Fin n) :
    ContDiff ℝ 1 (fun t => x t i) := contDiff_pi.mp hx i

theorem integrand_cont {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : Continuous F)
    {x : ℝ → (Fin n → ℝ)} (hx : ContDiff ℝ 1 x) : Continuous (integrand F x) := by
  unfold integrand
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp (hF.comp hx.continuous)).mul
    ((coord_contDiff hx i).continuous_deriv le_rfl)

theorem reparam {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : Continuous F)
    {x : ℝ → (Fin n → ℝ)} (hx : ContDiff ℝ 1 x) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (p q : ℝ) :
    lineIntegral F (fun s => x (u s)) p q = lineIntegral F x (u p) (u q) := by
  have hd : ∀ i s, deriv (fun s => x (u s) i) s = deriv (fun t => x t i) (u s) * deriv u s := by
    intro i s
    have h1 : HasDerivAt (fun t => x t i) (deriv (fun t => x t i) (u s)) (u s) :=
      ((coord_contDiff hx i).differentiable one_ne_zero (u s)).hasDerivAt
    have h2 : HasDerivAt u (deriv u s) s := (hu.differentiable one_ne_zero s).hasDerivAt
    exact (h1.comp s h2).deriv
  rw [li_eq, li_eq]
  have := intervalIntegral.integral_comp_mul_deriv (a := p) (b := q) (f := u) (f' := deriv u)
    (g := integrand F x)
    (fun s _ => (hu.differentiable one_ne_zero s).hasDerivAt) (hu.continuous_deriv le_rfl).continuousOn
    (integrand_cont hF hx)
  rw [← this]
  congr 1; funext s
  simp only [integrand, Function.comp, Finset.sum_mul, hd, mul_assoc]

noncomputable def uu (a b : ℝ) (s : ℝ) : ℝ := a + (b - a) * Real.smoothTransition s
theorem uu_cd (a b : ℝ) : ContDiff ℝ 1 (uu a b) :=
  contDiff_const.add (contDiff_const.mul Real.smoothTransition.contDiff)

theorem st_one (s : ℝ) (hs : 1 ≤ s) : Real.smoothTransition s = 1 :=
  Real.smoothTransition.one_of_one_le hs

theorem deriv_st (s : ℝ) (hs : 1 ≤ s) : deriv Real.smoothTransition s = 0 := by
  apply IsLocalMax.deriv_eq_zero
  exact Filter.Eventually.of_forall fun t => by
    rw [st_one s hs]; exact Real.smoothTransition.le_one _

theorem deriv_st0 (s : ℝ) (hs : s ≤ 0) : deriv Real.smoothTransition s = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.smoothTransition.zero_of_nonpos hs]; exact Real.smoothTransition.nonneg _

theorem concat {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : Continuous F)
    (x y : ℝ → (Fin n → ℝ)) (a b c d : ℝ)
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (hbc : x b = y c) :
    ∃ Z : ℝ → (Fin n → ℝ), ContDiff ℝ 1 Z ∧ Z 0 = x a ∧ Z 2 = y d ∧
      lineIntegral F Z 0 2 = lineIntegral F x a b + lineIntegral F y c d := by
  let v : ℝ → ℝ := fun s => uu c d (s - 1)
  have hv : ContDiff ℝ 1 v := (uu_cd c d).comp (contDiff_id.sub contDiff_const)
  let X : ℝ → (Fin n → ℝ) := fun s => x (uu a b s)
  let Y : ℝ → (Fin n → ℝ) := fun s => y (v s)
  let Z : ℝ → (Fin n → ℝ) := fun s => X s + Y s - x b
  have hX : ContDiff ℝ 1 X := hx.comp (uu_cd a b)
  have hY : ContDiff ℝ 1 Y := hy.comp hv
  have hZ : ContDiff ℝ 1 Z := (hX.add hY).sub contDiff_const
  have hZX : ∀ s ≤ 1, Z s = X s := by
    intro s hs
    show x (uu a b s) + y (c + (d - c) * Real.smoothTransition (s - 1)) - x b = x (uu a b s)
    rw [Real.smoothTransition.zero_of_nonpos (show s - 1 ≤ 0 by linarith), mul_zero, add_zero,
      ← hbc]; abel
  have hZY : ∀ s, 1 ≤ s → Z s = Y s := by
    intro s hs
    show x (uu a b s) + y (v s) - x b = y (v s)
    rw [uu, st_one s hs, show a + (b - a) * 1 = b by ring]; abel
  have hdY : ∀ i, ∀ s ≤ 1, deriv (fun s => Y s i) s = 0 := by
    intro i s hs
    have h1 : HasDerivAt (fun t => y t i) (deriv (fun t => y t i) (v s)) (v s) :=
      ((coord_contDiff hy i).differentiable one_ne_zero _).hasDerivAt
    have h0 : HasDerivAt (fun s : ℝ => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have h2 : HasDerivAt v ((d - c) * (deriv Real.smoothTransition (s - 1) * 1)) s :=
      ((((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero (s - 1)).hasDerivAt.comp
        s h0).const_mul (d - c)).const_add c
    show deriv ((fun t => y t i) ∘ v) s = 0
    rw [(h1.comp s h2).deriv, deriv_st0 (s - 1) (by linarith)]; simp
  have hdX : ∀ i, ∀ s, 1 ≤ s → deriv (fun s => X s i) s = 0 := by
    intro i s hs
    have h1 : HasDerivAt (fun t => x t i) (deriv (fun t => x t i) (uu a b s)) (uu a b s) :=
      ((coord_contDiff hx i).differentiable one_ne_zero _).hasDerivAt
    have h2 : HasDerivAt (uu a b) ((b - a) * deriv Real.smoothTransition s) s :=
      (((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero s).hasDerivAt.const_mul
        (b - a)).const_add a
    show deriv ((fun t => x t i) ∘ uu a b) s = 0
    rw [(h1.comp s h2).deriv, deriv_st s hs]; simp
  have hdZ : ∀ i s, deriv (fun s => Z s i) s
      = deriv (fun s => X s i) s + deriv (fun s => Y s i) s := by
    intro i s
    have hXi := ((coord_contDiff hX i).differentiable one_ne_zero s).hasDerivAt
    have hYi := ((coord_contDiff hY i).differentiable one_ne_zero s).hasDerivAt
    have := (hXi.add hYi).sub_const (x b i)
    show deriv (fun s => X s i + Y s i - x b i) s = _
    exact this.deriv
  have h01 : lineIntegral F Z 0 1 = lineIntegral F X 0 1 := by
    unfold lineIntegral
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    dsimp only
    rw [hZX s hs.2]
    exact Finset.sum_congr rfl fun i _ => by rw [hdZ, hdY i s hs.2, add_zero]
  have h12 : lineIntegral F Z 1 2 = lineIntegral F Y 1 2 := by
    unfold lineIntegral
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hs
    dsimp only
    rw [hZY s hs.1]
    exact Finset.sum_congr rfl fun i _ => by rw [hdZ, hdX i s hs.1, zero_add]
  have hsplit : lineIntegral F Z 0 2 = lineIntegral F Z 0 1 + lineIntegral F Z 1 2 := by
    rw [li_eq, li_eq, li_eq]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((integrand_cont hF hZ).intervalIntegrable _ _)
      ((integrand_cont hF hZ).intervalIntegrable _ _)).symm
  have hXr : lineIntegral F X 0 1 = lineIntegral F x a b := by
    rw [reparam hF hx (uu_cd a b)]
    simp only [uu, Real.smoothTransition.zero, Real.smoothTransition.one, mul_zero, add_zero,
      mul_one, add_sub_cancel]
  have hYr : lineIntegral F Y 1 2 = lineIntegral F y c d := by
    rw [reparam hF hy hv]
    simp only [v, uu, show (2 : ℝ) - 1 = 1 by norm_num, sub_self, Real.smoothTransition.zero,
      Real.smoothTransition.one, mul_zero, add_zero, mul_one, add_sub_cancel]
  refine ⟨Z, hZ, ?_, ?_, ?_⟩
  · rw [hZX 0 (by norm_num)]
    show x (uu a b 0) = x a
    simp only [uu, Real.smoothTransition.zero, mul_zero, add_zero]
  · rw [hZY 2 (by norm_num)]
    show y (uu c d (2 - 1)) = y d
    simp only [uu, show (2 : ℝ) - 1 = 1 by norm_num, Real.smoothTransition.one, mul_one,
      add_sub_cancel]
  · rw [hsplit, h01, h12, hXr, hYr]

theorem reverse {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : Continuous F)
    (y : ℝ → (Fin n → ℝ)) (hy : ContDiff ℝ 1 y) (c d : ℝ) :
    lineIntegral F (fun s => y (c + d - s)) c d = -lineIntegral F y c d := by
  rw [reparam hF hy (u := fun s => c + d - s) (contDiff_const.sub contDiff_id)]
  simp only [add_sub_cancel_right, add_sub_cancel_left]
  rw [li_eq, li_eq, intervalIntegral.integral_symm]

theorem fwd {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : Continuous F)
    (hclosed : ∀ (x : ℝ → (Fin n → ℝ)) (a b : ℝ), a ≤ b → ContDiff ℝ 1 x → x a = x b →
        lineIntegral F x a b = 0)
    (x y : ℝ → (Fin n → ℝ)) (a b c d : ℝ)
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (hac : x a = y c) (hbd : x b = y d) :
    lineIntegral F x a b = lineIntegral F y c d := by
  have hy' : ContDiff ℝ 1 (fun s => y (c + d - s)) := hy.comp (contDiff_const.sub contDiff_id)
  obtain ⟨Z, hZ, hZ0, hZ2, hZI⟩ := concat hF x (fun s => y (c + d - s)) a b c d hx hy'
    (by show x b = y (c + d - c); rw [add_sub_cancel_left]; exact hbd)
  have h0 := hclosed Z 0 2 (by norm_num) hZ
    (by rw [hZ0, hZ2]; show x a = y (c + d - d); rw [add_sub_cancel_right]; exact hac)
  rw [hZI, reverse hF y hy c d] at h0
  linarith

end Ag4Aux_VCGrad

theorem solution {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : Continuous F)
    (hclosed : ∀ (x : ℝ → (Fin n → ℝ)) (a b : ℝ), a ≤ b → ContDiff ℝ 1 x → x a = x b →
      lineIntegral F x a b = 0) (y : Fin n → ℝ) :
    grad (fun z => lineIntegral F (fun t => t • z) 0 1) y = F y := by
  funext i
  show deriv (fun s : ℝ => lineIntegral F (fun t => t • Function.update y i s) 0 1) (y i) = F y i
  have hray : ∀ z : Fin n → ℝ, ContDiff ℝ 1 (fun t : ℝ => t • z) :=
    fun z => contDiff_id.smul contDiff_const
  have hγ : ContDiff ℝ 1 (fun σ : ℝ => Function.update y i σ) := by
    rw [contDiff_pi]; intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact contDiff_id
    · simp only [Function.update_of_ne hj]; exact contDiff_const
  have hderivγ : ∀ σ j, deriv (fun σ => Function.update y i σ j) σ = if j = i then 1 else 0 := by
    intro σ j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self, if_true]; exact deriv_id σ
    · simp only [Function.update_of_ne hj, if_neg hj]; exact deriv_const σ _
  have hLIγ : ∀ p q, lineIntegral F (fun σ => Function.update y i σ) p q
      = ∫ σ in p..q, F (Function.update y i σ) i := by
    intro p q
    unfold lineIntegral
    congr 1; funext σ
    simp only [hderivγ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : ∀ s, lineIntegral F (fun t => t • Function.update y i s) 0 1
      = lineIntegral F (fun t => t • y) 0 1 + ∫ σ in y i..s, F (Function.update y i σ) i := by
    intro s
    have hu : ContDiff ℝ 1 (fun t : ℝ => y i + t * (s - y i)) :=
      contDiff_const.add (contDiff_id.mul contDiff_const)
    have hseg : ContDiff ℝ 1 (fun t : ℝ => Function.update y i (y i + t * (s - y i))) :=
      hγ.comp hu
    obtain ⟨Z, hZ, hZ0, hZ2, hZI⟩ := Ag4Aux_VCGrad.concat hF (fun t : ℝ => t • y)
      (fun t : ℝ => Function.update y i (y i + t * (s - y i))) 0 1 0 1 (hray y) hseg
      (by simp)
    have hpi := Ag4Aux_VCGrad.fwd hF hclosed (fun t => t • Function.update y i s) Z 0 1 0 2
      (hray _) hZ (by rw [hZ0]; simp) (by rw [hZ2]; simp)
    rw [hpi, hZI]
    congr 1
    rw [Ag4Aux_VCGrad.reparam hF hγ hu]
    simp only [zero_mul, add_zero, one_mul, add_sub_cancel]
    exact hLIγ _ _
  have hfun : (fun s : ℝ => lineIntegral F (fun t => t • Function.update y i s) 0 1)
      = fun s => lineIntegral F (fun t => t • y) 0 1
          + ∫ σ in y i..s, F (Function.update y i σ) i := funext key
  have hcont : Continuous (fun σ => F (Function.update y i σ) i) :=
    (continuous_apply i).comp (hF.comp hγ.continuous)
  rw [hfun, deriv_const_add, Continuous.deriv_integral _ hcont (y i) (y i)]
  simp
