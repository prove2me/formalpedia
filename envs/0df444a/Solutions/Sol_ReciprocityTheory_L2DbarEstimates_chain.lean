-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:31:15.509798+00:00
-- url     : https://prove2.me/submissions/92cc7716-6357-4f83-a15f-867d5ca2ed41

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_Imports
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_eq_leviV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates
open Filter Topology
private theorem wd_wdb_ofReal_comp_of_differentiableAt {n : ℕ} {φ : ℝ → ℝ} {u : V n → ℝ} {y : V n}
    (hφ : DifferentiableAt ℝ φ (u y)) (hu : DifferentiableAt ℝ u y) (j : Fin n) :
    wd n j (fun w => (φ (u w) : ℂ)) y = ((deriv φ (u y) : ℝ) : ℂ) * wd n j (fun w => (u w : ℂ)) y ∧
      wdb n j (fun w => (φ (u w) : ℂ)) y = ((deriv φ (u y) : ℝ) : ℂ) * wdb n j (fun w => (u w : ℂ)) y := by
  have h1 : HasFDerivAt (fun w => (φ (u w) : ℂ))
      (Complex.ofRealCLM.comp (deriv φ (u y) • fderiv ℝ u y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y (hφ.hasDerivAt.comp_hasFDerivAt y hu.hasFDerivAt)
  have h2 : HasFDerivAt (fun w => (u w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hu.hasFDerivAt
  constructor <;>
    simp only [wd, wdb, h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_mul] <;> ring
private theorem wdb_ofReal_eq_conj_wd_ofReal {n : ℕ} {u : V n → ℝ} {y : V n} (hu : DifferentiableAt ℝ u y) (j : Fin n) :
    wdb n j (fun w => (u w : ℂ)) y = (starRingEnd ℂ) (wd n j (fun w => (u w : ℂ)) y) := by
  have h2 : HasFDerivAt (fun w => (u w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hu.hasFDerivAt
  simp only [wd, wdb, h2.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, map_div₀,
    map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring
private theorem wd_mul_apply {n : ℕ} {p q : V n → ℂ} {y : V n} (hp : DifferentiableAt ℝ p y)
    (hq : DifferentiableAt ℝ q y) (j : Fin n) :
    wd n j (fun w => p w * q w) y = wd n j p y * q y + p y * wd n j q y := by
  have hF : fderiv ℝ (fun w => p w * q w) y = p y • fderiv ℝ q y + q y • fderiv ℝ p y :=
    (hp.hasFDerivAt.mul hq.hasFDerivAt).fderiv
  simp only [wd, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
private theorem differentiableAt_wdb_of_contDiffAt_two {n : ℕ} {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (k : Fin n) :
    DifferentiableAt ℝ (wdb n k g) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by norm_num)
  have hb : ∀ u : V n, DifferentiableAt ℝ (fun v => fderiv ℝ g v u) y := fun u =>
    (h1.clm_apply contDiffAt_const).differentiableAt one_ne_zero
  have := ((hb (bas n k)).add ((hb (Complex.I • bas n k)).const_mul Complex.I)).mul_const (2⁻¹ : ℂ)
  unfold wdb
  simp only [div_eq_mul_inv]
  exact this
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] : ChainStatement n M := by
  intro z hz φ v hφ hv x ξ
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hT : e.target ∈ 𝓝 (z x) := by
    rw [he hx]; exact e.open_target.mem_nhds (e.map_source hx)
  have hx' : e.symm (z x) = x := by rw [he hx, e.left_inv hx]
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ((v (e.symm y) : ℝ) : ℂ)) e.target := hv e he
  have hur : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => v (e.symm y)) e.target := by
    have := Complex.reCLM.contDiff.comp_contDiffOn hU
    exact this.congr fun y _ => by simp
  have hu2 : ∀ y ∈ e.target, ContDiffAt ℝ 2 (fun y => v (e.symm y)) y := fun y hy =>
    (contDiffOn_infty.1 hur 2).contDiffAt (e.open_target.mem_nhds hy)
  have hud : ∀ y ∈ e.target, DifferentiableAt ℝ (fun y => v (e.symm y)) y := fun y hy =>
    (hu2 y hy).differentiableAt (by simp)
  have hz0 : z x ∈ e.target := mem_of_mem_nhds hT
  have hU2 : ContDiffAt ℝ 2 (fun y => ((v (e.symm y) : ℝ) : ℂ)) (z x) :=
    (contDiffOn_infty.1 hU 2).contDiffAt hT
  have hφ1 : ContDiff ℝ 1 (deriv φ) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 (by rw [one_add_one_eq_two]; exact hφ)).2.2
  have hφd : ∀ t, DifferentiableAt ℝ φ t := fun t => hφ.differentiable (by simp) t
  have hφ1d : ∀ t, DifferentiableAt ℝ (deriv φ) t := fun t => hφ1.differentiable one_ne_zero t
  have ev : ∀ l, wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ)) =ᶠ[𝓝 (z x)]
      fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ) * wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) y := by
    intro l
    filter_upwards [hT] with y hy
    exact (wd_wdb_ofReal_comp_of_differentiableAt (hφd _) (hud y hy) l).2
  have key : ∀ j l, wd n j (wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ))) (z x) =
      ((deriv φ (v (e.symm (z x))) : ℝ) : ℂ) * wd n j (wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ))) (z x) +
        ((deriv (deriv φ) (v (e.symm (z x))) : ℝ) : ℂ) *
          (wd n j (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x) *
            (starRingEnd ℂ) (wd n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x))) := by
    intro j l
    have e1 : wd n j (wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ))) (z x) =
        wd n j (fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ) *
          wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) y) (z x) := by
      simp only [wd, (ev l).fderiv_eq]
    have hp : DifferentiableAt ℝ (fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ)) (z x) :=
      Complex.ofRealCLM.differentiableAt.comp (z x) ((hφ1d _).comp (z x) (hud _ hz0))
    rw [e1, wd_mul_apply hp (differentiableAt_wdb_of_contDiffAt_two hU2 l) j, (wd_wdb_ofReal_comp_of_differentiableAt (hφ1d _) (hud _ hz0) j).1, ← wdb_ofReal_eq_conj_wd_ofReal (hud _ hz0) l]
    try beta_reduce
    ring
  have hdd : dDot n z (fun y => (v y : ℂ)) x ξ =
      ∑ j, wd n j (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x) * ξ j := by
    unfold dDot
    exact Finset.sum_congr rfl fun j _ => by rw [d_eq_wd n z e he j _ x hx]; rfl
  rw [levi_eq_leviV n z e he _ x hx ξ, levi_eq_leviV n z e he v x hx ξ, hdd, Complex.sq_norm,
    ← Complex.mul_conj]
  unfold leviV
  try beta_reduce
  simp only [key, hx']
  rw [map_sum]
  simp only [map_mul]
  rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
end ReciprocityTheory.L2DbarEstimates
