-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.dbar_sq_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:08.965994+00:00
-- url     : https://prove2.me/submissions/f3c57879-f470-42f5-97ab-6cc81f7fb935

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_DerivSmoothTransitionOfOneLt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (e : M → ℝ) (he : SmoothR n z e) (x : M) :
    dbarSq n z (fun y => (k (e y) : ℂ)) x = deriv k (e x) ^ 2 * dbarSq n z (fun y => (e y : ℂ)) x := by
  unfold dbarSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold db
  split_ifs with h
  · obtain ⟨hc1, hc2⟩ := Classical.choose_spec h
    set c := Classical.choose h
    have hy : z x ∈ c.target := by rw [hc1 hc2]; exact c.map_source hc2
    have hE : DifferentiableAt ℝ ((fun y => (e y : ℂ)) ∘ c.symm) (z x) :=
      ((he c hc1).differentiableOn (by simp)).differentiableAt (c.open_target.mem_nhds hy)
    obtain ⟨r, hr⟩ : ∃ r : V n → ℝ, r = fun y => (((fun y => (e y : ℂ)) ∘ c.symm) y).re :=
      ⟨_, rfl⟩
    have hR : DifferentiableAt ℝ r (z x) := by
      rw [hr]; exact Complex.reCLM.differentiableAt.comp _ hE
    have hK : (fun y => ((k (e y) : ℝ) : ℂ)) ∘ c.symm = Complex.ofRealCLM ∘ (k ∘ r) := by
      funext y; simp [hr]
    have hG : (fun y => ((e y : ℝ) : ℂ)) ∘ c.symm = Complex.ofRealCLM ∘ r := by
      funext y; simp [hr]
    have hrx : r (z x) = e x := by simp [hr, hc1 hc2, c.left_inv hc2]
    have hk' : HasDerivAt k (deriv k (e x)) (r (z x)) := by
      rw [hrx]
      exact ((hk.differentiable (by simp)) (e x)).hasDerivAt
    have hd1 := Complex.ofRealCLM.hasFDerivAt.comp (z x) (hk'.comp_hasFDerivAt (z x) hR.hasFDerivAt)
    have hd2 := Complex.ofRealCLM.hasFDerivAt.comp (z x) hR.hasFDerivAt
    rw [hK, hG]
    unfold wdb
    rw [hd1.fderiv, hd2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.ofRealCLM_apply]
    rw [show ∀ a b c' : ℝ, (((a * b : ℝ) : ℂ) + Complex.I * ((a * c' : ℝ) : ℂ)) / 2 =
        (a : ℂ) * (((b : ℂ) + Complex.I * (c' : ℂ)) / 2) from fun a b c' => by push_cast; ring]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · simp
end ReciprocityTheory.L2DbarEstimates.F
