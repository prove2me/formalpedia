-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.kSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:42:32.974656+00:00
-- url     : https://prove2.me/submissions/0dad82e0-cba0-4e3d-acb0-e0904ceb2e41

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_KPsiHasCompactSupport
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_wvol_finiteOnCompacts
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_kPsi_inner
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_kPsi_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_kPsi_hasCompactSupport
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
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
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : KSubStatement n M := by
  unfold KSubStatement
  intro z hz ph₂ hph
  have : IsFiniteMeasureOnCompacts (wvol n z ph₂) := wvol_finiteOnCompacts n z hz ph₂ hph
  have hmem : ∀ φ, IsTest n z φ → ∀ j k, MemLp (kPsi n z ph₂ φ j k) 2 (wvol n z ph₂) :=
    fun φ hφ j k => (kPsi_continuous n z hz ph₂ hph φ hφ j k).memLp_of_hasCompactSupport
      (kPsi_hasCompactSupport n z ph₂ φ hφ j k)
  have hmeas : Measurable fun x => ENNReal.ofReal (Real.exp (-ph₂ x)) :=
    (Real.continuous_exp.comp hph.neg).measurable.ennreal_ofReal

  have hw : ∀ g : M → ℂ, ∫ x, g x ∂wvol n z ph₂ =
      ∫ x, (ENNReal.ofReal (Real.exp (-ph₂ x))).toReal • g x ∂vol n z :=
    fun g => integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) g
  have key : ∀ φ (hφ : IsTest n z φ) j k (F : Lp (V n) 2 (wvol n z ph₂)),
      ⟪(hmem φ hφ j k).toLp (kPsi n z ph₂ φ j k), F⟫_ℂ =
        ∫ x, (F x k * db n z j φ x - F x j * db n z k φ x) ∂vol n z := by
    intro φ hφ j k F
    rw [MeasureTheory.L2.inner_def]
    have hae := (hmem φ hφ j k).coeFn_toLp
    rw [integral_congr_ae (g := fun x => ⟪kPsi n z ph₂ φ j k x, F x⟫_ℂ)
      (by filter_upwards [hae] with x hx; rw [hx]), hw]
    exact integral_congr_ae (ae_of_all _ fun x => kPsi_inner n z ph₂ φ j k (F x) x)
  refine ⟨⨅ (φ : M → ℂ) (hφ : IsTest n z φ) (j : Fin n) (k : Fin n),
      LinearMap.ker ((innerSL ℂ ((hmem φ hφ j k).toLp (kPsi n z ph₂ φ j k)) :
        Lp (V n) 2 (wvol n z ph₂) →L[ℂ] ℂ) : Lp (V n) 2 (wvol n z ph₂) →ₗ[ℂ] ℂ), ?_, ?_⟩
  · simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun φ => isClosed_iInter fun hφ => isClosed_iInter fun j =>
      isClosed_iInter fun k => ContinuousLinearMap.isClosed_ker _
  · intro F
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    unfold IsWeakS
    refine forall_congr' fun φ => forall_congr' fun hφ => forall_congr' fun j =>
      forall_congr' fun k => ?_
    beta_reduce
    rw [key φ hφ j k F]
    simp
end ReciprocityTheory.L2DbarEstimates.F
