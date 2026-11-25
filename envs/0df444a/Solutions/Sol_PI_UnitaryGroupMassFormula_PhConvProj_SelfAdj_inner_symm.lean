-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.inner_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:56.320848+00:00
-- url     : https://prove2.me/submissions/0cb8a7c3-2b6f-4955-a6ec-b4bc29191089

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhConvProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_SelfAdj
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_SelfAdj_inner_map_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
open PI.PhConvProj
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
namespace PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
theorem _root_.solution [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant] (ph : G → ℂ) (hph : ∀ g, ph g⁻¹ = star (ph g))
    {π : G → (K →L[ℂ] K)} (hπ : IsURep π) {T : K →L[ℂ] K} (hT : IsOpInt μ π ph T) (x y : K) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have h1 : ⟪T x, y⟫_ℂ = ∫ g, ph g⁻¹ * ⟪x, π g⁻¹ y⟫_ℂ ∂μ := by
    rw [← inner_conj_symm, hT y x, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, inner_conj_symm, hph g]
    rw [(inner_map_left hπ)]
    rfl
  rw [h1, hT x y]
  exact integral_inv_eq_self (fun g => ph g * ⟪x, π g y⟫_ℂ) μ
end PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
