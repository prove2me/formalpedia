-- Prove2me | solution 1 for P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__mem_Isub_9bd49289c361
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:06.209733+00:00
-- url     : https://prove2.me/submissions/ead9f7bf-6b6b-4c49-a264-29c52e300a7d

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_RightCasimirMemSubmodule
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_eta_mem_Isub
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_right_casimir_mem_submodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh
variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}
namespace CompanionTheory.RgExh.Hk.UnitPf
theorem _root_.solution {H} (h : H ∈ Isub X) : Om' X H ∈ Isub X := by
  simp only [Om', LinearMap.add_apply, LinearMap.comp_apply]
  exact add_mem (right_casimir_mem_submodule h) (eta_mem_Isub _)
end CompanionTheory.RgExh.Hk.UnitPf
