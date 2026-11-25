-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_smul_mem_span_baseChange_1decc818f05e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:01.470909+00:00
-- url     : https://prove2.me/submissions/dc604e3b-cecf-480f-85a5-6d5cde896fa5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mem_chartRing_baseChange_9dea4a8b7af9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
open scoped Pointwise
noncomputable section
variable {S : Type*} [CommRing S] {O : Type*} [CommRing O] [Algebra S O] {Ω : Type*} [Field Ω]
  [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution {I : Chart x} (P : Set Ω) (a : chartRing S x I) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing O x I) P) : a • y ∈ Submodule.span (chartRing O x I) P := by
  have : a • y = (⟨(a : Ω), mem_chartRing_baseChange a.2⟩ : chartRing O x I) • y := by
    rw [chartRing_smul_def, chartRing_smul_def]
  rw [this]
  exact Submodule.smul_mem _ _ hy
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
