-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_nullMeasurableSet_preimage_prod_48ed4e534389
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:58.089685+00:00
-- url     : https://prove2.me/submissions/7d1fc296-46fb-4a3a-a508-8d5ce621a186

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_preimage_univ_prod_19221bf5a91f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_preimage_prod_eq_c1495817f774
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_quasiMeasurePreserving_fst_comp_d334dff1b519

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
set_option linter.unusedSectionVars false
noncomputable section
variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
variable {Φ : G ≃ₜ* G₁ × G₂} {μ : Measure G} {V : Set G₂}
variable [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [μ.IsHaarMeasure]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (hV : IsOpen V) (hVc : IsCompact V) {A : Set G₁}
    (hA : NullMeasurableSet A (Measure.haar : Measure G₁)) :
    NullMeasurableSet (Φ ⁻¹' (A ×ˢ V)) μ := by
  rw [preimage_prod_eq]
  exact (nullMeasurableSet_restrict (measurableSet_preimage_univ_prod hV).nullMeasurableSet).1
    (hA.preimage (quasiMeasurePreserving_fst_comp hV hVc))
end GroundTheory.Heights₂.Heights.FiniteCovolume
