-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_null_3c91a03dca52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:56.912968+00:00
-- url     : https://prove2.me/submissions/0547fdfe-be85-4308-937c-42f4af85e3c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_eq_restrict_0ba29adf8ab5
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
theorem _root_.solution (hV : IsOpen V) (hVc : IsCompact V) {N : Set G₁}
    (hN : (Measure.haar : Measure G₁) N = 0) : μ (Φ ⁻¹' (N ×ˢ V)) = 0 := by
  rw [measure_preimage_prod_eq_restrict hV]
  exact (quasiMeasurePreserving_fst_comp hV hVc).preimage_null hN
end GroundTheory.Heights₂.Heights.FiniteCovolume
