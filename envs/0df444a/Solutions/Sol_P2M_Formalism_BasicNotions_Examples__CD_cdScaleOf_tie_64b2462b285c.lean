-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_tie_64b2462b285c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:13:02.78919+00:00
-- url     : https://prove2.me/submissions/959fa613-e0a9-408a-8a14-ac6d2032d5f5

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_phi_cont_8ff9fa0bcb35
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_preimage_phi_e3189524c6f0
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_spec_07daed5ec9cb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
variable (C : CDHaar)
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (A : Set (UJ ε)) (hA : MeasurableSet A) :
    ((cdScaleOf C n ε : ℝ≥0∞) • muG ε) A =
      C.cd P Q {g | ∃ a ∈ A, ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.reindex e e (UpqT.mat g)} := by
  rw [← preimage_phi ε e h1 h2 A, ← Measure.map_apply (phi_cont ε e h1 h2).measurable hA,
    (cdScaleOf_spec C ε e h1 h2).2]
  rfl
end Formalism.BasicNotions.Examples₂.CD
