-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_monotone_56c5f6097949
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:58.995916+00:00
-- url     : https://prove2.me/submissions/35e5beeb-bfb0-47da-9395-f5068ee4610c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegMassMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SliceCut
theorem _root_.solution {n : ℕ} (h : HermNorm n) (x : Fin n → ℂ) : Monotone fun k => sliceCut h k x := by
  intro k m hkm
  simp only [sliceCut]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkm 1
  rcases le_or_gt 0 (Real.log (h.dualNorm x)) with hL | hL
  · apply Real.smoothTransition.monotone
    have := div_le_div_of_nonneg_left hL hk hkm'
    linarith
  · have h1 : ∀ j : ℕ, Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((j : ℝ) + 1)) = 1 := fun j =>
      Real.smoothTransition.one_of_one_le (by
        have : Real.log (h.dualNorm x) / ((j : ℝ) + 1) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hL.le (by positivity)
        linarith)
    rw [h1 k, h1 m]
end SliceCut
end GroundTheory.Heights₂.Heights
