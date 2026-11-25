-- Prove2me | solution 1 for P2M_GlobalTheory_BetaPos_bcWeight_nonneg__9ddd5f08771f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:19.305144+00:00
-- url     : https://prove2.me/submissions/8af99253-7b18-46ca-9f54-d72cbf8d71e0

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_BetaSelfReNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset MeasureTheory
open GlobalTheory GlobalTheory.BetaPos
namespace GlobalTheory.BetaPos
theorem _root_.solution (k r : ℕ) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl
end GlobalTheory.BetaPos
