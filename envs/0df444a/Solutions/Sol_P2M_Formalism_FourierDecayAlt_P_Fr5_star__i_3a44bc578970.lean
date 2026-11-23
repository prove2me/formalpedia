-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr5_star__i_3a44bc578970
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:52.384741+00:00
-- url     : https://prove2.me/submissions/b489d8dd-2229-4efe-9a2d-63d582350d6c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution {L : LevelData A r} (h : IsStarLevel L) : star L.ζi = L.ζbi := by
  have h' : star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT := h
  calc star L.ζi = star L.ζi * (L.ζb * L.ζbi) := by rw [L.ζb_ζbi, mul_one]
    _ = star (L.ζ * L.ζi) * L.ζbi := by rw [star_mul, h'.1, mul_assoc]
    _ = L.ζbi := by rw [L.ζ_ζi, star_one, one_mul]
end Formalism.FourierDecayAlt.P.Fr5
