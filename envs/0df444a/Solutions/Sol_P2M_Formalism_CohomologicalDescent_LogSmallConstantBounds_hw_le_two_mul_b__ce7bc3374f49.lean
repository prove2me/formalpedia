-- Prove2me | solution 1 for P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_hw_le_two_mul_b__ce7bc3374f49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:24.486263+00:00
-- url     : https://prove2.me/submissions/47b15ddf-c4be-4c14-a21c-1d15ad9e44a7

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsThin_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι} (hW : D.Widths P)
    {τ : ι} (hτ : τ ∉ D.T2) : D.hw τ ≤ 2 * P.b' := by
  have htop := G.top_le
  have hth := (paramsThin_holds P H G).2
  have hb' := H.b'_pos
  have hx := H.x_ge
  have hxinv : 0 ≤ P.b' / P.x := div_nonneg hb'.le (by linarith)
  have hxinv2 : 0 ≤ P.b' / P.x ^ 2 := div_nonneg hb'.le (by positivity)
  have htopE : P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) = P.b' + P.b' / P.x + P.b' / P.x ^ 2 := by ring
  rcases hW τ hτ with h | h <;> linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
