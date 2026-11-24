-- Prove2me | solution 1 for P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:02.171143+00:00
-- url     : https://prove2.me/submissions/ec08b674-1b4c-4672-b6d8-0d0c7a41a293

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero N] {K : ℕ} (hK : K + 1 ≤ N) (a : Fin (K + 1)) : ((ιF N K a) : ℕ) = a := by
  unfold ιF
  split_ifs with h
  · rfl
  · exact absurd (lt_of_lt_of_le a.isLt hK) h
end Formalism.GM.DimensionMonotonicity
