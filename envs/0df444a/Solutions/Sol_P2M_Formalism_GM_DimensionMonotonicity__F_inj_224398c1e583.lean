-- Prove2me | solution 1 for P2M_Formalism_GM_DimensionMonotonicity__F_inj_224398c1e583
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:00.707623+00:00
-- url     : https://prove2.me/submissions/fc3b70d4-5ce2-4d15-b802-00956be7820e

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f

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
theorem _root_.solution [NeZero N] {K : ℕ} (hK : K + 1 ≤ N) : Function.Injective (ιF N K) := by
  intro a b h
  apply Fin.ext
  rw [← ιF_val hK a, ← ιF_val hK b, h]
end Formalism.GM.DimensionMonotonicity
