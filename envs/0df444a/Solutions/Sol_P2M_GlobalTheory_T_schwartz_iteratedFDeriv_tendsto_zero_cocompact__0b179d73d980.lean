-- Prove2me | solution 1 for P2M_GlobalTheory_T_schwartz_iteratedFDeriv_tendsto_zero_cocompact__0b179d73d980
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:10.420815+00:00
-- url     : https://prove2.me/submissions/17c6195b-5d78-45dd-a3c3-af07a00323d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIteratedFDerivTendstoZeroCocompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIteratedFDerivTendstoZeroCocompactStatement
import Theorems.Thm_GlobalTheory_schwartz_iteratedFDeriv_tendsto_zero_cocompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (j : ℕ), Tendsto (fun z => iteratedFDeriv ℝ j f z) (cocompact E) (𝓝 0) := by
  first | exact @GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact | exact GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact | (intros; apply GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact <;> assumption)
end _root_.GlobalTheory.T
