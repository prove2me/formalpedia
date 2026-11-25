-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.continuous_Lc_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:49:42.1701+00:00
-- url     : https://prove2.me/submissions/09a46460-f417-407e-916c-c320fde324df

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution {X : Type*} [TopologicalSpace X] {f : X → E n} (hf : Continuous f) :
    Continuous fun x => Lc (f x) := by
  unfold Lc
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (((continuous_apply b).comp (continuous_apply a)).comp hf).smul
    (continuous_const : Continuous fun _ : X => Complex.ofRealCLM.comp (pr a b))
end PositivityTheory.Rg.Sw.WR.D
