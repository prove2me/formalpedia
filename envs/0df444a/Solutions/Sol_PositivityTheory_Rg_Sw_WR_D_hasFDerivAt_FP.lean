-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.hasFDerivAt_FP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:26.689056+00:00
-- url     : https://prove2.me/submissions/24c86984-0322-4071-b8bc-6fb2d49188f5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_Fi
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_Fd
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_integrable_Fi
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_integrable_bnd
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_norm_Fd_le
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_hasFDerivAt_Fi

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
variable (ε : Fin m → Bool) (c t : ℝ)
variable {ε c t}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    HasFDerivAt (FP ε c t P) (∫ x, Fd ε c t P y x) y := by
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun y x => Fi ε c t P y x)
    (F' := fun y x => Fd ε c t P y x) (x₀ := y) (bound := bnd ε c t P) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun y' => (continuous_Fi hq P y').aestronglyMeasurable) (integrable_Fi hI hq hc P y)
    (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x y' _ => norm_Fd_le P y' x)
    (integrable_bnd hI hc P) (ae_of_all _ fun x y' _ => hasFDerivAt_Fi P y' x)
  exact this
end PositivityTheory.Rg.Sw.WR.D
