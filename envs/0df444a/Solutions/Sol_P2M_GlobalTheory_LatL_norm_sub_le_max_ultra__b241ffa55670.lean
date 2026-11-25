-- Prove2me | solution 1 for P2M_GlobalTheory_LatL_norm_sub_le_max_ultra__b241ffa55670
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:31:51.185323+00:00
-- url     : https://prove2.me/submissions/e09849ca-5a12-4b1d-9795-69d484467025

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormSubLeMaxUltra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.LatL
namespace GlobalTheory.LatL
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _
end GlobalTheory.LatL
