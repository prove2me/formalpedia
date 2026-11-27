-- Prove2me | solution 1 for P2M_GlobalTheory_PhiGam_ModPG_linearIndependent___5ce28352564c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:51:08.972972+00:00
-- url     : https://prove2.me/submissions/07ad9157-de22-4d4c-aadd-1b4e52f20988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_P2M_GlobalTheory_PhiGam_ModPG_span___b6f5a61103e8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
variable [Module k V] {l n : ℕ} {R : RingPG k l}
namespace GlobalTheory.PhiGam
namespace ModPG
theorem _root_.solution (D : ModPG R n V) (i : ZMod n) {ι : Type} (b : Module.Basis ι k⸨X⸩ V) :
    LinearIndependent k⸨X⸩ fun j => D.φ i (b j) := by
  haveI := D.fin
  haveI := FiniteDimensional.fintypeBasisIndex b
  exact linearIndependent_of_top_le_span_of_card_eq_finrank (D.span_φ i b).ge
    (Module.finrank_eq_card_basis b).symm
end ModPG
end GlobalTheory.PhiGam
