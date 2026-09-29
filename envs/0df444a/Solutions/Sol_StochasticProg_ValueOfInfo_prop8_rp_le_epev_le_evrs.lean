-- Prove2me | solution 1 for StochasticProg.ValueOfInfo.prop8_rp_le_epev_le_evrs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T04:09:15.797264+00:00
-- url     : https://prove2.me/submissions/3962e35d-4d10-4f89-9a7f-c265e3480a80

import Mathlib
import Definitions.Def_StochasticProg_ValueOfInfo_Instance
import Definitions.Def_StochasticProg_ValueOfInfo_RP

set_option autoImplicit false

open StochasticProg.ValueOfInfo in
theorem solution {n1 d K : ℕ} (I : Instance n1 d K)
    (xir : Fin d → ℝ) (hpr1 : refProb I xir < 1)
    (xBarK : Fin K → (Fin n1 → ℝ))
    (hxBarK_mem : ∀ k, xBarK k ∈ I.K1)
    (hxBarK_opt : ∀ k, badd ((refProb I xir : EReal) * I.z (xBarK k) xir)
        (((1 - refProb I xir : ℝ) : EReal) * I.z (xBarK k) (I.xi k)) =
        pairsValue I xir k)
    (xBarR : Fin n1 → ℝ) (hxBarR_mem : xBarR ∈ I.K1)
    (hxBarR_opt : I.z xBarR xir = ⨅ x ∈ I.K1, I.z x xir) :
    RP I ≤ EPEV I xBarK xBarR ∧ EPEV I xBarK xBarR ≤ EVRS I xBarR := by
  constructor
  · unfold EPEV RP
    refine le_min (le_iInf (fun k => ?_)) ?_
    · exact iInf₂_le (xBarK k) (hxBarK_mem k)
    · exact iInf₂_le xBarR hxBarR_mem
  · unfold EPEV EVRS
    exact min_le_right _ _
