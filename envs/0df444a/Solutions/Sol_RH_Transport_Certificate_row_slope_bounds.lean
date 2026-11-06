-- Prove2me | solution 1 for RH.Transport.Certificate.row_slope_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:11.583415+00:00
-- url     : https://prove2.me/submissions/65b0333f-0106-4126-8a28-2d67e68aebc8

import Definitions.Def_Transport_Candidate
import Definitions.Def_Transport_Endpoint
import Definitions.Def_Transport_Certificate
import Theorems.Thm_RH_Transport_Certificate_adaptive_count_bounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.Certificate
noncomputable section
namespace RH.Transport.Certificate
theorem _root_.solution {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    0 ≤ rowSlope δ x ∧ rowSlope δ x ≤ 2 := by
  obtain ⟨hlo, hhi⟩ := adaptive_count_bounds hdlo hdhi hxlo hxhi
  unfold rowSlope
  constructor <;> linarith
end RH.Transport.Certificate
