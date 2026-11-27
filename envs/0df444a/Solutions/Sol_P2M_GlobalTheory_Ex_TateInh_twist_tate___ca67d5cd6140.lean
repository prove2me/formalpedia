-- Prove2me | solution 1 for P2M_GlobalTheory_Ex_TateInh_twist_tate___ca67d5cd6140
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:50.688695+00:00
-- url     : https://prove2.me/submissions/eff0fe3b-01b8-4425-856c-fe4a7680bebd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh
namespace GlobalTheory.Ex.TateInh
theorem _root_.solution (q u : Oˣ) (k : ℕ) (hk : k ≠ 0) (n : ℤ) :
    ((tate q).twist (tateBe q k hk) u).ψ n = (tate (q * u ^ k)).ψ n := by
  change q ^ n ^ 2 * u ^ ((2 * k : ℤ) * (n * n) / 2) = (q * u ^ k) ^ n ^ 2
  rw [mul_assoc, Int.mul_ediv_cancel_left _ two_ne_zero, mul_zpow, ← zpow_natCast, ← zpow_mul, sq]
end GlobalTheory.Ex.TateInh
