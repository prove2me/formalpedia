-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Be2.ker_ainfTower_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:01:32.248013+00:00
-- url     : https://prove2.me/submissions/91afeeb0-dc12-4c91-ad20-cfba85636b28

import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_SurjectiveAinfTowerZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
namespace ReciprocityTheory.PGsh.Be2
theorem _root_.solution : RingHom.ker ((ainfTowerL p O hv ε hε).q 0).1 =
    Ideal.span {((p : ℕ) : ((ainfTowerL p O hv ε hε).O : Type))} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  have hq : ((ainfTowerL p O hv ε hε).q 0).1 a =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ (0 + 1)}) a := rfl
  rw [hq]
  exact (Ideal.Quotient.eq_zero_iff_dvd _ _).trans (by rw [pow_one]; rfl)
end ReciprocityTheory.PGsh.Be2
