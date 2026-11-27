-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.c_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:30:59.281015+00:00
-- url     : https://prove2.me/submissions/93787d62-ef8d-4e39-bc05-bc9ff2fea951

import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_c_val

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
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution (c' : O) (h : v (algebraMap O C c') ^ (p - 1) ≤ v (p : C)) :
    fontaineTheta O p (nu p O ε) ∣ c' := by
  apply hv.dvd_of_le
  rw [← c_val p O hv ε hε] at h
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  exact (pow_le_pow_iff_left₀ zero_le zero_le hp1).1 h
end ReciprocityTheory.PGsh.Ainf
