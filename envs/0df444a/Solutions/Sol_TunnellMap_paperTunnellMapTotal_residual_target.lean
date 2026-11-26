-- Prove2me | solution 1 for TunnellMap.paperTunnellMapTotal_residual_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:15:50.804739+00:00
-- url     : https://prove2.me/submissions/83acf1ed-837b-4371-b053-08867bbd8511

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
import Theorems.Thm_TunnellMap_residual_orbit_card_eq
import Theorems.Thm_TunnellMap_some_paperTunnellMapTotal


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0) (hd : ¬ SourceUsedTriple p.1) :
    ¬ DirectTargetUsed (paperTunnellMapTotal hn hnpos hsq hbal p) := by
  classical
  set q : BOddRep n := ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩ with hq
  set x : BResidual n := ⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩ with hx
  have hcard := residual_orbit_card_eq hn hnpos
    (odd_card_eq_of_full_balance (fintype_balance_of_nat_card hbal))
  have hres := RecordDA.residualMapExecOpt_eq_some hn hnpos hsq hcard x
  have hopt : paperTunnellMapExecOpt hnpos hsq p =
      some (canonicalResidualMapOf hnpos
        (residualOrbitMatching hnpos hcard) x).1 := by
    rw [paperTunnellMapExecOpt, dif_neg hz]
    change oddMapExecOpt hnpos hsq q = _
    rw [oddMapExecOpt, dif_neg hd, hres]
    rfl
  have hval : paperTunnellMapTotal hn hnpos hsq hbal p =
      (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x).1 :=
    Option.some.inj
      ((some_paperTunnellMapTotal hn hnpos hsq hbal p).trans hopt)
  rw [hval]
  exact (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x).2
end TunnellMap
