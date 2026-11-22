-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.derived_endpoint_bounds
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:47:07.464453+00:00
-- url     : https://prove2.me/submissions/bdb2a946-7632-40ab-b86b-c91d5f739cf6

import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
theorem solution (x : World) (g : Rules) (s : Sane x g) (hn : 0< x.n) (v : ℕ) (u : Word) (d : Derives x.k g v u) :
    (∀j w,0≤ u j w ∧ u j w<(x.n:ℤ)) ∧ ∀j,g.len v≤ j → ∀w,u j w=0 := by
  induction d with
  | leaf ar nf =>
    constructor
    · intro j w;unfold atomWord;split
      · exact s.2 _ _ _
      · omega
    · intro j hj w;exact if_neg (by omega)
  | join ar yes h dl dr il ir =>
    obtain ⟨_,_,eq⟩:=h
    constructor
    · intro j w;unfold appendWords;split
      · exact il.1 _ _
      · split
        · exact ir.1 _ _
        · omega
    · intro j hj w;unfold appendWords;rw [if_neg (by omega),if_neg (by omega)]
