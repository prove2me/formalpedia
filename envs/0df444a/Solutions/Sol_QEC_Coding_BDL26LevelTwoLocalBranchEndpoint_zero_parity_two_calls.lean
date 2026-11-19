-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.zero_parity_two_calls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:21.279627+00:00
-- url     : https://prove2.me/submissions/bff22a59-2435-4026-a976-dde2200474fd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (h : Error S) (s t : Syndrome S)
    (hd : delta S h=s+t) (hp : parity S h=0)
    (hs : localSuccess S s) (ht : localSuccess S t) :
    ∃ p : Potential S, boundary S p=h+D S s+D S t := by
  obtain ⟨ws,hws⟩ := hs
  obtain ⟨wt,hwt⟩ := ht
  obtain ⟨hls,hds⟩ := returned_local_and_syndrome S s ws hws
  obtain ⟨hlt,hdt⟩ := returned_local_and_syndrome S t wt hwt
  obtain ⟨a,ha⟩ := parity_local_label S (D S s) hls (levelOneQDefault S)
  obtain ⟨b,hb⟩ := parity_local_label S (D S t) hlt (levelOneQDefault S)
  have hc : delta S (h+D S s+D S t)=0 := by
    rw [map_add,map_add,hd,hds,hdt]
    calc
      _ = (s+s)+(t+t) := by abel
      _ = 0 := by rw [twice,twice,add_zero]
  have hsup : ∀ q, parity S (h+D S s+D S t) q≠0 → q=a ∨ q=b := by
    intro q hq
    by_contra hn
    apply hq
    have hqa : q≠a := fun heq => hn (Or.inl heq)
    have hqb : q≠b := fun heq => hn (Or.inr heq)
    calc
      parity S (h+D S s+D S t) q=
          parity S (h+D S s) q+parity S (D S t) q :=
        congrFun (parity_add S (h+D S s) (D S t)) q
      _ = (parity S h q+parity S (D S s) q)+parity S (D S t) q := by
        have hmap := congrFun (parity_add S h (D S s)) q
        change parity S (h+D S s) q=parity S h q+parity S (D S s) q at hmap
        exact congrArg (fun value : Bit => value+parity S (D S t) q) hmap
      _ = 0 := by rw [hp,Pi.zero_apply,ha q hqa,hb q hqb,zero_add,zero_add]
  exact two_parity_endpoint S _ hc a b hsup
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
