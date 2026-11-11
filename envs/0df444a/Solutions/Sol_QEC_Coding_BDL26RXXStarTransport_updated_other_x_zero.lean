-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.updated_other_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:20:32.487737+00:00
-- url     : https://prove2.me/submissions/7d4cda31-9ea4-4b17-a86a-2622f1b51a8b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_updated_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_updated_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_starQ
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_x_q_disjoint
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.mem_starQ



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXXStarTransport
theorem _root_.solution (x y : XCoord S i) (hy : y≠x) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (updated S depth i h a b)=0 := by
  funext p
  apply zero_off_support _ _ (updated_supported S depth i h x a b he) p.val
  intro hp
  rcases Finset.mem_union.mp hp with hpx | hpq
  · exact (Finset.disjoint_left.mp
      ((rxData S depth i h).cx_correction_regions_pairwise_disjoint y x hy)) p.property hpx
  · obtain ⟨q,_,hq⟩ := (mem_starQ S depth i h x p.val).mp hpq
    exact (Finset.disjoint_left.mp (x_q_disjoint S depth i h y q)) p.property hq
end QEC.Coding.BDL26RXXStarTransport
