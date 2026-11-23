-- Prove2me | solution 1 for StableMSR.Recovery.SingleCodes.finite_ball_word_menu_exact
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:55.829881+00:00
-- url     : https://prove2.me/submissions/04883c0e-c417-4f14-8e55-5724d983c6ec

import Definitions.Def_StableMSR_SingleWindowCodes
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.Supplement
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleCodes StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
private lemma unpair (h g u : ℕ) (small : g< h+1) : encode h g u%(h+1)=g ∧ encode h g u/(h+1)=u:=by
  unfold encode
  constructor
  · simp [Nat.add_mod,Nat.mod_eq_of_lt small]
  · rw [Nat.mul_comm u _,Nat.mul_add_div (by omega),Nat.div_eq_of_lt small,Nat.add_zero]
theorem solution (x : World) (W : Cluster x.n) (h : ℕ) (P : Partition x.n) :
    P∈traceMenu x h W ↔ ∃c∈SingleCodes.menu x W h,SingleCodes.decode x W h c=P := by
  classical
  constructor
  · intro hp;obtain ⟨hp,yes⟩:=Finset.mem_filter.mp hp
    obtain ⟨⟨g,u⟩,gu,eq⟩:=Finset.mem_image.mp hp
    obtain ⟨gh,ur⟩:=Finset.mem_product.mp gu
    have z:=unpair h g u (Finset.mem_range.mp gh)
    have dec : SingleCodes.decode x W h (encode h g u)=P:=by simpa only [SingleCodes.decode,z.1,z.2] using eq
    refine ⟨encode h g u,List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨g,List.mem_range.mpr (Finset.mem_range.mp gh),List.mem_map.mpr ⟨u,List.mem_range.mpr (Finset.mem_range.mp ur),rfl⟩⟩,?_⟩,dec⟩
    simpa only [dec,decide_eq_true_eq] using yes
  · rintro ⟨c,hc,rfl⟩;obtain ⟨hw,yes⟩:=List.mem_filter.mp hc
    obtain ⟨g,hg,cu⟩:=List.mem_flatMap.mp hw
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp cu
    have z:=unpair h g u (List.mem_range.mp hg)
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(g,u),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (List.mem_range.mp hg),Finset.mem_range.mpr (List.mem_range.mp hu)⟩,?_⟩,of_decide_eq_true yes⟩
    simp only [SingleCodes.decode,z.1,z.2]
