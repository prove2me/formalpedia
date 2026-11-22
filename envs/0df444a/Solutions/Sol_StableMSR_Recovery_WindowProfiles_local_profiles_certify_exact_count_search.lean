-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.local_profiles_certify_exact_count_search
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:12:25.961101+00:00
-- url     : https://prove2.me/submissions/34d8111f-688d-4cad-8662-0a6eef6b2ea1

import Theorems.Thm_StableMSR_Recovery_WindowProfiles_canonical_region_sum
import Theorems.Thm_StableMSR_Recovery_WindowProfiles_routes_cover_processed_regions
import Theorems.Thm_StableMSR_Recovery_WindowProfiles_exact_count_routes_add_costs
import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

theorem solution (x : World) (e : ℚ) (m g : Mem) (hn : 0< x.n) (ok : Profiles x e m) (G : Grid (replace x m) g)
    (u : ℕ) (hu : u< x.rows) (pos : 0< scale x u)
    (tw : ∀W∈regions x u,RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist (scale x u) W) (widthBound (e:ℝ)))
    (P : Cluster x.n→Pick x.n) (validP : ∀W∈regions x u,valid x W (scale x u) (budget (e:ℝ)) (P W))
    (total : (∑W∈regions x u,number x W (scale x u) (P W))=x.k) :
    let y:=arena (replace x m) g
    let r:=node x.n u (x.n-1) x.k
    RegionalBallDP.vertex y r ∧ RegionalBallDP.InTable y r ∧
      ∃v,RegionalBallDP.Route y r v ∧ RegionalBallDP.weight y x.k v≤∑W∈regions x u,WindowCSP.price x W (scale x u) (P W) := by
  classical
  let y:=replace x m
  let z:=arena y g
  let t:=node x.n u (x.n-1) x.k
  let W:=piece x u
  let C (V : Cluster x.n):=number x V (scale x u) (P V)
  let B (V : Cluster x.n):=WindowCSP.price x V (scale x u) (P V)
  let d (i : ℕ):=if i∈keys x u then C (W i) else 0
  let f (i : ℕ):=if i∈keys x u then B (W i) else 0
  have gr:=canonical_region_sum x u
  have sumD : (∑i∈Finset.range x.n,d i)=x.k:=(gr.2 C).trans total
  have lim (i) (hi : i< x.n) : d i≤ x.k:=by
    rw [←sumD];exact Finset.single_le_sum (f:=d) (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr hi)
  have avail (i : ℕ) (hi : i< x.n) :
      active y u i (d i) ∧ RegionalBallDP.weight y (d i) (token y u i (d i))≤ f i:=by
    have h:=ok u hu i hi
    by_cases present : i∈keys x u
    · have mem:=(gr.1 i present).2
      have bound : C (W i)≤ x.k:=by simpa [d,present] using lim i hi
      simpa only [d,f,C,B,W,y,RegionalBallDP.weight,replace,if_pos present] using h.2.2 present pos (tw _ mem) (P (W i)) (validP _ mem) bound
    · refine ⟨by simpa [d,present,y] using h.2.1 present,?_⟩
      simp [d,f,present,RegionalBallDP.weight]
  obtain ⟨v,path,costV⟩:=exact_count_routes_add_costs y g G u hu hn d sumD (fun i hi=>(avail i hi).1)
  have low : x.n-1< x.n:=by omega
  obtain ⟨vertex,width⟩:=G.states u hu (x.n-1) low x.k le_rfl
  have ins : RegionalBallDP.InTable z t:=by
    have bound:=G.sized.2
    have vt:=vertex.2
    refine ⟨by change t≤ RegionalBallDP.slots z at vt;change 4*RegionalBallDP.slots z< z.rows at bound;omega,width,?_⟩
    intro w route
    have O:=routes_cover_processed_regions x m g G u hu (fun i hi=>(ok u hu i hi).1) _ low _ le_rfl w route
    refine ⟨O.2.1,?_⟩
    intro j hj;let p : Point x.n:=⟨j,hj⟩
    have inside : p∈Finset.univ.filter (fun p : Point x.n=>(rep x u p).val< x.n-1+1):=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,by have lt:=(rep x u p).isLt;omega⟩
    exact O.2.2 p inside
  refine ⟨vertex,ins,v,path,?_⟩
  change RegionalBallDP.weight y x.k v≤_
  change RegionalBallDP.weight y x.k v=∑i∈Finset.range x.n,RegionalBallDP.weight y (d i) (token y u i (d i)) at costV
  rw [costV];exact (Finset.sum_le_sum (fun i hi=>(avail i (Finset.mem_range.mp hi)).2)).trans_eq (gr.2 B)

