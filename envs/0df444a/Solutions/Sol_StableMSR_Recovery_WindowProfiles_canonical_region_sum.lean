-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.canonical_region_sum
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:09:58.625989+00:00
-- url     : https://prove2.me/submissions/af7b6e97-5a18-4b2a-ba5f-77060c69a74b

import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

theorem solution (x : World) (u : ℕ) : (∀i∈keys x u,i< x.n ∧ piece x u i∈regions x u) ∧
    ∀{A : Type} [AddCommMonoid A] (f : Cluster x.n→A),
      (∑i∈Finset.range x.n,if i∈keys x u then f (piece x u i) else 0)=∑W∈regions x u,f W := by
  classical
  have inside (p : Point x.n) : label x u (rep x u p)=label x u p :=
    (Finset.mem_filter.mp ((fibre x u p).min'_mem _)).2
  have same (p q : Point x.n) : rep x u p=rep x u q ↔ label x u p=label x u q:=by
    refine ⟨fun h=>(inside p).symm.trans ((congrArg (label x u) h).trans (inside q)),?_⟩
    intro eq
    have H : fibre x u p=fibre x u q:=by simp only [fibre,eq]
    simp only [rep,H]
  have fiber (p : Point x.n) : piece x u (rep x u p).val=fibre x u p:=by
    ext q;simp only [piece,fibre,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_inj,same]
  have img : (keys x u).image (piece x u)=regions x u:=by
    unfold keys regions;rw [Finset.image_image];apply Finset.image_congr
    intro p _;exact fiber p
  have inj (i) (hi : i∈keys x u) (j) (hj : j∈keys x u) (eq : piece x u i=piece x u j) : i=j:=by
    obtain ⟨p,_,hp⟩:=Finset.mem_image.mp hi
    have mem : p∈piece x u i:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
    rw [eq] at mem;exact hp.symm.trans (Finset.mem_filter.mp mem).2
  have subK : keys x u⊆Finset.range x.n:=by
    intro i hi;obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp hi;exact Finset.mem_range.mpr (rep x u p).isLt
  refine ⟨fun i hi=>⟨Finset.mem_range.mp (subK hi),img ▸ Finset.mem_image_of_mem _ hi⟩,?_⟩
  intro A _ f
  rw [←img,Finset.sum_image (fun i hi j hj h=>inj i hi j hj h),←Finset.sum_filter]
  have eq : (Finset.range x.n).filter (fun i=>i∈keys x u)=keys x u:=by
    ext i;simp only [Finset.mem_filter];exact ⟨And.right,fun h=>⟨subK h,h⟩⟩
  rw [eq]

