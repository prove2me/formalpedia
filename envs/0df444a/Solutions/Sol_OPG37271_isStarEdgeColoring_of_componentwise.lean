-- Prove2me | solution 1 for OPG37271.isStarEdgeColoring_of_componentwise
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:01:18.642841+00:00
-- url     : https://prove2.me/submissions/8a61f237-e3f1-44c7-bd0a-e0ae8ff5a2aa

import Definitions.Def_opg37271_star_edge_coloring

set_option autoImplicit false

open OPG37271
universe u

theorem solution
    {V : Type u} {ι : Type*} {H : SimpleGraph V} {K : Type*}
    (c : EdgeColoring H K) (comp : V → ι)
    (hcomp : ∀ {u v : V}, H.Adj u v → comp u = comp v)
    (hstar : ∀ k : ι, IsStarEdgeColoring
      (fun e => c ⟨Sym2.map Subtype.val e.1, by
        rcases e with ⟨e1, he1⟩
        induction e1 using Sym2.ind with
        | _ a b => exact he1⟩ :
        EdgeColoring (H.induce {v : V | comp v = k}) K)) :
    IsStarEdgeColoring c := by
  refine ⟨?_, ?_, ?_⟩
  · intro v u w hvu hvw huw heq
    let k := comp v
    have hu : comp u = k := (hcomp hvu).symm
    have hw : comp w = k := (hcomp hvw).symm
    have hprop := (hstar k).1 ⟨v, rfl⟩ ⟨u, hu⟩ ⟨w, hw⟩ hvu hvw
      (fun h => huw (congrArg Subtype.val h))
    exact hprop heq
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
    let k := comp v₀
    have hv1 : comp v₁ = k := (hcomp h01).symm
    have hv2 : comp v₂ = k := (hcomp h12).symm.trans hv1
    have hv3 : comp v₃ = k := (hcomp h23).symm.trans hv2
    have hv4 : comp v₄ = k := (hcomp h34).symm.trans hv3
    let u₀ : {v : V | comp v = k} := ⟨v₀, rfl⟩
    let u₁ : {v : V | comp v = k} := ⟨v₁, hv1⟩
    let u₂ : {v : V | comp v = k} := ⟨v₂, hv2⟩
    let u₃ : {v : V | comp v = k} := ⟨v₃, hv3⟩
    let u₄ : {v : V | comp v = k} := ⟨v₄, hv4⟩
    have hund : [u₀, u₁, u₂, u₃, u₄].Nodup := by
      have hmap : [u₀, u₁, u₂, u₃, u₄].map Subtype.val = [v₀, v₁, v₂, v₃, v₄] := rfl
      exact List.Nodup.of_map Subtype.val (hmap.symm ▸ hnd)
    exact (hstar k).2.1 ⟨u₀, u₁, u₂, u₃, u₄, hund, h01, h12, h23, h34, hc1, hc2⟩
  · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
    let k := comp v₀
    have hv1 : comp v₁ = k := (hcomp h01).symm
    have hv2 : comp v₂ = k := (hcomp h12).symm.trans hv1
    have hv3 : comp v₃ = k := (hcomp h23).symm.trans hv2
    let u₀ : {v : V | comp v = k} := ⟨v₀, rfl⟩
    let u₁ : {v : V | comp v = k} := ⟨v₁, hv1⟩
    let u₂ : {v : V | comp v = k} := ⟨v₂, hv2⟩
    let u₃ : {v : V | comp v = k} := ⟨v₃, hv3⟩
    have hund : [u₀, u₁, u₂, u₃].Nodup := by
      have hmap : [u₀, u₁, u₂, u₃].map Subtype.val = [v₀, v₁, v₂, v₃] := rfl
      exact List.Nodup.of_map Subtype.val (hmap.symm ▸ hnd)
    exact (hstar k).2.2 ⟨u₀, u₁, u₂, u₃, hund, h01, h12, h23, h30, hc1, hc2⟩

