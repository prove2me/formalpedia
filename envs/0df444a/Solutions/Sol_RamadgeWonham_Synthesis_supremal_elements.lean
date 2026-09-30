-- Prove2me | solution 1 for RamadgeWonham.Synthesis.supremal_elements
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:27:13.951559+00:00
-- url     : https://prove2.me/submissions/383ca37c-ee92-408f-9df8-619487a74a04

import Definitions.Def_RamadgeWonham_Synthesis_Controllable
import Mathlib.Tactic
set_option autoImplicit false
open RamadgeWonham RamadgeWonham.Synthesis

private theorem C_union {α : Type} (G : Shared.Generator α) (Ec : Set α) (L : Set (List α))
    (K : Set (Set (List α))) (hK : K ⊆ Cset G Ec L) : ⋃₀ K ∈ Cset G Ec L := by
  refine ⟨?_,?_,?_⟩
  · intro s hs
    obtain ⟨A,hA,hsA⟩ := hs
    exact (hK hA).1 hsA
  · intro s hs
    obtain ⟨A,hA,hsA⟩ := hs
    exact (hK hA).2.1 hsA
  · intro s σ hs hσ hstep
    obtain ⟨t,ht⟩ := hs
    obtain ⟨A,hA,htA⟩ := ht
    obtain ⟨v,hv⟩ := (hK hA).2.2 s σ ⟨t,htA⟩ hσ hstep
    exact ⟨v,A,hA,hv⟩

private theorem F_union {α : Type} (G : Shared.Generator α) (L : Set (List α))
    (K : Set (Set (List α))) (hK : K ⊆ Fset G L) : ⋃₀ K ∈ Fset G L := by
  constructor
  · intro s hs
    obtain ⟨A,hA,hsA⟩ := hs
    exact (hK hA).1 hsA
  · ext s
    constructor
    · rintro ⟨A,hA,hsA⟩
      have hh : s∈Shared.pre A ∩ G.Lm := (hK hA).2 ▸ hsA
      obtain ⟨t,ht⟩ := hh.1
      exact ⟨⟨t,A,hA,ht⟩,hh.2⟩
    · rintro ⟨⟨t,A,hA,ht⟩,hmark⟩
      refine ⟨A,hA,?_⟩
      rw [(hK hA).2]
      exact ⟨⟨t,ht⟩,hmark⟩

theorem solution {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (L : Set (List α)) (hL : L ⊆ G.L) :
    IsGreatest (Cset G Ec L) (sSup (Cset G Ec L)) ∧
      IsGreatest (Fset G L) (sSup (Fset G L)) ∧
      IsGreatest (Cset G Ec L ∩ Fset G L) (sSup (Cset G Ec L ∩ Fset G L)) := by
  refine ⟨⟨C_union G Ec L _ (fun _ h => h),?_⟩,⟨F_union G L _ (fun _ h => h),?_⟩,?_,?_⟩
  · intro K hK; exact le_sSup hK
  · intro K hK; exact le_sSup hK
  · exact ⟨C_union G Ec L _ (fun _ h => h.1),F_union G L _ (fun _ h => h.2)⟩
  · intro K hK; exact le_sSup hK
