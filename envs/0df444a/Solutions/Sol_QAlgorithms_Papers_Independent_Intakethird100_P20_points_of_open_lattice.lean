-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.points_of_open_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:20:21.159972+00:00
-- url     : https://prove2.me/submissions/24c1117d-a947-4c84-a99f-4d6786ade521

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.2; de Groote, Observables I, PDF p./pp. 37.
-/
theorem solution {M : Type u} [TopologicalSpace M] [RegularSpace M] [T2Space M]
    (p : Set (Opens M)) (hne : p.Nonempty) :
    IsLatticePoint p ↔ ∃! x : M, p = {U : Opens M | x ∈ (U : Set M)} := by
  classical
  constructor
  · intro hp
    have hD := hp.1
    let N : Opens M := sSup {U : Opens M | U ∉ p}
    have hN : N ∉ p := by
      intro h
      obtain ⟨U, hU, hUp⟩ := hp.2 {U : Opens M | U ∉ p} h
      exact hU hUp
    have htop : (⊤ : Opens M) ∈ p := by
      obtain ⟨U, hU⟩ := hne
      exact hD.2.2.1 U hU ⊤ le_top
    have hNtop : N ≠ ⊤ := by
      intro heq
      apply hN
      rw [heq]
      exact htop
    have hNset : (N : Set M) ≠ Set.univ := fun h => hNtop (SetLike.coe_injective h)
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem (N : Set M)).mp hNset
    have hmem (y : M) (hy : y ∉ (N : Set M)) (U : Opens M) (hyU : y ∈ (U : Set M)) : U ∈ p := by
      by_contra hU
      exact hy (Opens.mem_sSup.mpr ⟨U, hU, hyU⟩)
    have hout (y : M) (hy : y ∉ (N : Set M)) : y = x := by
      by_contra hyx
      obtain ⟨v, w, hv, hw, hyv, hxw, hvw⟩ := t2_separation hyx
      let V : Opens M := ⟨v, hv⟩
      let W : Opens M := ⟨w, hw⟩
      have hV := hmem y hy V hyv
      have hW := hmem x hx W hxw
      have hz : V ⊓ W = ⊥ := SetLike.coe_injective (disjoint_iff.mp hvw)
      have hVW := hD.2.2.2 V hV W hW
      exact hD.2.1 (hz ▸ hVW)
    have heq : p = {U : Opens M | x ∈ (U : Set M)} := by
      ext U
      constructor
      · intro hU
        by_contra hxU
        have hUN : U ≤ N := by
          intro y hyU
          by_contra hyN
          have hyx := hout y hyN
          exact hxU (hyx ▸ hyU)
        exact hN (hD.2.2.1 U hU N hUN)
      · exact hmem x hx U
    refine ⟨x, heq, ?_⟩
    intro y hy
    apply hout y
    intro hyN
    apply hN
    rw [hy]
    exact hyN
  · rintro ⟨x, heq, _⟩
    rw [heq]
    refine ⟨⟨⟨⊤, Set.mem_univ x⟩, ?_, ?_, ?_⟩, ?_⟩
    · intro h; exact h
    · intro U hU V hUV; exact hUV hU
    · intro U hU V hV; exact ⟨hU, hV⟩
    · intro s hs
      obtain ⟨U, hUs, hxU⟩ := Opens.mem_sSup.mp hs
      exact ⟨U, hUs, hxU⟩
