-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.open_atom_iff_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:45:25.426721+00:00
-- url     : https://prove2.me/submissions/508e8220-1771-4402-8764-fd18cfe3d92e

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {M : Type*} [TopologicalSpace M] [T1Space M]
    (U : TopologicalSpace.Opens M) : IsAtom U ↔ ∃ x : M, (U : Set M) = {x} := by
  classical
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty U).mp ha.ne_bot
    refine ⟨x, Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr hx)⟩
    intro y hy
    by_contra hyx
    have hyne : y ≠ x := fun h => hyx (Set.mem_singleton_iff.mpr h)
    let V : Opens M := ⟨(U : Set M) \ {x}, U.isOpen.sdiff isClosed_singleton⟩
    have hv : V ≠ ⊥ := (Opens.ne_bot_iff_nonempty V).mpr ⟨y, hy, hyne⟩
    have heq : V = U := (ha.le_iff_eq hv).mp Set.sdiff_subset
    have hxv : x ∈ (V : Set M) := by rw [heq]; exact hx
    exact hxv.2 rfl
  · rintro ⟨x, hU⟩
    apply isAtom_iff_le_of_ge.mpr
    have hx : x ∈ (U : Set M) := by rw [hU]; exact Set.mem_singleton x
    refine ⟨(Opens.ne_bot_iff_nonempty U).mpr ⟨x, hx⟩, ?_⟩
    intro V hv hVU
    obtain ⟨y, hy⟩ := (Opens.ne_bot_iff_nonempty V).mp hv
    have hyU : y ∈ (U : Set M) := hVU hy
    rw [hU] at hyU
    have hyx : y = x := hyU
    have hxV : x ∈ (V : Set M) := hyx ▸ hy
    intro z hz
    change z ∈ (U : Set M) at hz
    rw [hU] at hz
    exact (Set.mem_singleton_iff.mp hz).symm ▸ hxV
