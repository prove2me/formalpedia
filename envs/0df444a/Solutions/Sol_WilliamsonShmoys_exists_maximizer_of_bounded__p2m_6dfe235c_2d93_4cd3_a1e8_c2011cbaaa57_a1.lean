-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximizer_of_bounded__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:30:02.179945+00:00
-- url     : https://prove2.me/submissions/898df988-cedc-46ca-bc88-71c861f1142d

import Mathlib

theorem solution {α : Type} (P : α → Prop) (f : α → Nat)
    (hP : ∃ x, P x) (B : Nat)
    (hB : ∀ x, P x → f x ≤ B) :
    ∃ x, P x ∧ ∀ y, P y → f y ≤ f x := by
  classical
  let S : Finset Nat :=
    (Finset.range (B + 1)).filter (fun n => ∃ x, P x ∧ f x = n)
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hP
    refine ⟨f x, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ⟨x, hx, rfl⟩⟩⟩
    exact Nat.lt_succ_of_le (hB x hx)
  let m : Nat := S.max' hS
  have hm : m ∈ S := Finset.max'_mem S hS
  obtain ⟨x, hx, hfx⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨x, hx, ?_⟩
  intro y hy
  have hmem : f y ∈ S := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (hB y hy)
    · exact ⟨y, hy, rfl⟩
  have hle : f y ≤ m := by
    simpa [m] using (Finset.le_max' S (f y) hmem)
  calc
    f y ≤ m := hle
    _ = f x := hfx.symm