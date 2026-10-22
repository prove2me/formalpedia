-- Prove2me | solution 1 for OpenPitMIP.Hourglass.capacity_split
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:42:59.048433+00:00
-- url     : https://prove2.me/submissions/74f9fb28-267b-4ea9-bb79-1df55390a105

import Mathlib
import Definitions.Def_OpenPitMIP_Hourglass_Setting
set_option autoImplicit false
open OpenPitMIP.Hourglass

theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C]
    [DecidableEq B] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (d : D) (cbar : C) (S : Finset B)
    (hS : S ⊆ I.blocksOf (I.cl cbar \ {cbar}))
    (y : B → D → Fin T → ℝ) (hy0 : ∀ b d t, 0 ≤ y b d t) (hcap : I.DestCap y) :
    ∀ s : Fin T,
      ∑ b ∈ S, I.q b * y b d s + ∑ b ∈ I.blocksOf {cbar}, I.q b * y b d s
        + ∑ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.q b * y b d s ≤ I.Ud d s := by
  intro s
  classical
  haveI := hI.strictOrder
  have hirr : ∀ c, ¬ I.cprec c c := fun c => irrefl_of I.cprec c
  have htrans : ∀ a b c, I.cprec a b → I.cprec b c → I.cprec a c :=
    fun a b c h1 h2 => trans_of I.cprec h1 h2
  have memS : ∀ b ∈ S, I.clu b ≠ cbar ∧ I.cprec (I.clu b) cbar := by
    intro b hb
    have := hS hb
    simp only [PCPSPC.blocksOf, PCPSPC.cl, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_singleton] at this
    rcases this with ⟨h1 | h1, h2⟩
    · exact absurd h1 h2
    · exact ⟨h2, h1⟩
  have mem2 : ∀ b ∈ I.blocksOf {cbar}, I.clu b = cbar := by
    intro b hb
    simpa [PCPSPC.blocksOf] using hb
  have mem3 : ∀ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.clu b ≠ cbar ∧ I.cprec cbar (I.clu b) := by
    intro b hb
    simp only [PCPSPC.blocksOf, PCPSPC.rcl, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_singleton] at hb
    rcases hb with ⟨h1 | h1, h2⟩
    · exact absurd h1 h2
    · exact ⟨h2, h1⟩
  have h12 : Disjoint S (I.blocksOf {cbar}) := by
    rw [Finset.disjoint_left]
    intro b hb hb2
    exact (memS b hb).1 (mem2 b hb2)
  have h13 : Disjoint S (I.blocksOf (I.rcl cbar \ {cbar})) := by
    rw [Finset.disjoint_left]
    intro b hb hb3
    exact hirr _ (htrans _ _ _ (mem3 b hb3).2 (memS b hb).2)
  have h23 : Disjoint (I.blocksOf {cbar}) (I.blocksOf (I.rcl cbar \ {cbar})) := by
    rw [Finset.disjoint_left]
    intro b hb2 hb3
    exact (mem3 b hb3).1 (mem2 b hb2)
  have h123 : Disjoint (S ∪ I.blocksOf {cbar}) (I.blocksOf (I.rcl cbar \ {cbar})) :=
    Finset.disjoint_union_left.mpr ⟨h13, h23⟩
  rw [← Finset.sum_union h12, ← Finset.sum_union h123]
  have hnn : ∀ b ∈ (Finset.univ : Finset B), b ∉ (S ∪ I.blocksOf {cbar}) ∪
      I.blocksOf (I.rcl cbar \ {cbar}) → 0 ≤ I.q b * y b d s :=
    fun b _ _ => mul_nonneg (hI.q_nonneg b) (hy0 b d s)
  calc ∑ b ∈ (S ∪ I.blocksOf {cbar}) ∪ I.blocksOf (I.rcl cbar \ {cbar}), I.q b * y b d s
      ≤ ∑ b, I.q b * y b d s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) hnn
    _ = ∑ b, I.q b * y b d s := rfl
    _ ≤ I.Ud d s := hcap d s
