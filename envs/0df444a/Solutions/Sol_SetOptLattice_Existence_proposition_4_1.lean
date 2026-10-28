-- Prove2me | solution 1 for SetOptLattice.Existence.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:23:45.566326+00:00
-- url     : https://prove2.me/submissions/7e273b8c-ef65-4b76-9d9b-1e8db681a7a2

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

open Set Filter Topology
open scoped Pointwise

theorem solution {X : Type*}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X]
    (φ : X → EReal) (rbar : ℝ) (hlt : (⨅ x, φ x) < (rbar : EReal))
    (hc : ∀ r : ℝ, (⨅ x, φ x) < (r : EReal) → r ≤ rbar →
      IsCompact (SetOptLattice.Existence.sublevel φ r)) :
    ∃ xbar : X, φ xbar = ⨅ x, φ x := by
  set m := ⨅ x, φ x with hm
  obtain ⟨r0, hr0, hr0'⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  haveI : Nonempty {r : ℝ // m < (r : EReal) ∧ r ≤ rbar} :=
    ⟨⟨r0, hr0, by exact_mod_cast hr0'.le⟩⟩
  let t : {r : ℝ // m < (r : EReal) ∧ r ≤ rbar} → Set X :=
    fun r => SetOptLattice.Existence.sublevel φ r.1
  have htn : ∀ i, (t i).Nonempty := by
    intro i
    obtain ⟨x, hx⟩ := iInf_lt_iff.1 i.2.1
    exact ⟨x, hx.le⟩
  have hcomp : ∀ i, IsCompact (t i) := fun i => hc i.1 i.2.1 i.2.2
  have hdir : Directed (· ⊇ ·) t := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨⟨min a b, ?_, min_le_of_left_le ha.2⟩, ?_, ?_⟩
    · rcases le_total a b with h | h
      · rw [min_eq_left h]; exact ha.1
      · rw [min_eq_right h]; exact hb.1
    · intro x hx
      simp only [t, SetOptLattice.Existence.sublevel, mem_setOf_eq] at hx ⊢
      exact hx.trans (by exact_mod_cast min_le_left a b)
    · intro x hx
      simp only [t, SetOptLattice.Existence.sublevel, mem_setOf_eq] at hx ⊢
      exact hx.trans (by exact_mod_cast min_le_right a b)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir htn
    hcomp (fun i => (hcomp i).isClosed)
  rw [mem_iInter] at hx
  refine ⟨x, le_antisymm ?_ (iInf_le _ x)⟩
  by_contra hne
  push_neg at hne
  have h2 : m < min (rbar : EReal) (φ x) := lt_min hlt hne
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 h2
  have hrb : r ≤ rbar := by
    have := hr2.trans_le (min_le_left _ _)
    exact_mod_cast this.le
  have := hx ⟨r, hr1, hrb⟩
  have h3 : φ x ≤ (r : EReal) := this
  exact absurd (hr2.trans_le (min_le_right _ _)) (not_lt.2 h3)
