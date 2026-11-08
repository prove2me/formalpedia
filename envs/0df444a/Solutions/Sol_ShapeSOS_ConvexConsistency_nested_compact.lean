-- Prove2me | solution 1 for ShapeSOS.ConvexConsistency.nested_compact
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:21:02.505221+00:00
-- url     : https://prove2.me/submissions/91f17538-7910-41a5-a071-bcca589165ae

import Definitions.Def_ShapeSOS_ConvexConsistency_Geometry

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

open ShapeSOS.ConvexConsistency in
theorem solution (n : ℕ) (xstar : Vec n) (S : ℕ → Set (Vec n))
    (hne : ∀ j, (S j).Nonempty) (hcomp : ∀ j, IsCompact (S j))
    (hmono : ∀ j, S (j+1) ⊆ S j) (hinter : (⋂ j, S j) = {xstar}) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      S k ⊆ {x | norm₂ (x-xstar) < ε} := by
  intro ε hε
  set U : Set (Vec n) := {x | norm₂ (x - xstar) < ε} with hU
  have hcont : Continuous fun x : Vec n => norm₂ (x - xstar) := by
    unfold norm₂
    fun_prop
  have hUo : IsOpen U := isOpen_lt hcont continuous_const
  have hanti : Antitone S := antitone_nat_of_succ_le hmono
  by_contra hcon
  push_neg at hcon
  have htn : ∀ k, (S k \ U).Nonempty := by
    intro k
    obtain ⟨k', hk', hsub⟩ := hcon k
    obtain ⟨y, hy1, hy2⟩ := Set.not_subset.mp hsub
    exact ⟨y, hanti hk' hy1, hy2⟩
  have hne' := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k => S k \ U) (fun k => Set.diff_subset_diff_left (hmono k)) htn
    ((hcomp 0).diff hUo) (fun k => (hcomp k).isClosed.sdiff hUo)
  obtain ⟨y, hy⟩ := hne'
  rw [Set.mem_iInter] at hy
  have hyS : y ∈ ⋂ j, S j := Set.mem_iInter.mpr (fun j => (hy j).1)
  rw [hinter, Set.mem_singleton_iff] at hyS
  apply (hy 0).2
  rw [hyS]
  show norm₂ (xstar - xstar) < ε
  simp [norm₂, hε]
