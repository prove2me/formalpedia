-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.graph_deletion_change_count_le_maximum_shift
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:20:18.647195+00:00
-- url     : https://prove2.me/submissions/e6892824-c58f-47ae-9869-60e806e68b39

import Theorems.Thm_StabilityDichotomies_Bijunctive_occurrence_graph_deletions_have_short_certificate
import Theorems.Thm_StabilityDichotomies_Bijunctive_satisfiable_positive_shift_has_positive_literal_score
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution
    {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I F : Instance Γ V) (hF : Satisfiable F)
    (mask : Fin I.constraints.card → Bool) (δ : Literal V → ℝ) (hδ : ∀ a, 0 < δ a) (v : V) :
    let G := thinnedInstance I mask
    let bit := decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true))
    let changed := Finset.univ.filter (fun j : Fin I.constraints.card =>
      decide (literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,false) <
        literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,true)) ≠ bit)
    (changed.card : ℝ) ≤ max 0 (Finset.univ.sup' Finset.univ_nonempty δ) := by
  classical
  let G := thinnedInstance I mask
  let bit := decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true))
  have hpos : (0 : WithBot ℝ) < literalScore rep G F δ (v,bit) := by
    obtain ⟨b,hb⟩ := satisfiable_positive_shift_has_positive_literal_score rep G F hF δ hδ v
    by_cases h : literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)
    · have hbit : bit = true := by simp [bit,h]
      rw [hbit]
      cases b with
      | false => exact hb.trans h
      | true => exact hb
    · have hbit : bit = false := by simp [bit,h]
      rw [hbit]
      cases b with
      | false => exact hb
      | true => exact hb.trans_le (le_of_not_gt h)
  obtain ⟨root,n,S,hcard,hshort,hstable⟩ :=
    occurrence_graph_deletions_have_short_certificate rep I F mask δ v bit rfl hpos
  let changed := Finset.univ.filter (fun j : Fin I.constraints.card =>
      decide (literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,false) <
        literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,true)) ≠ bit)
  have hsubset : changed ⊆ S := by
    intro j hj
    have hchange := (Finset.mem_filter.mp hj).2
    by_contra hn
    exact hchange (hstable j hn)
  have hcn : changed.card ≤ n := (Finset.card_le_card hsubset).trans hcard
  have hroot : δ root ≤ Finset.univ.sup' Finset.univ_nonempty δ := Finset.le_sup' δ (Finset.mem_univ root)
  have hn : (changed.card : ℝ) ≤ n := by exact_mod_cast hcn
  exact hn.trans (le_trans (le_of_lt hshort) (hroot.trans (le_max_right _ _)))
