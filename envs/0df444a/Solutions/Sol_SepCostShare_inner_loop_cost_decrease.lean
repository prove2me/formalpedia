-- Prove2me | solution 1 for SepCostShare.inner_loop_cost_decrease
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:18:57.066824+00:00
-- url     : https://prove2.me/submissions/96d1d45d-4cd5-4ee5-acb4-99c9109ec0b1

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm
set_option autoImplicit false

namespace Aux_SepCostShare_inner_loop_cost_decrease

open SepCostShare

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

noncomputable def chat (G : MatroidGame N E) (g : E) (U : Finset N) : ℝ :=
  if U.Nonempty then G.c g U else 0

theorem cost_eq (G : MatroidGame N E) (B : N → Finset E) :
    G.cost B = ∑ g, chat G g (G.users g B) + ∑ j, ∑ g ∈ B j, G.d j g := by
  unfold MatroidGame.cost chat
  rw [Finset.sum_filter]

theorem deltaBar_congr (G : MatroidGame N E) {B B' : N → Finset E} {i : N} {e : E}
    (h : B i = B' i) : G.deltaBar B i e = G.deltaBar B' i e := by
  unfold MatroidGame.deltaBar MatroidGame.alts
  rw [h]

theorem deltaBar_eq_pi (G : MatroidGame N E) {B : N → Finset E} {i : N} {e f : E}
    (hf : G.IsArgmin B i e f) : G.deltaBar B i e = G.pi i f := by
  unfold MatroidGame.deltaBar
  have hne : (G.alts B i e).Nonempty := ⟨f, hf.1⟩
  rw [dif_pos hne]
  apply le_antisymm
  · exact Finset.inf'_le _ hf.1
  · exact Finset.le_inf' _ _ (fun g hg => hf.2 g hg)

theorem mem_users (G : MatroidGame N E) (B : N → Finset E) (g : E) (j : N) :
    j ∈ G.users g B ↔ g ∈ B j := by
  simp [MatroidGame.users]

theorem alts_base (G : MatroidGame N E) {B : N → Finset E} {i : N} {e f : E}
    (hf : f ∈ G.alts B i e) : (G.M i).IsBase (↑(insert f ((B i).erase e)) : Set E) := by
  unfold MatroidGame.alts at hf
  simpa using hf

theorem not_mem_of_alt (G : MatroidGame N E) {B : N → Finset E} (hB : G.IsProfile B) {i : N}
    {e f : E} (hei : e ∈ B i) (hfe : f ≠ e) (hf : f ∈ G.alts B i e) : f ∉ B i := by
  intro hf'
  have hbase := alts_base G hf
  have h1 : insert f ((B i).erase e) = (B i).erase e :=
    Finset.insert_eq_of_mem (Finset.mem_erase.mpr ⟨hfe, hf'⟩)
  rw [h1] at hbase
  have h2 := hbase.eq_of_subset_isBase (hB i) (by
    intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    exact Finset.mem_of_mem_erase hx)
  have h3 : (B i).erase e = B i := by exact_mod_cast h2
  have : e ∉ (B i).erase e := Finset.notMem_erase e (B i)
  rw [h3] at this
  exact this hei

section Swap

variable (G : MatroidGame N E) (B : N → Finset E) (i : N) (e f : E)

theorem users_swap_e (hfe : f ≠ e) :
    G.users e (G.swap B i e f) = (G.users e B).erase i := by
  ext j
  rw [mem_users, Finset.mem_erase, mem_users]
  unfold MatroidGame.swap
  by_cases hj : j = i
  · subst hj
    simp [Function.update_self, Ne.symm hfe]
  · simp [Function.update_of_ne hj, hj]

theorem users_swap_f :
    G.users f (G.swap B i e f) = insert i (G.users f B) := by
  ext j
  rw [mem_users, Finset.mem_insert, mem_users]
  unfold MatroidGame.swap
  by_cases hj : j = i
  · subst hj
    simp [Function.update_self]
  · simp [Function.update_of_ne hj, hj]

theorem users_swap_other (g : E) (hge : g ≠ e) (hgf : g ≠ f) :
    G.users g (G.swap B i e f) = G.users g B := by
  ext j
  rw [mem_users, mem_users]
  unfold MatroidGame.swap
  by_cases hj : j = i
  · subst hj
    simp [Function.update_self, hge, hgf]
  · simp [Function.update_of_ne hj]

theorem swap_ne (j : N) (hj : j ≠ i) : G.swap B i e f j = B j := by
  unfold MatroidGame.swap
  exact Function.update_of_ne hj _ _

theorem swap_self : G.swap B i e f i = insert f ((B i).erase e) := by
  unfold MatroidGame.swap
  exact Function.update_self _ _ _

end Swap

/-- cost change of one swap -/
theorem cost_swap (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E) (i : N)
    (e f : E) (hfe : f ≠ e) (hei : e ∈ B i) (hfi : f ∉ B i) :
    G.cost (G.swap B i e f) ≤ G.cost B + (chat G e ((G.users e B).erase i) -
      chat G e (G.users e B)) + G.pi i f - G.d i e := by
  rw [cost_eq, cost_eq]
  -- the c-part
  have hc : ∑ g, chat G g (G.users g (G.swap B i e f)) =
      ∑ g, chat G g (G.users g B) +
        ((chat G e ((G.users e B).erase i) - chat G e (G.users e B)) +
          (chat G f (insert i (G.users f B)) - chat G f (G.users f B))) := by
    have h0 : ∑ g, (chat G g (G.users g (G.swap B i e f)) - chat G g (G.users g B)) =
        (chat G e ((G.users e B).erase i) - chat G e (G.users e B)) +
          (chat G f (insert i (G.users f B)) - chat G f (G.users f B)) := by
      rw [Finset.sum_eq_add_of_mem e f (Finset.mem_univ e) (Finset.mem_univ f) (Ne.symm hfe)]
      · rw [users_swap_e G B i e f hfe, users_swap_f G B i e f]
      · intro g _ hg
        rw [users_swap_other G B i e f g hg.1 hg.2, sub_self]
    rw [← h0, Finset.sum_sub_distrib]
    ring
  -- the d-part
  have hd : ∑ j, ∑ g ∈ G.swap B i e f j, G.d j g =
      ∑ j, ∑ g ∈ B j, G.d j g + (G.d i f - G.d i e) := by
    have h0 : ∑ j, (∑ g ∈ G.swap B i e f j, G.d j g - ∑ g ∈ B j, G.d j g) =
        G.d i f - G.d i e := by
      rw [Finset.sum_eq_single i]
      · rw [swap_self, Finset.sum_insert (fun h => hfi (Finset.mem_of_mem_erase h)),
          Finset.sum_erase_eq_sub hei]
        ring
      · intro j _ hj
        rw [swap_ne G B i e f j hj, sub_self]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [← h0, Finset.sum_sub_distrib]
    ring
  rw [hc, hd]
  -- subadditivity at f
  have hsub : chat G f (insert i (G.users f B)) - chat G f (G.users f B) ≤ G.c f {i} := by
    have hiU : i ∉ G.users f B := by rw [mem_users]; exact hfi
    have hne : (insert i (G.users f B)).Nonempty := Finset.insert_nonempty _ _
    unfold chat
    rw [if_pos hne]
    by_cases hU : (G.users f B).Nonempty
    · rw [if_pos hU]
      have hss : G.users f B ⊂ Finset.univ :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,
          fun h => hiU (h ▸ Finset.mem_univ i)⟩
      have := hG.2 f (G.users f B) hss i
      linarith
    · rw [if_neg hU]
      rw [Finset.not_nonempty_iff_eq_empty] at hU
      rw [hU]
      simp
  unfold MatroidGame.pi
  linarith

noncomputable def Phi (G : MatroidGame N E) (e : E) (B : N → Finset E) : ℝ :=
  G.cost B - chat G e (G.users e B) + ∑ j ∈ G.users e B, (G.deltaBar B j e - G.d j e)

theorem step_phi (G : MatroidGame N E) (hG : G.Subadditive) {B B' : N → Finset E}
    (hB : G.IsProfile B) {e : E} (hs : G.InnerStep e B B') :
    G.IsProfile B' ∧ Phi G e B' ≤ Phi G e B := by
  obtain ⟨_, i, hi, hlt, f, hf, rfl⟩ := hs
  have hei : e ∈ B i := (mem_users G B e i).mp hi
  have hδ := deltaBar_eq_pi G hf
  have hfe : f ≠ e := by
    intro h
    subst h
    rw [hδ] at hlt
    exact lt_irrefl _ hlt
  have hfi := not_mem_of_alt G hB hei hfe hf.1
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj
      rw [swap_self]
      exact alts_base G hf.1
    · rw [swap_ne G B i e f j hj]
      exact hB j
  · have hc := cost_swap G hG B i e f hfe hei hfi
    unfold Phi
    rw [users_swap_e G B i e f hfe]
    have hsum : ∑ j ∈ (G.users e B).erase i,
        (G.deltaBar (G.swap B i e f) j e - G.d j e) =
        ∑ j ∈ G.users e B, (G.deltaBar B j e - G.d j e) - (G.deltaBar B i e - G.d i e) := by
      rw [← Finset.sum_erase_eq_sub hi]
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [deltaBar_congr G (B := G.swap B i e f) (B' := B) (swap_ne G B i e f j hji)]
    rw [hsum, hδ]
    linarith

theorem run_phi (G : MatroidGame N E) (hG : G.Subadditive) {B B' : N → Finset E}
    (hB : G.IsProfile B) {e : E} (hrun : Relation.TransGen (G.InnerStep e) B B') :
    G.IsProfile B' ∧ Phi G e B' ≤ Phi G e B := by
  induction hrun with
  | single h => exact step_phi G hG hB h
  | tail _ h ih =>
    obtain ⟨hp, hφ⟩ := ih
    obtain ⟨hp', hφ'⟩ := step_phi G hG hp h
    exact ⟨hp', le_trans hφ' hφ⟩


end Aux_SepCostShare_inner_loop_cost_decrease


open SepCostShare Aux_SepCostShare_inner_loop_cost_decrease in
theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B B' : N → Finset E)
    (hB : G.IsProfile B) (e : E) (hrun : Relation.TransGen (G.InnerStep e) B B')
    (hexit : ¬ G.cond2 B' e) :
    G.cost B' < G.cost B := by
  obtain ⟨_, hφ⟩ := run_phi G hG hB hrun
  obtain ⟨B1, h1, _⟩ := Relation.TransGen.head'_iff.mp hrun
  obtain ⟨⟨hne, hlt⟩, _⟩ := h1
  have hfin : chat G e (G.users e B') ≤
      ∑ j ∈ G.users e B', (G.deltaBar B' j e - G.d j e) := by
    unfold chat
    by_cases hU : (G.users e B').Nonempty
    · rw [if_pos hU]
      unfold MatroidGame.cond2 at hexit
      push_neg at hexit
      exact hexit hU
    · rw [if_neg hU]
      rw [Finset.not_nonempty_iff_eq_empty] at hU
      rw [hU, Finset.sum_empty]
  have hstart : chat G e (G.users e B) = G.c e (G.users e B) := by
    unfold chat
    rw [if_pos hne]
  unfold Phi at hφ
  rw [hstart] at hφ
  linarith
