-- Prove2me | solution 1 for SepCostShare.type1_cost_decrease
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:47:07.86956+00:00
-- url     : https://prove2.me/submissions/fdf79c61-23f4-4df1-b932-a7f989b90a98

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm

open SepCostShare in
theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E)
    (hB : G.IsProfile B) (i : N) (e f : E) (hi : i ∈ G.users e B)
    (h1 : G.deltaBar B i e < G.d i e) (hf : G.IsArgmin B i e f) :
    G.cost (G.swap B i e f) - G.cost B ≤ G.deltaBar B i e - G.d i e ∧
      G.deltaBar B i e - G.d i e < 0 := by
  have hfalts : f ∈ G.alts B i e := hf.1
  have hdb : G.deltaBar B i e = G.pi i f := by
    unfold MatroidGame.deltaBar
    rw [dif_pos ⟨f, hfalts⟩]
    apply le_antisymm
    · exact Finset.inf'_le _ hfalts
    · apply Finset.le_inf'
      intro g hg
      exact hf.2 g hg
  refine ⟨?_, by linarith⟩
  rw [hdb] at h1 ⊢
  have heB : e ∈ B i := by simpa [MatroidGame.users] using hi
  have hfe : f ≠ e := by
    intro hfe
    rw [hfe] at h1
    unfold MatroidGame.pi at h1
    have := G.c_nonneg e {i}
    linarith
  have hB'i : G.swap B i e f i = insert f ((B i).erase e) := by
    simp [MatroidGame.swap]
  have hB'j : ∀ j, j ≠ i → G.swap B i e f j = B j := by
    intro j hj
    simp [MatroidGame.swap, hj]
  have hU : ∀ g, g ≠ e → g ≠ f → G.users g (G.swap B i e f) = G.users g B := by
    intro g hge hgf
    unfold MatroidGame.users
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j = i
    · rw [hj, hB'i]
      simp [hge, hgf]
    · rw [hB'j j hj]
  have hUe : G.users e (G.swap B i e f) = (G.users e B).erase i := by
    unfold MatroidGame.users
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hj : j = i
    · rw [hj, hB'i]
      simp [Ne.symm hfe]
    · rw [hB'j j hj]
      simp [hj]
  have hUf : f ∉ B i → G.users f (G.swap B i e f) = insert i (G.users f B) := by
    intro hfB
    unfold MatroidGame.users
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hj : j = i
    · rw [hj, hB'i]
      simp
    · rw [hB'j j hj]
      simp [hj]
  have hUf' : f ∈ B i → G.users f (G.swap B i e f) = G.users f B := by
    intro hfB
    unfold MatroidGame.users
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j = i
    · rw [hj, hB'i]
      simp [hfB]
    · rw [hB'j j hj]
  -- pointwise bound on the congestion part
  have hpt : ∀ g, ((if (G.users g (G.swap B i e f)).Nonempty then
        G.c g (G.users g (G.swap B i e f)) else 0) -
      (if (G.users g B).Nonempty then G.c g (G.users g B) else 0)) ≤
      (if g = f then (if f ∈ B i then 0 else G.c f {i}) else 0) := by
    intro g
    by_cases hge : g = e
    · have hgf : g ≠ f := by rw [hge]; exact Ne.symm hfe
      rw [if_neg hgf, hge, hUe]
      have hne : (G.users e B).Nonempty := ⟨i, hi⟩
      rw [if_pos hne]
      split_ifs with h
      · have := hG.1 e _ _ (Finset.erase_subset i (G.users e B))
        linarith
      · have := G.c_nonneg e (G.users e B)
        linarith
    · by_cases hgf : g = f
      · rw [if_pos hgf, hgf]
        by_cases hfB : f ∈ B i
        · rw [if_pos hfB, hUf' hfB]
          simp
        · rw [if_neg hfB, hUf hfB]
          have hins : (insert i (G.users f B)).Nonempty := Finset.insert_nonempty _ _
          rw [if_pos hins]
          by_cases hne : (G.users f B).Nonempty
          · rw [if_pos hne]
            have hiU : i ∉ G.users f B := by simpa [MatroidGame.users] using hfB
            have hss : G.users f B ⊂ Finset.univ := by
              rw [Finset.ssubset_univ_iff]
              intro h
              apply hiU
              rw [h]
              exact Finset.mem_univ i
            have := hG.2 f (G.users f B) hss i
            linarith
          · rw [if_neg hne]
            have hemp : G.users f B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
            rw [hemp]
            simp
      · rw [if_neg hgf, hU g hge hgf]
        simp
  have hCsum :
      (∑ g ∈ Finset.univ.filter (fun g => (G.users g (G.swap B i e f)).Nonempty),
          G.c g (G.users g (G.swap B i e f))) -
        (∑ g ∈ Finset.univ.filter (fun g => (G.users g B).Nonempty), G.c g (G.users g B))
        ≤ if f ∈ B i then 0 else G.c f {i} := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ g, (if g = f then (if f ∈ B i then 0 else G.c f {i}) else 0) :=
          Finset.sum_le_sum (fun g _ => hpt g)
      _ = _ := by simp
  have hDsum : (∑ j : N, ∑ g ∈ G.swap B i e f j, G.d j g) - ∑ j : N, ∑ g ∈ B j, G.d j g
      = (∑ g ∈ G.swap B i e f i, G.d i g) - ∑ g ∈ B i, G.d i g := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [hB'j j hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hDi : (∑ g ∈ G.swap B i e f i, G.d i g) - ∑ g ∈ B i, G.d i g
      = (if f ∈ B i then 0 else G.d i f) - G.d i e := by
    rw [hB'i]
    by_cases hfB : f ∈ B i
    · have hins : insert f ((B i).erase e) = (B i).erase e :=
        Finset.insert_eq_of_mem (Finset.mem_erase.mpr ⟨hfe, hfB⟩)
      rw [hins, if_pos hfB, ← Finset.sum_erase_add _ _ heB]
      ring
    · rw [Finset.sum_insert (fun h => hfB (Finset.mem_of_mem_erase h)), if_neg hfB,
        ← Finset.sum_erase_add _ _ heB]
      ring
  have hXY : (if f ∈ B i then 0 else G.c f {i}) + (if f ∈ B i then 0 else G.d i f)
      ≤ G.c f {i} + G.d i f := by
    have := G.c_nonneg f {i}
    have := G.d_nonneg i f
    split_ifs <;> linarith
  unfold MatroidGame.cost MatroidGame.pi
  linarith
