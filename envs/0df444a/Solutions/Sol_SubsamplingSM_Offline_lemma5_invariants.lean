-- Prove2me | solution 1 for SubsamplingSM.Offline.lemma5_invariants
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:02:24.393351+00:00
-- url     : https://prove2.me/submissions/f775fa49-292d-4326-9f90-a785dfd98cef

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_SubsamplingSM_Offline_IsMinRemoval
import Definitions.Def_SubsamplingSM_Offline_alg2Init
import Definitions.Def_SubsamplingSM_Offline_alg2Step

namespace Aux_SubsamplingSM_lemma5

open SubsamplingSM.Offline

def Inv {α : Type*} [LinearOrder α] (I : Finset α → Prop) (st : Alg2State α) : Prop :=
  I st.O ∧ st.S ⊆ st.O ∧ st.O \ st.S ⊆ st.N' ∧ Disjoint st.S st.N'

theorem step_inv {α : Type*} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (hI : IsIndepSystem I)
    (sel : Finset α → Finset α → Finset α) (hsel : IsMinRemoval I sel)
    (b : Finset α) (st : Alg2State α) (H : Inv I st) : Inv I (alg2Step f I sel b st) := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := H
  unfold alg2Step
  split
  · next hC =>
    have hu : pick f st.S (cands f I st.N' st.S) hC ∈ cands f I st.N' st.S := by
      unfold pick
      exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1
    generalize pick f st.S (cands f I st.N' st.S) hC = u at hu ⊢
    unfold cands at hu
    replace hu := Finset.mem_filter.mp hu
    obtain ⟨huN, huI, -⟩ := hu
    have huS : u ∉ st.S := fun h => Finset.disjoint_left.mp h4 h huN
    dsimp only
    by_cases hb : u ∈ b
    · rw [if_pos hb]
      unfold Inv
      dsimp only
      obtain ⟨hsub, himp⟩ := hsel (insert u st.O) (insert u st.S)
      have heq : insert u st.O \ (insert u st.O \ insert u st.S) = insert u st.S := by
        ext w
        have := @h2 w
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        tauto
      have hex : ∃ Y ⊆ insert u st.O \ insert u st.S, I (insert u st.O \ Y) :=
        ⟨insert u st.O \ insert u st.S, subset_rfl, by rw [heq]; exact huI⟩
      refine ⟨(himp hex).1, ?_, ?_, ?_⟩
      · intro w hw
        rw [Finset.mem_sdiff]
        refine ⟨?_, fun hR => ?_⟩
        · rw [Finset.mem_insert] at hw ⊢
          rcases hw with hw | hw
          · exact Or.inl hw
          · exact Or.inr (h2 hw)
        · exact (Finset.mem_sdiff.mp (hsub hR)).2 hw
      · intro w hw
        rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert] at hw
        rw [Finset.mem_erase]
        push_neg at hw
        obtain ⟨⟨hw1, -⟩, hwu, hwS⟩ := hw
        exact ⟨hwu, h3 (Finset.mem_sdiff.mpr ⟨hw1.resolve_left hwu, hwS⟩)⟩
      · rw [Finset.disjoint_left]
        intro w hw hw'
        rw [Finset.mem_insert] at hw
        rw [Finset.mem_erase] at hw'
        rcases hw with rfl | hw
        · exact hw'.1 rfl
        · exact Finset.disjoint_left.mp h4 hw hw'.2
    · rw [if_neg hb]
      unfold Inv
      dsimp only
      refine ⟨hI.2 _ _ Finset.sdiff_subset h1, ?_, ?_,
        Disjoint.mono_right (Finset.erase_subset _ _) h4⟩
      · intro w hw
        rw [Finset.mem_sdiff]
        refine ⟨h2 hw, fun hR => ?_⟩
        split_ifs at hR with hO
        · rw [Finset.mem_singleton] at hR
          subst hR
          exact huS hw
        · simp at hR
      · intro w hw
        rw [Finset.mem_sdiff, Finset.mem_sdiff] at hw
        obtain ⟨⟨hwO, hwR⟩, hwS⟩ := hw
        rw [Finset.mem_erase]
        refine ⟨fun hwu => ?_, h3 (Finset.mem_sdiff.mpr ⟨hwO, hwS⟩)⟩
        subst hwu
        apply hwR
        rw [if_pos hwO]
        exact Finset.mem_singleton_self _
  · exact ⟨h1, h2, h3, h4⟩

end Aux_SubsamplingSM_lemma5

open SubsamplingSM.Offline in
theorem solution {α : Type*} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (hI : IsIndepSystem I)
    (sel : Finset α → Finset α → Finset α) (hsel : IsMinRemoval I sel)
    (O₀ : Finset α) (hO₀ : I O₀) :
    ∀ (b : Finset α) (t : ℕ),
      I ((alg2Step f I sel b)^[t] (alg2Init O₀)).O ∧
      ((alg2Step f I sel b)^[t] (alg2Init O₀)).S ⊆ ((alg2Step f I sel b)^[t] (alg2Init O₀)).O ∧
      ((alg2Step f I sel b)^[t] (alg2Init O₀)).O \ ((alg2Step f I sel b)^[t] (alg2Init O₀)).S ⊆
        ((alg2Step f I sel b)^[t] (alg2Init O₀)).N' := by
  intro b t
  have key : Aux_SubsamplingSM_lemma5.Inv I ((alg2Step f I sel b)^[t] (alg2Init O₀)) := by
    induction t with
    | zero =>
      refine ⟨hO₀, Finset.empty_subset _, fun w _ => Finset.mem_univ w, Finset.disjoint_empty_left _⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact Aux_SubsamplingSM_lemma5.step_inv f I hI sel hsel b _ ih
  exact ⟨key.1, key.2.1, key.2.2.1⟩
