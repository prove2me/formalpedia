-- Prove2me | solution 1 for OnlineCRS.Submod.char_crs_is_crs
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:41:53.749388+00:00
-- url     : https://prove2.me/submissions/e6174f1f-67ca-44fd-b2ea-b420ea71b40d

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Submod_Model
import Definitions.Def_OnlineCRS_Submod_CRS

set_option autoImplicit false

namespace OnlineCRS.Submod

lemma greedyRun_aux {α : Type} [DecidableEq α] (Fam : Finset (Finset α))
    (hdown : ∀ I ∈ Fam, ∀ J : Finset α, J ⊆ I → J ∈ Fam) (A : Finset α) :
    ∀ (σ : List α) (S0 : Finset α), S0 ⊆ A → S0 ∈ Fam →
      σ.foldl (fun S e => if e ∈ A ∧ insert e S ∈ Fam then insert e S else S) S0 ⊆ A ∧
      σ.foldl (fun S e => if e ∈ A ∧ insert e S ∈ Fam then insert e S else S) S0 ∈ Fam ∧
      S0 ⊆ σ.foldl (fun S e => if e ∈ A ∧ insert e S ∈ Fam then insert e S else S) S0 ∧
      ∀ e ∈ σ, OnlineCRS.Matroid.Selectable Fam A e → e ∈ A →
        e ∈ σ.foldl (fun S e => if e ∈ A ∧ insert e S ∈ Fam then insert e S else S) S0 := by
  intro σ
  induction σ with
  | nil => intro S0 h1 h2; simp [h1, h2]
  | cons a σ ih =>
    intro S0 h1 h2
    simp only [List.foldl_cons]
    set S1 := (if a ∈ A ∧ insert a S0 ∈ Fam then insert a S0 else S0) with hS1
    have hS1A : S1 ⊆ A ∧ S1 ∈ Fam ∧ S0 ⊆ S1 ∧
        (OnlineCRS.Matroid.Selectable Fam A a → a ∈ A → a ∈ S1) := by
      by_cases hc : a ∈ A ∧ insert a S0 ∈ Fam
      · rw [hS1, if_pos hc]
        refine ⟨?_, hc.2, Finset.subset_insert _ _, fun _ _ => Finset.mem_insert_self _ _⟩
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hc.1
        · exact h1 hx
      · rw [hS1, if_neg hc]
        refine ⟨h1, h2, subset_rfl, ?_⟩
        intro hsel haA
        exact absurd ⟨haA, hsel S0 h1 h2⟩ hc
    obtain ⟨a1, a2, a3, a4⟩ := hS1A
    obtain ⟨b1, b2, b3, b4⟩ := ih S1 a1 a2
    refine ⟨b1, b2, a3.trans b3, ?_⟩
    intro e he hsel heA
    rcases List.mem_cons.1 he with rfl | he
    · exact b3 (a4 hsel heA)
    · exact b4 e he hsel heA

lemma charMap_sub_run {α : Type} [Fintype α] [DecidableEq α] (𝓕 : Finset α → Prop)
    (Fam : Finset (Finset α)) (hFam : OnlineCRS.Matroid.IsGreedyFamily 𝓕 Fam) (A : Finset α)
    (σ : List α) (hσ : IsOrder σ) :
    charMap Fam A ⊆ greedyRun Fam A σ ∧ greedyRun Fam A σ ∈ Fam := by
  obtain ⟨h0, hdown, _⟩ := hFam
  obtain ⟨b1, b2, b3, b4⟩ := greedyRun_aux Fam hdown A σ ∅ (Finset.empty_subset _) h0
  refine ⟨?_, b2⟩
  intro e he
  classical
  unfold charMap at he
  rw [Finset.mem_filter] at he
  exact b4 e (hσ.2 e) he.2 he.1


open Classical in
lemma charCRS_apply {α : Type} [Fintype α] [DecidableEq α]
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (x : α → ℝ) (φ : Finset α → Finset α) :
    charCRS w x φ = ∑ Fam : Finset (Finset α), w x Fam * (if φ = charMap Fam then 1 else 0) := rfl

end OnlineCRS.Submod

open OnlineCRS.Submod in
theorem solution {α : Type} [Fintype α] [DecidableEq α] (𝓕 : Finset α → Prop)
    (P : Set (α → ℝ)) (hPoly : IsPolytope P) (hRel : IsRelaxation 𝓕 P)
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (hw : OnlineCRS.Matroid.IsRandGreedyOCRS 𝓕 w) :
    IsCRS P (charCRS w) := by
  classical
  intro x
  obtain ⟨hw0, hw1, hwg⟩ := hw x
  refine ⟨?_, ?_, ?_⟩
  · intro φ
    rw [charCRS_apply]
    exact Finset.sum_nonneg (fun Fam _ => mul_nonneg (hw0 Fam) (by split_ifs <;> norm_num))
  · simp only [charCRS_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
    exact hw1
  · intro φ hφ S
    rw [charCRS_apply] at hφ
    obtain ⟨Fam, -, hF⟩ := Finset.exists_ne_zero_of_sum_ne_zero hφ
    have hw' : w x Fam ≠ 0 := by
      intro h; apply hF; simp [h]
    have hφeq : φ = charMap Fam := by
      by_contra h; apply hF; simp [h]
    subst hφeq
    have hg := hwg Fam hw'
    refine ⟨?_, ?_⟩
    · intro e he
      unfold charMap at he
      exact (Finset.mem_filter.1 he).1
    · rw [hRel.2.2]
      obtain ⟨hr1, hr2⟩ := charMap_sub_run 𝓕 Fam hg S (Finset.univ.toList)
        ⟨Finset.nodup_toList _, fun e => Finset.mem_toList.2 (Finset.mem_univ e)⟩
      exact hRel.1 _ _ (hr1) (hg.2.2 _ hr2)
