-- Prove2me | solution 1 for SeqSubmod.Discrete.eq_38
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:57:08.8016+00:00
-- url     : https://prove2.me/submissions/a64ab99e-9184-4fd1-8cd0-fd61f3e0bfd0

import Mathlib
import Definitions.Def_SeqSubmod_Discrete_Setting

set_option autoImplicit false
open SeqSubmod.Discrete

private theorem ss_marg_cons {S : Type*} (u : List S → ℝ) (b : S) (B A : List S) :
    marginal u (b :: B) A = marginal u [b] A + marginal u B (A ++ [b]) := by
  unfold marginal
  have : A ++ b :: B = (A ++ [b]) ++ B := by simp
  rw [this]; ring

private theorem ss_marg_le_sum {S : Type*} (u : List S → ℝ) (hu : IsSeqSubmodular u)
    (A : List S) : ∀ B : List S, marginal u B A ≤ (B.map (fun b => marginal u [b] A)).sum := by
  intro B
  induction B with
  | nil => simp [marginal]
  | cons b B ih =>
    rw [ss_marg_cons]
    have h1 : marginal u B (A ++ [b]) ≤ marginal u B A :=
      hu A (A ++ [b]) B (List.sublist_append_left _ _)
    simp only [List.map_cons, List.sum_cons]
    linarith

private theorem ss_lemma10 {S : Type*} (u : List S → ℝ) (hu : IsSeqSubmodular u) (A B : List S)
    (hB : B ≠ []) :
    ∃ s : S, (1 / (B.length : ℝ)) * marginal u B A ≤ marginal u [s] A := by
  classical
  have hne : B.toFinset.Nonempty := by
    rw [List.toFinset_nonempty_iff]; exact hB
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image B.toFinset (fun b => marginal u [b] A) hne
  refine ⟨s, ?_⟩
  have hsum : (B.map (fun b => marginal u [b] A)).sum ≤ B.length • marginal u [s] A := by
    have := List.sum_le_card_nsmul (B.map (fun b => marginal u [b] A)) (marginal u [s] A) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact hmax b (List.mem_toFinset.mpr hb))
    simpa using this
  have hpos : (0 : ℝ) < B.length := by
    exact_mod_cast List.length_pos_iff.mpr hB
  have h2 := ss_marg_le_sum u hu A B
  rw [nsmul_eq_mul] at hsum
  rw [one_div, inv_mul_le_iff₀ hpos]
  linarith

private theorem ss_eq38 {S : Type*} [Fintype S] [Nonempty S] (u : List S → ℝ) (hu : Assumption2 u)
    (α : ℝ) (hα0 : 0 ≤ α) (H : List S) (hH : IsAlphaGreedy u α H)
    (O : List S) (hO : O.length ≤ H.length) (i : ℕ) (hi : i < H.length) :
    α / H.length * (u O - u (H.take i)) ≤ marginal u [H[i]] (H.take i) := by
  obtain ⟨⟨hmono, hzero⟩, hsub⟩ := hu
  have hg := hH i hi
  set A := H.take i with hA
  have hpos : (0 : ℝ) < H.length := by exact_mod_cast (by omega : 0 < H.length)
  have hnn : 0 ≤ marginal u [H[i]] A := by
    unfold marginal
    have := hmono A (A ++ [H[i]]) (List.sublist_append_left _ _)
    linarith
  by_cases hOe : O = []
  · subst hOe
    have h0 : 0 ≤ u A := by
      have := hmono [] A (List.nil_sublist _); linarith
    have : α / H.length * (u [] - u A) ≤ 0 := by
      rw [hzero]
      have : 0 ≤ α / H.length := by positivity
      nlinarith
    linarith
  · have hOne := hOe
    obtain ⟨s, hs⟩ := ss_lemma10 u hsub A O hOne
    have hsup : marginal u [s] A ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun s : S => marginal u [s] A) :=
      Finset.le_sup' (fun s : S => marginal u [s] A) (Finset.mem_univ s)
    have hOpos : (0 : ℝ) < O.length := by
      exact_mod_cast List.length_pos_iff.mpr hOne
    have hm : 0 ≤ marginal u O A := by
      unfold marginal
      have := hmono A (A ++ O) (List.sublist_append_left _ _)
      linarith
    have hu1 : u O - u A ≤ marginal u O A := by
      unfold marginal
      have := hmono O (A ++ O) (List.sublist_append_right _ _)
      linarith
    have hle : (1 : ℝ) / H.length ≤ 1 / O.length :=
      one_div_le_one_div_of_le hOpos (by exact_mod_cast hO)
    have h3 : α / H.length * (u O - u A) ≤ α * ((1 / (O.length : ℝ)) * marginal u O A) := by
      have e1 : α / H.length * (u O - u A) ≤ α / H.length * marginal u O A :=
        mul_le_mul_of_nonneg_left hu1 (by positivity)
      have e2 : α / H.length * marginal u O A ≤ α * ((1 / (O.length : ℝ)) * marginal u O A) := by
        have : α / H.length = α * (1 / H.length) := by ring
        rw [this, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hm) hα0
      linarith
    have h4 : α * ((1 / (O.length : ℝ)) * marginal u O A) ≤
        α * Finset.univ.sup' Finset.univ_nonempty (fun s : S => marginal u [s] A) :=
      mul_le_mul_of_nonneg_left (hs.trans hsup) hα0
    linarith

theorem solution {S : Type*} [Fintype S] [Nonempty S] (u : List S → ℝ) (hu : Assumption2 u)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (H : List S) (hH : IsAlphaGreedy u α H)
    (O : List S) (hO : O.length ≤ H.length) (i : ℕ) (hi : i < H.length) :
    α / H.length * (u O - u (H.take i)) ≤ marginal u [H[i]] (H.take i) :=
  ss_eq38 u hu α hα0 H hH O hO i hi
