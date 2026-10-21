-- Prove2me | solution 1 for SeqSubmod.Discrete.eq_41
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:57:09.801984+00:00
-- url     : https://prove2.me/submissions/04b4bc49-1266-4a3b-b04a-86d3fb6d4521

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

private theorem ss_eq41 {S : Type*} [Fintype S] [Nonempty S] (u : List S → ℝ) (hu : Assumption2 u)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (H : List S) (hH : IsAlphaGreedy u α H)
    (O : List S) (hO : O.length ≤ H.length) :
    (1 - (1 - α / H.length) ^ H.length) * u O ≤ u H := by
  rcases Nat.eq_zero_or_pos H.length with hk | hk
  · have : H = [] := List.length_eq_zero_iff.mp hk
    subst this
    simp [hu.1.2]
  · have hkr : (1 : ℝ) ≤ H.length := by exact_mod_cast hk
    set c : ℝ := α / H.length with hc
    have hc0 : 0 ≤ c := by positivity
    have hc1 : c ≤ 1 := by
      rw [hc, div_le_one (by linarith)]; linarith
    have key : ∀ i : ℕ, i ≤ H.length → (1 - (1 - c) ^ i) * u O ≤ u (H.take i) := by
      intro i
      induction i with
      | zero => intro _; simp [hu.1.2]
      | succ i ih =>
        intro hi
        have ih' := ih (by omega)
        have h38 := ss_eq38 u hu α hα0 H hH O hO i (by omega)
        have htk : H.take (i + 1) = H.take i ++ [H[i]] := by
          rw [List.take_succ]; simp [List.getElem?_eq_getElem (by omega : i < H.length)]
        have hm : marginal u [H[i]] (H.take i) = u (H.take (i + 1)) - u (H.take i) := by
          unfold marginal; rw [htk]
        rw [hm, ← hc] at h38
        have h1c : 0 ≤ 1 - c := by linarith
        have := mul_le_mul_of_nonneg_left ih' h1c
        rw [pow_succ]
        nlinarith
    simpa using key H.length le_rfl

theorem solution {S : Type*} [Fintype S] [Nonempty S] (u : List S → ℝ) (hu : Assumption2 u)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (H : List S) (hH : IsAlphaGreedy u α H)
    (O : List S) (hO : O.length ≤ H.length) :
    (1 - (1 - α / H.length) ^ H.length) * u O ≤ u H :=
  ss_eq41 u hu α hα0 hα1 H hH O hO
