-- Prove2me | solution 1 for SeqSubmod.Discrete.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:57:10.896831+00:00
-- url     : https://prove2.me/submissions/88bfed37-157f-4bd0-b389-d8e82ae4d79c

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

theorem solution {S : Type*} (u : List S → ℝ) (hu : IsSeqSubmodular u) (A B : List S)
    (hB : B ≠ []) :
    ∃ s : S, (1 / (B.length : ℝ)) * marginal u B A ≤ marginal u [s] A :=
  ss_lemma10 u hu A B hB
