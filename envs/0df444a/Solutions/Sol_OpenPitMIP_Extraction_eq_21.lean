-- Prove2me | solution 1 for OpenPitMIP.Extraction.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:35:47.268693+00:00
-- url     : https://prove2.me/submissions/da9d7a0f-f268-48f4-879c-27878b9ea0fd

import Mathlib
import Definitions.Def_OpenPitMIP_Extraction_Setting

set_option autoImplicit false
open OpenPitMIP.Extraction

theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible .F x y) :
    ∀ (c : C) (t : Fin T), PCPSPC.cum x c t = 0 ∨ PCPSPC.cum x c t = 1 := by
  intro c t
  have h01 : ∀ t', x c t' = 0 ∨ x c t' = 1 := fun t' => hxy.2.2.2.2.2 c t'
  have hnn : ∀ t', 0 ≤ x c t' := fun t' => by rcases h01 t' with h | h <;> rw [h] <;> norm_num
  have htot : ∑ t', x c t' ≤ 1 := hxy.2.1 c
  unfold PCPSPC.cum
  by_cases hall : ∀ t' ∈ Finset.Iic t, x c t' = 0
  · left
    exact Finset.sum_eq_zero hall
  · right
    push_neg at hall
    obtain ⟨t0, ht0, hne⟩ := hall
    have h1 : x c t0 = 1 := (h01 t0).resolve_left hne
    have hle : ∑ t' ∈ Finset.Iic t, x c t' ≤ 1 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hnn i)) htot
    have hge : x c t0 ≤ ∑ t' ∈ Finset.Iic t, x c t' :=
      Finset.single_le_sum (f := fun t' => x c t') (fun i _ => hnn i) ht0
    linarith
