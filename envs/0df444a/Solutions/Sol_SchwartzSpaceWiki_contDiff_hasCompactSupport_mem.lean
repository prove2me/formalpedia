-- Prove2me | solution 1 for SchwartzSpaceWiki.contDiff_hasCompactSupport_mem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:56:15.164962+00:00
-- url     : https://prove2.me/submissions/46657f0a-aeef-4a46-8553-4ea9a16829c5

import Definitions.Def_SchwartzSpaceWiki_Defs

open SchwartzSpaceWiki
open scoped ENNReal

private lemma partial_spec {n : ℕ} (i : Fin n) (f : Rn n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (partialDeriv i f) ∧ HasCompactSupport (partialDeriv i f) := by
  constructor
  · exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  · exact hs.fderiv_apply ℝ _

private lemma iterate_spec {n : ℕ} (i : Fin n) (k : ℕ) (f : Rn n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) ((partialDeriv i)^[k] f) ∧
      HasCompactSupport ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => exact ⟨hf, hs⟩
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using partial_spec i _ ih.1 ih.2

private lemma multi_spec {n : ℕ} (β : MultiIndex n) (f : Rn n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedPartialDeriv β f) ∧
      HasCompactSupport (iteratedPartialDeriv β f) := by
  unfold iteratedPartialDeriv
  generalize List.finRange n = l
  induction l with
  | nil => exact ⟨hf, hs⟩
  | cons i l ih => exact iterate_spec i (β i) _ ih.1 ih.2

theorem solution (n : ℕ) (f : Rn n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f) :
    f ∈ schwartzSpace n := by
  refine ⟨hf, ?_⟩
  intro α β
  obtain ⟨hd, hs⟩ := multi_spec β f hf hsupp
  have hm : Continuous (fun x : Rn n => (monomial α x : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    unfold monomial
    fun_prop
  have hc : Continuous (fun x => (monomial α x : ℂ) * iteratedPartialDeriv β f x) :=
    hm.mul hd.continuous
  have hs' : HasCompactSupport (fun x => (monomial α x : ℂ) * iteratedPartialDeriv β f x) :=
    hs.mul_left
  obtain ⟨C, hC⟩ := hs'.exists_bound_of_continuous hc
  apply lt_of_le_of_lt (iSup_le (fun x => ?_)) (ENNReal.ofReal_lt_top : ENNReal.ofReal C < ⊤)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC x)
