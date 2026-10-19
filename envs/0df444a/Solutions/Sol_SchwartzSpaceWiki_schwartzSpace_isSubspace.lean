-- Prove2me | solution 1 for SchwartzSpaceWiki.schwartzSpace_isSubspace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:01:37.230992+00:00
-- url     : https://prove2.me/submissions/20a86ab5-de70-429e-a04d-ddaa8c0b3bf9

import Definitions.Def_SchwartzSpaceWiki_Defs

open SchwartzSpaceWiki
open scoped ENNReal

private lemma partial_smooth {n : ℕ} (i : Fin n) (f : Rn n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (partialDeriv i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private lemma partial_linear {n : ℕ} (i : Fin n) (f g : Rn n → ℂ) (c : ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    partialDeriv i (f + c • g) = partialDeriv i f + c • partialDeriv i g := by
  ext x
  have hf' := hf.differentiable (by simp)
  have hg' := hg.differentiable (by simp)
  simp only [partialDeriv, Pi.add_apply, Pi.smul_apply]
  rw [fderiv_add (hf' x) ((hg'.const_smul c) x), fderiv_const_smul (hg' x)]
  simp

private lemma iterate_linear {n : ℕ} (i : Fin n) (k : ℕ) (f g : Rn n → ℂ) (c : ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) ((partialDeriv i)^[k] f) ∧
    ContDiff ℝ (⊤ : ℕ∞) ((partialDeriv i)^[k] g) ∧
    (partialDeriv i)^[k] (f + c • g) =
      (partialDeriv i)^[k] f + c • (partialDeriv i)^[k] g := by
  induction k with
  | zero => exact ⟨hf, hg, rfl⟩
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact ⟨partial_smooth i _ ih.1, partial_smooth i _ ih.2.1,
      ih.2.2 ▸ partial_linear i _ _ c ih.1 ih.2.1⟩

private lemma multi_linear {n : ℕ} (β : MultiIndex n) (f g : Rn n → ℂ) (c : ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    iteratedPartialDeriv β (f + c • g) =
      iteratedPartialDeriv β f + c • iteratedPartialDeriv β g := by
  have h : ∀ l : List (Fin n),
      ContDiff ℝ (⊤ : ℕ∞) (l.foldr (fun i h => (partialDeriv i)^[β i] h) f) ∧
      ContDiff ℝ (⊤ : ℕ∞) (l.foldr (fun i h => (partialDeriv i)^[β i] h) g) ∧
      l.foldr (fun i h => (partialDeriv i)^[β i] h) (f + c • g) =
        l.foldr (fun i h => (partialDeriv i)^[β i] h) f +
          c • l.foldr (fun i h => (partialDeriv i)^[β i] h) g := by
    intro l
    induction l with
    | nil => exact ⟨hf, hg, rfl⟩
    | cons i l ih =>
      simp only [List.foldr_cons]
      exact ⟨(iterate_linear i (β i) _ _ c ih.1 ih.2.1).1,
        (iterate_linear i (β i) _ _ c ih.1 ih.2.1).2.1,
        ih.2.2 ▸ (iterate_linear i (β i) _ _ c ih.1 ih.2.1).2.2⟩
  exact (h (List.finRange n)).2.2

private lemma multi_zero {n : ℕ} (β : MultiIndex n) :
    iteratedPartialDeriv β (0 : Rn n → ℂ) = 0 := by
  have h := multi_linear β 0 0 1 contDiff_const contDiff_const
  simp only [one_smul, add_zero] at h
  exact (add_left_cancel (show iteratedPartialDeriv β 0 + iteratedPartialDeriv β 0 =
    iteratedPartialDeriv β 0 + 0 by simpa using h.symm))

theorem solution (n : ℕ) :
    (0 : Rn n → ℂ) ∈ schwartzSpace n ∧
    (∀ f ∈ schwartzSpace n, ∀ g ∈ schwartzSpace n, f + g ∈ schwartzSpace n) ∧
    (∀ (c : ℂ), ∀ f ∈ schwartzSpace n, c • f ∈ schwartzSpace n) := by
  have hz : (0 : Rn n → ℂ) ∈ schwartzSpace n := by
    refine ⟨contDiff_const, ?_⟩
    intro α β
    simp [schwartzSeminorm, multi_zero]
  refine ⟨hz, ?_, ?_⟩
  · intro f hf g hg
    refine ⟨hf.1.add hg.1, ?_⟩
    intro α β
    have hd := multi_linear β f g 1 hf.1 hg.1
    simp only [one_smul] at hd
    apply lt_of_le_of_lt (b := schwartzSeminorm α β f + schwartzSeminorm α β g)
    · apply iSup_le
      intro x
      simp only [hd, Pi.add_apply, mul_add]
      exact (enorm_add_le _ _).trans
        (add_le_add (le_iSup (fun x => ‖(monomial α x : ℂ) *
          iteratedPartialDeriv β f x‖ₑ) x)
          (le_iSup (fun x => ‖(monomial α x : ℂ) * iteratedPartialDeriv β g x‖ₑ) x))
    · exact ENNReal.add_lt_top.mpr ⟨hf.2 α β, hg.2 α β⟩
  · intro c f hf
    refine ⟨contDiff_const.smul hf.1, ?_⟩
    intro α β
    have hd := multi_linear β 0 f c hz.1 hf.1
    simp only [zero_add, multi_zero] at hd
    apply lt_of_le_of_lt (b := ‖c‖ₑ * schwartzSeminorm α β f)
    · apply iSup_le
      intro x
      simp only [hd, Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, enorm_mul]
      exact mul_le_mul' le_rfl (le_iSup (fun x => ‖(monomial α x : ℂ) *
        iteratedPartialDeriv β f x‖ₑ) x)
    · exact ENNReal.mul_lt_top (by simp) (hf.2 α β)
