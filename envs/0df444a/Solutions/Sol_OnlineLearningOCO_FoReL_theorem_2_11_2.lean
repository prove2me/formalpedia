-- Prove2me | solution 2 for OnlineLearningOCO.FoReL.theorem_2_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:50:36.094441+00:00
-- url     : https://prove2.me/submissions/123fad54-35be-48be-b9e9-1459ddc9463b

import Mathlib
import Definitions.Def_OnlineLearningOCO_FoReL_regret
import Definitions.Def_OnlineLearningOCO_FoReL_IsFoReLRun
import Theorems.Thm_OnlineLearningOCO_FoReL_lemma_2_10

-- carved verbatim out of submission 51414896-7d2e-4bef-af01-02ffef0530b5, lines 139-178

section
set_option autoImplicit false
open OnlineLearningOCO.FoReL

theorem OLF_23_aux {E : Type*} (S : Set E) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hw : IsFoReLRun S f R w) (T : ℕ) :
    ∀ u ∈ S, ∑ t ∈ Finset.Icc 1 T, f t (w (t + 1)) + R (w 1) ≤
      ∑ t ∈ Finset.Icc 1 T, f t u + R u := by
  induction T with
  | zero =>
    intro u hu
    obtain ⟨_, hm⟩ := hw 1 le_rfl
    simpa using hm u hu
  | succ T ih =>
    intro u hu
    obtain ⟨hS2, hm2⟩ := hw (T + 2) (by omega)
    have h1 := ih (w (T + 2)) hS2
    have h2 := hm2 u hu
    have hI : Finset.Ico 1 (T + 2) = Finset.Icc 1 (T + 1) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hI, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)] at h2
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    linarith

theorem OLF_lemma_2_3 {E : Type*} (S : Set E) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hw : IsFoReLRun S f R w) (T : ℕ) :
    ∀ u ∈ S,
      ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t u)
        ≤ R u - R (w 1) + ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t (w (t + 1))) := by
  intro u hu
  have := OLF_23_aux S f R w hw T u hu
  simp only [Finset.sum_sub_distrib]
  linarith

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (hσ : 0 < σ) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hR : StrongConvexOn S σ R) (T : ℕ) (hT : 0 < T)
    (hf : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ S (f t))
    (Lt : ℕ → ℝ)
    (hLip : ∀ t ∈ Finset.Icc 1 T, ∀ u ∈ S, ∀ v ∈ S, |f t u - f t v| ≤ Lt t * ‖u - v‖)
    (L : ℝ) (hL : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, Lt t ^ 2 ≤ L ^ 2)
    (hw : IsFoReLRun S f R w) :
    ∀ u ∈ S, regret f w T u ≤ R u - sInf (R '' S) + T * L ^ 2 / σ := by
  intro u hu
  have hw1S : w 1 ∈ S := (hw 1 le_rfl).1
  have hmin : R (w 1) = sInf (R '' S) := by
    symm
    apply IsLeast.csInf_eq
    refine ⟨⟨w 1, hw1S, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have := (hw 1 le_rfl).2 v hv
    simpa using this
  have h23 := OLF_lemma_2_3 S f R w hw T u hu
  have h210 : ∀ t ∈ Finset.Icc 1 T, f t (w t) - f t (w (t + 1)) ≤ Lt t ^ 2 / σ := by
    intro t ht
    have ht' := Finset.mem_Icc.1 ht
    have := OnlineLearningOCO.FoReL.lemma_2_10 S σ hσ f R w hR t ht'.1
      (fun i hi => hf i (by simp only [Finset.mem_Icc] at hi ⊢; omega)) (Lt t) (hLip t ht) hw
    exact le_trans this.1 this.2
  have hsum : ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t (w (t + 1))) ≤ ∑ t ∈ Finset.Icc 1 T, Lt t ^ 2 / σ :=
    Finset.sum_le_sum h210
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hsq : ∑ t ∈ Finset.Icc 1 T, Lt t ^ 2 ≤ T * L ^ 2 := by
    have := hL
    rw [one_div, inv_mul_le_iff₀ hTpos] at this
    exact this
  have hdiv : ∑ t ∈ Finset.Icc 1 T, Lt t ^ 2 / σ ≤ T * L ^ 2 / σ := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hsq hσ.le
  unfold regret
  rw [hmin] at h23
  rw [Finset.sum_sub_distrib] at h23
  linarith

end
