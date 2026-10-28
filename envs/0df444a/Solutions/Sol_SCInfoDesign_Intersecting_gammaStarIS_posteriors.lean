-- Prove2me | solution 1 for SCInfoDesign.Intersecting.gammaStarIS_posteriors
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:44:59.163896+00:00
-- url     : https://prove2.me/submissions/271ed07a-8c06-4f8f-a1e7-bfa4fc907b0d

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

open SCInfoDesign.Intersecting in
theorem solution (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p₀ : ℝ) (hp₀ : 0 ≤ p₀) (hreg : P.ξ < P.τlowIS p₀) :
    SCInfoDesign.Nested.IsPolicy (P.gammaStarIS p₀) ∧
    SCInfoDesign.Nested.msgProb p₀ (P.gammaStarIS p₀) 0 = p₀ / P.pbreve ∧
    SCInfoDesign.Nested.msgProb p₀ (P.gammaStarIS p₀) 1 = 1 - p₀ / P.pbreve ∧
    (0 < p₀ → SCInfoDesign.Nested.posterior p₀ (P.gammaStarIS p₀) 0 = P.pbreve) ∧
    SCInfoDesign.Nested.posterior p₀ (P.gammaStarIS p₀) 1 = 0 := by
  have hL : 0 < P.b₁ - P.a₁ := by linarith
  have hA : 0 < P.a₀ - P.a₁ := by linarith
  have hreg' : P.ξ * (P.b₁ - P.a₁) < (1 - p₀) * (P.a₀ - P.a₁) := by
    unfold Params.τlowIS at hreg
    rwa [lt_div_iff₀ hL] at hreg
  have hξL : 0 < P.ξ * (P.b₁ - P.a₁) := mul_pos hξ0 hL
  have hp1 : p₀ < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hq : 0 < 1 - p₀ := by linarith
  have hD : 0 < (P.a₀ - P.a₁) - P.ξ * (P.b₁ - P.a₁) := by nlinarith
  have hpb : P.pbreve = ((P.a₀ - P.a₁) - P.ξ * (P.b₁ - P.a₁)) / (P.a₀ - P.a₁) := by
    unfold Params.pbreve
    rw [sub_div, div_self hA.ne']
  obtain ⟨r, hr⟩ : ∃ r, r = P.ξ * (P.b₁ - P.a₁) / ((P.a₀ - P.a₁) - P.ξ * (P.b₁ - P.a₁)) *
      (p₀ / (1 - p₀)) := ⟨_, rfl⟩
  have hg : P.gammaStarIS p₀ = ![![1, 0], ![r, 1 - r]] := by rw [hr]; rfl
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact mul_nonneg (div_nonneg hξL.le hD.le) (div_nonneg hp₀ hq.le)
  have hr1 : r ≤ 1 := by
    rw [hr, div_mul_div_comm, div_le_one (mul_pos hD hq)]
    nlinarith
  have hm0 : SCInfoDesign.Nested.msgProb p₀ (P.gammaStarIS p₀) 0 = p₀ / P.pbreve := by
    unfold SCInfoDesign.Nested.msgProb
    rw [hg, hpb, hr]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    field_simp
    ring
  have hm1 : SCInfoDesign.Nested.msgProb p₀ (P.gammaStarIS p₀) 1 = 1 - p₀ / P.pbreve := by
    rw [← hm0]
    unfold SCInfoDesign.Nested.msgProb
    rw [hg]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  refine ⟨?_, hm0, hm1, ?_, ?_⟩
  · rw [hg]
    refine ⟨?_, ?_⟩
    · intro ω m
      fin_cases ω <;> fin_cases m <;> simp <;> linarith
    · intro ω
      fin_cases ω <;> simp [Fin.sum_univ_two]
  · intro hp
    unfold SCInfoDesign.Nested.posterior
    rw [hm0, hpb]
    rw [hg]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    field_simp
  · unfold SCInfoDesign.Nested.posterior
    rw [hg]
    simp
