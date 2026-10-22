-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:54:32.875068+00:00
-- url     : https://prove2.me/submissions/4d43b180-4a3b-419a-909a-901179d79389

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
import Theorems.Thm_TwoStageSRO_AsymOpt_eq_3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace SROLemma2Aux
open TwoStageSRO.AsymOpt

variable {n d r m mt : ℕ}

/-- The worst-case cost of an affine policy over a (bounded) set `B(ẑ, ε) ∩ S` is finite. -/
theorem robCost_affine_lt_top (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (z : Fin d → ℝ) (ε : ℝ) (S : Set (Fin d → ℝ)) (y0 : Fin r → ℝ)
    (Y : Matrix (Fin r) (Fin d) ℝ) :
    robCost M (ball p z ε ∩ S) (fun ζ => y0 + Y *ᵥ ζ) < ⊤ := by
  let K : Set (Fin d → ℝ) :=
    (fun u : PiLp p (fun _ : Fin d => ℝ) => z + WithLp.ofLp u) ''
      Metric.closedBall (0 : PiLp p (fun _ : Fin d => ℝ)) ε
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image (continuous_const.add (PiLp.continuous_ofLp p _))
  have hsub : ball p z ε ⊆ K := by
    intro ζ hζ
    refine ⟨WithLp.toLp p (ζ - z), ?_, ?_⟩
    · rw [mem_closedBall_zero_iff]; exact hζ
    · simp
  have hg : Continuous fun ζ : Fin d → ℝ => M.q ⬝ᵥ (y0 + Y *ᵥ ζ) :=
    continuous_const.dotProduct (continuous_const.add (continuous_const.matrix_mulVec
      continuous_id))
  obtain ⟨B, hB⟩ := hK.bddAbove_image hg.continuousOn
  have : robCost M (ball p z ε ∩ S) (fun ζ => y0 + Y *ᵥ ζ) ≤ (B : EReal) := by
    unfold robCost
    refine iSup₂_le fun ζ hζ => ?_
    exact EReal.coe_le_coe_iff.2 (hB ⟨ζ, hsub hζ.1, rfl⟩)
  exact lt_of_le_of_lt this (EReal.coe_lt_top B)

end SROLemma2Aux

open TwoStageSRO.AsymOpt SROLemma2Aux in
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hsupp : μ (Xi M)ᶜ = 0)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ))
    (xs : Fin n → ℝ) (hxs : xs ∈ optSet M μ)
    (x : Fin n → ℝ) (C : Set (Matrix (Fin r) (Fin d) ℝ)) (εbar : ℝ) (hεbar : 0 < εbar)
    (hfeas : ∀ ζ ∈ XiStar M xs, QC M p C εbar x ζ < ⊤) :
    ∀ lam ∈ Set.Ioo (0 : ℝ) 1, ∃ ε : ℝ, 0 < ε ∧
      ∀ ζ ∈ XiStar M xs, QC M p C ε (lam • xs + (1 - lam) • x) ζ < ⊤ := by
  intro lam hlam
  -- `κ = 1 - λ` is the weight of `x`
  set κ : ℝ := 1 - lam with hκ
  have hκ' : κ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by rw [hκ]; linarith [hlam.2], by rw [hκ]; linarith [hlam.1]⟩
  obtain ⟨ε, hε, hinc⟩ := eq_3 M p μ hsupp hA2 hA3 xs hxs κ hκ' εbar hεbar
  refine ⟨ε, hε, fun zhat hzhat => ?_⟩
  obtain ⟨zbar, hzbar, hsub⟩ := hinc zhat hzhat
  -- a feasible linear rule around `zbar` for `x`, display (4)
  have h4 := hfeas zbar hzbar
  unfold QC at h4
  rw [iInf_lt_iff] at h4
  obtain ⟨⟨y0, Y⟩, h4⟩ := h4
  rw [iInf_lt_iff] at h4
  obtain ⟨⟨hYC, hrob⟩, -⟩ := h4
  -- a feasible recourse at `zbar` for `x*`, display (5)
  obtain ⟨-, ystar, h5⟩ := hzbar
  -- the combined rule
  set yhat : Fin r → ℝ := κ • y0 + (1 - κ) • ystar - (1 - κ) • (Y *ᵥ zbar) with hyhat
  have hfeasNew : robFeas M (lam • xs + (1 - lam) • x) (ball p zhat ε ∩ Xi M)
      (fun ζ => yhat + Y *ᵥ ζ) := by
    intro ζ' hζ'
    obtain ⟨ζ, hζ, rfl⟩ := hsub hζ'
    have hA := hrob ζ hζ
    simp only at hA
    intro j
    have hAj := hA j
    have h5j := h5 j
    simp only [Model.h, Pi.add_apply, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hyhat] at hAj h5j ⊢
    have e1 : lam = 1 - κ := by rw [hκ]; ring
    rw [e1]
    have hκ0 : 0 ≤ κ := hκ'.1.le
    have hκ1 : 0 ≤ 1 - κ := by linarith [hκ'.2]
    nlinarith [mul_le_mul_of_nonneg_left hAj hκ0, mul_le_mul_of_nonneg_left h5j hκ1]
  unfold QC
  refine lt_of_le_of_lt (iInf₂_le (yhat, Y) ⟨hYC, hfeasNew⟩) ?_
  exact robCost_affine_lt_top M p zhat ε (Xi M) yhat Y
