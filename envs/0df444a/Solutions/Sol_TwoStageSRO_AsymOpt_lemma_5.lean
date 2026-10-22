-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:40:56.783728+00:00
-- url     : https://prove2.me/submissions/8f20a21f-73ba-4a83-a5fe-d7c015b359e0

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

open TwoStageSRO.AsymOpt in
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1)
    (zhat : Fin d → ℝ) (hz : zhat ∈ Xi M) (ε : ℝ) (hε : 0 < ε)
    (hεΔ : (ε : EReal) ≤ radius M p zhat) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    ball p zhat (lam * ε) ∩ Xi M =
      (fun ζ => lam • ζ + (1 - lam) • zhat) '' (ball p zhat ε ∩ Xi M) := by
  have hnorm : ∀ (c : ℝ) (v : Fin d → ℝ), ‖WithLp.toLp p (c • v)‖ = |c| * ‖WithLp.toLp p v‖ := by
    intro c v
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
  ext ζ
  constructor
  · rintro ⟨hb, hx⟩
    refine ⟨zhat + lam⁻¹ • (ζ - zhat), ⟨?_, ?_⟩, ?_⟩
    · -- in the ball of radius ε
      show ‖WithLp.toLp p (zhat + lam⁻¹ • (ζ - zhat) - zhat)‖ ≤ ε
      have hb' : ‖WithLp.toLp p (ζ - zhat)‖ ≤ lam * ε := hb
      rw [add_sub_cancel_left, hnorm, abs_of_pos (inv_pos.mpr hlam0)]
      calc lam⁻¹ * ‖WithLp.toLp p (ζ - zhat)‖ ≤ lam⁻¹ * (lam * ε) :=
            mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr hlam0.le)
        _ = ε := by field_simp
    · -- in Ξ
      show M.g0 ≤ M.G *ᵥ (zhat + lam⁻¹ • (ζ - zhat))
      intro k
      have hzk := hz k
      have hxk := hx k
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub] at *
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at *
      obtain ⟨s, hs⟩ : ∃ s, s = (M.G *ᵥ zhat) k - M.g0 k := ⟨_, rfl⟩
      obtain ⟨a, ha⟩ : ∃ a, a = (M.G *ᵥ ζ) k - (M.G *ᵥ zhat) k := ⟨_, rfl⟩
      rw [← ha]
      by_contra hcon
      push Not at hcon
      -- s * lam + a < 0
      have h1 : s * lam + a < 0 := by
        have : lam * (s + lam⁻¹ * a) < 0 := mul_neg_of_pos_of_neg hlam0 (by linarith)
        have e : lam * (s + lam⁻¹ * a) = s * lam + a := by field_simp
        linarith
      have hs0 : 0 ≤ s := by linarith
      have ha0 : a < 0 := by nlinarith
      have hspos : 0 < s := by
        rcases hs0.lt_or_eq with h | h
        · exact h
        · exfalso
          have : 0 ≤ (M.G *ᵥ ζ) k - M.g0 k := by linarith
          nlinarith
      -- the point w = zhat + c • (ζ - zhat) lies on the hyperplane k
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -s / a := ⟨_, rfl⟩
      have hcpos : 0 < c := by rw [hc]; exact div_pos_of_neg_of_neg (neg_neg_of_pos hspos) ha0
      have hclam : c * lam < 1 := by
        rw [hc, div_mul_eq_mul_div, div_lt_one_of_neg ha0]
        linarith
      have hnot : zhat ∉ hyperplane M k := by
        intro h
        simp only [hyperplane, Set.mem_ofPred_eq] at h
        linarith
      have hw : zhat + c • (ζ - zhat) ∈ hyperplane M k := by
        simp only [hyperplane, Set.mem_ofPred_eq, Matrix.mulVec_add, Matrix.mulVec_smul,
          Matrix.mulVec_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        have hca : c * a = -s := by rw [hc, div_mul_cancel₀ _ ha0.ne]
        rw [← ha]
        linarith
      have hle : radius M p zhat ≤
          ((‖WithLp.toLp p (zhat + c • (ζ - zhat) - zhat)‖ : ℝ) : EReal) := by
        unfold radius
        exact iInf₂_le_of_le k hnot (iInf₂_le _ hw)
      have hb' : ‖WithLp.toLp p (ζ - zhat)‖ ≤ lam * ε := hb
      have hlt : ‖WithLp.toLp p (zhat + c • (ζ - zhat) - zhat)‖ < ε := by
        rw [add_sub_cancel_left, hnorm, abs_of_pos hcpos]
        calc c * ‖WithLp.toLp p (ζ - zhat)‖ ≤ c * (lam * ε) :=
              mul_le_mul_of_nonneg_left hb' hcpos.le
          _ = (c * lam) * ε := by ring
          _ < 1 * ε := mul_lt_mul_of_pos_right hclam hε
          _ = ε := one_mul ε
      have : (ε : EReal) < ε :=
        lt_of_le_of_lt (hεΔ.trans hle) (EReal.coe_lt_coe_iff.mpr hlt)
      exact lt_irrefl _ this
    · show lam • (zhat + lam⁻¹ • (ζ - zhat)) + (1 - lam) • zhat = ζ
      rw [smul_add, smul_smul, mul_inv_cancel₀ hlam0.ne', one_smul]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
  · rintro ⟨ζ', ⟨hb, hx⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show ‖WithLp.toLp p (lam • ζ' + (1 - lam) • zhat - zhat)‖ ≤ lam * ε
      have hb' : ‖WithLp.toLp p (ζ' - zhat)‖ ≤ ε := hb
      have e : lam • ζ' + (1 - lam) • zhat - zhat = lam • (ζ' - zhat) := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [e, hnorm, abs_of_pos hlam0]
      exact mul_le_mul_of_nonneg_left hb' hlam0.le
    · show M.g0 ≤ M.G *ᵥ (lam • ζ' + (1 - lam) • zhat)
      intro k
      have hzk := hz k
      have hxk := hx k
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
