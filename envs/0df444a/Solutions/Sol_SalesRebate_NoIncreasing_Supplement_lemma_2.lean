-- Prove2me | solution 1 for SalesRebate.NoIncreasing.Supplement.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:51.334802+00:00
-- url     : https://prove2.me/submissions/861121c9-478a-4558-abe0-2f9b41d8f518

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

open SalesRebate
open SalesRebate.NoIncreasing
open SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem solution (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hrhat : IsAdmissibleReward p rhat) (hspread : ∀ v w, rhat v - rhat w ≤ spreadBound M) :
    Monotone (fun x => x - p + M.condReward rhat x) := by
      obtain ⟨hmeas, hrange⟩ := hrhat
      have hθ := hM.σθ_pos
      have hε := hM.σε_pos
      have hs2pos : 0 < M.σv2 := by unfold Model.σv2; positivity
      set v : NNReal := M.σv2.toNNReal with hvdef
      have hv : v ≠ 0 := by
        intro h; rw [hvdef, Real.toNNReal_eq_zero] at h; linarith
      have hvcoe : (v : ℝ) = M.σv2 := Real.coe_toNNReal _ hs2pos.le
      set K : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ with hK
      have hK0 : 0 ≤ K := by positivity
      set S := spreadBound M with hS
      have hS0 : 0 ≤ S := by
        rw [hS]; unfold spreadBound Model.σ; positivity
      set a : ℝ := ⨅ w, rhat w with ha
      have hbdd : BddBelow (Set.range rhat) := ⟨0, by rintro _ ⟨w, rfl⟩; exact (hrange w).1⟩
      have hga : ∀ u, 0 ≤ rhat u - a := fun u => sub_nonneg.2 (ciInf_le hbdd u)
      have hgS : ∀ u, rhat u - a ≤ S := by
        intro u
        have : rhat u - S ≤ a := le_ciInf (fun w => by linarith [hspread u w])
        linarith
      have hint : ∀ m (h : ℝ → ℝ) (C : ℝ), Measurable h → (∀ u, |h u| ≤ C) →
          Integrable (fun u => gaussianPDFReal m v u * h u) := by
        intro m h C hh hC
        exact (integrable_gaussianPDFReal m v).mul_bdd hh.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun u => by rw [Real.norm_eq_abs]; exact hC u))
      have hcond : ∀ x, M.condReward rhat x = ∫ u, gaussianPDFReal (M.postMean x) v u * rhat u := by
        intro x
        unfold Model.condReward Model.posterior
        rw [integral_gaussianReal_eq_integral_smul hv]
        rfl
      have hφK : ∀ m u, gaussianPDFReal m v u ≤ K := by
        intro m u
        rw [gaussianPDFReal_def]
        have h1 : Real.exp (-(u - m) ^ 2 / (2 * v)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          apply div_nonpos_of_nonpos_of_nonneg
          · nlinarith [sq_nonneg (u - m)]
          · positivity
        calc K * Real.exp (-(u - m) ^ 2 / (2 * v)) ≤ K * 1 := mul_le_mul_of_nonneg_left h1 hK0
          _ = K := mul_one K
      have hcmp : ∀ m1 m2 u, (u - m1) ^ 2 ≤ (u - m2) ^ 2 →
          gaussianPDFReal m2 v u ≤ gaussianPDFReal m1 v u := by
        intro m1 m2 u h
        rw [gaussianPDFReal_def, gaussianPDFReal_def]
        apply mul_le_mul_of_nonneg_left _ hK0
        apply Real.exp_le_exp.2
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have hdec : ∀ m, ∫ u, gaussianPDFReal m v u * rhat u
          = (∫ u, gaussianPDFReal m v u * (rhat u - a)) + a := by
        intro m
        have : (fun u => gaussianPDFReal m v u * rhat u)
            = fun u => gaussianPDFReal m v u * (rhat u - a) + a * gaussianPDFReal m v u := by
          funext u; ring
        rw [this, integral_add (hint m (fun u => rhat u - a) S (hmeas.sub_const a)
          (fun u => by rw [abs_le]; constructor <;> linarith [hga u, hgS u]))
          ((integrable_gaussianPDFReal m v).const_mul a), integral_const_mul,
          integral_gaussianPDFReal_eq_one m hv, mul_one]
      have key : ∀ m1 m2, m1 ≤ m2 → (∫ u, gaussianPDFReal m1 v u * rhat u)
          - ∫ u, gaussianPDFReal m2 v u * rhat u ≤ S * ((m2 - m1) * K) := by
        intro m1 m2 hm
        set d := m2 - m1 with hd
        set mid := (m1 + m2) / 2 with hmid
        have hgint : ∀ m, Integrable (fun u => gaussianPDFReal m v u * (rhat u - a)) := fun m =>
          hint m (fun u => rhat u - a) S (hmeas.sub_const a)
            (fun u => by rw [abs_le]; constructor <;> linarith [hga u, hgS u])
        rw [hdec m1, hdec m2]
        have e1 : ((∫ u, gaussianPDFReal m1 v u * (rhat u - a)) + a)
            - ((∫ u, gaussianPDFReal m2 v u * (rhat u - a)) + a)
            = ∫ u, (gaussianPDFReal m1 v u - gaussianPDFReal m2 v u) * (rhat u - a) := by
          have : (fun u => (gaussianPDFReal m1 v u - gaussianPDFReal m2 v u) * (rhat u - a))
              = fun u => gaussianPDFReal m1 v u * (rhat u - a) - gaussianPDFReal m2 v u * (rhat u - a) := by
            funext u; ring
          rw [this, integral_sub (hgint m1) (hgint m2)]; ring
        rw [e1]
        have hdiff : Integrable (fun u => gaussianPDFReal m1 v u - gaussianPDFReal m2 v u) :=
          (integrable_gaussianPDFReal m1 v).sub (integrable_gaussianPDFReal m2 v)
        have step1 : ∫ u, (gaussianPDFReal m1 v u - gaussianPDFReal m2 v u) * (rhat u - a)
            ≤ ∫ u, S * (Set.Iic mid).indicator
                (fun u => gaussianPDFReal m1 v u - gaussianPDFReal m2 v u) u := by
          apply integral_mono
          · exact hdiff.mul_bdd (c := S) (hmeas.sub_const a).aestronglyMeasurable
              (Filter.Eventually.of_forall (fun u => by
                rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hga u, hgS u, hS0]))
          · exact (hdiff.indicator measurableSet_Iic).const_mul S
          · intro u
            simp only [Set.indicator_apply, Set.mem_Iic]
            split_ifs with hu
            · have : gaussianPDFReal m2 v u ≤ gaussianPDFReal m1 v u :=
                hcmp m1 m2 u (by nlinarith)
              have := hgS u
              nlinarith
            · have : gaussianPDFReal m1 v u ≤ gaussianPDFReal m2 v u :=
                hcmp m2 m1 u (by nlinarith)
              have := hga u
              nlinarith
        rw [integral_const_mul] at step1
        have hshift : ∫ u, (Set.Iic mid).indicator (gaussianPDFReal m2 v) u
            = ∫ u, (Set.Iic (mid - d)).indicator (gaussianPDFReal m1 v) u := by
          rw [← integral_sub_right_eq_self
            (fun w => (Set.Iic (mid - d)).indicator (gaussianPDFReal m1 v) w) d]
          congr 1
          funext u
          simp only [Set.indicator_apply, Set.mem_Iic]
          rw [gaussianPDFReal_sub]
          have : m1 + d = m2 := by rw [hd]; ring
          rw [this]
          split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)
        have step2 : ∫ u, (Set.Iic mid).indicator
                (fun u => gaussianPDFReal m1 v u - gaussianPDFReal m2 v u) u
            = ∫ u, ((Set.Iic mid).indicator (gaussianPDFReal m1 v) u
                - (Set.Iic (mid - d)).indicator (gaussianPDFReal m1 v) u) := by
          rw [Set.indicator_sub, integral_sub ((integrable_gaussianPDFReal m1 v).indicator measurableSet_Iic)
            ((integrable_gaussianPDFReal m2 v).indicator measurableSet_Iic), hshift,
            integral_sub ((integrable_gaussianPDFReal m1 v).indicator measurableSet_Iic)
            ((integrable_gaussianPDFReal m1 v).indicator measurableSet_Iic)]
        have step3 : ∫ u, ((Set.Iic mid).indicator (gaussianPDFReal m1 v) u
                - (Set.Iic (mid - d)).indicator (gaussianPDFReal m1 v) u)
            ≤ ∫ u, (Set.Ioc (mid - d) mid).indicator (fun _ => K) u := by
          apply integral_mono
          · exact ((integrable_gaussianPDFReal m1 v).indicator measurableSet_Iic).sub
              ((integrable_gaussianPDFReal m1 v).indicator measurableSet_Iic)
          · exact (integrable_indicator_iff measurableSet_Ioc).2
              (integrableOn_const (by simp [Real.volume_Ioc]) (by simp))
          · intro u
            have h0 := gaussianPDFReal_nonneg m1 v u
            have hK' := hφK m1 u
            simp only [Set.indicator_apply, Set.mem_Iic, Set.mem_Ioc]
            split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> first | linarith | (exfalso; linarith) | (exfalso; exact h3 ⟨by linarith, h1⟩)
        rw [integral_indicator_const K measurableSet_Ioc,
          Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul] at step3
        have : mid - (mid - d) = d := by ring
        rw [this] at step3
        rw [step2] at step1
        calc _ ≤ S * ∫ u, ((Set.Iic mid).indicator (gaussianPDFReal m1 v) u
                - (Set.Iic (mid - d)).indicator (gaussianPDFReal m1 v) u) := step1
          _ ≤ S * (d * K) := mul_le_mul_of_nonneg_left step3 hS0
      have htau : 0 < M.tau := by unfold Model.tau; positivity
      have hfinal : S * (M.tau * K) = 1 := by
        have hσ2 : M.σ ^ 2 = M.σε ^ 2 + M.σθ ^ 2 := by
          unfold Model.σ; rw [Real.sq_sqrt (by positivity)]
        have hσpos : 0 < M.σ := by unfold Model.σ; positivity
        have hsq : Real.sqrt (2 * Real.pi * v) = Real.sqrt (2 * Real.pi) * (M.σε * M.σθ / M.σ) := by
          rw [Real.sqrt_mul (by positivity), hvcoe]
          congr 1
          rw [show M.σv2 = (M.σε * M.σθ / M.σ) ^ 2 by
            unfold Model.σv2; rw [div_pow, hσ2]; ring]
          exact Real.sqrt_sq (by positivity)
        rw [hK, hsq, hS]
        unfold spreadBound Model.tau
        rw [← hσ2]
        have hpi : 0 < Real.sqrt (2 * Real.pi) := by positivity
        field_simp
      intro x y hxy
      show x - p + M.condReward rhat x ≤ y - p + M.condReward rhat y
      rw [hcond x, hcond y]
      have hm : M.postMean y - M.postMean x = M.tau * (y - x) := by unfold Model.postMean; ring
      have h1 := key (M.postMean x) (M.postMean y) (by nlinarith)
      rw [hm] at h1
      have h2 : S * (M.tau * (y - x) * K) = y - x := by
        calc S * (M.tau * (y - x) * K) = (y - x) * (S * (M.tau * K)) := by ring
          _ = y - x := by rw [hfinal, mul_one]
      linarith
