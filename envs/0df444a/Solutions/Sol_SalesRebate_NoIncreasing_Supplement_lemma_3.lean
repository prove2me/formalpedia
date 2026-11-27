-- Prove2me | solution 1 for SalesRebate.NoIncreasing.Supplement.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:03.125801+00:00
-- url     : https://prove2.me/submissions/c9c473b6-6807-4db3-b0d3-56bd9f1a6500

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

open SalesRebate
open SalesRebate.NoIncreasing
open SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem solution (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) (hrate : IsRateConstrained M rhat) :
    Monotone (fun x => x - p + M.condReward rhat x) := by
      have ht : 0 < M.tau := by
        unfold Model.tau
        exact div_pos (sq_pos_of_pos hM.σθ_pos)
          (add_pos (sq_pos_of_pos hM.σε_pos) (sq_pos_of_pos hM.σθ_pos))
      obtain ⟨D, ⟨hc, hfin, hC, hlim⟩, hd⟩ := hrate
      have hdiff : ∀ v ∉ D, DifferentiableAt ℝ rhat v := by
        intro v hv
        have hn : Dᶜ ∈ 𝓝 v := by
          have hclosed := (hfin (v - 1) (v + 1)).isClosed
          have hv' : v ∉ D ∩ Set.Icc (v - 1) (v + 1) := by
            intro h
            exact hv h.1
          have hi : Set.Ioo (v - 1) (v + 1) ∈ 𝓝 v := Ioo_mem_nhds (by linarith) (by linarith)
          filter_upwards [hclosed.compl_mem_nhds hv', hi] with z hz hzi
          intro hzD
          exact hz ⟨hzD, hzi.1.le, hzi.2.le⟩
        exact (hC.differentiableOn_one v hv).differentiableAt hn
      let f : ℝ → ℝ := fun v => rhat v + v / M.tau
      have hfc : Continuous f := hc.add (continuous_id.div_const _)
      have hfd : ∀ v ∉ D, DifferentiableAt ℝ f v ∧ 0 ≤ deriv f v := by
        intro v hv
        have hh := (hdiff v hv).hasDerivAt.add ((hasDerivAt_id v).div_const M.tau)
        change HasDerivAt (fun v => rhat v + v / M.tau) (deriv rhat v + 1 / M.tau) v at hh
        refine ⟨hh.differentiableAt, ?_⟩
        change 0 ≤ deriv (fun v => rhat v + v / M.tau) v
        rw [hh.deriv]
        have h := (abs_le.mp (hd v hv)).1
        linarith
      have hfinite : ∀ (s : Set ℝ), s.Finite → ∀ a b : ℝ, a ≤ b →
          (∀ z ∈ Set.Ioo a b, z ∉ s → DifferentiableAt ℝ f z ∧ 0 ≤ deriv f z) →
          f a ≤ f b := by
        intro s hs
        induction s, hs using Set.Finite.induction_on with
        | empty =>
          intro a b hab hh
          have hmono : MonotoneOn f (Set.Icc a b) := by
            apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hfc.continuousOn
            · intro z hz
              rw [interior_Icc] at hz
              exact (hh z hz (by simp)).1.differentiableWithinAt
            · intro z hz
              rw [interior_Icc] at hz
              exact (hh z hz (by simp)).2
          exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
        | @insert c s hcs hs ih =>
          intro a b hab hh
          by_cases hci : c ∈ Set.Ioo a b
          · have hleft : f a ≤ f c := by
              apply ih a c hci.1.le
              intro z hz hzs
              apply hh z ⟨hz.1, hz.2.trans hci.2⟩
              simp only [Set.mem_insert_iff, not_or]
              exact ⟨ne_of_lt hz.2, hzs⟩
            have hright : f c ≤ f b := by
              apply ih c b hci.2.le
              intro z hz hzs
              apply hh z ⟨hci.1.trans hz.1, hz.2⟩
              simp only [Set.mem_insert_iff, not_or]
              exact ⟨ne_of_gt hz.1, hzs⟩
            exact hleft.trans hright
          · apply ih a b hab
            intro z hz hzs
            apply hh z hz
            simp only [Set.mem_insert_iff, not_or]
            refine ⟨?_, hzs⟩
            intro heq
            exact hci (heq ▸ hz)
      have hmono : Monotone f := by
        intro a b hab
        apply hfinite (D ∩ Set.Icc a b) (hfin a b) a b hab
        intro z hz hzs
        apply hfd z
        intro hzD
        exact hzs ⟨hzD, hz.1.le, hz.2.le⟩
      let μ : Measure ℝ := gaussianReal 0 M.σv2.toNNReal
      have hint : ∀ x : ℝ, Integrable (fun z => rhat (z + M.postMean x)) μ := by
        intro x
        apply (integrable_const p).mono' (hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        exact ae_of_all _ (fun z => by
          change ‖rhat (z + M.postMean x)‖ ≤ p
          rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]
          exact (hbound _).2)
      have hreward : ∀ x, M.condReward rhat x = ∫ z, rhat (z + M.postMean x) ∂μ := by
        intro x
        have hm : μ.map (fun z => z + M.postMean x) = M.posterior x := by
          simpa [μ, Model.posterior] using
            (gaussianReal_map_add_const (μ := 0) (v := M.σv2.toNNReal) (M.postMean x))
        rw [Model.condReward, ← hm]
        exact integral_map (by fun_prop) hc.aestronglyMeasurable
      intro x y hxy
      have hpoint : ∀ z : ℝ,
          x - p + rhat (z + M.postMean x) ≤ y - p + rhat (z + M.postMean y) := by
        intro z
        have hmean : z + M.postMean x ≤ z + M.postMean y := by
          dsimp [Model.postMean]
          nlinarith
        have hh := hmono hmean
        change rhat (z + M.postMean x) + (z + M.postMean x) / M.tau ≤
          rhat (z + M.postMean y) + (z + M.postMean y) / M.tau at hh
        have heq : (z + M.postMean y) / M.tau - (z + M.postMean x) / M.tau = y - x := by
          dsimp [Model.postMean]
          field_simp
          ring
        linarith
      have hi := integral_mono ((integrable_const (x - p)).add (hint x))
        ((integrable_const (y - p)).add (hint y)) hpoint
      change (∫ z, x - p + rhat (z + M.postMean x) ∂μ) ≤
        (∫ z, y - p + rhat (z + M.postMean y) ∂μ) at hi
      rw [integral_add (integrable_const (x - p)) (hint x),
        integral_add (integrable_const (y - p)) (hint y)] at hi
      change x - p + M.condReward rhat x ≤ y - p + M.condReward rhat y
      rw [hreward x, hreward y]
      simpa [μ] using hi
