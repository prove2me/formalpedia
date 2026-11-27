-- Prove2me | solution 1 for PerishablePricing.Backlog.Supplement.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:50.016113+00:00
-- url     : https://prove2.me/submissions/f9808069-9c34-4668-a8dc-e6dce61eb7e5

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Supplement_IntegerDemand

open PerishablePricing
open PerishablePricing.Backlog
open PerishablePricing.Backlog.Supplement

/-- Proposition 3 with its full conclusion and the necessary degeneracy consequence.
In particular these assumptions admit no strictly positive-width demand interval. -/
theorem solution :
    (∀ (Q : DemandData), Q.C1 → Q.C2 →
      Q.dlo = Q.dhi ∧ LNatConcaveOn Q.revenueDomain Q.revenueJoint) ∧
    (∀ (Q : IntegerDemandData), Q.C1 → Q.C2 →
      Q.lower = Q.upper ∧ LNatConcaveOnZ Q.revenueDomain Q.revenueJoint) := by
        have hbelow : ∀ (Q : DemandData) (z : ℝ), z < Q.A → Q.cdf z = 0 := by
          intro Q z hz
          have hsub : Set.Iic z ⊆ (Set.Icc Q.A Q.B)ᶜ := by
            intro x hx hx'
            exact (not_le_of_gt hz) (le_trans hx'.1 hx)
          have hμ : Q.μ (Set.Iic z) = 0 := MeasureTheory.measure_mono_null hsub Q.support
          simp [DemandData.cdf, hμ]
        have hboundary : ∀ (Q : DemandData) (d : ℝ), 0 ≤ d + Q.A →
            (0 < Q.tail (0 - d) → DifferentiableAt ℝ Q.cdf (0 - d) ∧ 1 ≤ Q.rho d 0) →
            d = -Q.A ∧ ∀ y : ℝ, 0 ≤ y → Q.revenue d y = 0 := by
          intro Q d hd htest
          let : MeasureTheory.IsProbabilityMeasure Q.μ := Q.isProb
          have hle : 0 - d ≤ Q.A := by linarith
          have htail : ¬ 0 < Q.tail (0 - d) := by
            intro ht
            obtain ⟨hdf, hr⟩ := htest ht
            have heq : Q.cdf =ᶠ[nhdsWithin (0 - d) (Set.Iio (0 - d))] (fun _ : ℝ => 0) := by
              filter_upwards [self_mem_nhdsWithin] with x hx
              exact hbelow Q x (lt_of_lt_of_le hx hle)
            have hval : Q.cdf (0 - d) = 0 := by
              exact tendsto_nhds_unique hdf.continuousAt.continuousWithinAt
                (tendsto_const_nhds.congr' heq.symm)
            have hder : deriv Q.cdf (0 - d) = 0 := by
              have hc : HasDerivWithinAt Q.cdf 0 (Set.Iio (0 - d)) (0 - d) :=
                (hasDerivWithinAt_const (0 - d) (Set.Iio (0 - d)) (0 : ℝ)).congr_of_eventuallyEq
                  heq hval
              have h₁ := hdf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio (0 - d))
              have h₂ := hc.derivWithin (uniqueDiffWithinAt_Iio (0 - d))
              exact h₁.symm.trans h₂
            have hrho : Q.rho d 0 = 0 := by
              unfold DemandData.rho
              rw [hder]
              simp
            rw [hrho] at hr
            norm_num at hr
          have hF : Q.cdf (0 - d) = 1 := by
            have hup : Q.cdf (0 - d) ≤ 1 := by
              unfold DemandData.cdf
              simpa using ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤)
                (MeasureTheory.prob_le_one : Q.μ (Set.Iic (0 - d)) ≤ 1)
            unfold DemandData.tail at htail
            linarith
          have heq : d = -Q.A := by
            by_contra hn
            have hlt : 0 - d < Q.A := by
              rcases lt_or_eq_of_le hle with h | h
              · exact h
              · exfalso
                apply hn
                linarith
            have := hbelow Q (0 - d) hlt
            linarith
          refine ⟨heq, ?_⟩
          intro y hy
          have hmass : Q.μ (Set.Iic (0 - d)) = 1 :=
            (ENNReal.toReal_eq_one_iff _).mp hF
          have hu : ∀ᵐ ε ∂Q.μ, ε ∈ Set.Iic (0 - d) :=
            (MeasureTheory.mem_ae_iff_prob_eq_one measurableSet_Iic).mpr hmass
          have hl : ∀ᵐ ε ∂Q.μ, ε ∈ Set.Icc Q.A Q.B :=
            MeasureTheory.mem_ae_iff.mpr Q.support
          have hi : (∫ ε, min (d + ε) y ∂Q.μ) = 0 := by
            apply MeasureTheory.integral_eq_zero_of_ae
            filter_upwards [hu, hl] with ε hε hε'
            have hz : d + ε = 0 := by
              have := hε'.1
              change ε ≤ 0 - d at hε
              linarith
            simp [hz, min_eq_left hy]
          simp [DemandData.revenue, hi]
        constructor
        · intro Q hC1 hC2
          have hb := hboundary Q Q.dhi (by linarith [Q.demand_nonneg, Q.dlo_le_dhi])
            (fun ht => by
              have h := hC2 Q.dhi ⟨Q.dlo_le_dhi, le_rfl⟩ 0 le_rfl ht
              exact ⟨h.1, h.2.2⟩)
          have heq : Q.dlo = Q.dhi := by linarith [hb.1, Q.demand_nonneg, Q.dlo_le_dhi]
          have hdom : ∀ w ∈ Q.revenueDomain, w 0 = Q.dhi ∧ 0 ≤ w 1 := by
            intro w hw
            exact ⟨le_antisymm hw.1.2 (heq ▸ hw.1.1), hw.2⟩
          have hzero : ∀ w ∈ Q.revenueDomain, Q.revenueJoint w = 0 := by
            intro w hw
            obtain ⟨h0, h1⟩ := hdom w hw
            simpa [DemandData.revenueJoint, h0] using hb.2 (w 1) h1
          have hconv : LNatConvexSet Q.revenueDomain := by
            intro u hu v hv a ha
            obtain ⟨hu0, hu1⟩ := hdom u hu
            obtain ⟨hv0, hv1⟩ := hdom v hv
            constructor
            · change (min (u 0 + a * 1) (v 0) ∈ Set.Icc Q.dlo Q.dhi) ∧
                0 ≤ min (u 1 + a * 1) (v 1)
              simp only [hu0, hv0, mul_one]
              rw [min_eq_right (by linarith : Q.dhi ≤ Q.dhi + a)]
              exact ⟨⟨Q.dlo_le_dhi, le_rfl⟩, le_min (by linarith) hv1⟩
            · change (max (u 0) (v 0 - a * 1) ∈ Set.Icc Q.dlo Q.dhi) ∧
                0 ≤ max (u 1) (v 1 - a * 1)
              simp only [hu0, hv0, mul_one]
              rw [max_eq_left (by linarith : Q.dhi - a ≤ Q.dhi)]
              exact ⟨⟨Q.dlo_le_dhi, le_rfl⟩, le_trans hu1 (le_max_left _ _)⟩
          refine ⟨heq, hconv, ?_⟩
          intro u hu v hv a ha
          have hc := hconv u hu v hv a ha
          change -Q.revenueJoint _ + -Q.revenueJoint _ ≤ -Q.revenueJoint u + -Q.revenueJoint v
          rw [hzero _ hc.1, hzero _ hc.2, hzero _ hu, hzero _ hv]
        · intro Q hC1 hC2
          have hlo : (Q.lower : ℝ) ≤ (Q.upper : ℝ) := by
            simpa [Q.lower_eq, Q.upper_eq] using Q.dlo_le_dhi
          have hle : Q.lower ≤ Q.upper := by exact_mod_cast hlo
          have hb := hboundary Q.toDemandData (Q.upper : ℝ) (by
            have hn := Q.demand_nonneg
            rw [Q.lower_eq] at hn
            linarith)
            (fun ht => by
              have h := hC2 Q.upper ⟨hle, le_rfl⟩ 0 le_rfl (by simpa using ht)
              exact ⟨by simpa using h.1, by simpa using h.2.2⟩)
          have heqR : (Q.lower : ℝ) = (Q.upper : ℝ) := by
            have hn := Q.demand_nonneg
            rw [Q.lower_eq] at hn
            linarith [hb.1]
          have heq : Q.lower = Q.upper := by exact_mod_cast heqR
          have hdom : ∀ w ∈ Q.revenueDomain, w 0 = Q.upper ∧ 0 ≤ w 1 := by
            intro w hw
            exact ⟨le_antisymm hw.1.2 (heq ▸ hw.1.1), hw.2⟩
          have hzero : ∀ w ∈ Q.revenueDomain, Q.revenueJoint w = 0 := by
            intro w hw
            obtain ⟨h0, h1⟩ := hdom w hw
            have hr := hb.2 (w 1) (by exact_mod_cast h1)
            simpa [IntegerDemandData.revenueJoint, IntegerDemandData.revenue, h0] using hr
          have hconv : LNatConvexSetZ Q.revenueDomain := by
            intro u hu v hv a ha
            obtain ⟨hu0, hu1⟩ := hdom u hu
            obtain ⟨hv0, hv1⟩ := hdom v hv
            constructor
            · change (min (u 0 + a * 1) (v 0) ∈ Set.Icc Q.lower Q.upper) ∧
                0 ≤ min (u 1 + a * 1) (v 1)
              simp only [hu0, hv0, mul_one]
              rw [min_eq_right (by omega : Q.upper ≤ Q.upper + a)]
              exact ⟨⟨hle, le_rfl⟩, le_min (by omega) hv1⟩
            · change (max (u 0) (v 0 - a * 1) ∈ Set.Icc Q.lower Q.upper) ∧
                0 ≤ max (u 1) (v 1 - a * 1)
              simp only [hu0, hv0, mul_one]
              rw [max_eq_left (by omega : Q.upper - a ≤ Q.upper)]
              exact ⟨⟨hle, le_rfl⟩, le_trans hu1 (le_max_left _ _)⟩
          refine ⟨heq, hconv, ?_⟩
          intro u hu v hv a ha
          have hc := hconv u hu v hv a ha
          change -Q.revenueJoint _ + -Q.revenueJoint _ ≤ -Q.revenueJoint u + -Q.revenueJoint v
          rw [hzero _ hc.1, hzero _ hc.2, hzero _ hu, hzero _ hv]
