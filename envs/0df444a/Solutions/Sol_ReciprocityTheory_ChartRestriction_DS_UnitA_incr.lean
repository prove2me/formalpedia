-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.incr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:59.26371+00:00
-- url     : https://prove2.me/submissions/56d20952-0fe5-45d2-9cd5-fda1e44d61ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_int_norm_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_memLp_rt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_nrm_rt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_ftc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}
variable [μ.IsMulRightInvariant] [SFinite μ]
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
theorem _root_.solution {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) {a a' b : G → ℂ}
    (ha' : Continuous a') (hb : Continuous b)
    (haL : MemLp a 2 μ) (ha'L : MemLp a' 2 μ) (hbL : MemLp b 2 μ)
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => pr μ (fun x => a' (x * φ s)) b) MeasureTheory.volume 0 t ∧
    pr μ (fun x => a (x * φ t)) b - pr μ a b =
      ∫ s in (0:ℝ)..t, pr μ (fun x => a' (x * φ s)) b := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hFc : Continuous (fun p : ℝ × G => star (a' (p.2 * φ p.1)) * b p.2) :=
    (continuous_star.comp (ha'.comp (continuous_snd.mul (hφc.comp continuous_fst)))).mul
      (hb.comp continuous_snd)
  have hm : AEStronglyMeasurable (fun p : ℝ × G => star (a' (p.2 * φ p.1)) * b p.2)
      ((volume.restrict (Set.Ioc (0:ℝ) t)).prod μ) := hFc.aestronglyMeasurable
  have hFint : Integrable (fun p : ℝ × G => star (a' (p.2 * φ p.1)) * b p.2)
      ((volume.restrict (Set.Ioc (0:ℝ) t)).prod μ) := by
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall fun s => pr_int (memLp_rt ha'L (φ s)) hbL, ?_⟩
    refine Integrable.mono' (integrable_const (nrm μ a' * nrm μ b)) hm.norm.integral_prod_right'
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have h := int_norm_le (memLp_rt ha'L (φ s)) hbL
    rwa [nrm_rt ha'L.aestronglyMeasurable] at h
  have hInner := hFint.integral_prod_left
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hInner, ?_⟩
  have h1 : ∀ x, star (a (x * φ t) - a x) * b x =
      ∫ s in Set.Ioc 0 t, star (a' (x * φ s)) * b x := by
    intro x
    rw [← ftc hφc hφ0 ha' hd x t, intervalIntegral.integral_of_le ht, integral_mul_const]
    congr 1
    have h := integral_conj (μ := volume.restrict (Set.Ioc (0:ℝ) t)) (f := fun s => a' (x * φ s))
    simp only [starRingEnd_apply] at h
    exact h.symm
  have hL : pr μ (fun x => a (x * φ t)) b - pr μ a b = ∫ x, star (a (x * φ t) - a x) * b x ∂μ := by
    rw [← pr_sub_left (memLp_rt haL (φ t)) haL hbL]
    rfl
  rw [hL, intervalIntegral.integral_of_le ht]
  simp_rw [h1]
  exact (integral_integral_swap (f := fun s x => star (a' (x * φ s)) * b x) hFint).symm
end ReciprocityTheory.ChartRestriction.DS.UnitA
