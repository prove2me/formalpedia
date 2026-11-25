-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:16.736051+00:00
-- url     : https://prove2.me/submissions/67b4aa6a-bcdb-4e7d-afa9-6693f1dc8ee2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_star
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_neg_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_memLp_rt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_nrm_rt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_incr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_small_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}
section Invariant
variable [μ.IsMulRightInvariant]
end Invariant
section Flow
variable [μ.IsMulRightInvariant] [SFinite μ]
private theorem negder_lemma {φ : ℝ → G} {a a' : G → ℂ}
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) :
    ∀ x t, HasDerivAt (fun s => a (x * φ (-s))) (-a' (x * φ (-t))) t := by
  intro x t
  have h := (hd x (-t)).scomp t (hasDerivAt_id t).neg
  simpa [Function.comp_def] using h
private theorem inv_lemma_2 {φ : ℝ → G} (hφ0 : φ 0 = 1) (hφa : ∀ s t, φ (s + t) = φ s * φ t) (s : ℝ) :
    (φ s)⁻¹ = φ (-s) := by
  have h : φ s * φ (-s) = 1 := by
    rw [← hφa]
    simp [hφ0]
  exact (eq_inv_of_mul_eq_one_right h).symm
private theorem lin_lemma_3 {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1)
    (hφa : ∀ s t, φ (s + t) = φ s * φ t) {a a' b b' : G → ℂ}
    (ha' : Continuous a') (hb : Continuous b) (hb' : Continuous b')
    (haL : MemLp a 2 μ) (ha'L : MemLp a' 2 μ) (hbL : MemLp b 2 μ) (hb'L : MemLp b' 2 μ)
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t)
    (hdb : ∀ x t, HasDerivAt (fun s => b (x * φ s)) (b' (x * φ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    ‖(pr μ (fun x => a (x * φ t)) b - pr μ a b) - (t : ℂ) * pr μ a' b‖ ≤
      t * (t * (nrm μ a' * nrm μ b')) := by
  have hψc : Continuous fun s => φ (-s) := hφc.comp continuous_neg
  obtain ⟨hI, hE⟩ := incr hφc hφ0 ha' hb haL ha'L hbL hd ht
  have hbd : ∀ s ∈ Set.uIoc 0 t,
      ‖pr μ (fun x => a' (x * φ s)) b - pr μ a' b‖ ≤ t * (nrm μ a' * nrm μ b') := by
    intro s hs
    rw [Set.uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have e1 : pr μ (fun x => a' (x * φ s)) b = pr μ a' (fun x => b (x * φ (-s))) := by
      rw [pr_shift, inv_lemma_2 hφ0 hφa]
    have e2 : pr μ (fun x => b (x * φ (-s))) a' - pr μ b a' =
        ∫ r in (0:ℝ)..s, pr μ (fun x => -b' (x * φ (-r))) a' :=
      (incr (φ := fun s => φ (-s)) hψc (by simp [hφ0]) (a' := fun y => -b' y) hb'.neg ha' hbL
        hb'L.neg ha'L (negder_lemma hdb) hs0).2
    have e3 : pr μ (fun x => a' (x * φ s)) b - pr μ a' b =
        star (pr μ (fun x => b (x * φ (-s))) a' - pr μ b a') := by
      rw [e1, star_sub, pr_star, pr_star]
    have hC : ∀ r ∈ Set.uIoc 0 s, ‖pr μ (fun x => -b' (x * φ (-r))) a'‖ ≤ nrm μ b' * nrm μ a' := by
      intro r _
      have h := pr_bound (memLp_rt hb'L.neg (φ (-r))) ha'L
      have hn : nrm μ (fun x => (-b') (x * φ (-r))) = nrm μ b' := by
        rw [nrm_rt hb'L.neg.aestronglyMeasurable]
        unfold nrm
        rw [eLpNorm_neg]
      rw [hn] at h
      exact h
    rw [e3, norm_star, e2]
    calc _ ≤ (nrm μ b' * nrm μ a') * |s - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hC
      _ ≤ t * (nrm μ a' * nrm μ b') := by
        rw [sub_zero, abs_of_nonneg hs0]
        have h1 : 0 ≤ nrm μ a' := ENNReal.toReal_nonneg
        have h2 : 0 ≤ nrm μ b' := ENNReal.toReal_nonneg
        have h3 : 0 ≤ nrm μ a' * nrm μ b' := mul_nonneg h1 h2
        nlinarith [hs.2]
  have hmain : pr μ (fun x => a (x * φ t)) b - pr μ a b - (t : ℂ) * pr μ a' b =
      ∫ s in (0:ℝ)..t, (pr μ (fun x => a' (x * φ s)) b - pr μ a' b) := by
    rw [intervalIntegral.integral_sub hI intervalIntegrable_const, intervalIntegral.integral_const, ← hE,
      sub_zero, Complex.real_smul]
  rw [hmain]
  calc _ ≤ (t * (nrm μ a' * nrm μ b')) * |t - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = _ := by rw [sub_zero, abs_of_nonneg ht]; ring
end Flow
end ReciprocityTheory.ChartRestriction.DS.UnitA
end
end

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
theorem _root_.solution {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) (hφa : ∀ s t, φ (s + t) = φ s * φ t)
    {u u' v v' : G → ℂ} (hu : Continuous u) (hu' : Continuous u') (hv : Continuous v)
    (hv' : Continuous v')
    (huL : MemLp u 2 μ) (hu'L : MemLp u' 2 μ) (hvL : MemLp v 2 μ) (hv'L : MemLp v' 2 μ)
    (hdu : ∀ x t, HasDerivAt (fun s => u (x * φ s)) (u' (x * φ t)) t)
    (hdv : ∀ x t, HasDerivAt (fun s => v (x * φ s)) (v' (x * φ t)) t) :
    pr μ u' v = -pr μ u v' := by
  have hψc : Continuous fun s => φ (-s) := hφc.comp continuous_neg
  have hψa : ∀ s t, φ (-(s + t)) = φ (-s) * φ (-t) := fun s t => by rw [neg_add, hφa]
  have hnv : nrm μ (fun y => -v' y) = nrm μ v' := by
    unfold nrm
    rw [show (fun y => -v' y) = -v' from rfl, eLpNorm_neg]
  have hnu : nrm μ (fun y => -u' y) = nrm μ u' := by
    unfold nrm
    rw [show (fun y => -u' y) = -u' from rfl, eLpNorm_neg]
  suffices h : pr μ u' v + pr μ u v' = 0 by linear_combination h
  apply small_zero (C := 2 * (nrm μ u' * nrm μ v'))
  intro t ht0 ht1
  have E1 : ‖(pr μ (fun x => u (x * φ t)) v - pr μ u v) - (t : ℂ) * pr μ u' v‖ ≤
      t * (t * (nrm μ u' * nrm μ v')) :=
    lin_lemma_3 hφc hφ0 hφa hu' hv hv' huL hu'L hvL hv'L hdu hdv ht0.le
  have E2 : ‖(pr μ (fun x => v (x * φ (-t))) u - pr μ v u) - (t : ℂ) * pr μ (fun y => -v' y) u‖ ≤
      t * (t * (nrm μ (fun y => -v' y) * nrm μ (fun y => -u' y))) :=
    lin_lemma_3 (φ := fun s => φ (-s)) hψc (by simp [hφ0]) hψa hv'.neg hu hu'.neg hvL hv'L.neg huL
      hu'L.neg (negder_lemma hdv) (negder_lemma hdu) ht0.le
  rw [hnv, hnu] at E2
  have e1 : pr μ (fun x => u (x * φ t)) v = pr μ u (fun x => v (x * φ (-t))) := by
    rw [pr_shift, inv_lemma_2 hφ0 hφa]
  have e2 : star ((pr μ (fun x => v (x * φ (-t))) u - pr μ v u) - (t : ℂ) * pr μ (fun y => -v' y) u) =
      (pr μ (fun x => u (x * φ t)) v - pr μ u v) + (t : ℂ) * pr μ u v' := by
    rw [star_sub, star_sub, star_mul', pr_star, pr_star, pr_star, e1, Complex.star_def,
      Complex.conj_ofReal, pr_neg_right]
    ring
  have E3 : ‖(pr μ (fun x => u (x * φ t)) v - pr μ u v) + (t : ℂ) * pr μ u v'‖ ≤
      t * (t * (nrm μ u' * nrm μ v')) := by
    rw [← e2, norm_star]
    linarith [E2]
  have key : (t : ℂ) * (pr μ u' v + pr μ u v') =
      ((pr μ (fun x => u (x * φ t)) v - pr μ u v) + (t : ℂ) * pr μ u v') -
        ((pr μ (fun x => u (x * φ t)) v - pr μ u v) - (t : ℂ) * pr μ u' v) := by ring
  have hn : ‖(t : ℂ) * (pr μ u' v + pr μ u v')‖ ≤ 2 * (t * (t * (nrm μ u' * nrm μ v'))) := by
    rw [key]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le] at hn
  exact le_of_mul_le_mul_left (by linarith : t * ‖pr μ u' v + pr μ u v'‖ ≤
    t * (t * (2 * (nrm μ u' * nrm μ v')))) ht0
end ReciprocityTheory.ChartRestriction.DS.UnitA
