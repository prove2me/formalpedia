-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.scl_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:21.342544+00:00
-- url     : https://prove2.me/submissions/94b832d2-2372-41bb-97b3-aec64c1c8db0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private lemma fL_det (τ : ℝ) (p : ℕ) : LinearMap.det (fL τ p) = τ ^ 2 := by
  unfold fL
  rw [LinearMap.det_pi, Fin.prod_univ_succ]
  simp [gL, Fin.succ_ne_zero, LinearMap.det_smul, Complex.finrank_real_complex]
private lemma sclL_apply (τ : ℝ) (p m : ℕ) (x : Xp (p + 1) m) : sclL τ p m x = scl τ x := by
  obtain ⟨a, b, c, d⟩ := x
  have h1 : fL τ p a = Function.update a 0 ((τ : ℂ) * a 0) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [fL, gL, Complex.real_smul]
    · simp [fL, gL, hi, Function.update_apply]
  have h2 : fL τ⁻¹ p b = Function.update b 0 (b 0 / (τ : ℂ)) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [fL, gL, Complex.real_smul, div_eq_inv_mul]
    · simp [fL, gL, hi, Function.update_apply]
  simp [sclL, scl, h1, h2]
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (τ : ℝ) (hτ : τ ≠ 0) :
    MeasurePreserving (scl (p := p) (m := m) τ) volume volume := by
  have hdet : LinearMap.det (sclL τ p m) = 1 := by
    unfold sclL
    rw [LinearMap.det_prodMap, LinearMap.det_prodMap, fL_det, fL_det, LinearMap.det_id, mul_one,
      inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hτ)]
  have hf : (scl (p := p) (m := m) τ) = sclL τ p m := funext fun x => (sclL_apply τ p m x).symm
  rw [hf]
  haveI : BorelSpace ((Fin m → ℂ) × ℝ) := Prod.borelSpace
  haveI : BorelSpace ((Fin (p + 1) → ℂ) × (Fin m → ℂ) × ℝ) := Prod.borelSpace
  haveI : BorelSpace (Xp (p + 1) m) := Prod.borelSpace
  haveI hp1 : (volume : Measure (Fin (p + 1) → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => volume).IsAddHaarMeasure
    infer_instance
  haveI hm1 : (volume : Measure (Fin m → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => volume).IsAddHaarMeasure
    infer_instance
  haveI : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure := by
    show ((volume : Measure (Fin m → ℂ)).prod (volume : Measure ℝ)).IsAddHaarMeasure
    infer_instance
  haveI : (volume : Measure ((Fin (p + 1) → ℂ) × (Fin m → ℂ) × ℝ)).IsAddHaarMeasure := by
    show ((volume : Measure (Fin (p + 1) → ℂ)).prod
      (volume : Measure ((Fin m → ℂ) × ℝ))).IsAddHaarMeasure
    exact Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (Xp (p + 1) m)).IsAddHaarMeasure := by
    show ((volume : Measure (Fin (p + 1) → ℂ)).prod
      (volume : Measure ((Fin (p + 1) → ℂ) × (Fin m → ℂ) × ℝ))).IsAddHaarMeasure
    exact Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(sclL τ p m).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (by rw [hdet]; norm_num), hdet]
  simp
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
