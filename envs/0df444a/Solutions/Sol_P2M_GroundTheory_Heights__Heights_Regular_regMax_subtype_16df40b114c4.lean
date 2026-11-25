-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_regMax_subtype_16df40b114c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:53.393072+00:00
-- url     : https://prove2.me/submissions/a391ad1c-1e6b-4bec-9559-a1fcbc5412c5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_abs_lt_of_k__ne_zero_f718908ff862
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_integral_k__4854bf227994
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_le_tmax_639e995f5930
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_tmax_le_5df8adbdca5e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → Prop) [DecidablePred p]
    [Nonempty {i // p i}] {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ)
    (hdom : ∀ i, ¬ p i → ∃ k, p k ∧ t i + η ≤ t k) :
    regMax η t = regMax η (fun k : {i // p i} => t k) := by
  unfold regMax
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p
  have hmp : MeasurePreserving e (volume : Measure (ι → ℝ))
      ((volume : Measure ({i // p i} → ℝ)).prod (volume : Measure ({i // ¬ p i} → ℝ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℝ)) p
  rw [← (hmp.symm e).integral_comp']
  have hpt : ∀ q : ({i // p i} → ℝ) × ({i // ¬ p i} → ℝ),
      tmax (fun j => t j + η * e.symm q j) * ∏ j, kθ (e.symm q j) =
        (tmax (fun k : {i // p i} => t k + η * q.1 k) * ∏ k, kθ (q.1 k)) *
          ∏ k, kθ (q.2 k) := by
    intro q
    have hv1 : ∀ k : {i // p i}, e.symm q k = q.1 k := fun k => by
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, k.2]
    have hv2 : ∀ k : {i // ¬ p i}, e.symm q k = q.2 k := fun k => by
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, k.2]
    have hprod : ∏ j, kθ (e.symm q j) = (∏ k : {i // p i}, kθ (q.1 k)) * ∏ k, kθ (q.2 k) := by
      rw [← Fintype.prod_subtype_mul_prod_subtype p]
      simp [hv1, hv2]
    rw [hprod]
    by_cases hall : ∀ j, kθ (e.symm q j) ≠ 0
    · have hb : ∀ j, |e.symm q j| < 1 / 2 := fun j => abs_lt_of_kθ_ne_zero (hall j)
      have htm : tmax (fun j => t j + η * e.symm q j) =
          tmax (fun k : {i // p i} => t k + η * q.1 k) := by
        refine le_antisymm (tmax_le fun j => ?_) (tmax_le fun k => ?_)
        · by_cases hj : p j
          · have := le_tmax (fun k : {i // p i} => t k + η * q.1 k) ⟨j, hj⟩
            simpa [hv1 ⟨j, hj⟩] using this
          · obtain ⟨k, hk, hjk⟩ := hdom j hj
            have h1 := (abs_lt.1 (hb j)).2
            have h2 := (abs_lt.1 (hb k)).1
            have h3 := le_tmax (fun k : {i // p i} => t k + η * q.1 k) ⟨k, hk⟩
            simp only [← hv1 ⟨k, hk⟩] at h3
            have h4 : η * e.symm q j ≤ η * (1 / 2) := mul_le_mul_of_nonneg_left h1.le hη
            have h5 : η * (-(1 / 2)) ≤ η * e.symm q k := mul_le_mul_of_nonneg_left h2.le hη
            linarith
        · have := le_tmax (fun j => t j + η * e.symm q j) k
          simpa [hv1 k] using this
      rw [htm, mul_assoc]
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have h0 : ∏ j, kθ (e.symm q j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
      rw [hprod] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · rw [h]; ring
      · rw [h]; ring
  simp_rw [hpt]
  rw [integral_prod_mul (fun h1 : {i // p i} → ℝ =>
      tmax (fun k : {i // p i} => t k + η * h1 k) * ∏ k, kθ (h1 k))
    (fun h2 : {i // ¬ p i} → ℝ => ∏ k, kθ (h2 k))]
  have hH : ∫ h2 : {i // ¬ p i} → ℝ, ∏ k, kθ (h2 k) = 1 := by
    rw [show (volume : Measure ({i // ¬ p i} → ℝ)) = Measure.pi fun _ => volume from rfl,
      integral_fintype_prod_eq_prod (fun _ => kθ)]
    simp [integral_kθ]
  rw [hH, mul_one]
end GroundTheory.Heights₂.Heights.Regular
