-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_law_Ici_f045ceeff4d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:49:24.058859+00:00
-- url     : https://prove2.me/submissions/1417914a-6079-4405-8255-c759685e0868

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawFirstCoord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_eq_bc9be0c0ec41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_piFinSuccAbove_zero_apply_389038ca931c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_nonneg_b8444e370306
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_pos_of_ne_zero_64c6d51818d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_succ_4c218d8f435d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_std_norm_eq_aeefb71df068
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_ne_top_34fed7d837d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_pos_a1becdcd33ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_singleton_zero_b8b7cba0e078


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory ProbabilityTheory Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawFirstCoord
open SphereMean
namespace GroundTheory.Heights₂.Heights.SphereLawFirstCoord
theorem _root_.solution (k : ℕ) (c : ℝ) :
    ((sphereLaw (k + 1 + 1)).map (fun z ↦ ‖z 0‖ ^ 2)) (Ici c) =
      ENNReal.ofReal ((1 - min (max c 0) 1) ^ (k + 1)) := by
  have hGm : Measurable fun (u : Fin 1 × Fin (k + 1 + 1) → ℂ) (j : Fin (k + 1 + 1)) ↦
      sphereNormalize (HermNorm.std (k + 1 + 1)) 1 u (0, j) := by
    unfold sphereNormalize
    simp only [HermNorm.std_norm_eq]
    fun_prop
  have hFm : Measurable fun z : Fin (k + 1 + 1) → ℂ ↦ ‖z 0‖ ^ 2 := by fun_prop
  have hBm : MeasurableSet (sphereBall (HermNorm.std (k + 1 + 1)) 1) :=
    (isOpen_sphereBall_std _).measurableSet
  rw [Measure.map_apply hFm measurableSet_Ici, sphereLaw,
    Measure.map_apply hGm (hFm measurableSet_Ici), cond_apply hBm]

  set eq := Equiv.uniqueProd (Fin (k + 1 + 1)) (Fin 1)
  set P := MeasurableEquiv.piCongrLeft (fun _ : Fin (k + 1 + 1) ↦ ℂ) eq
  have hP : MeasurePreserving P volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin (k + 1 + 1) ↦ ℂ) eq
  have hPapp : ∀ u j, P u j = u (0, j) := by
    intro u j
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (k + 1 + 1) ↦ ℂ) eq u (0, j)
    simpa [eq] using this
  have hPu : ∀ u : Fin 1 × Fin (k + 1 + 1) → ℂ, (fun j ↦ u (0, j)) = P u :=
    fun u ↦ funext fun j ↦ (hPapp u j).symm
  have hB : sphereBall (HermNorm.std (k + 1 + 1)) 1 = P ⁻¹' ballSet (k + 1 + 1) 1 := by
    ext u
    simp only [sphereBall, mem_ofPred_eq, mem_preimage, ballSet, std_norm_eq, Fin.forall_fin_one,
      hPu, Real.sqrt_lt' one_pos, one_pow]
  set T : Set (Fin (k + 1 + 1) → ℂ) :=
    {v | sqNorm v < 1 ∧ c ≤ ‖((√(sqNorm v) : ℝ) : ℂ)⁻¹ * v 0‖ ^ 2} with hT_def
  have hT : sphereBall (HermNorm.std (k + 1 + 1)) 1 ∩
      ((fun (u : Fin 1 × Fin (k + 1 + 1) → ℂ) (j : Fin (k + 1 + 1)) ↦
        sphereNormalize (HermNorm.std (k + 1 + 1)) 1 u (0, j)) ⁻¹'
        ((fun z : Fin (k + 1 + 1) → ℂ ↦ ‖z 0‖ ^ 2) ⁻¹' Ici c)) = P ⁻¹' T := by
    rw [hB]
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Ici, sphereNormalize, std_norm_eq, hPu, hT_def,
      mem_ofPred_eq, ballSet, hPapp]
  rw [hT, hB, hP.measure_preimage_equiv, hP.measure_preimage_equiv]
  have hV0 := (volume_ballSet_one_pos (k + 1 + 1)).ne'
  have hVt := volume_ballSet_one_ne_top (k + 1 + 1)
  have hnorm : ∀ v : Fin (k + 1 + 1) → ℂ,
      ‖((√(sqNorm v) : ℝ) : ℂ)⁻¹ * v 0‖ ^ 2 = ‖v 0‖ ^ 2 / sqNorm v := by
    intro v
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      inv_pow, Real.sq_sqrt (sqNorm_nonneg v)]
    ring

  have hTpos : 0 < c → T = {v | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} \ {0} := by
    intro hc
    ext v
    simp only [hT_def, mem_ofPred_eq, mem_sdiff, mem_singleton_iff, hnorm]
    by_cases hv : v = 0
    · subst hv
      simp [sqNorm]
      exact hc
    · have hs := sqNorm_pos_of_ne_zero hv
      rw [le_div_iff₀ hs]
      tauto
  rcases le_or_gt c 0 with hc | hc
  · have hTB : T = ballSet (k + 1 + 1) 1 := by
      ext v
      simp only [hT_def, mem_ofPred_eq, ballSet, and_iff_left_iff_imp]
      intro _
      exact hc.trans (by positivity)
    rw [hTB, ENNReal.inv_mul_cancel hV0 hVt, max_eq_right hc, min_eq_left zero_le_one]
    simp
  rcases lt_or_ge c 1 with hc1 | hc1
  · rw [hTpos hc, measure_sdiff_null (volume_singleton_zero _), volume_capSet_eq hc.le hc1,
      ← mul_assoc, mul_comm _ (ENNReal.ofReal _), mul_assoc, ENNReal.inv_mul_cancel hV0 hVt,
      mul_one, max_eq_left hc.le, min_eq_left hc1.le]
  ·
    have he := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1 + 1) ↦ ℂ) 0
    have hsub : T ⊆ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1 + 1) ↦ ℂ) 0 ⁻¹'
        (univ ×ˢ {0}) := by
      rw [hTpos hc]
      rintro v ⟨⟨h1, _⟩, hv⟩
      simp only [mem_preimage, piFinSuccAbove_zero_apply, mem_prod, mem_univ, true_and,
        mem_singleton_iff]
      by_contra htl
      have := sqNorm_pos_of_ne_zero htl
      rw [sqNorm_succ] at h1
      nlinarith [sqNorm_nonneg (Fin.tail v), norm_nonneg (v 0)]
    have h0 : volume T = 0 := by
      refine measure_mono_null hsub ?_
      rw [he.measure_preimage (MeasurableSet.univ.prod (measurableSet_singleton _)).nullMeasurableSet,
        Measure.volume_eq_prod, Measure.prod_prod, volume_singleton_zero, mul_zero]
    rw [h0, mul_zero, max_eq_left hc.le, min_eq_right hc1, sub_self, zero_pow (Nat.succ_ne_zero _),
      ENNReal.ofReal_zero]
end GroundTheory.Heights₂.Heights.SphereLawFirstCoord
