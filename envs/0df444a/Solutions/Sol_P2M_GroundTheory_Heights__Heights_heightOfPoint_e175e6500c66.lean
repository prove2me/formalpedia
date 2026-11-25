-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_heightOfPoint_e175e6500c66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:28.394381+00:00
-- url     : https://prove2.me/submissions/c525d7fc-c17f-4729-b3ac-b0bd6cee952c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_sum_le_30e128122f54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_finite_adicAbv_ne_one_e06b12e8b8b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_adicAbv_intToField_le_one_e530369dfcdb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_archDualNorm_pos_3023062927e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_adicAbv_f04fbb456bfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_eq_gaussNormOf_d4ed71b31023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_log_norm_embeddings_2fdebfa8404c


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
open MvPolynomial NumberField ComplexAt TensorProduct
noncomputable section
open HeightOfPointAlt
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : HeightOfPoint.Statement := by
  intro F _ _ W _ _ _ _ h n w hw K _ _ _ yv hyv
  have hspan : ∀ x : W, ∃ c : Fin n → 𝓞 F, ∑ k, c k • w k = x := fun x =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp (hw ▸ Submodule.mem_top)
  have hyvx : ∀ c : Fin n → 𝓞 F, yv (∑ k, c k • w k) = ∑ k, intToField F K (c k) * yv (w k) := by
    intro c
    simp only [map_sum, map_smulₛₗ, smul_eq_mul]
  set M : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) with hMdef
  have hM0 : ∀ v, 0 ≤ M v := fun v => Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _
  have hleM : ∀ v k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) ≤ M v := fun v k =>
    by
    show _ ≤ ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k))
    exact le_ciSup (f := fun k => NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)))
      (Finite.bddAbove_range _) k
  have hle : ∀ v x, NumberField.HeightOneSpectrum.adicAbv K v (yv x) ≤ M v := by
    intro v x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) :=
          mul_le_mul_of_nonneg_right (adicAbv_intToField_le_one v (c k)) (AbsoluteValue.nonneg _ _)
      _ ≤ M v := by rw [one_mul]; exact hleM v k
  have hdual : ∀ v, dualNormAt v yv = M v := by
    intro v
    have hbdd : BddAbove (Set.range fun x : W =>
        NumberField.HeightOneSpectrum.adicAbv K v (yv x)) := by
      refine ⟨M v, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hle v x
    unfold dualNormAt
    refine le_antisymm (Real.iSup_le (hle v) (hM0 v)) ?_
    exact Real.iSup_le (fun k => le_ciSup hbdd (w k))
      (Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _)
  have hgauss : ∀ v, gaussNorm v (∑ k, C (yv (w k)) * X k : MvPolynomial (Fin n) K) = M v := by
    intro v
    rw [gaussNorm_eq_gaussNormOf]
    refine le_antisymm (gaussNormOf_le _ (hM0 v) fun m => ?_) ?_
    · rw [coeff_sum]
      refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
      rw [coeff_C_mul, map_mul, coeff_X]
      split_ifs
      · rw [map_one, mul_one]; exact hleM v k
      · rw [map_zero, mul_zero]; exact hM0 v
    · refine Real.iSup_le (fun k => ?_) (gaussNormOf_nonneg _ _)
      have hc : coeff (Finsupp.single k 1) (∑ j, C (yv (w j)) * X j : MvPolynomial (Fin n) K) =
          yv (w k) := by
        rw [coeff_sum, Finset.sum_eq_single k]
        · rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one]
        · intro j _ hj
          rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
          intro hjk
          exact hj (Finsupp.single_left_injective one_ne_zero hjk)
        · intro hk; exact absurd (Finset.mem_univ k) hk
      rw [← hc]
      exact le_gaussNormOf _ _ _

  obtain ⟨k₀, hk₀⟩ : ∃ k, yv (w k) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hyv
    ext x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    simp [hcon]
  have hMpos : ∀ v, 0 < M v := fun v =>
    lt_of_lt_of_le ((NumberField.HeightOneSpectrum.adicAbv K v).pos hk₀) (hleM v k₀)
  have hMfin : (Function.support fun v => Real.log (M v)).Finite := by
    refine (Set.Finite.biUnion (Set.toFinite {k | yv (w k) ≠ 0})
      fun k hk => finite_adicAbv_ne_one hk).subset ?_
    intro v hv
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hnot
    apply hv
    have h1 : M v = 1 := by
      refine le_antisymm (Real.iSup_le (fun k => ?_) zero_le_one) ?_
      · by_cases hk : yv (w k) = 0
        · rw [hk, map_zero]; exact zero_le_one
        · exact (hnot k hk).le
      · rw [← hnot k₀ hk₀]; exact hleM v k₀
    simp only [h1, Real.log_one]
  refine ⟨fun v => ⟨hdual v, (hdual v).trans (hgauss v).symm⟩, fun x hx => ?_⟩
  have hAfin : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x))).Finite := by
    refine (finite_adicAbv_ne_one hx).subset ?_
    intro v hv h1
    apply hv
    simp only [h1, Real.log_one]
  have e1 : ∀ v, Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x) / dualNormAt v yv) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x)) - Real.log (M v) := by
    intro v
    rw [hdual, Real.log_div ((NumberField.HeightOneSpectrum.adicAbv K v).pos hx).ne' (hMpos v).ne']
  have e2 : ∀ τ : K →+* ℂ, Real.log (‖τ (yv x)‖ / archDualNorm h τ yv) =
      Real.log ‖τ (yv x)‖ - Real.log (archDualNorm h τ yv) := by
    intro τ
    exact Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero τ).mpr hx))
      (archDualNorm_pos h τ yv x hx).ne'
  have e3 : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (dualNormAt v yv) =
      ∑ᶠ v, Real.log (M v) := finsum_congr fun v => by rw [hdual]
  unfold heightWith
  simp only [e1, e2]
  rw [finsum_sub_distrib hAfin hMfin, Finset.sum_sub_distrib, finsum_log_adicAbv hx,
    sum_log_norm_embeddings hx, e3]
  ring
end GroundTheory.Heights₂.Heights
