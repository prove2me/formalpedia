-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_proof_1628a7ac80ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:40.100988+00:00
-- url     : https://prove2.me/submissions/6ef1b112-a167-430c-b311-81f634cf0095

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsRegLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_abs_half_log_le_9e14d95ff747
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_tendsto_half_log_202190eeb978
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_regLine_8cd27babf8cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_logNorm_eq_log_secNorm_66b2fbd2f820
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_regLine_h_743c8a7df0e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regLine_a_a2bda8d846c3
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_projB_null


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace PtsRegLimit
theorem _root_.solution (hInt : PtsIntegrableStatement) (hAbs : PtsAbsIntegrable.Statement) :
    PtsRegLimit.Statement := by
  intro K _ ι _ Q e M E t ht hQ hM hE htQ
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  swap
  · simp only [dif_neg hΨ]
    exact tendsto_const_nhds
  simp only [dif_pos hΨ]
  have hgood := hΨ.choose_spec
  generalize hΨ.choose = Ψ at hgood ⊢
  unfold ptsIntegralAt
  obtain ⟨a, haE, hta⟩ := id ht
  have hfin : ∀ y, (fibre Q Ψ y).Finite := fibreFinite K ι Q e Ψ hQ hgood
  have h1 : (1 : MRing ι) ∉ Q := fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  have hone : ∀ ε, IsSectionOn Q (regLine E t ht ε) 1 := fun ε =>
    ⟨fun _ => 0, fun k => by rw [regLine_a]; simp, fun m hm k => by
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp, h1⟩

  have hsdlog : ∀ (B : HermLine ι) y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (B.h z)) y w =
      -sheetDensity Q Ψ (pot M) (logNorm B 1) y w := by
    intro B y w
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ, logNorm, map_one, norm_one, one_div, Real.log_inv]
      ring
    · simp only [sheetDensity, dif_neg hγ, neg_zero]
  have hFint : ∀ ε, 0 < ε → Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y,
      sheetDensity Q Ψ (pot M) (fun z => Real.log ((regLine E t ht ε).h z)) y w) := by
    intro ε hε
    refine (hInt K ι Q e Ψ M (regLine E t ht ε) 1 hQ hgood hM (isSmoothHerm_regLine hE hε)
      (hone ε)).neg.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.neg_apply]
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun w _ => (hsdlog _ y w).symm

  have hJ : IsMultiHomogIdeal (Ideal.span {t}) :=
    ⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩
  have hJP : ¬ Ideal.span {t} ≤ Q := fun h => htQ (h (Ideal.subset_span rfl))
  have hN : ∀ᵐ y, y ∈ {y : Fin e → ℂ | ∃ z ∈ mcPts Q, z ∈ mcPts (Ideal.span {t}) ∧
      Ψ (segre z) = Fin.cons 1 y}ᶜ := compl_mem_ae_iff.mpr (projB_null Ψ hQ hgood hJ hJP)
  have hpt : ∀ y, y ∈ {y : Fin e → ℂ | ∃ z ∈ mcPts Q, z ∈ mcPts (Ideal.span {t}) ∧
      Ψ (segre z) = Fin.cons 1 y}ᶜ → ∀ w (hγ : ∃ γ, IsSheet Q Ψ y w γ), secNorm E t (hγ.choose y) ≠ 0 := by
    intro y hy w hγ h0
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have hev0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact norm_eq_zero.mp h
      · exact absurd h (E.pos _ hmem.1).ne'
    refine hy ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, hev0, mul_zero]
  have hB1 : ∀ z, |Real.log ((regLine E t ht 1).h z)| = |Real.log (secNorm E t z ^ 2 + 1) / 2| := fun z => by
    rw [log_regLine_h]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => ∑ᶠ w ∈ fibre Q Ψ y, |sheetDensity Q Ψ (pot M) (logNorm E t) y w| +
      ∑ᶠ w ∈ fibre Q Ψ y, |sheetDensity Q Ψ (pot M) (fun z => Real.log ((regLine E t ht 1).h z)) y w|)
    (eventually_mem_nhdsWithin.mono fun ε hε => (hFint ε hε).aestronglyMeasurable) ?_ ?_ ?_
  ·
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hN] with y hy
    rw [Real.norm_eq_abs, finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ, abs_mul, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [hB1, log_regLine_h, logNorm_eq_log_secNorm]
      exact PtsRegLimit.abs_half_log_le (hpt y hy w hγ) hε.1 hε.2.le
    · simp only [sheetDensity, dif_neg hγ, abs_zero, add_zero, le_refl]
  ·
    have hts : IsSectionOn Q E t := ⟨a, haE, hta, htQ⟩
    refine (hAbs K ι Q e Ψ M E t hQ hgood hM hE hts).add ((hAbs K ι Q e Ψ M (regLine E t ht 1) 1 hQ hgood hM
      (isSmoothHerm_regLine hE one_pos) (hone 1)).congr (Eventually.of_forall fun y => ?_))
    exact finsum_mem_congr rfl fun w _ => by rw [hsdlog, abs_neg]
  ·
    filter_upwards [hN] with y hy
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    simp only [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun w _ => ?_
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ]
      refine Tendsto.mul_const _ ?_
      simp only [log_regLine_h, logNorm_eq_log_secNorm]
      exact PtsRegLimit.tendsto_half_log (hpt y hy w hγ)
    · simp only [sheetDensity, dif_neg hγ]
      exact tendsto_const_nhds
end PtsRegLimit
end GroundTheory.Heights₂.Heights.Inter
