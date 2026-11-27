-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PtsMonoSemiPos_proof_43daecbcb967
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:01:04.332124+00:00
-- url     : https://prove2.me/submissions/39e8704c-4e89-4b6c-ace9-b3231492bb34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsMonoSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSheetHessPSD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsMonoSemiPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_nonneg_of_posSemidef
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace PtsMonoSemiPos
theorem _root_.solution (hInt : PtsIntegrableStatement) (hHess : SheetHessPSD.Statement) :
    PtsMonoSemiPos.Statement := by
  intro K _ ι _ Q e M E D t hQ hMs hMp hE ht hD hDa hle
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  swap
  · rw [dif_neg hΨ, dif_neg hΨ]
  rw [dif_pos hΨ, dif_pos hΨ]
  set Ψ := hΨ.choose with hΨdef
  have hΨg : IsGoodProj Q Ψ := hΨ.choose_spec
  unfold ptsIntegralAt
  have hD1 : IsSectionOn Q D 1 := by
    refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
      fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have key : ∀ y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w =
      -sheetDensity Q Ψ (pot M) (logNorm D 1) y w := by
    intro y w
    unfold sheetDensity
    split_ifs <;> simp [logNorm, Real.log_inv]
  have h1 := hInt K ι Q e Ψ M E t hQ hΨg hMs hE ht
  have h2 : Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y,
      sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w) := by
    simp only [key, finsum_neg_distrib]
    exact (hInt K ι Q e Ψ M D 1 hQ hΨg hMs hD hD1).neg
  obtain ⟨a, -, hta, htQ⟩ := ht
  have hJ : IsMultiHomogIdeal (Ideal.span {t}) :=
    ⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩
  have hJQ : ¬ Ideal.span {t} ≤ Q := fun h => htQ (h (Ideal.subset_span rfl))
  have hnull := projB_null Ψ hQ hΨg hJ hJQ
  refine integral_mono_ae h1 h2 ?_
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra hyB
  apply hy
  have hfin := fibreFinite K ι Q e Ψ hQ hΨg y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold sheetDensity
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · rw [dif_pos hγ, dif_pos hγ]
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have ht0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) ≠ 0 := by
      intro h0
      refine hyB ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      rw [map_mul, map_mul, h0, mul_zero]
    have hma : 0 ≤ maDensity (fun j y' => pot M j (hγ.choose y')) y :=
      ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j =>
        hHess K ι Q e Ψ (M j) y w hγ.choose (hMs j) (hMp j) hγ.choose_spec
    exact mul_le_mul_of_nonneg_right (hle _ hmem ht0) hma
  · rw [dif_neg hγ, dif_neg hγ]
end PtsMonoSemiPos
end GroundTheory.Heights₂.Heights.Inter
