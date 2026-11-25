-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_proof_3b57906f00c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:59.346235+00:00
-- url     : https://prove2.me/submissions/d5576f94-710a-4914-b19f-6e59bb181d25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_pot_cons_16aca8894e01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_sheetDensity_add_d0b4d35821bf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite


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
namespace PtsAddFirst
theorem _root_.solution (hInt : PtsIntegrableStatement) : PtsAddFirst.Statement := by
  intro K _ ι _ Q e L M N E t hQ hL hM hN hE ht
  have hL' : ∀ A : HermLine ι, IsSmoothHerm A → ∀ j, IsSmoothHerm ((Fin.cons A L : Fin (e + 1) → _) j) :=
    fun A hA j => Fin.cases hA (fun i => hL i) j
  have hMN : IsSmoothHerm (M.tensor N) := hM.mul hN
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ), IsGoodProj Q Ψ
  · simp only [ptsIntegral, dif_pos hΨ, ptsIntegralAt]
    have hI : ∀ A : HermLine ι, IsSmoothHerm A → Integrable (fun y => ∑ᶠ w ∈ fibre Q hΨ.choose y,
        sheetDensity Q hΨ.choose (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm E t) y w) := by
      intro A hA
      have h := hInt K ι Q (e + 1) hΨ.choose (Fin.cons A L) E t hQ hΨ.choose_spec (hL' A hA) hE ht
      rwa [PtsAddFirst.pot_cons] at h
    rw [← integral_add (hI M hM) (hI N hN)]
    congr 1
    funext y
    rw [← finsum_mem_add_distrib (fibreFinite K ι Q (e + 1) hΨ.choose hQ hΨ.choose_spec y)]
    exact finsum_mem_congr rfl fun w _ => PtsAddFirst.sheetDensity_add Q _ L M N hM hN _ y w
  · simp only [ptsIntegral, dif_neg hΨ, add_zero]
end PtsAddFirst
end GroundTheory.Heights₂.Heights.Inter
