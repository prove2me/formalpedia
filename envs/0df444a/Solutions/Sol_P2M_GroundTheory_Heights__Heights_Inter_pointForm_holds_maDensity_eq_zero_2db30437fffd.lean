-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointForm_holds_maDensity_eq_zero_2db30437fffd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:18.129841+00:00
-- url     : https://prove2.me/submissions/25fac3c4-c5c0-444b-aaef-38a6cdcb3725

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MixedDiscEqZeroOfMulVec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_mulVec_eec48391f62a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_blocks_ne_zero_restrict_c2698d5c05ab
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sheet_analyticAt


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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace pointForm_holds
theorem _root_.solution (hR : pointFormRank_holds.Statement) (hE : pointFormEuler_holds.Statement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d n : ℕ}
    {L : Fin n → HermLine ι} {L' : Fin n → HermLine ι'} (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hdn : d < n + 1) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} {y : Fin n → ℂ} {w : ((k : K') → ι' k) → ℂ}
    {γ : (Fin n → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((L' j).h (γ y'))) y = 0 := by
  set F : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y' p => γ y' (v p) with hF
  have hγa : AnalyticAt ℂ γ y := sheet_analyticAt osgood hγ
  have hFa : AnalyticAt ℂ F y := analyticAt_pi_iff.mpr fun p => analyticAt_coord hγa (v p)
  have hFy : ∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0 := blocks_ne_zero_restrict hv hγ.2.self_of_nhds.2.1.1
  have hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts (imageZ v P') := by
    filter_upwards [hγ.2] with y' h
    refine ⟨blocks_ne_zero_restrict hv h.2.1.1, fun f hf => ?_⟩
    have h0 := h.2.1.2 _ (Ideal.mem_comap.mp hf)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h0
    exact h0
  obtain ⟨x, hx, c, hxc⟩ := hR K ι (imageZ v P') d n F y hQ (by omega) hFa hFQ
  have hpot : ∀ j, (fun y' => Real.log ((L' j).h (γ y'))) = fun y' => Real.log ((L j).h (F y')) :=
    fun j => funext fun y' => by rw [(hLL j).2]
  simp only [maDensity, hpot]
  rw [mixedDisc_eq_zero_of_mulVec (u := star x) (star_ne_zero.mpr hx)
    fun j => hE K ι (L j) n F y x c (hL j) hFa hFy hxc]
  simp
end pointForm_holds
end GroundTheory.Heights₂.Heights.Inter
