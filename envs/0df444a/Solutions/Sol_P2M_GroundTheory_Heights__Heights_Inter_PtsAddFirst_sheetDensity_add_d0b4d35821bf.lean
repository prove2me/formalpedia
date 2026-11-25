-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_sheetDensity_add_d0b4d35821bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:57:39.188538+00:00
-- url     : https://prove2.me/submissions/167a99be-2399-4d1e-a358-5898909d56eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_cxHessian_add_d424e060e9c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_maDensity_cons_add_e9022f5e9455
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pot_contDiffAt
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace PtsAddFirst
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {e : ℕ} (Q : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ))
    (L : Fin e → HermLine ι) (M N : HermLine ι) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (e + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) g y w =
      sheetDensity Q Ψ (Fin.cons (fun z => Real.log (M.h z)) (pot L)) g y w +
        sheetDensity Q Ψ (Fin.cons (fun z => Real.log (N.h z)) (pot L)) g y w := by
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · simp only [sheetDensity, dif_pos hγ]
    set γ := hγ.choose
    have hs : IsSheet Q Ψ y w γ := hγ.choose_spec
    have han : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ γ y' := (sheet_analyticAt osgood hs).eventually_analyticAt
    have hmc : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts Q := hs.2.mono fun _ h => h.2.1
    have hcd : ∀ {A : HermLine ι}, IsSmoothHerm A →
        ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (A.h (γ y''))) y' := fun hA =>
      (han.and hmc).mono fun y' h => pot_contDiffAt hA h.1 h.2.1
    have hsum : (fun y' => Real.log ((M.tensor N).h (γ y'))) =ᶠ[𝓝 y]
        fun y' => Real.log (M.h (γ y')) + Real.log (N.h (γ y')) := hmc.mono fun y' h =>
      Real.log_mul (M.pos _ h.1).ne' (N.pos _ h.1).ne'
    have hcons : ∀ u : ((Σ k, ι k) → ℂ) → ℝ,
        (fun j y' => (Fin.cons u (pot L) : Fin (e + 1) → _) j (γ y')) =
          Fin.cons (fun y' => u (γ y')) (fun j y' => pot L j (γ y')) := by
      intro u
      funext j y'
      refine Fin.cases ?_ (fun i => ?_) j <;> simp
    rw [hcons, hcons, hcons, PtsAddFirst.maDensity_cons_add _ _ _ _ _
      (PtsAddFirst.cxHessian_add (hcd hM) (hcd hN) hsum), mul_add]
  · simp only [sheetDensity, dif_neg hγ, add_zero]
end PtsAddFirst
end GroundTheory.Heights₂.Heights.Inter
