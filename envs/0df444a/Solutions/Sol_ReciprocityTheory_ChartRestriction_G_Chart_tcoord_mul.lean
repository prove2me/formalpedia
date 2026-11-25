-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tcoord_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:47.373787+00:00
-- url     : https://prove2.me/submissions/b16f26e3-aa16-43a6-99d6-00625f3106aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_comp_qD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_snd_rD_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fstD_comp_rD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scaleD_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_scaleD_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_restrictDiag_comp_incl_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_restrictDiag_comp_incl_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {w₁ w₂ : sp (R₀ := R) (DualNumber R) ⟶ G} (h₁ : IsTan w₁) (h₂ : IsTan w₂) :
    tcoord hx (w₁ * w₂) (isTan_mul h₁ h₂) = tcoord hx w₁ h₁ + tcoord hx w₂ h₂ := by
  let P : sp (R₀ := R) (JetR R (Fin 2) 1) ⟶ G := (spMap (qD 0) ≫ w₁) * (spMap (qD 1) ≫ w₂)
  have hP : spMap (jetAug R (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, jetAug_comp_qD,
      jetAug_comp_qD, h₁, h₂, _root_.mul_one]
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, -⟩ := hx.2.2 _ (jetAug R (Fin 2) 1) 1 (ker_jetAug_pow (Fin 2) 1) P hP
  have key : ∀ l : R × R →ₗ[R] R,
      spMap (rD l) ≫ P = spMap (dualLift (fun j => (rD l (ψ (zR 1 j))).snd)) ≫ x 1 := by
    intro l
    rw [hψ2, ← Category.assoc, spMap_comp,
      eq_dualLift ((rD l).comp ψ) (by rw [← AlgHom.comp_assoc, fstD_comp_rD, hψ1])]
    rfl
  have hval : ∀ l : R × R →ₗ[R] R,
      spMap (rD l) ≫ P = (spMap (scaleD (l ((1 : R), (0 : R)))) ≫ w₁) * (spMap (scaleD (l ((0 : R), (1 : R)))) ≫ w₂) := by
    intro l
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, restrictDiag_comp_incl_fst, restrictDiag_comp_incl_snd]
  have e1 : w₁ = spMap (dualLift (fun j => (rD (LinearMap.fst R R R) (ψ (zR 1 j))).snd)) ≫ x 1 := by
    rw [← key, hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [scaleD_one, spMap_id, Category.id_comp, spMap_scaleD_zero h₂, _root_.mul_one]
  have e2 : w₂ = spMap (dualLift (fun j => (rD (LinearMap.snd R R R) (ψ (zR 1 j))).snd)) ≫ x 1 := by
    rw [← key, hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [scaleD_one, spMap_id, Category.id_comp, spMap_scaleD_zero h₁, _root_.one_mul]
  have e12 : w₁ * w₂ = spMap (dualLift (fun j =>
      (rD (LinearMap.fst R R R + LinearMap.snd R R R) (ψ (zR 1 j))).snd)) ≫ x 1 := by
    rw [← key, hval]
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]
    rw [scaleD_one, spMap_id, Category.id_comp, Category.id_comp]
  rw [tcoord_eq hx _ _ _ e12, tcoord_eq hx _ _ _ e1, tcoord_eq hx _ _ _ e2]
  funext j
  exact snd_rD_add _
end ReciprocityTheory.ChartRestriction.G.Chart
