-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.cocycle_identity_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:25.003207+00:00
-- url     : https://prove2.me/submissions/86a7a9ed-441e-47c4-a76e-42ba2d307c9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
section Bundles
variable {X : Scheme.{0}}
private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end Bundles
section Unif
open ReciprocityTheory.ChartRestriction.G.Out
end Unif
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {L : LB X} (hL : L.IsLB) (p₁ p₂ q₁ q₂ : L.ι) :
    res (inf_le_left : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂) (L.g p₁ p₂) =
      res (inf_le_inf inf_le_left inf_le_left : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁) (L.g p₁ q₁) *
        (res (inf_le_inf inf_le_right inf_le_right : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₂ ⊓ L.U q₂) (L.g p₂ q₂))⁻¹ *
      res (inf_le_right : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U q₁ ⊓ L.U q₂) (L.g q₁ q₂) := by
  have h1 := congrArg (res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
      L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂ ⊓ L.U q₂)) (hL.cocycle p₁ p₂ q₂)
  have h2 := congrArg (res (le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_right) :
      L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁ ⊓ L.U q₂)) (hL.cocycle p₁ q₁ q₂)
  simp only [map_mul, res_res_lemma] at h1 h2
  rw [eq_mul_inv_of_mul_eq h1, ← h2]
  exact mul_right_comm _ _ _
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
