-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.res_eq_of_gm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:39.501705+00:00
-- url     : https://prove2.me/submissions/d37b183d-5524-48b3-b298-856134cc65c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {Y : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂} {h₃ : V ≤ U₃}
    {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : ∀ y ∈ V, gm (𝟙 Y) y U₁ a * gm (𝟙 Y) y U₂ b = gm (𝟙 Y) y U₃ c * gm (𝟙 Y) y U₄ d) :
    res h₁ a * res h₂ b = res h₃ c * res h₄ d := by
  apply Units.ext
  refine TopCat.Presheaf.section_ext Y.sheaf V _ _ (fun y hy => ?_)
  have key := H y hy
  rw [← gm_res (𝟙 Y) y h₁ hy a, ← gm_res (𝟙 Y) y h₂ hy b, ← gm_res (𝟙 Y) y h₃ hy c, ← gm_res (𝟙 Y) y h₄ hy d,
    ← map_mul, ← map_mul] at key
  have hy' : (𝟙 Y) y ∈ V := hy
  simp only [gm, dif_pos hy', MonoidHom.comp_apply] at key
  have key2 := congrArg Units.val key
  exact key2
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
