-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.Tri.pmaps_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:11.426525+00:00
-- url     : https://prove2.me/submissions/01fa89cf-cae0-422e-b4d9-44b44dbff6d0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq

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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
variable {K : Type} [Fintype K] {Y Y' Y'' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {φ'' : K → (Y'' ⟶ X'')}
  {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L' φ' ε)} {t'' : LB.Gen (LB.LinComb L'' φ'' ε)}
  {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace Tri
theorem _root_.solution (T : Tri w w' w'') (hL' : L'.IsLB) (hc : ∀ k, φ'' k ≫ F' = h' ≫ φ' k)
    (H : PMaps w φ' φ ε t' t h) (H' : PMaps w' φ'' φ' ε t'' t' h') : PMaps w'' φ'' φ ε t'' t (h' ≫ h) := by
  intro Z r z p q hp hq
  choose i hi using fun k => exists_chart hL' (F' (φ'' k (r z)))
  have hp' : ∀ k, F (φ' k ((r ≫ h') z)) ∈ L.U (p k) := fun k => by
    rw [Scheme.Hom.comp_apply, pt_eq hc]; exact hp k
  have hi' : ∀ k, φ' k ((r ≫ h') z) ∈ L'.U (i k) := fun k => by
    rw [Scheme.Hom.comp_apply, pt_eq hc]; exact hi k
  rw [T.prod hc Z r z p i q hp hi hq, ← Category.assoc, H Z (r ≫ h') z p i hp' hi', H' Z r z i q hi hq,
    mul_assoc]
end Tri
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
