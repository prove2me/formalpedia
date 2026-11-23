-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.cPoint_y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:03.122772+00:00
-- url     : https://prove2.me/submissions/23231761-a025-4e5c-9e1b-912606c15bbc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
variable {D F}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {k : ℕ} (p : QkPt D F k) : cP D _ p.y = p.g.b ^ k := by
  obtain ⟨h, ⟨gs, h0, hadd, hlast⟩, hio⟩ := p.eq
  have key : ∀ i : Fin (k + 1), (gs i).b = p.g.b ^ (i : ℕ) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [h0.1, Fin.val_zero, pow_zero]
      rfl
    | succ i ih =>
      rw [(hadd i).1, Fin.val_succ, pow_succ, ← Fin.coe_castSucc, ← ih]
      rfl
  show DegPre.cF D F p.y = _
  rw [← hio.1, ← hlast, key (Fin.last k), Fin.val_last]
end ReciprocityTheory.ChartRestriction.G.DVR
