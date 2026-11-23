-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.rs_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:18.962409+00:00
-- url     : https://prove2.me/submissions/a9aff0da-162f-468d-973e-dc81961119dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x : Γ(Z, U)ˣ) :
    rs h (x : Γ(Z, U)) = ((res h x : Γ(Z, V)ˣ) : Γ(Z, V)) := rfl
end ReciprocityTheory.ChartRestriction.G.DVR
