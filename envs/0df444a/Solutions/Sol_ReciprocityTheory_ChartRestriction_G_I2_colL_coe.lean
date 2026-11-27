-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.colL_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:01.663021+00:00
-- url     : https://prove2.me/submissions/a657e783-97b2-4dbd-99e4-581ce5d5b94f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivDeterminantPolyTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MvPolynomial
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ} {dim : (E →+* ℂ) → ℕ}
variable (X : PT E) (bs : Fin nb → Block E n X.dim)
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (T : Choice bs) (k : Fin n) :
    ((colL (lst X bs T) k : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
      ((Multiset.map (letter bs T) Finset.univ.val).filter (fun l => l.1 = k)).map
        (fun l => EuclideanSpace.single l.2 (1 : ℂ)) := by
  rw [colL, lst, List.filter_map, List.map_map, ← Multiset.map_coe]
  conv_rhs => rw [← Multiset.coe_toList (Multiset.map (letter bs T) Finset.univ.val),
    Multiset.filter_coe, Multiset.map_coe]
  rfl
end ReciprocityTheory.ChartRestriction.G.I2
