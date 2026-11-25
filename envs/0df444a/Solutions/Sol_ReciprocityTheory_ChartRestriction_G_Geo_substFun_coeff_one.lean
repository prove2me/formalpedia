-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.substFun_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:09.887861+00:00
-- url     : https://prove2.me/submissions/84abd03d-e959-45fa-a352-9269543ea0d7

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {r : ℕ} (lam : Fin r → k) (j : Fin (r + 1)) :
    (substFun lam j).coeff 1 = C ((Fin.cons (1 : k) lam : Fin (r + 1) → k) j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [substFun]
  · simp [substFun, Polynomial.coeff_C]
end ReciprocityTheory.ChartRestriction.G.Geo
