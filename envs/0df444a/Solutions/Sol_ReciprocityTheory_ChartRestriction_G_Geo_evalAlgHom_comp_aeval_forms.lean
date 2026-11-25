-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.evalAlgHom_comp_aeval_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:13:55.485639+00:00
-- url     : https://prove2.me/submissions/0805d277-f2b0-40af-ae28-c433430e15a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushC

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {F : Type} (Q : F → Ideal (MRing ι))
    {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ) (W : F) :
    (Pi.evalAlgHom ℚ (fun W : F => MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal (Q W)) W).comp
        (aeval (forms (fun t W => segQ (Q W) t) L)) = aeval (forms (segQ (Q W)) L) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [forms]
end ReciprocityTheory.ChartRestriction.G.Geo
