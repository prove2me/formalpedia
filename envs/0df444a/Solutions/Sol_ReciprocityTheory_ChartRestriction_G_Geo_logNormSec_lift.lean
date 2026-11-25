-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.logNormSec_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:54.705232+00:00
-- url     : https://prove2.me/submissions/9cdca71f-66a2-4ad9-b9c1-0498f61ece9a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {P J : Ideal (MRing ι)} {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (R : AnLogRes P J e) (A : HermLine ι) (s : MRing ι) (y : R.X) :
    logNormSec (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) y =
      logNorm A s (R.lift y y) := by
  have hpos := A.pos _ (R.mem y y (R.mem_U y)).1
  simp only [logNormSec, logNorm, potOf]
  rw [Real.exp_neg, Real.exp_log hpos, div_eq_mul_inv]
end ReciprocityTheory.ChartRestriction.G.Geo
