-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_eval_aeval__5dda70722a7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:27.863834+00:00
-- url     : https://prove2.me/submissions/2b057cbc-1203-496a-a196-8260037a8434

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Mathlib.Algebra.MvPolynomial.Funext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_FFVMap

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open NumberField IsDedekindDomain Formalism.L2.Pj MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k K : Type} [Field k] [Field K]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {ι κ : Type} (g : ι → MvPolynomial κ k) (x : κ → k) (Q : MvPolynomial ι k) :
    eval x (aeval g Q) = eval (fun ℓ => eval x (g ℓ)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ℓ hp => simp only [map_mul, hp, aeval_X, eval_X]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
