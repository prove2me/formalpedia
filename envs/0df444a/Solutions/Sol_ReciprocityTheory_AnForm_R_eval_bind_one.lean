-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.eval_bind_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:59.168898+00:00
-- url     : https://prove2.me/submissions/af87d1c4-7706-467f-b503-b255e8c68fd6

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {m : ℕ} (y : Fin m → ℂ) {τ : Type} (g : τ → MvPolynomial (Fin m) ℂ)
    (φ : MvPolynomial τ ℂ) : eval y (bind₁ g φ) = eval (fun q => eval y (g q)) φ := by
  induction φ using MvPolynomial.induction_on
  · simp
  · simp [*]
  · simp [*]
end ReciprocityTheory.AnForm.R
