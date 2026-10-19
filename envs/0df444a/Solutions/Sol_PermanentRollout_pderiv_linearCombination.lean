-- Prove2me | solution 1 for PermanentRollout.pderiv_linearCombination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/b2329044-3c87-4837-9baf-04338075b59d

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι κ : Type*} (input : ι)
    (family : κ → MvPolynomial ι ℂ) (coefficients : κ →₀ ℂ) :
    MvPolynomial.pderiv input
        (Finsupp.linearCombination ℂ family coefficients) =
      Finsupp.linearCombination ℂ
        (fun index => MvPolynomial.pderiv input (family index))
        coefficients := by
  simpa [Function.comp_def] using
    Finsupp.apply_linearCombination ℂ
      (MvPolynomial.pderiv input).toLinearMap family coefficients
end PermanentRollout
