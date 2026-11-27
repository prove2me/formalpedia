-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.eq_of_pOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:24.735315+00:00
-- url     : https://prove2.me/submissions/ecc58410-24a7-4b0e-ab86-ba633d9ab620

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
noncomputable section
variable {W : Scheme.{0}} {U : W.Opens}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution (hU : IsAffineOpen U) {z z' : W} (hz : z ∈ U) (hz' : z' ∈ U)
    (h : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨z', hz'⟩) : z = z' := by
  have h1 := hU.fromSpec_primeIdealOf ⟨z, hz⟩
  have h2 := hU.fromSpec_primeIdealOf ⟨z', hz'⟩
  rw [h] at h1
  exact h1.symm.trans h2
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
