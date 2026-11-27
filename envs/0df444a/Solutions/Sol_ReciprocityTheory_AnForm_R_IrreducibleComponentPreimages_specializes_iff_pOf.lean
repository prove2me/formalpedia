-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.specializes_iff_pOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:23:35.31495+00:00
-- url     : https://prove2.me/submissions/6fcce396-8a04-4602-a8c5-af76e0411b42

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
theorem _root_.solution (hU : IsAffineOpen U) {z z' : W} (hz : z ∈ U) (hz' : z' ∈ U) :
    z ⤳ z' ↔ hU.primeIdealOf ⟨z, hz⟩ ≤ hU.primeIdealOf ⟨z', hz'⟩ := by
  have := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff
    (x := hU.primeIdealOf ⟨z, hz⟩) (y := hU.primeIdealOf ⟨z', hz'⟩)
  rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
  rw [PrimeSpectrum.le_iff_specializes]
  exact this
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
