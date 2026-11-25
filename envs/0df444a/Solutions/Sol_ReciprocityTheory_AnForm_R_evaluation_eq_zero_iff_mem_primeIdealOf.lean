-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.evaluation_eq_zero_iff_mem_primeIdealOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:37.552544+00:00
-- url     : https://prove2.me/submissions/3f9b4a72-227c-424b-9e34-91eab19a48e8

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.evaluation U x hx s = 0 ↔ s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  have e : x ∈ X.basicOpen s ↔ hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen s := by
    rw [← hU.fromSpec_preimage_basicOpen]
    change x ∈ X.basicOpen s ↔ hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen s
    rw [show hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x from hU.fromSpec_primeIdealOf ⟨x, hx⟩]
  rw [e, PrimeSpectrum.mem_basicOpen, not_not]
end ReciprocityTheory.AnForm.R
