-- Prove2me | solution 1 for PIW.ENSpec.homog_mem_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:28.522798+00:00
-- url     : https://prove2.me/submissions/cc8534f8-f5f3-4fd5-9854-89f91d9b69f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {R : Type u} [CommRing R] {D : ℕ}
local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))
namespace PIW.ENSpec
theorem _root_.solution {a : ℕ} {p : MvPolynomial (Fin D) R} (hp : p.IsHomogeneous a)
    (h : p ∈ 𝔛 ^ (a + 1)) : p = 0 := by
  rw [show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff] at h
  ext d
  by_contra hne
  have h0 := hp hne
  have h1 : d.degree = a := by rw [Finsupp.degree_eq_weight_one]; exact h0
  have h2 := h d (mem_support_iff.2 hne)
  omega
end PIW.ENSpec
