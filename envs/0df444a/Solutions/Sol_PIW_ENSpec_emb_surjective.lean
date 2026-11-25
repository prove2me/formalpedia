-- Prove2me | solution 1 for PIW.ENSpec.emb_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:06.651771+00:00
-- url     : https://prove2.me/submissions/3eeb08fe-596b-4d2c-a2f1-6dcc021fdc68

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
theorem _root_.solution (a : ℕ) : Function.Surjective (emb (R := R) (D := D) a) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearMap.mem_ker, gmap_mk, Submodule.Quotient.mk_eq_zero] at hq
  refine ⟨⟨homogeneousComponent a p, homogeneousComponent_mem a p⟩, ?_⟩
  apply Subtype.ext
  change (Submodule.Quotient.mk (homogeneousComponent a p) : MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) =
    Submodule.Quotient.mk p
  rw [Submodule.Quotient.eq, show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff']
  rw [show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff'] at hq
  intro d hd
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : d.degree = a
  · simp [h]
  · have : d.degree < a := by omega
    simp [h, hq d this]
end PIW.ENSpec
