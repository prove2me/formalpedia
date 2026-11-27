-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EmultiplicityOrd_proof_39412d3e8e9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:10.38089+00:00
-- url     : https://prove2.me/submissions/3c4e7aa1-d142-4b50-aa78-41ac6843e496

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PEmultiplicityOrd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace EmultiplicityOrd
theorem _root_.solution (h₁ : LocalizationPrimeDVR.Statement) : EmultiplicityOrd.Statement := by
  intro R _ _ _ _ q x p _ hq hp hx
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₁ R q p hq hp
  set O := Localization.AtPrime p
  have hfin : FiniteMultiplicity q x := FiniteMultiplicity.of_prime_left hq hx
  obtain ⟨y, hxy, hy⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hfin.emultiplicity_eq_multiplicity]

  have hyu : IsUnit (algebraMap R O y) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff O p y]
    change y ∉ p
    rw [hp, Ideal.mem_span_singleton]
    exact hy

  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O, congrArg (Ideal.map (algebraMap R O)) hp,
      Ideal.map_span, Set.image_singleton]
  have hirr : Irreducible (algebraMap R O q) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hnz : algebraMap R O q ∈ nonZeroDivisors O :=
    mem_nonZeroDivisors_of_ne_zero hirr.ne_zero
  conv_rhs => rw [hxy, map_mul, map_pow, Ring.ord_mul_of_isUnit_right hyu, Ring.ord_pow hnz,
    Ring.ord_of_irreducible hirr]
  simp
end EmultiplicityOrd
end GroundTheory.Heights₂.Heights
