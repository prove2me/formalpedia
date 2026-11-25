-- Prove2me | solution 1 for ReciprocityTheory.CA.mk_mem_maximalIdeal_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:44.007914+00:00
-- url     : https://prove2.me/submissions/6f096f2e-f068-432d-aab3-527ae847b898

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
theorem _root_.solution (I : Ideal R) [IsLocalRing (R ⧸ I)] {r : R}
    (hr : r ∈ maximalIdeal R) : Ideal.Quotient.mk I r ∈ maximalIdeal (R ⧸ I) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective v
  have h1 : r * s - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
  have h2 : r * s - 1 ∉ maximalIdeal R := by
    intro h
    have h' : r * s - (r * s - 1) ∈ maximalIdeal R :=
      (maximalIdeal R).sub_mem ((maximalIdeal R).mul_mem_right s hr) h
    rw [sub_sub_cancel] at h'
    exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top inferInstance) h'
  have h3 : IsUnit (r * s - 1) := by
    by_contra h
    exact h2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have h4 : IsUnit (Ideal.Quotient.mk I (r * s - 1)) := h3.map _
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr h1] at h4
  exact not_isUnit_zero h4
end ReciprocityTheory.CA
