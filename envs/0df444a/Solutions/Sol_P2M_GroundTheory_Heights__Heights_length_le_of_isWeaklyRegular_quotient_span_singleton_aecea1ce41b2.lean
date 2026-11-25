-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_length_le_of_isWeaklyRegular_quotient_span_singleton_aecea1ce41b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:03.540237+00:00
-- url     : https://prove2.me/submissions/79005bcf-99a0-4270-bc79-488cd3c3f640

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound

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
open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) [IsLocalRing (R ⧸ span {x})] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d + 1)
    (rs : List (R ⧸ span {x})) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal (R ⧸ span {x}))
    (hreg : IsWeaklyRegular (R ⧸ span {x}) rs) : rs.length ≤ d := by
  let lift : R ⧸ span {x} → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective
  have hrs' : (rs.map lift).map (algebraMap R (R ⧸ span {x})) = rs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id rs]
    exact List.map_congr_left fun b _ ↦ by simp [Ideal.Quotient.algebraMap_eq, hlift]
  have hloc : IsLocalHom (Ideal.Quotient.mk (span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (R ⧸ span {x})).comap (Ideal.Quotient.mk (span {x})) =
      maximalIdeal R := IsLocalRing.maximalIdeal_comap _
  have hmem : ∀ r ∈ x :: rs.map lift, r ∈ maximalIdeal R := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
      rw [← hcomap, Ideal.mem_comap, hlift]
      exact hrs b hb
  have e : (R ⧸ span {x}) ≃ₗ[R] QuotSMulTop x R :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
  have hreg' : IsWeaklyRegular R (x :: rs.map lift) := by
    rw [isWeaklyRegular_cons_iff]
    refine ⟨hxR, (e.isWeaklyRegular_congr _).mp ?_⟩
    rw [← isWeaklyRegular_map_algebraMap_iff (R ⧸ span {x}), hrs']
    exact hreg
  have := hd _ hmem hreg'
  simp only [List.length_cons, List.length_map] at this
  omega
end GroundTheory.Heights₂.Heights
