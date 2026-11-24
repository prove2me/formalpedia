-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_finite_maximal_of_ne_zero_b905aca18701
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:45.462806+00:00
-- url     : https://prove2.me/submissions/8851b711-67ad-4669-9f9b-1b3ea14db36b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime

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
open GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
theorem _root_.solution [CharZero L] (B : Subring L) [Module.Finite ℤ B] {s : B} (hs : s ≠ 0) :
    Set.Finite {m : Ideal B | m.IsMaximal ∧ s ∈ m} := by
  have : Module.Free ℤ B := Module.free_of_finite_type_torsion_free'
  have hI : Ideal.span {s} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hs
  have : Finite (B ⧸ Ideal.span {s}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  refine Set.Finite.of_finite_image (f := fun m : Ideal B => Ideal.Quotient.mk (Ideal.span {s}) '' (m : Set B))
    (Set.toFinite _) ?_
  have key : ∀ m m' : Ideal B, s ∈ m' →
      Ideal.Quotient.mk (Ideal.span {s}) '' (m : Set B) = Ideal.Quotient.mk (Ideal.span {s}) '' (m' : Set B) →
      m ≤ m' := by
    intro m m' hs' h x hx
    obtain ⟨y, hy, hxy⟩ : Ideal.Quotient.mk (Ideal.span {s}) x ∈
        Ideal.Quotient.mk (Ideal.span {s}) '' (m' : Set B) := h ▸ ⟨x, hx, rfl⟩
    have hd : x - y ∈ Ideal.span {s} := Ideal.Quotient.eq.mp hxy.symm
    have hle : Ideal.span {s} ≤ m' := (Ideal.span_singleton_le_iff_mem _).mpr hs'
    have := m'.add_mem (hle hd) hy
    simpa using this
  intro m hm m' hm' h
  exact le_antisymm (key m m' hm'.2 h) (key m' m hm.2 h.symm)
end GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
