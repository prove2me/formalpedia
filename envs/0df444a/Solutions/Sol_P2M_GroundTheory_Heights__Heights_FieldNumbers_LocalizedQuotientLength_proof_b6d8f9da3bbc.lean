-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_LocalizedQuotientLength_proof_b6d8f9da3bbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:55:30.707711+00:00
-- url     : https://prove2.me/submissions/861c70f7-2b2f-4400-b3c3-19509f362467

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalizedQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PLocalizedQuotientLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
universe u v
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace LocalizedQuotientLength
theorem _root_.solution : LocalizedQuotientLength.Statement.{u, v} := by
  intro S _ P W _ x R _ _ hR
  let f : S →+* R := (algebraMap (S ⧸ P) R).comp (Ideal.Quotient.mk P)
  have hu : ∀ t : W.primeCompl, IsUnit (f t) := fun t => IsLocalization.map_units R
    (⟨Ideal.Quotient.mk P t, Submonoid.mem_map_of_mem _ t.2⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  let g : Localization.AtPrime W →+* R := IsLocalization.lift (M := W.primeCompl) hu
  have hg : ∀ s, g (algebraMap S (Localization.AtPrime W) s) = f s := IsLocalization.lift_eq hu
  have gsurj : Function.Surjective g := by
    intro r
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (W.primeCompl.map (Ideal.Quotient.mk P)) r
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨t, ht, hmt⟩ := Submonoid.mem_map.mp m.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime W) s ⟨t, ht⟩, ?_⟩
    rw [IsLocalization.lift_mk'_spec, mul_comm]
    show algebraMap (S ⧸ P) R (Ideal.Quotient.mk P s) = _ * algebraMap (S ⧸ P) R (Ideal.Quotient.mk P t)
    rw [hmt, IsLocalization.mk'_spec]
  let _ : Algebra (Localization.AtPrime W) R := g.toAlgebra
  let _ : Algebra S R := f.toAlgebra
  have _ : IsScalarTower S (Localization.AtPrime W) R := IsScalarTower.of_algebraMap_eq fun s => (hg s).symm
  set J := Ideal.span {algebraMap (S ⧸ P) R (Ideal.Quotient.mk P x)}
  rw [← Module.length_eq_of_surjective (S := Localization.AtPrime W) (R := R) (M := R ⧸ J) gsurj]
  have hI : P ⊔ Ideal.span {x} ≤ LinearMap.ker (Algebra.linearMap S (R ⧸ J)) := by
    refine sup_le (fun p hp => ?_) (Ideal.span_le.2 ?_)
    · show Ideal.Quotient.mk J (algebraMap (S ⧸ P) R (Ideal.Quotient.mk P p)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero, map_zero]
    · rintro _ rfl
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  let φ : (S ⧸ (P ⊔ Ideal.span {x})) →ₗ[S] R ⧸ J := (P ⊔ Ideal.span {x}).liftQ _ hI
  have _ : IsLocalizedModule W.primeCompl φ := by
    constructor
    · intro t
      obtain ⟨u, hu'⟩ := hu t
      rw [Module.End.isUnit_iff]
      have key : ∀ q : R ⧸ J, algebraMap S (Module.End S (R ⧸ J)) t q = (u : R) • q := fun q => by
        rw [Module.algebraMap_end_apply, hu', ← algebraMap_smul R (t : S) q]; rfl
      refine ⟨fun a b hab => ?_, fun q => ⟨(↑u⁻¹ : R) • q, ?_⟩⟩
      · rw [key, key] at hab
        simpa [smul_smul] using congrArg ((↑u⁻¹ : R) • ·) hab
      · rw [key, smul_smul, Units.mul_inv, one_smul]
    · intro q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨z, rfl⟩ := gsurj r
      obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
      refine ⟨⟨Ideal.Quotient.mk _ s, t⟩, ?_⟩
      show Ideal.Quotient.mk J (f t * g (IsLocalization.mk' _ s t)) = Ideal.Quotient.mk J (f s)
      rw [← hg, ← hg, ← map_mul, IsLocalization.mk'_spec']
    · intro a1 a2 h
      obtain ⟨a1, rfl⟩ := Ideal.Quotient.mk_surjective a1
      obtain ⟨a2, rfl⟩ := Ideal.Quotient.mk_surjective a2
      change Ideal.Quotient.mk J (f a1) = Ideal.Quotient.mk J (f a2) at h
      rw [Ideal.Quotient.eq, ← map_sub, Ideal.mem_span_singleton'] at h
      obtain ⟨r, hr⟩ := h
      obtain ⟨z, rfl⟩ := gsurj r
      obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
      have e : f t * g (IsLocalization.mk' _ b t) = f b := by
        rw [← hg, ← hg, ← map_mul, IsLocalization.mk'_spec']
      have h2 : f (t * (a1 - a2) - b * x) = 0 := by
        rw [map_sub, map_mul, map_mul, ← hr, ← mul_assoc, e]
        exact sub_self _
      obtain ⟨⟨m, hm⟩, hm0⟩ := (IsLocalization.map_eq_zero_iff
        (W.primeCompl.map (Ideal.Quotient.mk P)) R (Ideal.Quotient.mk P _)).1 h2
      obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hm
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm0
      refine ⟨⟨u, hu⟩ * t, ?_⟩
      show Ideal.Quotient.mk _ ((u * t) * a1) = Ideal.Quotient.mk _ ((u * t) * a2)
      rw [Ideal.Quotient.eq, show u * t * a1 - u * t * a2 = u * (t * (a1 - a2) - b * x) + u * b * x by ring]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hm0)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)))
  exact ((IsLocalizedModule.iso W.primeCompl φ).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq
end LocalizedQuotientLength
end GroundTheory.Heights₂.Heights.FieldNumbers
