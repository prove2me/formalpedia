-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:23:07.38682+00:00
-- url     : https://prove2.me/submissions/3bcc5886-6de9-4d94-8ae2-ee53d3bfbbe8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FiniteOfFiniteOverNormal
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NonemptyNormalModelOfPresentation
import Theorems.Thm_UpperTheory_integralClosure_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_extension {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (R S : Type) [CommRing R] [Nontrivial R] [Algebra ℂ R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R) (hπ : Function.Surjective π) (hJ : RingHom.ker π = J)
    (hinj : Function.Injective (algebraMap R S))
    (hfrac : ∀ s : S, ∃ a b : R, b ≠ 0 ∧ algebraMap R S b * s = algebraMap R S a) :
    Nonempty (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  let φ : MvPolynomial (Fin n ⊕ Fin m) ℂ →+* S :=
    eval₂Hom ((algebraMap R S).comp (algebraMap ℂ R))
      (Sum.elim (fun i => algebraMap R S (π (X i))) s)
  have hcomp : φ.comp (rename Sum.inl :
      MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      = (algebraMap R S).comp π.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h : π (C r) = algebraMap ℂ R r := π.commutes r
      simp [φ, h]
    · intro i
      simp [φ]
  have hren : ∀ q, φ (rename Sum.inl q) = algebraMap R S (π q) := fun q =>
    RingHom.congr_fun hcomp q
  have hY : ∀ i, φ (X (Sum.inr i)) = s i := fun i => by simp [φ]
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hy
    choose p hp using fun i => hπ (c i)
    refine ⟨∑ i, rename Sum.inl (p i) * X (Sum.inr i), ?_⟩
    simp only [map_sum, map_mul, hren, hY, hp, Algebra.smul_def]
  refine ⟨⟨m, RingHom.ker φ, RingHom.ker_isPrime _,
    IsIntegrallyClosed.of_equiv (RingHom.quotientKerEquivOfSurjective hsurj).symm, ?_, ?_, ?_⟩⟩
  · ext q
    rw [Ideal.mem_comap, RingHom.mem_ker, hren, ← hJ, RingHom.mem_ker,
      map_eq_zero_iff _ hinj]
  · intro i
    obtain ⟨Q, hQ, hQ0⟩ : IsIntegral R (s i) := Algebra.IsIntegral.isIntegral _
    obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (f := π.toRingHom) (Polynomial.mem_lifts_of_surjective hπ Q) hQ
    refine ⟨P, hPm, ?_⟩
    rw [RingHom.mem_ker, Polynomial.hom_eval₂, hcomp, hY, ← Polynomial.eval₂_map, hP, hQ0]
  · intro i
    obtain ⟨a, b, hb, hab⟩ := hfrac (s i)
    obtain ⟨a, rfl⟩ := hπ a
    obtain ⟨b, rfl⟩ := hπ b
    refine ⟨a, b, ?_, ?_⟩
    · rw [← hJ, RingHom.mem_ker]
      exact hb
    · rw [RingHom.mem_ker, map_sub, map_mul, hren, hren, hY, hab, sub_self]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Gc5
theorem _root_.solution :
    ∀ {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type) [inst : CommRing R] [IsDomain R] [inst_2 : Algebra ℂ R]
    (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R),
    Function.Surjective (⇑π : MvPolynomial (Fin n) ℂ → R) →
      RingHom.ker π = J →
        Nonempty
          (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalModel
            J) := by
  intro n J R _ _ _ π hπ hJ
  haveI : Algebra.FiniteType ℂ R := Algebra.FiniteType.of_surjective π hπ
  haveI : Module.Finite R (integralClosure R (FractionRing R)) := UpperTheory.integralClosure_finite ℂ R (FractionRing R)
  haveI : IsIntegrallyClosed (integralClosure R (FractionRing R)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  refine UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_extension J R
    (integralClosure R (FractionRing R)) π hπ hJ ?_ ?_
  · intro x y hxy
    exact IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hxy)
  · intro s
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) (s : FractionRing R)
    refine ⟨a, b, nonZeroDivisors.coe_ne_zero b, Subtype.ext ?_⟩
    rw [mul_comm] at hab
    exact hab
end UpperTheory.Reformulated.B.Gc5
