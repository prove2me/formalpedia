-- Prove2me | solution 1 for PI.LocalEndW.algebraMap_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:07.373271+00:00
-- url     : https://prove2.me/submissions/f6db1526-48cb-4f29-a2c1-9f3dab45135f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IsUniformInducingOfVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_AlgebraMapMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Polynomial
namespace PI.LocalEndW
private theorem aeval_ringHom_apply_lemma {L M : Type*} [Field L] [Field M] [Algebra ℚ L] [Algebra ℚ M]
    (φ : L →+* M) (p : ℚ[X]) (x : L) : aeval (φ x) p = φ (aeval x p) := by
  rw [aeval_def, aeval_def, hom_eval₂, RingHom.ext_rat (φ.comp (algebraMap ℚ L)) (algebraMap ℚ M)]
end PI.LocalEndW
end

set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open PI PI.LocalEndW
namespace PI.LocalEndW
theorem _root_.solution {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (τ : v.adicCompletion F →+* v.adicCompletion F) (a : F) :
    algebraMap F (v.adicCompletion F) a ∈ Set.range τ := by
  set K := v.adicCompletion F
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let _ : Algebra ℚ K := DivisionRing.toRatAlgebra
  set p := minpoly ℚ a with hp
  have hp0 : p ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite ℚ a)
  set S : Set K := p.rootSet K
  have hmem : ∀ x : K, x ∈ S ↔ aeval x p = 0 := fun x => by
    rw [mem_rootSet]
    exact ⟨fun h => h.2, fun h => ⟨hp0, h⟩⟩
  have haS : algebraMap F K a ∈ S := by
    rw [hmem, aeval_ringHom_apply_lemma (algebraMap F K) p a, hp, minpoly.aeval, map_zero]
  have hmaps : Set.MapsTo τ S S := fun x hx => by
    rw [hmem] at hx ⊢
    rw [aeval_ringHom_apply_lemma τ p x, hx, map_zero]
  have : Finite S := (rootSet_finite p K).to_subtype
  let g : S → S := hmaps.restrict τ S S
  have hg : Function.Injective g := fun x y h => Subtype.ext (τ.injective (congrArg Subtype.val h))
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective hg ⟨algebraMap F K a, haS⟩
  exact ⟨r.1, congrArg Subtype.val hr⟩
end PI.LocalEndW
