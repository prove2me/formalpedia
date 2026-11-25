-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_finiteDimensional_of_isFractionRing_922184a718b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:08:32.464686+00:00
-- url     : https://prove2.me/submissions/9433508e-d728-4220-8fb8-7833dc465248

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointOfAlgebraicDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
variable {F : Type*} [Field F] [NumberField F] {S : Type*} [CommRing S]
  [Algebra (𝓞 F) S] {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K] [Algebra F K]
namespace GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
theorem _root_.solution [Algebra.FiniteType (𝓞 F) S]
    [Algebra.IsAlgebraic (𝓞 F) S]
    (hc : ∀ r : 𝓞 F, algebraMap F K (algebraMap (𝓞 F) F r) = algebraMap S K (algebraMap (𝓞 F) S r)) :
    FiniteDimensional F K := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := 𝓞 F) (A := S)
  let f : S →ₐ[𝓞 F] K :=
    { algebraMap S K with
      commutes' := fun r ↦ by
        rw [IsScalarTower.algebraMap_apply (𝓞 F) F K]
        exact (hc r).symm }
  set t : Set K := f '' (s : Set S)
  have hinj : Function.Injective (algebraMap (𝓞 F) F) := IsFractionRing.injective _ _
  have hint : ∀ x ∈ t, IsIntegral F x := by
    rintro _ ⟨x, -, rfl⟩
    exact (((Algebra.IsAlgebraic.isAlgebraic (R := 𝓞 F) x).algHom f).extendScalars hinj).isIntegral
  have : Finite t := (s.finite_toSet.image _).to_subtype
  have hfin := IntermediateField.finiteDimensional_adjoin hint
  set E := IntermediateField.adjoin F t
  have hS : ∀ x : S, algebraMap S K x ∈ E := by
    have hle : (⊤ : Subalgebra (𝓞 F) S) ≤ (E.toSubalgebra.restrictScalars (𝓞 F)).comap f := by
      rw [← hs]
      exact Algebra.adjoin_le fun x hx ↦ IntermediateField.subset_adjoin F t ⟨x, hx, rfl⟩
    exact fun x ↦ hle Algebra.mem_top
  have hE : E = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) z
    exact E.div_mem (hS a) (hS b)
  rw [hE] at hfin
  exact (IntermediateField.topEquiv (F := F) (E := K)).toLinearEquiv.finiteDimensional
end GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
