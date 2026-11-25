-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_exists_maximal_of_fibre_9a1f67ed3c4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:02.973211+00:00
-- url     : https://prove2.me/submissions/78fc44c5-5624-4ca5-a6a3-1a609f9a490d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointThroughPrime

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
open IsDedekindDomain NumberField
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (v : HeightOneSpectrum (𝓞 F)) (P : Ideal R)
    (u : R) (hP : P.IsPrime) (hPv : P.comap (algebraMap (𝓞 F) R) = v.asIdeal) (hu : u ∉ P) :
    ∃ M : Ideal R, M.IsMaximal ∧ P ≤ M ∧ u ∉ M := by
  have hc : (P.comap (algebraMap (𝓞 F) R)).IsMaximal := hPv ▸ v.isMaximal
  let : Field (𝓞 F ⧸ P.comap (algebraMap (𝓞 F) R)) := Ideal.Quotient.field _
  have : Algebra.FiniteType (𝓞 F) (R ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (𝓞 F) P)
      (Ideal.Quotient.mkₐ_surjective (𝓞 F) P)
  have : Algebra.FiniteType (𝓞 F ⧸ P.comap (algebraMap (𝓞 F) R)) (R ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (𝓞 F) _ _
  have : IsJacobsonRing (R ⧸ P) :=
    isJacobsonRing_of_finiteType (A := 𝓞 F ⧸ P.comap (algebraMap (𝓞 F) R))
  have hbot : (⊥ : Ideal (R ⧸ P)).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.1 inferInstance ⊥ Ideal.isPrime_bot
  have hu' : Ideal.Quotient.mk P u ∉ (⊥ : Ideal (R ⧸ P)).jacobson := by
    rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact hu
  rw [Ideal.jacobson, Ideal.mem_sInf] at hu'
  push Not at hu'
  obtain ⟨J, ⟨-, hJ⟩, huJ⟩ := hu'
  refine ⟨J.comap (Ideal.Quotient.mk P),
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective, ?_, huJ⟩
  intro a ha
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  exact J.zero_mem
end GroundTheory.Heights₂.Heights.FourB
