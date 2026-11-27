-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FormalFibresRegularPolynomial_proof_9ca6962740fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:56:47.567949+00:00
-- url     : https://prove2.me/submissions/f9211f52-e9e7-4f2e-9542-f586cd3c17ad

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegularPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianPrimeDerivations
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationAdicCompletion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAdicCompletionRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationCotangentIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularQuotientIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormalFibresRegularPolynomial
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_localization_atPrime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FormalFibresRegularPolynomial
theorem _root_.solution (hJ : JacobianPrimeDerivations.Statement)
    (hE : DerivationAdicCompletion.Statement) (hC : AdicCompletionRegular.Statement)
    (hI : DerivationCotangentIndependent.Statement) (hQ : RegularQuotientIndependent.Statement) :
    FormalFibresRegularPolynomial.Statement := by
  intro k _ n M hM P _
  let B := MvPolynomial (Fin n) k
  let Bh := AdicCompletion M B
  let L := Localization.AtPrime P
  obtain ⟨h, f, D, s, hfp, hs, hsp, hdet⟩ := hJ k n (P.comap (algebraMap B Bh)) (Ideal.comap_isPrime _ _)
  choose D' hD' using fun j => hE B M (D j)
  have : IsRegularLocalRing Bh := hC B inferInstance M inferInstance
  have : IsRegularLocalRing L := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime P
  have hdet' : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))).det ∉ P := by
    have hm : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))) =
        (algebraMap B Bh).mapMatrix (Matrix.of fun i j => D j (f i)) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact hD' j (f i)
    rw [hm, ← RingHom.map_det]
    exact hdet
  have hmem : ∀ i, algebraMap Bh L (algebraMap B Bh (f i)) ∈ maximalIdeal L := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mpr (hfp i)
  have hreg := hQ L h _ hmem (hI Bh P h D' (fun i => algebraMap B Bh (f i)) hfp hdet')
  have heq : Ideal.span (Set.range fun i => algebraMap Bh L (algebraMap B Bh (f i))) =
      Ideal.map (algebraMap Bh L) (Ideal.map (algebraMap B Bh) (P.comap (algebraMap B Bh))) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hfp i))
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      have hu : IsUnit (algebraMap Bh L (algebraMap B Bh s)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff L P _).mpr hs
      have hsx := Ideal.mem_map_of_mem ((algebraMap Bh L).comp (algebraMap B Bh)) (hsp x hx)
      rw [Ideal.map_span, ← Set.range_comp, map_mul] at hsx
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hsx
  exact IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq heq)
end FormalFibresRegularPolynomial
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
