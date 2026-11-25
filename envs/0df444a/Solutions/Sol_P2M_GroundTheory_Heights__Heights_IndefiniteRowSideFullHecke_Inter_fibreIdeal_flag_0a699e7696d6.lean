-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_flag_0a699e7696d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:02.626729+00:00
-- url     : https://prove2.me/submissions/5bcee58d-638c-4842-accf-a7023b444af4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMinor_mul_6314ae5d4dfc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) [hP : P.IsPrime] (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    fibreIdeal Sum.inl (flagGenFibre P hP B) =
      (flagIdealOver (FnField P) n).comap
        (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B)).toRingHom := by
  show RingHom.ker (aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)),
      fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl k =>
        algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P)))
          (flagMap P B (X ⟨q.1.1, q.2⟩))) :
      MRingOver (FnField P) (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl) →ₐ[FnField P]
        FractionRing (MvPolynomial (Fin n × Fin n) (FnField P))) = _
  have key : ∀ f, aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)),
      fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl k =>
        algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P)))
          (flagMap P B (X ⟨q.1.1, q.2⟩))) f =
      algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P)))
        (aeval (fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat (FnField P) n) q.1 q.2)
          (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B) f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [aeval_C, show (C a : MRingOver (FnField P) (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl)) =
        algebraMap (FnField P) _ a from rfl, AlgHom.commutes, AlgHom.commutes]
      exact IsScalarTower.algebraMap_apply _ _ _ a
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add, map_add]
    | mul_X p q hp =>
      rw [map_mul, hp, map_mul, map_mul, map_mul]
      congr 1
      rw [aeval_X, blockLinSubst, aeval_X]
      obtain ⟨⟨k, hk⟩, S⟩ := q
      match k, hk, S with
      | .inl k, h, _ => exact (h ⟨k, rfl⟩).elim
      | .inr j, h, S =>
        congr 1
        rw [flagMap, eval₂Hom_X']
        refine (flagMinor_mul (genMat (FnField P) n) (B.map C) j S).trans ?_
        simp only [map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]
        refine Finset.sum_congr rfl fun S' _ => ?_
        exact (mul_comm _ _).trans
          (congrArg (· * flagMinor (genMat (FnField P) n) j S') (RingHom.map_det C _).symm)
  ext f
  simp only [flagIdealOver, RingHom.mem_ker, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [key, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
