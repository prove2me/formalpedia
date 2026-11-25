-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primitive_with_resultant_denominator_cfd22a00b3ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:11.060559+00:00
-- url     : https://prove2.me/submissions/cb81ef2b-9624-44f7-a85b-5241d4fc58a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPrimitiveForm

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
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericPrimitive.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscrAdjoin.Statement)
    {R S : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) [Algebra.IsIntegral R S] (c : ℂ →+* R)
    {n : ℕ} (z : Fin n → S) :
    ∃ (cc : Fin n → ℂ) (p : R[X]), p.Monic ∧ 0 < p.natDegree ∧
      aeval (∑ j, algebraMap R S (c (cc j)) * z j) p = 0 ∧
      p.resultant (derivative p) p.natDegree (p.natDegree - 1) ≠ 0 ∧
      ∀ i, ∃ f : R[X], f.natDegree < p.natDegree ∧
        aeval (∑ j, algebraMap R S (c (cc j)) * z j) f =
          algebraMap R S (p.resultant (derivative p) p.natDegree (p.natDegree - 1)) * z i := by
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hinj
  let _ : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R (FractionRing S)
  let ι : S →ₐ[R] FractionRing S := IsScalarTower.toAlgHom R S (FractionRing S)
  have hι : Function.Injective ι := IsFractionRing.injective S (FractionRing S)
  have hint : ∀ s : S, IsIntegral R (ι s) := fun s => (Algebra.IsIntegral.isIntegral s).map ι
  let zb : Fin n → FractionRing S := fun j => ι (z j)
  let L' := IntermediateField.adjoin (FractionRing R) (Set.range zb)
  have : FiniteDimensional (FractionRing R) L' := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨j, rfl⟩
    exact (hint (z j)).tower_top)
  let _ : Algebra ℂ (FractionRing R) := ((algebraMap R (FractionRing R)).comp c).toAlgebra
  let _ : Algebra ℂ L' := ((algebraMap (FractionRing R) L').comp (algebraMap ℂ (FractionRing R))).toAlgebra
  have : IsScalarTower ℂ (FractionRing R) L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing R)).injective
  have : Algebra.IsSeparable (FractionRing R) L' := inferInstance
  let V : L' →ₐ[R] FractionRing S := (IntermediateField.val L').restrictScalars R
  have hV : Function.Injective V := Subtype.val_injective
  let x : Fin n → L' := fun j => ⟨zb j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩
  have hVx : ∀ j, V (x j) = ι (z j) := fun j => rfl
  have hx : IntermediateField.adjoin (FractionRing R) (Set.range x) = ⊤ := by
    apply IntermediateField.map_injective L'.val
    rw [IntermediateField.adjoin_map, ← Set.range_comp, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    rfl
  obtain ⟨Dp, hDp0, hDp⟩ := hG ℂ (FractionRing R) L' n x hx
  obtain ⟨cc, hcc⟩ : ∃ cc : Fin n → ℂ, MvPolynomial.eval cc Dp ≠ 0 := by
    by_contra! h
    exact hDp0 (MvPolynomial.funext fun v => by simpa using h v)
  have hprim := hDp cc hcc
  set ℓs : S := ∑ j, algebraMap R S (c (cc j)) * z j with hℓs
  set ℓ' : L' := ∑ j, cc j • x j with hℓ'
  have hVℓ : V ℓ' = ι ℓs := by
    simp only [hℓ', hℓs, map_sum, map_mul, Algebra.smul_def, hVx]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S)]
    rfl
  have hintL : ∀ w : L', IsIntegral R (V w) → IsIntegral R w := fun w h =>
    (isIntegral_algHom_iff V hV).1 h
  have hℓint : IsIntegral R ℓ' := hintL _ (by rw [hVℓ]; exact hint _)
  obtain ⟨-, hdisc, hmem⟩ := hD R (FractionRing R) L' ℓ' hℓint hprim
  set p := minpoly R ℓ' with hp
  have hpm : p.Monic := minpoly.monic hℓint
  have hpos : 0 < p.natDegree := minpoly.natDegree_pos hℓint
  have htransfer : ∀ (f : R[X]) (s : S) (w : L'), V w = ι s → ι (aeval s f) = V (aeval w f) :=
    fun f s w h => by rw [← aeval_algHom_apply, ← aeval_algHom_apply, h]
  have hres : p.resultant (derivative p) p.natDegree (p.natDegree - 1) =
      (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) * p.discr := by
    rw [resultant_deriv (natDegree_pos_iff_degree_pos.1 hpos), hpm.leadingCoeff, mul_one]
  refine ⟨cc, p, hpm, hpos, ?_, ?_, fun i => ?_⟩
  · apply hι
    rw [htransfer p ℓs ℓ' hVℓ, minpoly.aeval, map_zero, map_zero]
  · rw [hres]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hdisc
  · have hxi : IsIntegral R (x i) := hintL _ (by rw [hVx]; exact hint _)
    have hm : p.resultant (derivative p) p.natDegree (p.natDegree - 1) • x i ∈ Algebra.adjoin R {ℓ'} := by
      rw [hres, mul_smul]
      exact Subalgebra.smul_mem _ (hmem _ hxi) _
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨f, hf⟩ := hm
    refine ⟨f %ₘ p, natDegree_modByMonic_lt f hpm (minpoly.ne_one R ℓ'), ?_⟩
    apply hι
    rw [htransfer _ ℓs ℓ' hVℓ, aeval_modByMonic_eq_self_of_root (minpoly.aeval R ℓ')]
    have hf' : aeval ℓ' f = _ := hf
    rw [hf', map_smul, hVx, ← map_smul, Algebra.smul_def]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
