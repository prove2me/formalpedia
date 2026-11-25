-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_trdeg_add_card_le_8e491c0ffaac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:46.424115+00:00
-- url     : https://prove2.me/submissions/9b339822-8565-4615-9ec5-e11a40582b5e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreIncompTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraicIndependent_forgotten_dc1a9fb6b9cc

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
variable {S : Type} [CommRing S]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
theorem _root_.solution [Nontrivial S] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (V' : Ideal (MRingOver S ι')) [V'.IsPrime] (hV' : IsMultiHomogIdeal V') (hrel : IsRelevant V')
    (hinj : Function.Injective (algebraMap S
      (MRingOver S ι ⧸ V'.comap (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom))) :
    Algebra.trdeg S (MRingOver S ι ⧸ V'.comap (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom) +
        Fintype.card (FibreBlock κ) ≤ Algebra.trdeg S (MRingOver S ι' ⧸ V') := by
  classical
  set φ := (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom with hφ
  set j := Ideal.quotientMap V' φ le_rfl with hj
  let _ := j.toAlgebra
  choose i hi using fun k : FibreBlock κ => hrel k.1
  have hind := algebraicIndependent_forgotten hv V' hV' i hi
  have : IsScalarTower S (MRingOver S ι ⧸ V'.comap φ) (MRingOver S ι' ⧸ V') := by
    refine IsScalarTower.of_algebraMap_eq (R := S) (S := MRingOver S ι ⧸ V'.comap φ)
      (A := MRingOver S ι' ⧸ V') fun r => ?_
    rw [RingHom.algebraMap_toAlgebra, hj, ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap,
      Ideal.quotientMap_mk]
    congr 1
    exact (AlgHom.commutes (rename v : MRingOver S ι →ₐ[S] MRingOver S ι') r).symm
  have : FaithfulSMul S (MRingOver S ι ⧸ V'.comap φ) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : FaithfulSMul (MRingOver S ι ⧸ V'.comap φ) (MRingOver S ι' ⧸ V') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective
  rw [← trdeg_add_eq S (MRingOver S ι ⧸ V'.comap φ) (A := MRingOver S ι' ⧸ V')]
  gcongr
  rw [← Cardinal.mk_fintype]
  exact hind.cardinalMk_le_trdeg
end GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
