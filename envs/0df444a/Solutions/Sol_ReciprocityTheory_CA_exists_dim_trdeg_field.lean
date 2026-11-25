-- Prove2me | solution 1 for ReciprocityTheory.CA.exists_dim_trdeg_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:58.102166+00:00
-- url     : https://prove2.me/submissions/2c8667b0-ac82-4d28-b363-16c4a8ab7fc9

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_isIntegral_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
universe u
namespace ReciprocityTheory.CA
theorem _root_.solution {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, ringKrullDim A = s ∧ Algebra.trdeg K A = s := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) K) A := hfin
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) A :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin s) K) A) := hinj
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj'
  haveI : FaithfulSMul K (MvPolynomial (Fin s) K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective _ _)
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral_of_injective hinj']
    have h6 := height_add_ringKrullDim_quotient_mvPolynomial_field K s (⊥ : Ideal (MvPolynomial (Fin s) K))
    rw [Ideal.height_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at h6
    simpa using h6
  · have h := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A)
    rw [trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := A), add_zero, MvPolynomial.trdeg_of_isDomain] at h
    rw [← h]
    simp
end ReciprocityTheory.CA
