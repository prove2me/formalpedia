-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer.exists_directSemilocalUniformizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:45:41.17593+00:00
-- url     : https://prove2.me/submissions/51f35b81-40a4-4786-82cb-647b0b151edc

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalUniformizer_directFactorPlace_order_semilocalMultiplier_eq_zero_of_ne
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalLogarithmicResidue_directFactorPlace_order_semilocalMultiplier_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalMultiplier_exists_directFactorSemilocalMultiplier
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
open DirectIntegralDifferentialResidue
open DirectFactorSemilocalLogarithmicResidue
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer._p2m_local_instance_46770e045f_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer._p2m_local_instance_46770e045f_42
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    ∃ t : B k F, t ≠ 0 ∧
      ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        GlobalPlace.order
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (algebraMap (B k F) F t) = 1 := by
  classical
  let S := (factors
    (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset
  choose t ht J hspan hcop using fun P : S =>
    DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
      k F p P
  let T : B k F := ∏ P : S, t P
  have hT_ne : T ≠ 0 := by
    dsimp only [T]
    exact Finset.prod_ne_zero_iff.mpr fun P _ => ht P
  refine ⟨T, hT_ne, ?_⟩
  intro Q
  let Qplace : GlobalPlace k F :=
    AffinePlace.globalPlace k F (directFactorPlace k F p Q)
  have htF_ne (P : S) : algebraMap (B k F) F (t P) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (B k F) F)).mpr (ht P)
  have hcomponent (P : S) :
      Qplace.order (algebraMap (B k F) F (t P)) = if P = Q then 1 else 0 := by
    by_cases hPQ : P = Q
    · subst P
      rw [if_pos rfl]
      exact directFactorPlace_order_semilocalMultiplier_eq_one
        k F p Q (J Q) (hcop Q) (t Q) (ht Q) (hspan Q)
    · rw [if_neg hPQ]
      exact directFactorPlace_order_semilocalMultiplier_eq_zero_of_ne
        k F p P Q (Ne.symm hPQ) (J P) (hcop P) (t P) (ht P) (hspan P)
  have horderProd (s : Finset S) :
      Qplace.order (∏ P ∈ s, algebraMap (B k F) F (t P)) =
        ∑ P ∈ s, Qplace.order (algebraMap (B k F) F (t P)) := by
    induction s using Finset.induction_on with
    | empty =>
        simp [GlobalPlace.order]
    | @insert P s hPs ih =>
        have hs_ne : (∏ Q ∈ s, algebraMap (B k F) F (t Q)) ≠ 0 := by
          exact Finset.prod_ne_zero_iff.mpr fun Q _ => htF_ne Q
        rw [Finset.prod_insert hPs, Finset.sum_insert hPs,
          Qplace.order_mul (htF_ne P) hs_ne, ih]
  change Qplace.order (algebraMap (B k F) F T) = 1
  rw [show algebraMap (B k F) F T =
      ∏ P : S, algebraMap (B k F) F (t P) by
        simp only [T, map_prod]]
  rw [horderProd]
  calc
    (∑ P : S, Qplace.order (algebraMap (B k F) F (t P))) =
        ∑ P : S, if P = Q then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro P _
      exact hcomponent P
    _ = 1 := by simp
end QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
