-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum.quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:50:29.3745+00:00
-- url     : https://prove2.me/submissions/863fa0dc-7eeb-4e86-b217-2a3eec345fcc

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalPrincipalFactorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalCokernelTraceSum
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_Ideal_Factors_quotientTrace_to_factorResidueTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorPrimaryTrace_primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_quotientMul_eq_add
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
private theorem directFactors_isCoprime_of_ne
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P Q : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (hPQ : P ≠ Q) :
    IsCoprime (P : Ideal (B k F)) (Q : Ideal (B k F)) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.IsMaximal.coprime_of_ne
    ((Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P))
    ((Ideal.Factors.isPrime p.asIdeal Q).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal Q))
  intro hideal
  apply hPQ
  exact Subtype.ext hideal
private theorem primaryTorsionTrace_product_directFactors_eq_sum
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth)
    (s : Finset
      ((factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)) :
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k)
          (B k F ⧸ (∏ P ∈ s, (P : Ideal (B k F))))
          (Ideal.Quotient.mk (∏ P ∈ s, (P : Ideal (B k F))) b)) depth =
      ∑ P ∈ s,
        Algebra.trace (R k ⧸ p.asIdeal)
          (B k F ⧸ (P : Ideal (B k F)))
          (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      apply primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
        p.asIdeal (1 : Ideal (B k F))
      exact Ideal.isCoprime_iff_sup_eq.mpr (by simp)
  | @insert P s hPs ih =>
      have hPprod : IsCoprime (P : Ideal (B k F))
          (∏ Q ∈ s, (Q : Ideal (B k F))) := by
        apply IsCoprime.prod_right
        intro Q hQs
        apply directFactors_isCoprime_of_ne k F p P Q
        intro hPQ
        apply hPs
        simpa only [hPQ] using hQs
      rw [Finset.prod_insert hPs, Finset.sum_insert hPs,
        primaryTorsionTrace_quotientMul_eq_add p.asIdeal
          (P : Ideal (B k F))
          (∏ Q ∈ s, (Q : Ideal (B k F))) hPprod b depth,
        DirectFactorPrimaryTrace.primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
          k F p P b depth hdepth,
        ih]
end QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum._p2m_local_instance_fa03a56197_45
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum._p2m_local_instance_fa03a56197_50
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (∏ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          (P : Ideal (B k F))) * J)
    (depth : ℕ) (hdepth : 0 < depth) :
    Ideal.Factors.quotientResidueEquiv p.asIdeal
        (primaryTorsionTrace p.asIdeal
          (principalCokernelMul (R := R k) t b) depth) =
      ∑ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  classical
  let M : Ideal (B k F) :=
    Ideal.map (algebraMap (R k) (B k F)) p.asIdeal
  let S := (factors M).toFinset
  let K : Ideal (B k F) := ∏ P : S, (P : Ideal (B k F))
  have hKJ : IsCoprime K J := by
    apply IsCoprime.prod_left
    intro P _
    have hM_le_P : M ≤ (P : Ideal (B k F)) := by
      exact Ideal.le_of_dvd
        (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup_right hM_le_P J
  have hJzero : primaryTorsionTrace p.asIdeal
      (Algebra.lmul (R k) (B k F ⧸ J) (Ideal.Quotient.mk J b)) depth = 0 :=
    primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
      p.asIdeal J hcop
        (Algebra.lmul (R k) (B k F ⧸ J) (Ideal.Quotient.mk J b)) depth
  have hKsum : primaryTorsionTrace p.asIdeal
      (Algebra.lmul (R k) (B k F ⧸ K) (Ideal.Quotient.mk K b)) depth =
        ∑ P : S,
          Algebra.trace (R k ⧸ p.asIdeal)
            (B k F ⧸ (P : Ideal (B k F)))
            (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
    simpa only [K] using
      primaryTorsionTrace_product_directFactors_eq_sum
        k F p b depth hdepth (Finset.univ : Finset S)
  have hprimary : primaryTorsionTrace p.asIdeal
      (principalCokernelMul (R := R k) t b) depth =
        ∑ P : S,
          Algebra.trace (R k ⧸ p.asIdeal)
            (B k F ⧸ (P : Ideal (B k F)))
            (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
    calc
      primaryTorsionTrace p.asIdeal
          (principalCokernelMul (R := R k) t b) depth =
        primaryTorsionTrace p.asIdeal
          (Algebra.lmul (R k) (B k F ⧸ (K * J))
            (Ideal.Quotient.mk (K * J) b)) depth :=
        primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq
          p.asIdeal t b (K * J) (by simpa only [M, S, K] using hspan) depth
      _ = primaryTorsionTrace p.asIdeal
            (Algebra.lmul (R k) (B k F ⧸ K) (Ideal.Quotient.mk K b)) depth +
          primaryTorsionTrace p.asIdeal
            (Algebra.lmul (R k) (B k F ⧸ J) (Ideal.Quotient.mk J b)) depth :=
        primaryTorsionTrace_quotientMul_eq_add
          p.asIdeal K J hKJ b depth
      _ = _ := by rw [hJzero, add_zero, hKsum]
  rw [hprimary, map_sum]
  apply Finset.sum_congr rfl
  intro P _
  exact Ideal.Factors.quotientTrace_to_factorResidueTrace p.asIdeal P b
end QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
