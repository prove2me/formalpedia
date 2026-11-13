-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.K_eq_V_index_pq
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:33:09.669446+00:00
-- url     : https://prove2.me/submissions/dde133f1-e623-43be-af40-a9822e41ec14

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean
--   OddOrder/Peterfalvi/S11_CaseAOddPartBound.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
--   OddOrder/Peterfalvi/S15_ComplementStructure.lean
--   OddOrder/Peterfalvi/S11_GaloisFieldModel.lean
--   OddOrder/Peterfalvi/S15_SSideGaloisFieldModel.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S16_PairingBessel.lean
--   OddOrder/Peterfalvi/S16_G0Coprime.lean
--   OddOrder/Peterfalvi/S15_CaseBReducibleCoherence.lean
--   OddOrder/Peterfalvi/S15_CaseACoherence.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayerCore.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayer.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Theorems.Thm_OddOrder_RepresentationTheory_ConjugationFieldModel_exists_normOne_galoisField_conjugation_repr
import Theorems.Thm_OddOrder_RepresentationTheory_SemilinearFieldModel_fieldModelEmbedding
import Theorems.Thm_OddOrder_RepresentationTheory_SemilinearFieldModel_hcompatLift_of_equivariant
import Theorems.Thm_OddOrder_Isaacs_Ch06_IsFrobeniusGroup_conjComplement
import Theorems.Thm_OddOrder_Peterfalvi_S11_caseB_exists_galoisField_repr
import Theorems.Thm_OddOrder_Peterfalvi_S11_caseA_blockScalarFacts
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_S
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_false_of_parameters_and_typeIOverNormalizerData
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_analytic_inequality_of_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_sSet_irr
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_forces_T_caseB_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseB_member
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseA
import Theorems.Thm_OddOrder_Peterfalvi_S15_card_LF_coprime_pq
import Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_V_card_Q_of_disjoint
import Theorems.Thm_OddOrder_Peterfalvi_S15_Q_elementaryAbelian_T
import Theorems.Thm_OddOrder_Peterfalvi_S15_exists_conj_typeP_V_of_coprime
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseB_order_u_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S15_numeric_bounds_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_c_eq_one_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_numeric_parameters
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_nuGridSupply_swap
import Theorems.Thm_OddOrder_Peterfalvi_S16_orderOf_coprime_p_of_not_mem_conj
import Theorems.Thm_OddOrder_Peterfalvi_S16_orderOf_coprime_q_of_not_mem_conj
import Theorems.Thm_OddOrder_Peterfalvi_S16_TFieldModelData_derived_inf_centralizer_le_Q
import Theorems.Thm_OddOrder_Peterfalvi_S16_cyclotomic_ratio_gt_of_q_lt_p
import Theorems.Thm_OddOrder_Peterfalvi_S16_exists_LHypothesis
import Theorems.Thm_OddOrder_Peterfalvi_S16_frobenius_PU_of_field_repr
import Theorems.Thm_OddOrder_Peterfalvi_S16_MHypothesis_line83_le_displayed_upper
import Theorems.Thm_OddOrder_Peterfalvi_S16_norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
import Theorems.Thm_OddOrder_Peterfalvi_S16_main_size_bounds_structural
import Theorems.Thm_OddOrder_Peterfalvi_S16_betaM_expansion
import Theorems.Thm_OddOrder_Peterfalvi_S16_one_le_norm_eta_grid_signed_sum
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_side_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_ratio_le

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The Dade image defining `β` is supported on the corresponding Dade support. -/
theorem beta_support_subset_dadeSupport (H78 : Hypothesis78 G A L) :
    H78.beta.support ⊆ H78.hyp76.hyp71.hyp.dadeSupport := by
  intro g hg
  by_contra hnot
  exact hg (by
    rw [H78.beta_def]
    exact H78.hyp76.hyp71.isDadeMap.map_eq_zero_of_not_mem_dadeSupport
      H78.indMinusZetaSupp g hnot)

/-- Variant of `sourceDiffNormEvaluation_of_inner_values` using irreducibility of
the chosen `ζ` instead of a raw self-inner-product evaluation. -/
theorem sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.SourceDiffNormEvaluation :=
  H78.sourceDiffNormEvaluation_of_inner_values
    hind_norm hzeta_ind hind_zeta
    (H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr)

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- If `Γ` has Peterfalvi's residual norm formula, its upper bound follows. -/
theorem gammaNormSq_le_of_normQuadraticCorrection_eq
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hgamma : H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD) :
    H78.smallIndex → H78.gammaNormSq hBD ≤ (H78.complementIndex : ℝ) - 1 := by
  intro hsmall
  rw [hgamma]
  have hh_nonneg : 0 ≤ (H78.kernelOrder : ℝ) := by positivity
  have hquad := H78.normQuadraticCorrection_nonneg_of_smallIndex hBD hsmall
  have hprod : 0 ≤ (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD :=
    mul_nonneg hh_nonneg hquad
  linarith

/-- Exact quadratic norm formulas are enough to package Peterfalvi (7.8.b)'s
`NormEstimates`.  This isolates the remaining character-theoretic work to proving
those two formulas from (7.7.b), `BetaDecomp`, and `‖β‖² = e + 1`. -/
theorem normEstimates_of_normQuadraticCorrection_eqs
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hgamma : H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD) :
    H78.NormEstimates hBD where
  zetaNuRho_norm_sq_ge :=
    H78.zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq hBD hzeta
  gamma_norm_sq_le :=
    H78.gammaNormSq_le_of_normQuadraticCorrection_eq hBD hgamma

/-- Once the orthogonal expansion of `‖β‖²` is known, the residual norm formula
for `Γ` is just the arithmetic rearrangement in Peterfalvi (7.8.b). -/
theorem gammaNormSq_eq_of_betaNormSq_expand
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hbetaNorm : H78.betaNormSq = (H78.complementIndex : ℝ) + 1)
    (hexpand : H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD) :
    H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD := by
  have hh_ne : (H78.kernelOrder : ℝ) ≠ 0 := by
    exact_mod_cast H78.kernelOrder_pos.ne'
  have he_ne : (H78.complementIndex : ℝ) ≠ 0 := by
    exact_mod_cast H78.complementIndex_pos.ne'
  rw [hbetaNorm] at hexpand
  have hquad :
      (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD =
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) := by
    rw [normQuadraticCorrection]
    field_simp [hh_ne, he_ne]
  rw [hquad]
  linarith

/-- Irreducibility and distinctness of the source `S`-family give its
orthogonality matrix. -/
theorem sourceZeta_orthogonal_of_irreducible_distinct (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0 := by
  intro i hi j hj
  by_cases hij : i = j
  · rw [if_pos hij, hij]
  · rw [if_neg hij]
    let χ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
      ⟨H78.hyp76.zeta i, hirr i hi⟩
    let ψ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
      ⟨H78.hyp76.zeta j, hirr j hj⟩
    have hne : χ ≠ ψ := by
      intro hχψ
      exact hdistinct i hi j hj hij (congrArg
        (fun θ : OddOrder.RepresentationTheory.IrreducibleCharacter L =>
          (θ : ClassFunction L ℂ)) hχψ)
    simpa [χ, ψ, hne] using
      (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite χ ψ)

/-- Irreducibility of the source `S`-family makes every source norm nonzero. -/
theorem sourceZeta_norm_ne_of_irreducible (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 := by
  intro i hi
  let χ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
    ⟨H78.hyp76.zeta i, hirr i hi⟩
  have hχ : ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1 := by
    simpa [χ] using
      (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite χ χ)
  rw [hχ]
  norm_num

/-- Source-side beta norm data give Peterfalvi's residual norm formula for `Γ`. -/
theorem gammaNormSq_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD :=
  H78.gammaNormSq_eq_of_betaNormSq_expand hBD
    (H78.betaNormSq_eq_complementIndex_add_one hsrc)
    (H78.betaNormSq_eq_of_source_orthogonal hBD
      horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr)

/-- Once the remaining `(ζ^ν)^ρ` quadratic formula is supplied, the source-side
beta norm data package Peterfalvi (7.8.b)'s `NormEstimates`. -/
theorem normEstimates_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD :=
  H78.normEstimates_of_normQuadraticCorrection_eqs hBD hzeta
    (H78.gammaNormSq_eq_of_source_orthogonal hBD hsrc
      horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr)

/-- Version of `normEstimates_of_source_orthogonal` using the natural source
hypotheses that the `S`-family consists of distinct irreducible characters. -/
theorem normEstimates_of_irreducible_source_data
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD := by
  have hzeta_mem : H78.zetaDistinct ∈ (Finset.univ.erase H78.ind1H) := by
    simp [H78.zetaDistinct_ne_ind1H]
  exact H78.normEstimates_of_source_orthogonal hBD hsrc
    (H78.sourceZeta_orthogonal_of_irreducible_distinct hirr hdistinct)
    (H78.sourceZeta_norm_ne_of_irreducible hirr)
    hzeta_degree hdegree_sum (hirr H78.zetaDistinct hzeta_mem) hzeta

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean =====
namespace OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

variable [Finite G]

/-- **Conjugate subgroups have the same type I status**: if `L` is type I and `conj g • L = M`,
then `M` is type I.  The Peterfalvi (13.17.b) input ruling out conjugacy of a type-`I` subgroup to
the type-II subgroups `S`, `T`. -/
theorem isTypeI_of_conj {L M : Subgroup G} (h : IsTypeI L) {g : G}
    (hconj : MulAut.conj g • L = M) : IsTypeI M :=
  hconj ▸ isTypeI_pointwise_smul (MulAut.conj g) h

end OddOrder.GroupTheory

-- ===== OddOrder/Peterfalvi/S13_TypeDetermination.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

/-- **Peterfalvi (11.9.b), character core** (Peterfalvi §11
coherence / Dade norm).  For a Type III/IV maximal subgroup `S` (the Hypothesis (11.2) case), with
κ-Hall factor `K` and dual factor `K* = M_σ(S) ⊓ C_G(K)`, the coherence / norm-inequality bound on
the character set `S(HC)` forces `q > p`, i.e. the dual factor is the smaller: `|K*| < |K|`
(`q = |W₁| = |K|`, `p = |W₂| = |K*|`).

The proof is now **fully assembled** from three pieces: (i) the carrier translation `|K| = w₁` (both
`K` and `W₁` complement `M'`, so both equal the derived index — `card_kappaHall_eq_derived_index`,
`TypePData.card_W1_eq_derived_index`); (ii) the carrier translation `|K*| = w₂`
(`card_Msigma_inf_centralizer_eq_card_W2`, axiom-clean BG §14 group theory); and (iii) the §11
character reduction `w₂ < w₁` (`S13.w2_lt_w1_of_hypothesis_H0C_unconditional` — the honest
narrow-`𝒮(H₀C)` route on the unconditional (11.3), issues 1019/1020; the deprecated wide
`S12.w2_lt_w1_of_hypothesis` and its false uniform-degree lemma have been retired).  All of
(i)/(ii) and the reduction spine of (iii) are proven; the residual is the genuine Peterfalvi
(11.8) non-orthogonality (`S13.exists_zeta_residual_not_orthogonal_H0C_of_refuter`), which
rests on the §14 Sibley glue `(6.7)`/`(5.8)` and the `(9.11)` caseA refuter (the `(10.8)`
residual is discharged by `S_not_coherent_unconditional`).  All of these are now proved. -/
theorem card_kappaHall_lt_of_isTypeIIIorIV {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hIIIorIV : IsTypeIII S ∨ IsTypeIV S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- `K` is cyclic, as a subgroup of the cyclic `Z = K ⊔ K*` (BG 14.7(d), via `typeP_duality`).
  obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
    BG.Ch4.S14.typeP_duality hG hS hSP hKS hK hKstar
  have : IsCyclic ↥(K ⊔ Kstar) := hcyc
  have : IsCyclic ↥K :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Kstar))
      (Subgroup.inclusion_injective _)
  -- Build the §10 hypothesis on `S` (type III/IV ⊆ III/IV/V).
  obtain ⟨hyp⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG hS
    (hIIIorIV.imp id Or.inl)
  -- `|K| = w₁`: both `K` and `W₁` complement `M'`, so both equal the derived index.
  have hKw1 : Nat.card ↥K = hyp.w1 := by
    rw [BG.Ch4.S16.card_kappaHall_eq_derived_index hG hS hSP hKS hK]
    exact hyp.typeP.card_W1_eq_derived_index.symm
  -- `|K*| = w₂`: the carrier bridge (lane-b W3, BG §14 group theory, now in `S10`).
  have hKstarw2 : Nat.card ↥Kstar = hyp.w2 := by
    rw [hKstar]
    exact OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG hS hSP hKS hK hyp.typeP
  -- The two (11.5)/(11.7) structural facts, discharged via §13 (`secondDerived_eq_HC`,
  -- `H_elementaryAbelian`): `M'' = H ⊔ C_U(H)` and `|H| = |W₂|^{|W₁|}`.
  have hM2 : secondDerivedInAmbient S
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)) :=
    OddOrder.Peterfalvi.S13.secondDerived_eq_fitting_of_base hG hyp hIIIorIV
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
  have hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1 :=
    OddOrder.Peterfalvi.S13.card_H_eq_of_base hG hyp hIIIorIV
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
  -- `w₂ < w₁` (Peterfalvi (11.9.b), from the genuine (11.8) via the honest narrow `𝒮(H₀C)` route
  -- on the unconditional (11.3) — `w2_lt_w1_of_hypothesis_H0C_unconditional`, issues 1019/1020).
  rw [hKstarw2, hKw1]
  exact OddOrder.Peterfalvi.S13.w2_lt_w1_of_hypothesis_H0C_unconditional hG hyp hIIIorIV hM2
    hHcard

/-- **Peterfalvi (13.2.a), character core** (mmd §13, `references/peterfalvi/04.15_*`).

For the type-`P` member `S` of a dual maximal pair (BG Theorem 14.7), with κ-Hall factor `K` and
dual factor `K* = M_σ(S) ⊓ C_G(K)`, the type-`P₁` alternative (`S` of Type III/IV/V) carries the
*larger* κ-Hall factor: `|K*| < |K|`.  In Peterfalvi's notation `q = |W₁| = |K|`, `p = |W₂| = |K*|`,
this is "`S` of Type III ⟹ `q > p`".

**Type-V exclusion via the unconditional Theorem (10.10)** (issue 1020 Phase 3 relayering): by
the type dictionary `proposition_type_classification`, a type-`P₁` `S` is Type III/IV (if
`M_F ≠ M_σ`) or Type V (if `M_F = M_σ`); the latter is impossible by
`no_typeV_maximal_unconditional` (`S12_Noncoherence` — the honest (10.8) → (10.10) chain,
including the (6.5) gate lemmas of issue 2022), so `S` is Type III/IV and the
genuinely §11 character core `card_kappaHall_lt_of_isTypeIIIorIV` ((11.9.b)) applies.  Consumed
by `isTypeP2_of_typeP_kappaHall_lt`. -/
theorem card_kappaHall_lt_of_isTypeP1 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hP1 : BG.Ch4.S14.IsTypeP1 S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- Type dictionary: `S` type-`P₁` ⟹ Type III/IV (`M_F ≠ M_σ`) or Type V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ := BG.Ch4.S16.proposition_type_classification hG hS
  -- Type V is excluded by Theorem (10.10) `no_typeV_maximal`, so `M_F ≠ M_σ` and `S` is III/IV.
  have hMF : BG.Ch4.S15.MF S ≠ BG.Ch3.S10.Msigma S := fun hMF =>
    OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG ⟨S, hS, hdV.mpr ⟨hP1, hMF⟩⟩
  -- The genuinely §11 character core (11.9.b) gives `|K*| < |K|`.
  exact card_kappaHall_lt_of_isTypeIIIorIV hG hS hSP hKS hK hKstar (hcIII_IV.mpr ⟨hP1, hMF⟩)

/-- **Peterfalvi (13.2.a)** (mmd §13, `references/peterfalvi/04.15_*`): the type-`P` member `S` of a
dual maximal pair whose κ-Hall factor `K` is the *smaller* of the two coprime factors of
`W = K × K*` is of type `P₂` (BG) / Type II (Peterfalvi).

This selects, out of the type-duality disjunction `IsTypeP2 S ∨ IsTypeP2 T` (BG Theorem 14.7,
`typeP_duality`, which carries no order information), the determinate side `IsTypeP2 S` fixed by the
ordering `|K| < |K*|`.  Skeleton proof: `S` is type-`P`, hence type `P₁` or `P₂`
(`isTypeP_iff_isTypeP1_or_isTypeP2`); the `P₁` branch is excluded by `card_kappaHall_lt_of_isTypeP1`
(the Pf §10–§11 character core), leaving `P₂`.

Consumed by `section16MaximalPair_of_isMinimalSimpleOdd` to carry `Section16MaximalPair.S_typeP2`
(relane #4, issues 4009/2019), which unblocks the §15 `basic_structure` `TypePData` carrier wiring
(`exists_typePData_W1_eq_of_isTypeP2`). -/
theorem isTypeP2_of_typeP_kappaHall_lt {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hlt : Nat.card ↥K < Nat.card ↥Kstar) :
    BG.Ch4.S14.IsTypeP2 S := by
  rcases BG.Ch4.S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hSP with hP1 | hP2
  · exact absurd (card_kappaHall_lt_of_isTypeP1 hG hS hSP hKS hK hKstar hP1) (lt_asymm hlt)
  · exact hP2

end OddOrder

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.b,c,e) — the `M_F`-structure residual** (faithful obligation, §16-gated).

The genuinely §16-structural half of (13.2): the Fitting kernel `P = S_F` is elementary abelian of
order `p^q` (13.2.b,c), the complement `U` is abelian (13.2.a), `u ≤ (p^q − 1)/(p − 1)` (13.2.e),
and `A_0(S)` is a TI-subset (13.2.e).

Unlike the *type determination* and the `U W₁` *Frobenius structure* of (13.2.a) — both now read off
sorry-free from the carrier (`isTypeII_of_isTypeP2`, `typeP_uW1_frobenius` on `Sdata`) — these are
the σ-structure facts of the type-`P₂` member `S`: `M_σ = M_F` is the elementary-abelian `p`-group
of
rank `q` on which the prime-order `κ`-Hall factor `W₁` acts (BG §10/§14 σ-theory), giving the
`u`-bound from the count of `W₁`-orbits.  No repo theorem yet states "`M_σ` elementary abelian of
order `p^q`"; declared here as the localized faithful gate (the
`card_Q_eq`/`coprime_card_U_card_P_of_disjoint` pattern) so that `basic_structure`'s assembly — its
honest type determination and Frobenius structure — are `sorry`-free. -/
structure BasicStructureGated (hyp : Hypothesis (G := G)) where
  U_commutative : IsMulCommutative ↥hyp.U
  P_elementaryAbelian : IsElementaryAbelian hyp.p ↥hyp.P
  P_order : Nat.card ↥hyp.P = hyp.p ^ hyp.q
  u_bound : hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1)
  A0S_TI : Prop
  A0S_TI_holds : A0S_TI
  tauS_eq_induction : Prop
  tauS_eq_induction_holds : tauS_eq_induction

/-- **(Rung B, reduction) `IsTISubset (A(S)) S ⟹ all `S`-instance Dade stabilizers vanish.**  A
TI-subset `A` has `C_G(x) ≤ L` for every `x ∈ A` (`IsTISubset.centralizer_le`), so no `A(S)`-point
escapes `S`; then `forall_dadeHypS_H_eq_bot_of_not_escaping` applies.  This is the direction of
Peterfalvi (2.3) that turns the `normedTI` conclusion (Rung C/D) into the trivial-stabilizer datum
the honest `dade = Ind` bridge consumes. -/
theorem Hypothesis.forall_dadeHypS_H_eq_bot_of_isTISubset [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTI : OddOrder.GroupTheory.IsTISubset (S10.typePACore hyp.S) hyp.S) :
    ∀ a : {a : G // a ∈ S10.typePACore hyp.S}, (hyp.dadeHypS hG).H a = ⊥ :=
  hyp.forall_dadeHypS_H_eq_bot_of_not_escaping hG
    (fun _a ha hesc => hesc.2 (hTI.centralizer_le ha))

/-- **(Rung B, the equivalence, Peterfalvi (2.3) for the honest `S`-instance)**: the three forms of
the (13.2.e) `normedTI` gate coincide —
`IsTISubset (A(S)) S` ⟺ every `A(S)`-point is non-escaping ⟺ every `S`-instance Dade stabilizer
`dadeHypS.H a` is trivial.

The `A(S)`-set is sharp (`S10.typePACore_subset_sharp`, `1 ∉ A(S)`), lies in `S`
(`S10.typePACore_subset`), and is `S`-conjugation invariant (`S10.typePACore_conj_mem`), so the
general `S04.isTISubset_iff_exists_hypothesis_with_trivial_H` (2.3) applies; but here we get the
*specific* `dadeHypS` stabilizers, via the (8.14) kernel formula.  This closes Rung B: reducing the
missing input of `sInstance_dade_eq_induce_of_supported_trivial_H` (with `A₁ = A(S)` full) to the
single TI fact `IsTISubset (A(S)) S` = Coq `FTtypeP_facts` (e). -/
theorem Hypothesis.isTISubset_typePACore_iff_forall_dadeHypS_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (S10.typePACore hyp.S) hyp.S ↔
      ∀ a : {a : G // a ∈ S10.typePACore hyp.S}, (hyp.dadeHypS hG).H a = ⊥ := by
  refine ⟨hyp.forall_dadeHypS_H_eq_bot_of_isTISubset hG, fun hH => ?_⟩
  -- The reverse direction is Peterfalvi (2.3): trivial Dade stabilizers ⟹ TI.
  exact (hyp.dadeHypS hG).isTISubset_of_forall_H_eq_bot hH

/-- **(13.2.e) `normedTI`, TI half — `A(S)` is a TI-subset with normalizer `S`** (Coq
`FTtypeP_facts` (e), the `normedTI 'A0(S) G S` conclusion; PFsection13.v:197).  Closes the
gate G2 of issue 1017 update #22: Rung B's equivalence fed by Rung C. -/
theorem Hypothesis.isTISubset_typePACore [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (S10.typePACore hyp.S) hyp.S := by
  have : Fintype G := Fintype.ofFinite G
  exact (hyp.isTISubset_typePACore_iff_forall_dadeHypS_H_eq_bot hG).mpr
    (hyp.forall_dadeHypS_H_eq_bot hG hnoV)

open scoped FiniteInduce in
/-- **Peterfalvi (13.2)(e), the book statement, unconditional** — *"`A₀(S)` is a TI-subset of `G`
with normalizer `S` and the Dade isometry `τ` relative to `A₀(S)` coincides with `Ind_S^G`"*
(p. 75; Coq `FTtypeP_facts` (e), the `normedTI 'A0(S) G S` + `{in 'CF(S, 'A0(S)), tau =1 'Ind}`
pair).

Both halves already exist (`isTISubset_typePACore`, `sInstance_dade_eq_induce`); this bundles
them and **discharges the Type-V exclusion** with the axiom-clean Theorem (10.10)
`S12.no_typeV_maximal_unconditional`, so the (13.2)(e) statement is available with no hypothesis
beyond `hG` and the (13.1) carrier.

Recorded because the `BasicStructureGated`/`BasicStructureData` carriers expose (13.2)(e) only as
the `Prop`-valued data fields `A0S_TI` / `tauS_eq_induction`, which `basic_structure_gated`
instantiates with `True` — a reader of `basic_structure`'s conclusion cannot see the clause
(issue 0172 §13 audit). -/
theorem Hypothesis.A0S_normedTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (S10.typePACore hyp.S) hyp.S ∧
      ∀ [Fintype G], ∀ {f : ClassFunction ↥hyp.S ℂ},
        f.support ⊆
            OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S →
          OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
              ((hyp.dadeHypS hG).fullDadeIsometryData) f
            = ClassFunction.induce hyp.S f :=
  ⟨hyp.isTISubset_typePACore hG (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG),
    fun {_} {_} hf =>
      hyp.sInstance_dade_eq_induce hG
        (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG) hf⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory OddOrder.GroupTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk')

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **Peterfalvi (9.7.a): the qualitative block-scalar product embedding.**  Projection of
`caseA_blockScalarFacts`; see there for the accompanying `a`-form divisibility. -/
theorem caseA_exists_blockScalarRatioEmbedding [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    ∃ ψ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (Fin (data.q - 1) → (ZMod chief.p)ˣ),
      Function.Injective ψ :=
  (caseA_blockScalarFacts chars caseA).1

open scoped Classical in
/-- **Peterfalvi (9.7.a): imprimitive block-scalar order divisibility.**  From the case-(a) Clifford
data, the image `Ū = U/C_U(H̄)` embeds as a subgroup of `((𝔽_p)ˣ)^{q-1}`; hence its order
`u = |Ū|` divides `(p - 1)^{q-1}`.  This strengthened form retains the odd-part information used
in Peterfalvi (13.13). -/
theorem caseA_u_dvd_pred_pow [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    chars.u ∣ (chief.p - 1) ^ (data.q - 1) := by
  have : Fact chief.p.Prime := ⟨chief.p_prime⟩
  obtain ⟨ψ, hψ⟩ := caseA_exists_blockScalarRatioEmbedding chars caseA
  have hunits : Nat.card (ZMod chief.p)ˣ = chief.p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime chief.p_prime]
  have hdiv := Subgroup.card_dvd_of_injective ψ hψ
  rw [Nat.card_pi, hunits] at hdiv
  have hu : chars.u = Nat.card ↥(uActionHom data chief).range :=
    chars.u_eq_card_quotient
  rw [hu]
  simpa using hdiv

end OddOrder.Peterfalvi.S11

-- ===== OddOrder/Peterfalvi/S11_CaseAOddPartBound.lean =====
namespace OddOrder.Peterfalvi.S11

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.13), case-A odd-part divisibility.**  The imprimitive block action gives
`u ∣ (p - 1)^(q - 1)`; since `u` is odd, coprimality with `2^(q - 1)` removes that factor from
`(p - 1)^(q - 1) = 2^(q - 1) ((p - 1) / 2)^(q - 1)`. -/
theorem caseA_u_dvd_half_pred_pow [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars) :
    chars.u ∣ ((chief.p - 1) / 2) ^ (data.q - 1) := by
  have hdiv := caseA_u_dvd_pred_pow chars caseA
  have heven : 2 ∣ chief.p - 1 :=
    even_iff_two_dvd.mp (chiefFactor_p_sub_one_even (chief := chief) hG)
  have hsplit : chief.p - 1 = 2 * ((chief.p - 1) / 2) :=
    (Nat.mul_div_cancel' heven).symm
  rw [hsplit, mul_pow] at hdiv
  have hcop : Nat.Coprime chars.u (2 ^ (data.q - 1)) :=
    (Nat.coprime_two_right.mpr (u_odd hG chars)).pow_right _
  exact hcop.dvd_of_dvd_mul_left hdiv

end OddOrder.Peterfalvi.S11

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.a), ordered refinement**: if `q < p`, then `S` is of Type II.

Use the intrinsic κ-Hall factor `Sdata.W1`.  The generic type-`P` bridge identifies the order of
`M_σ(S) ∩ C_G(Sdata.W1)` with the order of `Sdata.W2`; the carried reconciliations turn the
hypothesis `q < p` into precisely the strict κ-ordering required by
`isTypeP2_of_typeP_kappaHall_lt`. -/
theorem Hypothesis.isTypeII_of_q_lt_p [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hqp : hyp.q < hyp.p) : IsTypeII hyp.S := by
  have hSP : OddOrder.BG.Ch4.S14.IsTypeP hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
  let : IsCyclic ↥hyp.Sdata.W1 := hyp.Sdata.W1_cyclic
  have hW1hall := OddOrder.Peterfalvi.S12.typePData_W1_isHallSubgroup_kappa
    hG hyp.S_maximal hSP hyp.Sdata
  have hbridge := OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG
    hyp.S_maximal hSP hyp.Sdata.W1_le hW1hall hyp.Sdata
  have hlt : Nat.card ↥hyp.Sdata.W1 <
      Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓
        Subgroup.centralizer (hyp.Sdata.W1 : Set G)) := by
    rw [hbridge, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq,
      ← hyp.q_eq_card_W1, ← hyp.p_eq_card_W2]
    exact hqp
  have hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.S :=
    OddOrder.isTypeP2_of_typeP_kappaHall_lt hG hyp.S_maximal hSP hyp.Sdata.W1_le
      hW1hall rfl hlt
  exact OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hP2

/-- **Peterfalvi (13.2.b)/(11.7) for the `S`-instance**: `P = S_F` is elementary abelian of
exponent `p`.  Assembled from the §11 chief-factor data of `S` (`exists_chiefFactorData` on
`toTypesIIIIIIVSetupS`): the chief kernel `N = ⊥` (`toTypesIIIIIIVSetupS_chief_N_eq_bot`), so
`P/⊥ ≅ P` *is* the chief factor and carries `ChiefFactorData.quotient_elementaryAbelian` at the
chief prime `chief.p = p` (forced by `|P| = p^q`).  **Ungated** — the `S`-instance `H₀ = ⊥` is
proven (`P` itself is the chief factor), unlike the generic `chief_H0_eq_bot_of_noncoherent`
(then sorried, since proved).  Discharges
`basic_structure_gated.P_elementaryAbelian`. -/
theorem Hypothesis.P_elementaryAbelian [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.p ↥hyp.P := by
  classical
  obtain ⟨chief, _⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
    change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hN : chief.N = ⊥ := hyp.toTypesIIIIIIVSetupS_chief_N_eq_bot hG chief
  -- `chief.p = p` from `|P| = p^q = chief.p^q · |N|` with `|N| = 1`.
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
    change Nat.card ↥hyp.Sdata.W1 = hyp.q; rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hq] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  have hdvd : chief.p ∣ hyp.p ^ hyp.q := by
    refine dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.p :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  -- Transport `quotient_elementaryAbelian` along `↥H ⧸ ⊥ ≃* ↥H`, then rewrite `H = P`.
  have hEA : IsElementaryAbelian hyp.p ↥(hyp.toTypesIIIIIIVSetupS hG).H := by
    have h := chief.quotient_elementaryAbelian
    rw [hpp] at h
    exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot) h
  rwa [hHeq] at hEA

/-- **`S`-instance chief-factor `q` identity**: the `(9.x)` chief-factor prime `data.q` of the
`S`-instance `toTypesIIIIIIVSetupS` is the type-`P` invariant `q = |W₁|`.  Extracted from
`u_le_cyclotomicQuotient` for reuse by the (13.3.b) dichotomy translations. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_q_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
  change Nat.card ↥hyp.Sdata.W1 = hyp.q
  rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]

/-- **`S`-instance chief-factor prime identity**: the chief prime `chief.p = p`, forced by
`|P| = p^q = chief.p^q · |N|`.  Extracted from `u_le_cyclotomicQuotient`. -/
theorem Hypothesis.chiefFactorS_p_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.p = hyp.p := by
  have := chief.N_normal
  have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
    change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hyp.toTypesIIIIIIVSetupS_q_eq hG] at hquot
  have hsplitP := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplitP
  have hdvd : chief.p ∣ hyp.p ^ hyp.q :=
    dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') (hsplitP ▸ Dvd.intro _ rfl)
  exact (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
    (chief.p_prime.dvd_of_dvd_pow hdvd)

/-- **`S`-instance `u` identity**: the `U`-action image order `chars.u = |Ū| = [U : C_U(P)] = u`.
Extracted from `u_le_cyclotomicQuotient`; the (13.3.b) dichotomy uses it to transport the
`caseB_of_no_irreducible_sOf_H0Cprime` conclusion `chars.u = (p^q−1)/(p−1)` to `hyp.u`. -/
theorem Hypothesis.mkSection11CharacterDataS_u_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    (hyp.mkSection11CharacterDataS hG chief).u = hyp.u := by
  have hc0 : 0 < hyp.c := hyp.c_eq_card_C ▸ Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hc0 ?_
  have key : (hyp.mkSection11CharacterDataS hG chief).u
      * Nat.card ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
      = Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).U := by
    rw [← OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u (hyp.mkSection11CharacterDataS hG chief)]
    have h := Subgroup.index_mul_card
      ((OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief).subgroupOf
        (hyp.toTypesIIIIIIVSetupS hG).U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupS hG) chief)).toEquiv] at h
  rw [hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief, ← hyp.c_eq_card_C,
    show (hyp.toTypesIIIIIIVSetupS hG).U = hyp.U from hyp.Sdata_U_eq, hyp.card_U_eq_uc] at key
  exact key

/-- **Peterfalvi (13.2.b,c,e)** structural producer: the `M_F`-structure of the type-`P₂` member
`S`.  Faithful obligation on the §16 σ-structure (`BasicStructureGated` docstring).

`U_commutative` (13.2.a U-side) and `P_order` (13.2.b order part) are now **genuine**:
* `U_commutative` from the carried `S_U_commutative` (BG Lemma 15.1(b)
`typeP_hall_derived_eq_and_abelian`, `U` the `(κ∪σ)'`-Hall, supplied at construction);
* `P_order` = `|P| = p^q` from `card_P_eq` fed by the carried `Sdata_W2_eq` (the intrinsic dual
factor `Sdata.W2 = C_{S'}(W₁#)` equals the abstract `W₂ = K*`, via
`typePData_of_kappaHall_hallComplement_W2`).

The `A_0(S)`/`τ_S` clauses are the opaque scaffold Props (`True`).  The two former concrete
residuals are now **genuine** (both discharged ungated on the `S`-instance `toTypesIIIIIIVSetupS`):
* `P_elementaryAbelian` — Pf (11.7), from the §11 chief factor `P = S_F` (`H₀ = ⊥`), via
  `Hypothesis.P_elementaryAbelian`;
* `u_bound` — Pf (9.7) `u ≤ (p^q−1)/(p−1)`, via `Hypothesis.u_le_cyclotomicQuotient`
  (cites the proven unconditional `S11.u_le_cyclotomicQuotient`; issue 9000 lane-b cite). -/
noncomputable def basic_structure_gated [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : BasicStructureGated hyp where
  U_commutative := hyp.S_U_commutative
  P_elementaryAbelian := hyp.P_elementaryAbelian hG
  P_order := hyp.card_P_eq hG hyp.Sdata_W2_eq
  u_bound := hyp.u_le_cyclotomicQuotient hG
  A0S_TI := True
  A0S_TI_holds := trivial
  tauS_eq_induction := True
  tauS_eq_induction_holds := trivial

/-- **Peterfalvi (13.2.a--c,e)**: `S` is type II or III, `P` is elementary
abelian of order `p^q`, `u` is bounded, and `A_0(S)` is a TI-subset.

The **type determination** (13.2.a) is discharged without the stronger `S_typeP2` carrier:
`isTypeII_or_isTypeIII_of_isTypeNonI` gives the unconditional alternative, while
`Hypothesis.isTypeII_of_q_lt_p` applies the genuine κ-ordering theorem when `q < p`.  The
remaining `M_F`-structure data (13.2.b,c) is read off the faithful §16-gated producer
`basic_structure_gated`.

**(13.2.e)** is stated *genuinely* here — `A₀(S)` is a TI-subset with normalizer `S`
(`Hypothesis.A0S_normedTI`, whose Type-V exclusion is discharged by the unconditional Theorem
(10.10)).  The carrier fields `BasicStructureData.A0S_TI` / `tauS_eq_induction` remain `Prop`-valued
placeholders that `basic_structure_gated` fills with `True`; the conclusion no longer routes
through them (issue 0172 §13 audit).  The isometry half `τ = Ind_S^G` is the second conjunct of
`A0S_normedTI`. -/
theorem basic_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ _data : BasicStructureData hyp,
      (IsTypeII hyp.S ∨ IsTypeIII hyp.S) ∧ IsElementaryAbelian hyp.p ↥hyp.P ∧
        Nat.card ↥hyp.P = hyp.p ^ hyp.q ∧
        hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) ∧
        OddOrder.GroupTheory.IsTISubset
          (OddOrder.Peterfalvi.S10.typePACore hyp.S) hyp.S := by
  -- (13.2.a): the honest II/III alternative; its witness-independent core gives `Sdata.U ≠ ⊥`.
  have hStype : IsTypeII hyp.S ∨ IsTypeIII hyp.S :=
    OddOrder.Peterfalvi.S13.isTypeII_or_isTypeIII_of_isTypeNonI
      _hG hyp.S_maximal hyp.S_nonI
  let setup := hyp.toTypesIIIIIIVSetupS _hG
  have hSdataUne := setup.nontrivial.1
  change hyp.Sdata.U ≠ ⊥ at hSdataUne
  -- (13.2.a) `U W₁` Frobenius: sorry-free from the carrier `Sdata` (`typeP_uW1_frobenius`,
  -- reconciled `Sdata.U = U`, `Sdata.W1 = W1`).
  have hUW1frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.U ⊔ hyp.W1) (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
        (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    rwa [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at h
  -- (13.2.b,c,e) `M_F`-structure: the localized faithful §16 producer.
  let core := basic_structure_gated _hG hyp
  refine ⟨{ S_typeII_or_typeIII := hStype
            q_lt_p_forces_typeII := hyp.isTypeII_of_q_lt_p _hG
            U_commutative := core.U_commutative
            UW1_frobenius := hUW1frob
            P_elementaryAbelian := core.P_elementaryAbelian
            P_order := core.P_order
            u_bound := core.u_bound
            A0S_TI := core.A0S_TI
            A0S_TI_holds := core.A0S_TI_holds
            tauS_eq_induction := core.tauS_eq_induction
            tauS_eq_induction_holds := core.tauS_eq_induction_holds }, ?_⟩
  exact ⟨hStype, core.P_elementaryAbelian, core.P_order, core.u_bound,
    (hyp.A0S_normedTI _hG).1⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`H = PC` is abelian** (Peterfalvi (13.2.a,b)): `P` is (elementary) abelian
(`basic_structure`), `C ≤ U` is abelian (`S_U_commutative`), and `C` centralizes `P`
(`C = U ⊓ C_S(P)`), so the join is abelian (`isMulCommutative_sup_of_le_centralizer`).
The `habelian` input of the (13.7) Parseval bookkeeping. -/
theorem Hypothesis.H_mulCommutative [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : IsMulCommutative ↥hyp.H := by
  obtain ⟨-, -, hPel, -, -, -⟩ := basic_structure hG hyp
  have hPab : IsMulCommutative ↥hyp.P := ⟨⟨hPel.1⟩⟩
  have hCab : IsMulCommutative ↥hyp.C := by
    have hCU : hyp.C ≤ hyp.U := hyp.C_eq ▸ inf_le_left
    exact ⟨⟨fun a b => Subtype.ext (by
      have h := hyp.S_U_commutative.is_comm.comm
        (⟨(a : G), hCU a.2⟩ : ↥hyp.U) ⟨(b : G), hCU b.2⟩
      simpa using congrArg Subtype.val h)⟩⟩
  have hCP : hyp.C ≤ Subgroup.centralizer (hyp.P : Set G) := hyp.C_eq ▸ inf_le_right
  change IsMulCommutative ↥(hyp.P ⊔ hyp.C)
  rw [sup_comm]
  exact OddOrder.BG.Ch4.S15.isMulCommutative_sup_of_le_centralizer hCab hPab hCP

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

/-- **Peterfalvi (13.3.b), dichotomy glue** (§9-generic, issue 9013 gate 3): if the §9 family
`𝒮(H₀C')` contains **no** irreducible character, then case (9.7.b) holds
(a `CliffordCaseBData` — carrying the Singer facts `Ū` cyclic, `u ∣ (p^q−1)/(p−1)`, irreducible
action), with `C = ⊥` and the full value `u = (p^q − 1)/(p − 1)`.

Assembly of the sorry-free §9 endpoints: `clifford_dichotomy` splits into the two Clifford cases;
in case (a) the (9.8.c) witness (`caseA_character_counts` conjunct (c)) is an irreducible member
of `𝒮(H₀C) ⊆ 𝒮(H₀C')` (`sOf_antitone`, `C' ≤ C`) — contradicting the hypothesis; in case (b) the
(9.9.c) conjunct (d) of `caseB_character_counts` delivers both values.  This is the C=1/u-full
half of (13.3.b); the "case (9.7.b) holds"半 is the returned `CliffordCaseBData` itself.  Stated
generically over `M` so both the `S`- and `T`-instances (via `toTypesIIIIIIVSetupS` /
`toTypesIIIIIIVSetupT`) can cite it — the T-instance is the (13.4) θ-package's (13.3.b)-on-`T`
input (contrapositive form). -/
theorem caseB_of_no_irreducible_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    ∃ _caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData chars,
      chars.C = ⊥ ∧ chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) := by
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG chars with hA | hB
  · exfalso
    obtain ⟨caseA⟩ := hA
    obtain ⟨-, -, ⟨χ, hχmem, hχirr, -⟩, -⟩ :=
      OddOrder.Peterfalvi.S11.caseA_character_counts hG chars caseA
    exact hno ⟨χ,
      OddOrder.Peterfalvi.S11.sOf_antitone data
        (sup_le_sup_left chars.Cprime_le_C chief.H0) hχmem, hχirr⟩
  · obtain ⟨caseB⟩ := hB
    exact ⟨caseB,
      (OddOrder.Peterfalvi.S11.caseB_character_counts hG chars caseB).2.2.2 hno⟩

end CountingLayer

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- Lower estimate for the analytic parameter `m` of **Peterfalvi (13.10)**.
Dropping the (positive) last summand and bounding `(q-1)/q^p ≤ 1/q^2` (valid once
`p ≥ 3`) gives `m ≥ 1 - 1/(q-1) - 1/q^2`. -/
theorem m_value_ge_aux {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (1 : ℚ) - 1 / ((q : ℚ) - 1) - 1 / (q : ℚ) ^ 2 ≤
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hXpos : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hX3 : (q : ℚ) ^ 3 ≤ (q : ℚ) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hfrac : ((q : ℚ) - 1) / (q : ℚ) ^ p ≤ 1 / (q : ℚ) ^ 2 := by
    rw [div_le_div_iff₀ hXpos (by positivity)]
    have e : (q : ℚ) ^ 3 = ((q : ℚ) - 1) * (q : ℚ) ^ 2 + (q : ℚ) ^ 2 := by ring
    have hsq : (0 : ℚ) ≤ (q : ℚ) ^ 2 := sq_nonneg _
    linarith [hX3, e, hsq]
  have hpos : (0 : ℚ) ≤ 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by positivity
  linarith [hfrac, hpos]

/-- **Peterfalvi (13.11.b)** numeric bound: `q ≥ 5 ⇒ m > 7/10`. -/
theorem m_value_gt_seven_tenths {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (7 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have haux := m_value_ge_aux hq hp
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq5]
  linarith [haux, h1, h2]

namespace Hypothesis

/-- **Peterfalvi (13.11.b)** at the Section 15 hypothesis level: if `q ≥ 5`,
then the concrete analytic parameter satisfies `m > 7/10`. -/
theorem m_gt_seven_tenths_of_five_le_q (hyp : Hypothesis (G := G))
    (hq5 : 5 ≤ hyp.q) :
    hyp.m > (7 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_seven_tenths hq5 hyp.three_le_p

end Hypothesis

/-- **Peterfalvi (13.13)**: if case (9.7.a) holds for `S`, then
`q = 3` and `u = (p - 1)^2 / 4`.

The hypothesis is the genuine §11 `CliffordCaseAData` for the `S`-side chief factor.  Its block
decomposition supplies `u ∣ ((p - 1)/2)^(q - 1)`; (13.10), (13.11), and `c = 1` then feed the
pure elimination `caseA_numeric_parameters`. -/
theorem caseA_parameters_of_analytic_inequality [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief)) :
    hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  have hc1 := c_eq_one_of_analytic_inequality hG hyp h1310
  have hdiv := OddOrder.Peterfalvi.S11.caseA_u_dvd_half_pred_pow hG
    (hyp.mkSection11CharacterDataS hG chief) caseA
  rw [hyp.mkSection11CharacterDataS_u_eq hG chief,
    hyp.chiefFactorS_p_eq hG chief, hyp.toTypesIIIIIIVSetupS_q_eq hG] at hdiv
  have hpeven : 2 ∣ hyp.p - 1 := by
    have h := even_iff_two_dvd.mp
      (OddOrder.Peterfalvi.S11.chiefFactor_p_sub_one_even (chief := chief) hG)
    rwa [hyp.chiefFactorS_p_eq hG chief] at h
  have h1310c := h1310
  rw [hc1] at h1310c
  norm_num at h1310c
  have h1310' : (hyp.u : ℚ) >
      hyp.m * (((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ)) / (hyp.q : ℚ) := by
    have hpowcast : (((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ)) =
        (hyp.p : ℚ) ^ (hyp.q - 1) := by
      push_cast
      ring
    rw [hpowcast]
    exact h1310c
  have h13c : hyp.q = 3 →
      (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6) < (hyp.u : ℚ) := by
    intro hq3
    obtain ⟨_, _, hnum⟩ := numeric_bounds_of_analytic_inequality hyp h1310
    have h := (hnum hq3).2
    rw [hc1] at h
    simpa using h
  exact caseA_numeric_parameters hyp.three_le_p hyp.q_prime hyp.q_ne_two hpeven
    hyp.m_gt_seven_tenths_of_five_le_q h13c h1310' hdiv

/-- The `p ≡ 1 [MOD q]` divisibility part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_dvd_of_modEq_one {p q : ℕ} (hp : p.Prime)
    (hpq : p ≡ 1 [MOD q]) :
    q ∣ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [← Nat.modEq_zero_iff_dvd]
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD q] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpq
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  exact hterms.trans (by simp [hsum_one])

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **`T`-instance chief-factor `q` identity**: `data.q = p = |W₂|`.  Mirror of
`toTypesIIIIIIVSetupS_q_eq`. -/
theorem Hypothesis.toTypesIIIIIIVSetupT_q_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).q = hyp.p := by
  change Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).W1 = hyp.p
  rw [hyp.toTypesIIIIIIVSetupT_W1_eq hG hvd, ← hyp.p_eq_card_W2]

/-- **`T`-instance chief-factor prime identity**: `chief.p = q`, forced by
`|Q| = q^p = chief.p^p · |N|` (`card_Q_eq_qp`).  Mirror of `chiefFactorS_p_eq`. -/
theorem Hypothesis.chiefFactorT_p_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    chief.p = hyp.q := by
  have := chief.N_normal
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).H = hyp.q ^ hyp.p := by
    rw [show ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q from
      hyp.toTypesIIIIIIVSetupT_H_eq hG hvd]
    exact hyp.card_Q_eq_qp hG
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hyp.toTypesIIIIIIVSetupT_q_eq hG hvd] at hquot
  have hsplitQ := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplitQ
  have hdvd : chief.p ∣ hyp.q ^ hyp.p :=
    dvd_trans (dvd_pow_self chief.p hyp.p_prime.pos.ne') (hsplitQ ▸ Dvd.intro _ rfl)
  exact (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.q_prime).mp
    (chief.p_prime.dvd_of_dvd_pow hdvd)

/-- **Peterfalvi (13.2.b) at `T`, structure part**: `Q = T_F` is elementary abelian of
exponent `q`.

This is the `T`-side mirror of `Hypothesis.P_elementaryAbelian`.  It uses the general
type-`P`/type-II–IV setup on `T`, not the later (14.9) conclusion that `T` is type II:
`card_Q_eq_qp` makes the §9 chief kernel trivial, so the elementary-abelian chief factor
`Q/N` is `Q` itself, and `chiefFactorT_p_eq` identifies its prime with `q`. -/
theorem Hypothesis.Q_elementaryAbelian [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.q ↥hyp.Q := by
  classical
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one hG
  obtain ⟨chief, _⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupT hG hvd)
  have hN : chief.N = ⊥ := hyp.toTypesIIIIIIVSetupT_chief_N_eq_bot hG hvd chief
  have hp : chief.p = hyp.q := hyp.chiefFactorT_p_eq hG hvd chief
  have hEA : IsElementaryAbelian hyp.q ↥(hyp.toTypesIIIIIIVSetupT hG hvd).H := by
    have h := chief.quotient_elementaryAbelian
    rw [hp] at h
    exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot) h
  have hHeq : ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q :=
    hyp.toTypesIIIIIIVSetupT_H_eq hG hvd
  rwa [hHeq] at hEA

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.b)/(14.2.a), `T`-side dual of `W2_le_P`: `W₁ ≤ Q`.**  The cyclic factor `W₁`
(of prime order `q`) lies in `Q = T_F`, the maximal nilpotent normal Hall subgroup of `T`.  Dual to
`W2_le_P` (`W₂ ≤ P`), but read off the `T`-side type-`P` decomposition (`reconciled_typePData_T`)
rather than the coprime-index order count: the intrinsic dual cyclic factor
`data.W2 = C_{T'}(W₂#) = W₁` sits inside `data.H = maxNilpotentNormalHall T = Q`
(`data.W2_le`, `data.H_eq`, `Q_eq_TF`).  This is conjunct (1) of the (13.16)
`normalizer_W1_structure_of_D_eq_bot`
and is consumed by the `W₁`-side Maschke/Wielandt confinement (the dual of the `W₂`-side, where
`normalizer_U_inf_W2_eq_bot_of_data` uses `W2_le_P` at the analogous step). -/
theorem W1_le_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W1 ≤ hyp.Q := by
  obtain ⟨tpd, _, _, htpdW1⟩ := reconciled_typePData_T hG hyp
  have hHeq : tpd.H = hyp.Q := by rw [tpd.H_eq, hyp.Q_eq_TF]
  rw [← htpdW1, ← hHeq]
  exact le_trans tpd.W2_le inf_le_left

/-- **`T`-side dual of `not_normalizer_U_le_S`** (Pf (13.17), V-side): if `V` is a `T`-conjugate of
the `TypeIIData` witness's complement `tdata.typeP.U`, then `N_G(V) ⊄ T`.  Transfers the type-II
property `tdata.normalizer_not_le` along the conjugation `V = (typeP.U)^x`, `x ∈ T`. -/
theorem not_normalizer_V_le_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.T)
    (hconj : ∃ x : G, x ∈ hyp.T ∧ hyp.V = MulAut.conj x • tdata.typeP.U) :
    ¬ Subgroup.normalizer (hyp.V : Set G) ≤ hyp.T := by
  obtain ⟨x, hxT, hVconj⟩ := hconj
  intro hNVT
  refine tdata.normalizer_not_le ?_
  have hTfix : MulAut.conj x • hyp.T = hyp.T :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxT)
  have hnorm_eq : Subgroup.normalizer (hyp.V : Set G)
      = MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G) := by
    rw [hVconj]
    exact (OddOrder.BG.Ch3.S12.normalizer_conj_smul x tdata.typeP.U).symm
  rw [hnorm_eq] at hNVT
  have hle : MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G)
      ≤ MulAut.conj x • hyp.T := by rw [hTfix]; exact hNVT
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp hle

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Type is conjugacy-invariant** (the (13.17.a/b) `L ~ S`/`L ~ T` rule-out): a type-`I` maximal
subgroup `L` is not conjugate to any non-type-`I` maximal subgroup `M`.  If `conj g • L = M` then
`M` would be type `I` (`isTypeI_of_conj`, the automorphism-equivariance of the Peterfalvi taxonomy
— `OddOrder.GroupTheory.MaximalSubgroupTypeConj`), contradicting
`not_isTypeI_of_isTypeNonI`.  This is **gate-4 piece 1**, now discharged (sorry-free, axiom-clean);
reusable across the §16 conjugacy arguments. -/
theorem not_conj_of_isTypeI_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L M : Subgroup G} (hLI : IsTypeI L) (hMmax : M ∈ maximalSubgroups G)
    (hMnonI : IsTypeNonI M) : ¬ ∃ g : G, MulAut.conj g • L = M :=
  fun ⟨_g, hg⟩ =>
    OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG hMmax hMnonI
      (OddOrder.GroupTheory.isTypeI_of_conj hLI hg)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_ComplementStructure.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`T`-side dual of `q_not_dvd_kernel`** (V-side): `p = |W₂|` is coprime to the type-I Frobenius
kernel `L_F` (`p ∤ |L_F|`).  Mirror; same gated input `card_LF_coprime_pq` (`|L_F| ⟂ pq`). -/
theorem p_not_dvd_kernel [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L) :
    ¬ hyp.p ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf L) := by
  have hnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  have hcop := card_LF_coprime_pq _hG hyp hLmax hLI hnconjS hnconjT
  have hcopp : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.p :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right hyp.p hyp.q) hcop
  have hnotdvd : ¬ hyp.p ∣ Nat.card ↥(maxNilpotentNormalHall L) :=
    hyp.p_prime.coprime_iff_not_dvd.mp hcopp.symm
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hHleL : frob.typeI.typeF.H ≤ L := by
    rw [hHeq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleL).toEquiv, hHeq]
  exact hnotdvd

/-- **`T`-side dual of `exists_typeIFrobeniusData_W1_le`** (V-side): the type-I Frobenius
decomposition of `L` can be taken with the complement containing `W₂` (`|W₂| = p` coprime to the
kernel by `p_not_dvd_kernel`, Schur–Zassenhaus complement conjugacy). -/
theorem exists_typeIFrobeniusData_W2_le [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLtypeI : IsTypeI L) (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    ∃ frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L, frob.kernel_eq_MF ∧
      hyp.W2 ≤ frob.complement.map L.subtype := by
  obtain ⟨frob₀, hker₀⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hnoV hLmax hLtypeI
  have hW2L : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  have : (frob₀.typeI.typeF.H.subgroupOf L).Normal := frob₀.frobenius.isNormal
  have hLsolv : Group.IsSolvable ↥L :=
    _hG.isSolvable_of_lt_top L (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hLmax).1)
  have : Group.IsSolvable ↥(frob₀.typeI.typeF.H.subgroupOf L) := inferInstance
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W2.subgroupOf L))
      (Nat.card ↥(frob₀.typeI.typeF.H.subgroupOf L)) := by
    have hW2card : Nat.card ↥(hyp.W2.subgroupOf L) = hyp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L).toEquiv]
      exact hyp.p_eq_card_W2.symm
    rw [hW2card]
    exact (hyp.p_prime.coprime_iff_not_dvd).mpr (p_not_dvd_kernel _hG hyp hLmax hLtypeI frob₀)
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    inferInstance frob₀.frobenius.isComplement hcop
  refine ⟨{ frob₀ with
      complement := frob₀.complement.map (MulAut.conj x).toMonoidHom
      frobenius := frob₀.frobenius.conjComplement x }, frob₀.kernel_eq_MF_holds, ?_⟩
  have : hyp.W2 = (hyp.W2.subgroupOf L).map L.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le hW2L]
  rw [this]
  exact Subgroup.map_mono hx

/-- **Frobenius index bridge** (Pf (14.11), structural): for a type-I maximal `M` with
`TypeIFrobeniusData`, the index `|M : M_F|` of the Fitting kernel equals the order of the Frobenius
complement.  Immediate from the complement structure `M = M_F ⋊ complement` (`IsComplement'`) and
the
kernel identity `typeF.H = M_F`.  Supplies the `e = |M : K| = p q` half of `MHypothesis`
(`e_eq_index` + `complement_card_eq_pq`): combined with the V-side `complement_card_eq_pq`
(`= p q`),
the Fitting-kernel index of the type-I maximal over `N_G(V)` is `p q`. -/
theorem typeIFrobenius_kernel_index_eq_complement {M : Subgroup G}
    (data : OddOrder.Peterfalvi.S14.TypeIFrobeniusData M) :
    ((maxNilpotentNormalHall M).subgroupOf M).index = Nat.card data.complement := by
  rw [← data.typeI.typeF.H_eq]
  exact data.frobenius.isComplement.symm.index_eq_card

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S11_GaloisFieldModel.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory OddOrder.RepresentationTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The realized subgroup `C = C_U(H̄)` being trivial makes `uActionHom` injective. -/
theorem uActionHom_injective_of_cSub_eq_bot [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hC : cSub data chief = ⊥) : Function.Injective (uActionHom data chief) := by
  apply (uActionHom data chief).ker_eq_bot_iff.mp
  have hmap : ((uActionHom data chief).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
      (data.typeP.U ⊔ data.typeP.W1).subtype = ⊥ := hC
  rwa [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _),
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hmap

/-- **Peterfalvi (9.7.b), original-`U` field model.**  If `C_U(H̄) = 1`, transport the faithful
image model along `U.subgroupOf (U ⊔ W₁) ≃ U`.  This is the form used by the §14 `S`-side after
the §13 conclusion `C = 1`. -/
theorem caseB_exists_galoisField_repr_of_cSub_eq_bot [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (hC : cSub data chief = ⊥) :
    letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
    ∃ (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
      (μ : ↥data.typeP.U →* (GaloisField chief.p data.q)ˣ),
      Function.Injective μ ∧
      ∀ (u : ↥data.typeP.U) (x : ↥data.H ⧸ chief.N),
        e (Additive.ofMul
          (uActionHom data chief
            ((Subgroup.subgroupOfEquivOfLe
              (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).symm u) x)) =
          ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
            e (Additive.ofMul x) := by
  let : Fact chief.p.Prime := ⟨chief.p_prime⟩
  obtain ⟨e, μbar, hμbar, hcompat⟩ := caseB_exists_galoisField_repr chars caseB
  let eU := Subgroup.subgroupOfEquivOfLe
    (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)
  let toRange : ↥data.typeP.U →*
      ↥(MonoidHom.range (uActionHom data chief)) :=
    (uActionHom data chief).rangeRestrict.comp eU.symm.toMonoidHom
  let μ : ↥data.typeP.U →* (GaloisField chief.p data.q)ˣ := μbar.comp toRange
  have htoRange : Function.Injective toRange := by
    intro a b hab
    apply eU.symm.injective
    apply uActionHom_injective_of_cSub_eq_bot hC
    exact congrArg Subtype.val hab
  refine ⟨e, μ, hμbar.comp htoRange, ?_⟩
  intro u x
  have h := hcompat (toRange u) x
  change e (Additive.ofMul (uActionHom data chief (eU.symm u) x)) =
    ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
      e (Additive.ofMul x) at h
  simpa only [eU] using h

end OddOrder.Peterfalvi.S11

-- ===== OddOrder/Peterfalvi/S15_SSideGaloisFieldModel.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

section

private noncomputable def galoisFieldCongr
    {p p' q q' : ℕ} [Fact p.Prime] [Fact p'.Prime]
    (hp : p = p') (hq : q = q') :
    GaloisField p q ≃+* GaloisField p' q' := by
  subst p'
  subst q'
  exact RingEquiv.refl _

/-- **Peterfalvi (9.7.b)/(14.6), the S-side Galois-field model.**

If the §9 Clifford dichotomy is in case (b) and `c = |C_U(P)| = 1`, then
there are an additive equivalence `P ≃+ GF(p^q)` and an injective homomorphism
`U → GF(p^q)ˣ` which linearize the actual conjugation action of `U` on `P`.

The proof transports `caseB_exists_galoisField_repr_of_cSub_eq_bot` along
`H₀ = ⊥`, `H = P`, the identification of the abstract and named complements,
and the equalities of the two field parameters. -/
theorem caseB_exists_sSide_galoisField_repr_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData
      (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief))
    (hc : hyp.c = 1) :
    letI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
    ∃ (e : Additive ↥hyp.P ≃+ GaloisField hyp.p hyp.q)
      (μ : ↥hyp.U →* (GaloisField hyp.p hyp.q)ˣ),
      Function.Injective μ ∧
      ∀ (v : ↥hyp.U) (x : ↥hyp.P),
        e (Additive.ofMul
            (⟨(v : G) * (x : G) * (v : G)⁻¹, hyp.conj_mem_P v x⟩ : ↥hyp.P))
          = ((μ v : (GaloisField hyp.p hyp.q)ˣ) : GaloisField hyp.p hyp.q) *
            e (Additive.ofMul x) := by
  classical
  let : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
  let : Fact chief.p.Prime := ⟨chief.p_prime⟩
  have hN : chief.N = ⊥ := hyp.toTypesIIIIIIVSetupS_chief_N_eq_bot hG chief
  have hC :
      OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief = ⊥ := by
    rw [hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]
    apply Subgroup.eq_bot_of_card_eq
    rw [← hyp.c_eq_card_C, hc]
  have hp : chief.p = hyp.p := hyp.chiefFactorS_p_eq hG chief
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q :=
    hyp.toTypesIIIIIIVSetupS_q_eq hG
  obtain ⟨e₀, μ₀, hμ₀, hcompat₀⟩ :=
    OddOrder.Peterfalvi.S11.caseB_exists_galoisField_repr_of_cSub_eq_bot
      (hyp.mkSection11CharacterDataS hG chief) caseB hC
  have hH : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    change hyp.Sdata.H = hyp.P
    rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hU : (hyp.toTypesIIIIIIVSetupS hG).typeP.U = hyp.U :=
    hyp.Sdata_U_eq
  let eHP : ↥(hyp.toTypesIIIIIIVSetupS hG).H ⧸ chief.N ≃* ↥hyp.P :=
    ((QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientBot
        (G := ↥(hyp.toTypesIIIIIIVSetupS hG).H))).trans
      (MulEquiv.subgroupCongr hH)
  let eU : ↥(hyp.toTypesIIIIIIVSetupS hG).typeP.U ≃* ↥hyp.U :=
    MulEquiv.subgroupCongr hU
  let eF : GaloisField chief.p (hyp.toTypesIIIIIIVSetupS hG).q ≃+*
      GaloisField hyp.p hyp.q := galoisFieldCongr hp hq
  let e : Additive ↥hyp.P ≃+ GaloisField hyp.p hyp.q :=
    (eHP.toAdditive.symm.trans e₀).trans eF.toAddEquiv
  let eFUnits :
      (GaloisField chief.p (hyp.toTypesIIIIIIVSetupS hG).q)ˣ ≃*
        (GaloisField hyp.p hyp.q)ˣ :=
    Units.mapEquiv eF.toMulEquiv
  let μ : ↥hyp.U →* (GaloisField hyp.p hyp.q)ˣ :=
    eFUnits.toMonoidHom.comp (μ₀.comp eU.symm.toMonoidHom)
  refine ⟨e, μ, eFUnits.injective.comp (hμ₀.comp eU.symm.injective), ?_⟩
  intro v x
  have h := hcompat₀ (eU.symm v) (eHP.symm x)
  have eHP_symm_apply (y : ↥hyp.P) :
      eHP.symm y = QuotientGroup.mk ((MulEquiv.subgroupCongr hH).symm y) := by
    apply eHP.injective
    simp [eHP]
  have hact :
      OddOrder.Peterfalvi.S11.uActionHom (hyp.toTypesIIIIIIVSetupS hG) chief
          ((Subgroup.subgroupOfEquivOfLe
            (le_sup_left : (hyp.toTypesIIIIIIVSetupS hG).typeP.U ≤
              (hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔
                (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)).symm (eU.symm v))
          (eHP.symm x)
        = eHP.symm
          ⟨(v : G) * (x : G) * (v : G)⁻¹, hyp.conj_mem_P v x⟩ := by
    apply eHP.injective
    rw [eHP_symm_apply x, eHP_symm_apply]
    rw [OddOrder.Peterfalvi.S11.uActionHom, MonoidHom.comp_apply,
      OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply]
    simp only [eHP, MulEquiv.trans_apply,
      QuotientGroup.quotientMulEquivOfEq_mk]
    simp only [QuotientGroup.quotientBot]
    congr 1
  rw [hact] at h
  have h' := congrArg eF h
  simpa [e, μ, eFUnits, eF, eHP, eU,
    OddOrder.Peterfalvi.S11.uActionHom,
    OddOrder.Peterfalvi.S11.typeP_conjAction_apply] using h'

/-- **Peterfalvi (14.6), downstream-facing S-side Galois-field model.**

Assume `c = 1`, the type-I maximal-subgroup data over `N_G(U)`, and that every
actual Clifford case-(a) certificate supplies the sharp parameter equalities
`q = 3` and `u = (p - 1)² / 4`.  Then the named S-side Galois-field model
exists.

The parameter equalities are deliberately conditional on the case-(a)
certificate: (13.13) proves them only in that branch.  This is the exact
interface needed by downstream consumers.  It also keeps the currently
relayered analytic producer explicit rather than hiding it in this theorem. -/
theorem sSide_galoisField_repr_of_c_eq_one_and_caseA_parameters
    [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hc : hyp.c = 1)
    (hcaseAParams :
      ∀ {chief : OddOrder.Peterfalvi.S11.ChiefFactorData
          (hyp.toTypesIIIIIIVSetupS hG)},
        OddOrder.Peterfalvi.S11.CliffordCaseAData
            (hyp.mkSection11CharacterDataS hG chief) →
          hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4)
    (data : TypeIOverNormalizerData hyp) :
    letI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
    ∃ (e : Additive ↥hyp.P ≃+ GaloisField hyp.p hyp.q)
      (μ : ↥hyp.U →* (GaloisField hyp.p hyp.q)ˣ),
      Function.Injective μ ∧
      ∀ (v : ↥hyp.U) (x : ↥hyp.P),
        e (Additive.ofMul
            (⟨(v : G) * (x : G) * (v : G)⁻¹, hyp.conj_mem_P v x⟩ : ↥hyp.P))
          = ((μ v : (GaloisField hyp.p hyp.q)ˣ) : GaloisField hyp.p hyp.q) *
            e (Additive.ofMul x) := by
  classical
  let : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
      (hyp.toTypesIIIIIIVSetupS hG)
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
      (hyp.mkSection11CharacterDataS hG chief) with hA | hB
  · obtain ⟨caseA⟩ := hA
    obtain ⟨hq, hu⟩ := hcaseAParams caseA
    exact
      (caseA_false_of_parameters_and_typeIOverNormalizerData
        hG hyp caseA hc hq hu data).elim
  · obtain ⟨caseB⟩ := hB
    exact caseB_exists_sSide_galoisField_repr_of_c_eq_one
      hG hyp caseB hc

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_PairingCoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- The zeta family of `h78` is the placed induced family (definitional). -/
theorem h78_zeta_eq (i : Fin (data.n + 1)) :
    (data.h78 hG).hyp76.zeta i = data.zeta i := rfl

/-- The distinguished index of `h78` is `0` (definitional). -/
theorem h78_zetaDistinct_eq : (data.h78 hG).zetaDistinct = 0 := rfl

/-- The principal index of `h78` is `ind1H` (definitional). -/
theorem h78_ind1H_eq : (data.h78 hG).ind1H = data.ind1H := rfl

/-- The kernel of `h78`'s (7.6) layer is the Fitting kernel (definitional). -/
theorem h78_H_eq : (data.h78 hG).hyp76.H = data.kernel := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is irreducible** (Frobenius kernel induction,
[Is] Thm 6.34). -/
theorem h78_zeta_irreducible :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) := by
  have := data.kernelIn_normal
  rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **Each `ζ_i^ν` (`i ≠ ind1H`) is a unit-norm virtual character.** -/
theorem nu_zeta_norm_one {i : Fin (data.n + 1)} (hi : i ≠ (data.h78 hG).ind1H) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)) = 1 := by
  have := data.kernelIn_normal
  rw [(data.h78 hG).nu_isometry i i hi hi]
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial (by rw [← data.h78_ind1H_eq hG]; exact hi))
  exact IsIrreducibleCharacter.inner_self_eq_one hirr

/-- **Each nontrivial family member induces irreducibly** (general-index form of
`h78_zeta_irreducible`). -/
theorem zeta_irreducible_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
  have := data.kernelIn_normal
  rw [data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
    (data.theta_ne_trivial hi)

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_PairingBessel.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- `e = [L : H]` as the `subgroupOf` index (bundle form). -/
theorem complementIndex_eq :
    (data.h78 hG).complementIndex = (data.kernelIn).index :=
  complementIndex_eq_subgroupOf_index (data.h78 hG)

/-- `h = |H|` (bundle form). -/
theorem kernelOrder_eq :
    (data.h78 hG).kernelOrder = Nat.card ↥data.kernelIn := by
  rw [show (data.h78 hG).kernelOrder = Nat.card data.kernel from rfl]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.kernel_le).toEquiv).symm

/-- **`ζ_{ind1H}(1) = e`** (the induced principal degree). -/
theorem zeta_ind1H_apply_one :
    (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) (1 : ↥L)
      = ((data.h78 hG).complementIndex : ℂ) := by
  have := data.kernelIn_normal
  rw [data.complementIndex_eq hG]
  change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ) (1 : ↥L)
    = ((data.kernelIn).index : ℂ)
  rw [data.triv]
  exact induce_trivialChar_apply_eq_index data.kernelIn (Subgroup.one_mem _)

/-- **`‖ζ_{ind1H}‖² = e`** (the induced principal norm). -/
theorem zeta_ind1H_normSq :
    ClassFunction.inner ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H))
      ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H))
      = ((data.h78 hG).complementIndex : ℂ) := by
  have := data.kernelIn_normal
  rw [data.complementIndex_eq hG]
  change ClassFunction.inner
      (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ))
      (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ))
    = ((data.kernelIn).index : ℂ)
  rw [data.triv]
  exact induce_trivialChar_normSq_eq_index data.kernelIn

/-- **`ζ_0(1) = e`** (the distinguished degree, bundle form). -/
theorem zeta_zero_apply_one :
    (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.h78 hG).complementIndex : ℂ) := by
  rw [data.complementIndex_eq hG]
  exact data.deg0

/-- **The (7.8) source-side norm evaluation** `‖Ind 1_H − ζ‖² = e + 1`. -/
theorem sourceDiffNormEvaluation :
    (data.h78 hG).SourceDiffNormEvaluation := by
  have := data.kernelIn_normal
  refine (data.h78 hG).sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
    (data.zeta_ind1H_normSq hG) ?_ ?_ (data.h78_zeta_irreducible hG)
  · exact induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj 0 data.ind1H
      (Ne.symm data.ind1H_ne_zero)
  · exact induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj data.ind1H 0
      data.ind1H_ne_zero

set_option backward.isDefEq.respectTransparency false in
/-- **The (1.5.d) family degree-square sum** in the `star` form consumed by the
(7.8.b) `NormEstimates` producer: `Σ_{i ≠ ind1H} ζ_i(1)·(ζ_i(1))*/‖ζ_i‖² = (h−1)·e`. -/
theorem degree_sum_star :
    (∑ i ∈ (Finset.univ.erase (data.h78 hG).ind1H),
        (data.h78 hG).hyp76.zeta i (1 : ↥L)
          * star ((data.h78 hG).hyp76.zeta i (1 : ↥L)) /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i))
      = (((data.h78 hG).kernelOrder : ℂ) - 1) * ((data.h78 hG).complementIndex : ℂ) := by
  have := data.kernelIn_normal
  have hstar : ∀ i ∈ Finset.univ.erase (data.h78 hG).ind1H,
      (data.h78 hG).hyp76.zeta i (1 : ↥L)
          * star ((data.h78 hG).hyp76.zeta i (1 : ↥L)) /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i)
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) ^ 2 /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i) := by
    intro i _
    have hreal : star ((data.h78 hG).hyp76.zeta i (1 : ↥L))
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) := by
      rw [data.h78_zeta_eq]
      exact induce_apply_one_star data.kernelIn (data.θ i)
    rw [hreal, sq]
  have h := family_degree_sum data.kernelIn data.θ data.inj data.cover data.ind1H data.triv
  calc (∑ i ∈ (Finset.univ.erase (data.h78 hG).ind1H),
        (data.h78 hG).hyp76.zeta i (1 : ↥L)
          * star ((data.h78 hG).hyp76.zeta i (1 : ↥L)) /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i))
      = ∑ i ∈ (Finset.univ.erase (data.h78 hG).ind1H),
          (data.h78 hG).hyp76.zeta i (1 : ↥L) ^ 2 /
            ClassFunction.inner ((data.h78 hG).hyp76.zeta i)
              ((data.h78 hG).hyp76.zeta i) := Finset.sum_congr rfl hstar
    _ = ((data.kernelIn).index : ℂ) * ((Nat.card ↥data.kernelIn : ℂ) - 1) := h
    _ = (((data.h78 hG).kernelOrder : ℂ) - 1) * ((data.h78 hG).complementIndex : ℂ) := by
        rw [data.complementIndex_eq hG, data.kernelOrder_eq hG]
        ring

/-- **`2e + 1 ≤ h`** (`smallIndex`): the Frobenius kernel of odd order is more than
twice the complement. -/
theorem smallIndex : (data.h78 hG).smallIndex := by
  have := data.kernelIn_normal
  have hKodd : Odd (Nat.card ↥data.kernelIn) :=
    (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)).of_dvd_nat
      (Subgroup.card_subgroup_dvd_card _)
  have hCodd : Odd (Nat.card ↥data.C) :=
    (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)).of_dvd_nat
      (Subgroup.card_subgroup_dvd_card data.C)
  have hfrobB := OddOrder.Peterfalvi.S14.frobenius_two_mul_card_complement_add_one_le_card_kernel
    data.hFrob hKodd hCodd data.hFrob.ne_bot_kernel
  change 2 * (data.h78 hG).complementIndex + 1 ≤ (data.h78 hG).kernelOrder
  have hcompl : Nat.card ↥data.kernelIn * Nat.card ↥data.C = Nat.card ↥L :=
    data.hFrob.isComplement.card_mul_card
  have hce : (data.h78 hG).complementIndex = Nat.card ↥data.C := by
    change Nat.card ↥L / Nat.card data.kernel = Nat.card ↥data.C
    rw [show Nat.card data.kernel = Nat.card ↥data.kernelIn from
        (data.kernelOrder_eq hG) ▸ rfl,
      ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
  rw [data.kernelOrder_eq hG, hce]
  exact hfrobB

/-- `d_{ind1H} = 1` for the constructor-computed `hyp76.d`. -/
theorem hyp76_d_ind1H_eq_one : (data.h78 hG).hyp76.d ((data.h78 hG).ind1H) = 1 := by
  have := data.kernelIn_normal
  change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ) (1 : ↥L) /
      ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) = 1
  rw [← data.zeta_deg_match, div_self (induce_apply_one_ne_zero _ (data.θ 0))]

/-- The coherence agreement in constructor-computed `d`/`psiSupp` form (the
`hagree'` input of the `cCoeff` evaluations). -/
theorem hagree_hyp76 (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∀ i : Fin (data.n + 1), i ≠ 0 → i ≠ (data.h78 hG).ind1H →
      (data.h78 hG).hyp76.hyp71.τ ((data.h78 hG).hyp76.psiSupp i)
        = (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
          - (data.h78 hG).hyp76.d i • (data.h78 hG).nu ((data.h78 hG).hyp76.zeta 0) := by
  have := data.kernelIn_normal
  intro i hi0 hii
  have hz0 : ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (data.θ 0)
  have hdeq : (data.h78 hG).hyp76.d i = data.d i := by
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) = data.d i
    rw [div_eq_iff hz0]; exact data.zeta_deg i
  have hsub : (data.h78 hG).hyp76.psiSupp i
      = (⟨data.zeta i - data.d i • data.zeta 0, data.psi_support hG i⟩ :
        OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ
          (typeIA L data.typeIHyp.typeI) L) := by
    apply Subtype.ext
    change data.zeta i - (data.h78 hG).hyp76.d i • data.zeta 0
      = data.zeta i - data.d i • data.zeta 0
    rw [hdeq]
  rw [hsub, hdeq]
  exact data.hagree hG i hi0 hii

/-- **The (7.8.b) quadratic norm identity** `‖ζ_0^{νρ}‖² = Q(a) + (1 − e/h)` for the
bundle (the `hzeta` input of `NormEstimates`), discharged from the Dade-family facts
exactly as in `zetaNuRhoNormSqGeOfDade`. -/
theorem zetaNuRhoNormSq_eq_normQuad (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).zetaNuRhoNormSq =
      (data.h78 hG).normQuadraticCorrection (data.betaDecomp hG) +
        (1 - ((data.h78 hG).complementIndex : ℝ) / ((data.h78 hG).kernelOrder : ℝ)) := by
  have := data.kernelIn_normal
  have hz0 : ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (data.θ 0)
  have hz0_compl : ClassFunction.induce data.kernelIn
      (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) = ((data.h78 hG).complementIndex : ℂ) :=
    data.zeta_zero_apply_one hG
  refine zetaNuRhoNormSq_eq_normQuad_of_facts (data.h78 hG) (data.betaDecomp hG) rfl
    (induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj) ?_ ?_ ?_ ?_ ?_
    (data.zeta_ind1H_normSq hG) (data.zeta_ind1H_apply_one hG) ?_
  · -- `c_{ind1H} = a − 1`.
    rw [cCoeff_nu_zeta_zero_ind1H_eq (data.h78 hG) (data.h78 hG).nu rfl
      (data.hyp76_d_ind1H_eq_one hG)]
    show ClassFunction.inner (data.h78 hG).beta
        ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta 0)) = ((data.betaDecomp hG).a : ℂ) - 1
    have ha := Classical.choose_spec (exists_betaDecomp_a (data.h78 hG)
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (data.θ 0).property.mem_ZIrr))
      (data.coh.extension_mem_ZIrr _ (Submodule.subset_span
        (data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)))))
    have hBDa : ((data.betaDecomp hG).a : ℂ)
        = ClassFunction.inner (data.h78 hG).beta
            ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta 0)) + 1 := ha
    rw [hBDa]; ring
  · -- `c_i = −d_i` for the non-distinguished, non-`ind1H` indices.
    exact fun i hi0 hii => cCoeff_nu_zeta_zero_eq_neg_d (data.h78 hG).hyp76 (data.h78 hG).nu
      (data.hagree_hyp76 hG) (data.h78 hG).nu_isometry (Ne.symm data.ind1H_ne_zero)
      (fun i hi => induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj i 0 hi)
      data.zeta_zero_norm_one i hi0 hii
  · -- `d_i` is real.
    intro i
    change star (ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L))
      = ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L)
    rw [star_div₀, induce_apply_one_star, induce_apply_one_star]
  · -- `ζ_i(1)` is real.
    exact fun i => induce_apply_one_star data.kernelIn (data.θ i)
  · -- `d_i = ζ_i(1)/e`.
    intro i
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L)
      = ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L)
        / ((data.h78 hG).complementIndex : ℂ)
    rw [hz0_compl]
  · -- The `Ioi`-sum `G = e(h−1) − e²`.
    rw [data.complementIndex_eq hG,
      show ((data.h78 hG).kernelOrder : ℂ) = (Nat.card ↥data.kernelIn : ℂ) from by
        rw [data.kernelOrder_eq hG]]
    exact family_degree_sum_Ioi data.kernelIn data.θ data.inj data.cover data.ind1H
      data.ind1H_ne_zero data.triv
      (by rw [← data.complementIndex_eq hG]; exact hz0_compl) data.zeta_zero_norm_one

/-- **The (7.8.b) `NormEstimates` of the bundle**: both the `ζ`-lower bound
`1 − e/h ≤ ‖ζ_0^{νρ}‖²` and the residual bound `‖Γ‖² ≤ e − 1`. -/
theorem normEstimates (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).NormEstimates (data.betaDecomp hG) := by
  have := data.kernelIn_normal
  refine (data.h78 hG).normEstimates_of_irreducible_source_data (data.betaDecomp hG)
    (data.sourceDiffNormEvaluation hG) ?_ ?_ (data.zeta_zero_apply_one hG)
    (data.degree_sum_star hG) (data.zetaNuRhoNormSq_eq_normQuad hG)
  · -- Every non-`ind1H` member is irreducible.
    intro i hi
    exact data.zeta_irreducible_at hG (Finset.mem_erase.mp hi).1
  · -- Distinct indices give distinct characters.
    intro i _ j _ hij heq
    exact hij (data.inj heq)

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_G0Coprime.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.11.3), the `W`-orbit bridge**: an element avoiding the conjugates of the
regular set `W − (W₁ ∪ W₂)`, of `P#`, and of `Q#` avoids the conjugates of all of `W#`.
Indeed `W = W₁ × W₂` (cyclic join with trivial intersection), so
`W# = (W − (W₁∪W₂)) ⊔ W₁# ⊔ W₂#`, and the singular parts are absorbed by the kernels:
`W₁ ≤ Q` (`S15.W1_le_Q`) and `W₂ ≤ P` (`S15.W2_le_P`).  This reconciles the §16 generic set
(which excludes only the regular `W`-orbit) with Peterfalvi's (14.11.3) set (which excludes
`(W#)^G`). -/
theorem not_mem_conjClassSet_sharp_W [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) {g : G}
    (hreg : g ∉ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))))
    (hP : g ∉ conjClassSet (sharpSubgroup hyp.P))
    (hQ : g ∉ conjClassSet (sharpSubgroup hyp.Q)) :
    g ∉ conjClassSet (sharpSubgroup hyp.W) := by
  rintro ⟨w, ⟨hwW, hwne⟩, y, rfl⟩
  let := hyp.W_cyclic
  let : CommGroup ↥hyp.W := IsCyclic.commGroup
  have hW1le : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2le : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  -- decompose `w = x · z` with `x ∈ W₁`, `z ∈ W₂` inside the commutative `W`
  have hwmem : (⟨w, hwW⟩ : ↥hyp.W) ∈
      (hyp.W1.subgroupOf hyp.W) ⊔ (hyp.W2.subgroupOf hyp.W) := by
    have h1 : (hyp.W1 ⊔ hyp.W2).subgroupOf hyp.W = ⊤ := by
      rw [← hyp.W_eq_join, Subgroup.subgroupOf_self]
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, h1]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, z, hz, hxz⟩ := Subgroup.mem_sup.mp hwmem
  have hcoe : (x : G) * (z : G) = w := by
    have h := congrArg (Subtype.val) hxz
    simpa using h
  have hxW1 : (x : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp hx
  have hzW2 : (z : G) ∈ hyp.W2 := Subgroup.mem_subgroupOf.mp hz
  by_cases hx1 : x = 1
  · by_cases hz1 : z = 1
    · -- `w = 1`, contradicting `w ∈ W#`
      refine hwne ?_
      have hw1 : w = 1 := by rw [← hcoe, hx1, hz1]; simp
      simp [hw1]
    · -- `w = z ∈ W₂# ⊆ P#`
      refine hP ⟨w, ⟨?_, hwne⟩, y, rfl⟩
      have hwz : w = (z : G) := by rw [← hcoe, hx1]; simp
      exact hwz ▸ OddOrder.Peterfalvi.S15.W2_le_P hG hyp hzW2
  · by_cases hz1 : z = 1
    · -- `w = x ∈ W₁# ⊆ Q#`
      refine hQ ⟨w, ⟨?_, hwne⟩, y, rfl⟩
      have hwx : w = (x : G) := by rw [← hcoe, hz1]; simp
      exact hwx ▸ OddOrder.Peterfalvi.S15.W1_le_Q hG hyp hxW1
    · -- both parts nontrivial: `w` is regular
      refine hreg ⟨w, ⟨hwW, ?_⟩, y, rfl⟩
      rintro (hw1 | hw2)
      · -- `w ∈ W₁` forces `z ∈ W₁ ⊓ W₂ = ⊥`
        refine hz1 ?_
        have hzW1 : (z : G) ∈ hyp.W1 := by
          have hzeq : (z : G) = (x : G)⁻¹ * w := by
            rw [← hcoe]; group
          rw [hzeq]
          exact hyp.W1.mul_mem (hyp.W1.inv_mem hxW1) hw1
        have hbot : (z : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨hzW1, hzW2⟩
        rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
        exact Subtype.ext hbot
      · -- `w ∈ W₂` forces `x ∈ W₁ ⊓ W₂ = ⊥`
        refine hx1 ?_
        have hxW2 : (x : G) ∈ hyp.W2 := by
          have hxeq : (x : G) = w * (z : G)⁻¹ := by
            rw [← hcoe]; group
          rw [hxeq]
          exact hyp.W2.mul_mem hw2 (hyp.W2.inv_mem hzW2)
        have hbot : (x : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨hxW1, hxW2⟩
        rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
        exact Subtype.ext hbot

/-- **Peterfalvi (14.11.3), support half**: an element avoiding the conjugates of the regular
set `W − (W₁ ∪ W₂)`, of `P#`, and of `Q#` — i.e. any element of the generic set `G₀` off the
Dade support — has order prime to `pq`.  Assembles the `W`-orbit bridge with the two one-prime
cores.  This is the group-theoretic half of (14.11.3); the character half ((3.9.a/c) `η`-grid
integrality/pairing on `G₀`) consumes it through `EtaGenericData`. -/
theorem orderOf_coprime_pq_of_not_mem_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T)
    (hfrob : ∀ x ∈ sharpSubgroup hyp.P,
      derivedInG hyp.S ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.P)
    (hfrobT : ∀ x ∈ sharpSubgroup hyp.Q,
      derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.Q) {g : G}
    (hreg : g ∉ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))))
    (hP : g ∉ conjClassSet (sharpSubgroup hyp.P))
    (hQ : g ∉ conjClassSet (sharpSubgroup hyp.Q)) :
    Nat.Coprime (orderOf g) (hyp.p * hyp.q) := by
  have hW := not_mem_conjClassSet_sharp_W hG hyp hreg hP hQ
  exact Nat.Coprime.mul_right (orderOf_coprime_p_of_not_mem_conj hG hyp hfrob hW hP)
    (orderOf_coprime_q_of_not_mem_conj hG hyp hTII hfrobT hW hQ)

/-- **T-side field-model producer** (`(14.4)`-dual of `fieldNormalizerData_of_repr`): from the
`(9.7.b)` T-side field-algebra package — an additive field iso `e : Additive ↥Q ≃+ 𝔽_{q^p}`, a
norm-one Singer character `μ : ↥V →* 𝔽_{q^p}ˣ`, the `V`-conjugation closure `hVQ` on `Q`, and the
`(14.2)(a)`-dual equivariance `hcompat` (`e (ofMul (v x v⁻¹)) = μ v • e (ofMul x)`) — assemble the
injective realization `σ : F_{q^p} ⋊ V* →* G` with kernel `Q` and complement `V`, i.e. a
`TFieldModelData hyp`.  The `Q ⊓ V = ⊥` disjointness is the ungated `hyp.Q_inf_V_eq_bot` field.

This is the ungated heart of the T-side `(14.4)` reduction: it invokes the generic
`SemilinearFieldModel.fieldModelEmbedding` (`E = Q`, `C = V`, `r = q`, `s = p`), routing the lift
compatibility through the generic `hcompatLift_of_equivariant`.  Carries no `sorry`; its only
external inputs are the field-algebra data `(e, μ, hcompat)`, which the `(9.7.b)` resolution for
`T` (`exists_field_semilinear` + Singer, issue-9000 sphere) supplies. -/
theorem tFieldModelData_of_repr (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (e : letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
         Additive ↥hyp.Q ≃+ GaloisField hyp.q hyp.p)
    (μ : letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
         ↥hyp.V →* (GaloisField hyp.q hyp.p)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.q hyp.p)
    (hVQ : ∀ (v : ↥hyp.V) (x : ↥hyp.Q), (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.Q)
    (hcompat : letI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
         ∀ (v : ↥hyp.V) (x : ↥hyp.Q),
           e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hVQ v x⟩ : ↥hyp.Q))
             = ((μ v : (GaloisField hyp.q hyp.p)ˣ) : GaloisField hyp.q hyp.p) *
                 e (Additive.ofMul x)) :
    Nonempty (TFieldModelData hyp) := by
  let : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  have hcompatLift :=
    OddOrder.RepresentationTheory.SemilinearFieldModel.hcompatLift_of_equivariant
      e μ hμ_inj hμ_range hVQ hcompat
  obtain ⟨sigma, hinj, hker, hcomp⟩ :=
    OddOrder.RepresentationTheory.SemilinearFieldModel.fieldModelEmbedding
      e μ hμ_inj hμ_range hcompatLift hyp.Q_inf_V_eq_bot
  exact ⟨{ sigma := sigma
           sigma_injective := hinj
           sigma_Q_eq_Q := hker
           sigma_V_eq_V := hcomp }⟩

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S15_CaseBReducibleCoherence.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
/-- **`ℤ[𝒮]`-elements are supported in `A(S) ∪ {1}`** (issue 2035, the `zSpan`-closure of the
member-level honest (4.7) support fact `sSet_member_support_subset`).  Support is subadditive
under the lattice operations, so the union bound survives arbitrary `ℤ`-combinations. -/
theorem Hypothesis.zSpan_sSet_support_subset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupS hG))) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S ∪ {1} := by
  have : Fintype G := Fintype.ofFinite G
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hyp.sSet_member_support_subset hG hx
  | zero => simp
  | add x y _ _ hx hy =>
      exact (ClassFunction.support_add_subset x y).trans (Set.union_subset hx hy)
  | smul z x _ hx =>
      refine subset_trans ?_ hx
      rw [← Int.cast_smul_eq_zsmul ℂ z x]
      exact ClassFunction.support_smul_subset _ x

open OddOrder.Peterfalvi.S11 in
/-- **Degree-`0` elements of `ℤ[𝒮]` are `A(S)`-supported** (issue 2035, the (13.2.e)-input
support step for the `tau1S_apply_induce_sub` supply): a `ℤ`-combination of `𝒮`-members that
vanishes at `1` has its support inside the honest Dade support `A(S)` — the `{1}`-corner of
`zSpan_sSet_support_subset` is exactly the vanishing degree. -/
theorem Hypothesis.zSpan_sSet_degree_zero_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupS hG)))
    (hφ1 : φ (1 : ↥hyp.S) = 0) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
  have : Fintype G := Fintype.ofFinite G
  intro z hz
  rcases hyp.zSpan_sSet_support_subset hG hφ hz with h | h
  · exact h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact absurd hφ1 hz

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseACoherence.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c), the `μ`-column formula for `τ₁ = tau1S_ofHonest`** (issue 2035; Coq
`FTtypeP_coherence`, `PFsection13.v:347`): the (9.11)-coherent extension sends every reducible
`μ`-column sum `μ_j = ∑_i μ_{ij}` (`j ≠ 0`) to the aligned `η`-column sum `∑_i η_{ij}` — either
uniformly, or (the `p = 3` sign-flip exception) with a global negative sign and the two nonzero
columns swapped.  The `.choose_spec` of the pinned carrier `sSet_coherent_indS_A_pinned`; this is
the exact shape of the `CharacterDegreeData.mu_tau1_formula` field (`Machinery135`). -/
theorem Hypothesis.tau1S_ofHonest_muColumn_formula [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    (∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = ∑ i : Fin hyp.q, hyp.eta i j) ∨
    (hyp.p = 3 ∧ ∀ j j' : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      j' ≠ ⟨0, hyp.p_prime.pos⟩ → j ≠ j' →
      hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = -∑ i : Fin hyp.q, hyp.eta i j') :=
  (hyp.sSet_coherent_indS_A_pinned hG hnoV chief).choose_spec

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a)+(13.3.c), the distinguished `μ`-column for `τ₁ = tau1S_ofHonest`**
(issue 2035): a column `j ≠ 0` whose sum is induced from a linear character of `H = PC`
((13.3.a), `mu_j_isIndPC`) and whose `τ₁`-image is `±∑_i η_{i1}` — the (13.3.c) formula routed to
the `η`-column `1` (`j = 1, δ = 1` in the clean branch; the `p = 3` sign-flip exception takes
`j = 2, δ = -1`).  This is the honest supply of the `CharacterDegreeData.mu_col_tau1_eta_col_one`
field. -/
theorem Hypothesis.tau1S_ofHonest_mu_col_eta_col_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    ∃ (j : Fin hyp.p) (δ : ℤ) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      j ≠ ⟨0, hyp.p_prime.pos⟩ ∧
      (δ = 1 ∨ δ = -1) ∧
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
      (∑ i : Fin hyp.q, hyp.mu i j) = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
      hyp.tau1S_ofHonest hG hnoV chief (∑ i : Fin hyp.q, hyp.mu i j)
        = (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by
  classical
  have := hyp.finiteG
  have hp1 : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  rcases hyp.tau1S_ofHonest_muColumn_formula hG hnoV chief with hclean | ⟨hp3, hflip⟩
  · -- clean branch: `j = 1`, `δ = 1`
    obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG ⟨1, hyp.p_prime.one_lt⟩ hp1
    exact ⟨⟨1, hyp.p_prime.one_lt⟩, 1, θ, hp1, Or.inl rfl, hθirr, hθ1, hθeq,
      by rw [hclean ⟨1, hyp.p_prime.one_lt⟩ hp1]; push_cast; rw [one_smul]⟩
  · -- `p = 3` sign-flip branch: `j = 2`, `δ = -1`
    have h2lt : 2 < hyp.p := by omega
    have hj2 : (⟨2, h2lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
      intro h; exact absurd (congrArg Fin.val h) (by norm_num)
    have hne : (⟨2, h2lt⟩ : Fin hyp.p) ≠ ⟨1, hyp.p_prime.one_lt⟩ := by
      intro h; exact absurd (congrArg Fin.val h) (by norm_num)
    obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG ⟨2, h2lt⟩ hj2
    refine ⟨⟨2, h2lt⟩, -1, θ, hj2, Or.inr rfl, hθirr, hθ1, hθeq, ?_⟩
    rw [hflip ⟨2, h2lt⟩ ⟨1, hyp.p_prime.one_lt⟩ hj2 hp1 hne]
    push_cast
    rw [neg_one_smul]

open scoped FiniteInduce in
/-- **Type-alignment probe for the (13.3) `τ₁` route** (issue 2035 step 4 verification): confirms
`coherent_H0Cprime_S` obtains and its `.extension` is definitionally `tau1S_ofHonest`, of the
expected `IntegralCharacterMap ↥S G` type; and that `extends_on_supported` gives
`τ₁ φ = Ind_S^G φ` on the supported span (`tau1S_apply_induce` on the family) — the input to the
(13.3) `tau1S_apply_induce_sub` / `tau1S_inner_induce` / `tau1S_induce_mem_ZIrr` fields. -/
theorem Hypothesis.tau1S_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (φ : ClassFunction ↥hyp.S ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport) :
    hyp.tau1S_ofHonest hG hnoV chief φ = ClassFunction.induce hyp.S φ := by
  have h := (hyp.coherent_H0Cprime_S hG hnoV chief).extends_on_supported φ hφ
  -- `.extension φ = chars.tau φ = indS φ = Ind_S^G φ`
  simpa [Hypothesis.tau1S_ofHonest, Hypothesis.mkSection11CharacterDataS_honest,
    Hypothesis.indS_apply] using h

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ isometry on the `H`-induced family** (issue 2035 step 5a): `τ₁ = tau1S_ofHonest`
preserves inner products of `Ind_{PC}^S θ` for irreducible `θ` of `H = PC` with `P ⊄ Ker θ`.  From
the coherence field `extension_inner_eq` (isometric on all of `ℤ[𝒮]`) together with the family
membership `induce_H_mem_zSpan_S`.  This is the honest engine for the `CharacterDegreeData`
`tau1S_inner_induce` field (with the `P ⊄ Ker` hypothesis the (13.3) consumers actually satisfy —
`μ_j`, `λ` all have `P ⊄ Ker`). -/
theorem Hypothesis.tau1S_ofHonest_inner_induce [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    ClassFunction.inner
        (hyp.tau1S_ofHonest hG hnoV chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
        (hyp.tau1S_ofHonest hG hnoV chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
      = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  exact (hyp.coherent_H0Cprime_S hG hnoV chief).extension_inner_eq _ _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)
    (hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P)

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ sends the `H`-induced family into `ℤ[Irr G]`** (issue 2035 step 5a): for
irreducible `θ` of `H = PC` with `P ⊄ Ker θ`, `τ₁ (Ind_{PC}^S θ) ∈ ℤ[Irr G]`.  From the coherence
field `extension_mem_ZIrr` (virtual-character codomain on all of `ℤ[𝒮]`) and the family membership
`induce_H_mem_zSpan_S`.  Honest engine for the `CharacterDegreeData` `tau1S_induce_mem_ZIrr`
field. -/
theorem Hypothesis.tau1S_ofHonest_induce_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    hyp.tau1S_ofHonest hG hnoV chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G :=
  (hyp.coherent_H0Cprime_S hG hnoV chief).extension_mem_ZIrr _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)

open scoped FiniteInduce in
/-- **(13.2.e)+(7.2), the τ₁-extension semantics on `H`-induced differences** (issue 2035, the
honest supply for the `CharacterDegreeData.tau1S_apply_induce_sub` field): for irreducible
characters `θ, θ'` of `H = PC` with `P ⊄ Ker` (the guard the (13.5) proof carries — Peterfalvi
converts `(ζ_i − ζ_0)^{τ}` to `Ind_S^G` *only* for the `𝒮₁`-members `i ≤ n`, the `P`-kernel side
staying as the unknown `α`), `τ₁` agrees with `Ind_S^G` on the difference `Ind θ − Ind θ'`.

Assembly: both inductions lie in `ℤ[𝒮]` (`induce_H_mem_zSpan_S`, the (1.5.a) membership); `H` is
abelian ((13.2.a)) so both are degree `uq` and the difference vanishes at `1`; hence the
difference is `A(S)`-supported (`zSpan_sSet_degree_zero_support`) and `extends_on_supported`
evaluates `τ₁` as `Ind_S^G` there. -/
theorem Hypothesis.tau1S_ofHonest_apply_induce_sub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    hyp.tau1S_ofHonest hG hnoV chief
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
          - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
      = ClassFunction.induce hyp.S
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
            - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  have := hyp.finiteG
  -- `ℤ[𝒮]` membership of both inductions ((1.5.a))
  have hmem := hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP
  have hmem' := hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P
  have hsub : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
      ∈ OddOrder.Peterfalvi.S07.zSpan
          (OddOrder.Peterfalvi.S11.sSet (hyp.toTypesIIIIIIVSetupS hG)) :=
    Submodule.sub_mem _ hmem hmem'
  -- `H = PC` abelian ((13.2.a)): both inducing characters are linear, the difference has degree 0
  have hHcomm : IsMulCommutative ↥(hyp.H.subgroupOf hyp.S) := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hθ1 : θ 1 = 1 :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative hθ
  have hθ'1 : θ' 1 = 1 :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative hθ'
  have hdeg : (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') (1 : ↥hyp.S) = 0 := by
    rw [ClassFunction.sub_apply,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, hθ'1, sub_self]
  -- `A(S)`-support of the degree-0 difference, then the (13.2.d) extension evaluates as `Ind`
  exact hyp.tau1S_ofHonest_extends_on_supported hG hnoV chief _
    ⟨hsub, hyp.zSpan_sSet_degree_zero_support hG hsub hdeg⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁`-images of `ℤ[𝒮 ∩ Irr S]` are orthogonal to the `η`-grid** (Peterfalvi
(4.1)+(5.3.b), issue 2035): span induction over the (5.3.b) crux
`coherentIndS_image_inner_eta_eq_zero` — `τ₁` is `ℤ`-linear and the inner product is linear in
the first slot, so the member-level grid-orthogonality extends to the integral span of the
irreducible members. -/
theorem Hypothesis.tau1S_ofHonest_zSpanIrr_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q) (j : Fin hyp.p)
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥hyp.S ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) ∧
        OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ}) :
    ClassFunction.inner (hyp.tau1S_ofHonest hG hnoV chief φ) (hyp.eta i j) = 0 := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  induction hφ using Submodule.span_induction with
  | mem ζ hζ =>
      exact coherentIndS_image_inner_eta_eq_zero hG hnoV hyp
        (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG))
        (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG))
        (fun ζ' hζ' => by
          rw [show ζ' - (ζ' : ClassFunction ↥hyp.S ℂ).conj
              = -((ζ' : ClassFunction ↥hyp.S ℂ).conj - ζ') from (neg_sub _ _).symm,
            ClassFunction.support_neg]
          exact hyp.sSet_member_conjDiff_supported hG hζ')
        (hyp.coherent_H0Cprime_S hG hnoV chief) hζ.1 hζ.2 i j
  | zero => rw [map_zero, OddOrder.RepresentationTheory.ClassFunction.inner_zero_left]
  | add x y _ _ hx hy =>
      rw [map_add, OddOrder.RepresentationTheory.ClassFunction.inner_add_left, hx, hy, add_zero]
  | smul z x _ hx =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ z,
        OddOrder.RepresentationTheory.ClassFunction.inner_smul_left, hx, mul_zero]

open scoped FiniteInduce in
/-- **(4.1)+(5.3.b) honest supply for the `tau1S_induce_inner_eta` field** (issue 2035/9094): for
an irreducible `θ ∈ Irr H` (`H = PC`, `P ⊄ Ker θ`) whose induction `Ind_{PC}^S θ` is irreducible,
the `τ₁`-image is orthogonal to the whole `η`-grid.  Composition of the `ℤ[𝒮 ∩ Irr S]`
membership (`induce_H_mem_zSpan_sSet_irr`, Coq `S1cases` irreducible branch) with the span-level
grid orthogonality (`tau1S_ofHonest_zSpanIrr_inner_eta`). -/
theorem Hypothesis.tau1S_ofHonest_induce_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q) (j : Fin hyp.p)
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) :
    ClassFunction.inner (hyp.eta i j)
      (hyp.tau1S_ofHonest hG hnoV chief
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0 := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    hyp.tau1S_ofHonest_zSpanIrr_inner_eta hG hnoV chief i j
      (hyp.induce_H_mem_zSpan_sSet_irr hG θ hθ hθP hind),
    star_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁`-images of the full lattice `ℤ[𝒮]` are orthogonal to the `η`-column `0`**
(Peterfalvi (4.1)+(5.3.b) + (13.3.c), issue 2035): span induction over the *mixed* family —
an irreducible member is grid-orthogonal by the (5.3.b) crux; a reducible member is a
`μ`-column (`sSet_reducible_eq_muColumnSum`) whose `τ₁`-image is a (signed) *nonzero*-column
`η`-sum (`tau1S_ofHonest_muColumn_formula`), orthogonal to column `0` by the grid
orthonormality. -/
theorem Hypothesis.tau1S_ofHonest_zSpan_inner_eta_col_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q)
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupS hG))) :
    ClassFunction.inner (hyp.tau1S_ofHonest hG hnoV chief φ)
      (hyp.eta i ⟨0, hyp.p_prime.pos⟩) = 0 := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  induction hφ using Submodule.span_induction with
  | mem ζ hζ =>
      by_cases hζirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter ζ
      · -- irreducible member: full grid orthogonality by the (5.3.b) crux
        exact coherentIndS_image_inner_eta_eq_zero hG hnoV hyp
          (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG))
          (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG))
          (fun ζ' hζ' => by
            rw [show ζ' - (ζ' : ClassFunction ↥hyp.S ℂ).conj
                = -((ζ' : ClassFunction ↥hyp.S ℂ).conj - ζ') from (neg_sub _ _).symm,
              ClassFunction.support_neg]
            exact hyp.sSet_member_conjDiff_supported hG hζ')
          (hyp.coherent_H0Cprime_S hG hnoV chief) hζ hζirr i ⟨0, hyp.p_prime.pos⟩
      · -- reducible member: a nonzero `μ`-column, sent by (13.3.c) into a nonzero `η`-column
        obtain ⟨j, hj, rfl⟩ := hyp.sSet_reducible_eq_muColumnSum hG hζ hζirr
        rcases hyp.tau1S_ofHonest_muColumn_formula hG hnoV chief with hclean | ⟨-, hflip⟩
        · rw [hclean j hj, OddOrder.RepresentationTheory.inner_sum_left]
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [hyp.eta_orthonormal l i j ⟨0, hyp.p_prime.pos⟩, if_neg (fun h => hj h.2)]
        · have h2lt : 2 < hyp.p := by have := hyp.three_le_p; omega
          set j1 : Fin hyp.p := ⟨1, hyp.p_prime.one_lt⟩ with hj1
          set j2 : Fin hyp.p := ⟨2, h2lt⟩ with hj2
          have hj10 : j1 ≠ ⟨0, hyp.p_prime.pos⟩ := by
            intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          have hj20 : j2 ≠ ⟨0, hyp.p_prime.pos⟩ := by
            intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          -- route through the other nonzero column `j' ≠ 0, j' ≠ j`
          obtain ⟨j', hj'0, hjj'⟩ : ∃ j' : Fin hyp.p,
              j' ≠ ⟨0, hyp.p_prime.pos⟩ ∧ j ≠ j' := by
            rcases eq_or_ne j j1 with rfl | hne1
            · exact ⟨j2, hj20, fun h => absurd (congrArg Fin.val h) (by norm_num)⟩
            · exact ⟨j1, hj10, hne1⟩
          rw [hflip j j' hj hj'0 hjj',
            OddOrder.RepresentationTheory.ClassFunction.inner_neg_left,
            OddOrder.RepresentationTheory.inner_sum_left]
          rw [Finset.sum_eq_zero fun l _ => by
            rw [hyp.eta_orthonormal l i j' ⟨0, hyp.p_prime.pos⟩, if_neg (fun h => hj'0 h.2)]]
          exact neg_zero
  | zero => rw [map_zero, OddOrder.RepresentationTheory.ClassFunction.inner_zero_left]
  | add x y _ _ hx hy =>
      rw [map_add, OddOrder.RepresentationTheory.ClassFunction.inner_add_left, hx, hy, add_zero]
  | smul z x _ hx =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ z,
        OddOrder.RepresentationTheory.ClassFunction.inner_smul_left, hx, mul_zero]

open scoped FiniteInduce in
/-- **(4.1)+(5.3.b)+(13.3.c) honest supply for the `tau1S_induce_inner_eta_col_zero` field**
(issue 2035/9094): for *any* irreducible `θ ∈ Irr H` (`H = PC`, `P ⊄ Ker θ`) — the induction
`Ind_{PC}^S θ` may be irreducible or a `μ`-column — the `τ₁`-image is orthogonal to the
`η`-column `0`.  Composition of the `ℤ[𝒮]` membership (`induce_H_mem_zSpan_S`) with the
mixed-family column-`0` orthogonality (`tau1S_ofHonest_zSpan_inner_eta_col_zero`). -/
theorem Hypothesis.tau1S_ofHonest_induce_inner_eta_col_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q)
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.inner (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
      (hyp.tau1S_ofHonest hG hnoV chief
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0 := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    hyp.tau1S_ofHonest_zSpan_inner_eta_col_zero hG hnoV chief i
      (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP),
    star_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a) with the `P`-witness** (issue 2035 更新 #22, the guard the (13.5)
consumers thread): the inducing linear character `θ` of the nonzero `μ`-column sum
`μ_j = Ind_{PC}^S θ` has `P ⊄ Ker θ` — i.e. `μ_j ∈ 𝒮₁` in the sense of (13.5).

**Proof.**  `mu_j_isIndPC` supplies `θ`; if `P ⊆ Ker θ` then `P ⊆ Ker μ_j` by the elementary
half of (1.6.a) (`subsetCharacterKernel_induce_of_subgroupOf`, `P ⊴ S`).  But `μ_j ∈ 𝒮(H₀)`
(`mu_colSum_mem_sOf_H0`) is induced from an `S'`-source `χ ∈ 𝒳` with `P ⊄ Ker χ`, and the
converse of (1.6.a) ([Is] 2.21, `mem_characterKernel_of_mem_characterKernel_induce`, `S' ⊴ S`)
pushes `P ⊆ Ker μ_j` down to `P ⊆ Ker χ` — contradiction. -/
theorem Hypothesis.mu_j_isIndPC_not_ker [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
        (∑ i : Fin hyp.q, hyp.mu i j)
          = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
        ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
            Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel θ) := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨θ, hθirr, hθ1, hμeq⟩ := hyp.mu_j_isIndPC hG j hj
  refine ⟨θ, hθirr, hθ1, hμeq, fun hker => ?_⟩
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  -- the `S'`-level source: `μ_j = Ind_{HU}^S χ`, `χ ∈ 𝒳` (so `P ⊄ Ker χ`)
  obtain ⟨χ, hχ, hμeq'⟩ := OddOrder.Peterfalvi.S11.mem_sOf.mp
    (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)
  let : Fintype ↥(OddOrder.Peterfalvi.S11.huSub data) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(OddOrder.Peterfalvi.S11.huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hHUnorm : (OddOrder.Peterfalvi.S11.huSub data).Normal := by
    rw [OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data]
    infer_instance
  -- `P ⊴ S`, realised in `↥S`
  have hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
    have hPle : hyp.P ≤ hyp.S := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr ?_
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPH : hyp.P.subgroupOf hyp.S ≤ hyp.H.subgroupOf hyp.S :=
    Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
  -- (1.6.a) forward: `P ⊆ Ker θ` pushes up to `P ⊆ Ker μ_j`
  have hkerInd : OddOrder.Peterfalvi.S03.SubsetCharacterKernel
      ((hyp.P.subgroupOf hyp.S : Subgroup ↥hyp.S) : Set ↥hyp.S)
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) :=
    OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf hPH θ hker
  -- rewrite the induced character as the `S'`-stage induction
  have hInd_eq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      = ClassFunction.induce (OddOrder.Peterfalvi.S11.huSub data)
          (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ) := by
    rw [← hμeq, hμeq']
    exact OddOrder.Peterfalvi.S11.induceHU_eq_induce data _
  -- contradict `χ ∈ 𝒳`: `P (in HU) ⊆ Ker χ`
  apply hχ.1
  intro x hx
  have hxP : (x : ↥hyp.S) ∈ hyp.P.subgroupOf hyp.S := by
    have hx' : x ∈ (data.H.subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data) := hx
    have hPeq : data.H = hyp.P := by
      change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    rw [hPeq] at hx'
    exact Subgroup.mem_subgroupOf.mp hx'
  have hxkerInd : (x : ↥hyp.S) ∈ OddOrder.Peterfalvi.S03.characterKernel
      (ClassFunction.induce (OddOrder.Peterfalvi.S11.huSub data)
        (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ)) := by
    rw [← hInd_eq]
    exact hkerInd hxP
  have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
    χ.isIrreducible x.2 hxkerInd
  simpa using h

open scoped FiniteInduce in
/-- **The λ-free core producer** (issue 9094 RULING 案 A): every field of
`CharacterDegreeCore` from the landed engines — `τ₁ = tau1S_ofHonest` with its five guarded
field supplies, the (13.3.a) `𝒮₁`-witnessed `μ`-facts (`mu_j_isIndPC_not_ker`,
`tau1S_ofHonest_mu_col_eta_col_one`), the (13.3.c) `S`-side signs (`delta_eq_one_S`; the
δ′-half is restate-dropped from the field, issue 2035 #92 — supply stays in
`deltaPrime_eq_one_T`), and the (13.3.c) column formula
(`tau1S_ofHonest_muColumn_formula`). -/
noncomputable def Hypothesis.characterDegreeCore [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    CharacterDegreeCore hyp where
  tau1S := hyp.tau1S_ofHonest hG hnoV chief
  tau1T := hyp.indT
  tau1S_apply_induce_sub := fun θ θ' hθ hθ' hθP hθ'P =>
    hyp.tau1S_ofHonest_apply_induce_sub hG hnoV chief θ θ' hθ hθ' hθP hθ'P
  tau1S_inner_induce := fun θ θ' hθ hθ' hθP hθ'P =>
    hyp.tau1S_ofHonest_inner_induce hG hnoV chief θ θ' hθ hθ' hθP hθ'P
  tau1S_induce_mem_ZIrr := fun θ hθ hθP =>
    hyp.tau1S_ofHonest_induce_mem_ZIrr hG hnoV chief θ hθ hθP
  tau1S_induce_inner_eta := fun i j θ hθ hθP hind =>
    hyp.tau1S_ofHonest_induce_inner_eta hG hnoV chief i j θ hθ hθP hind
  tau1S_induce_inner_eta_col_zero := fun i θ hθ hθP =>
    hyp.tau1S_ofHonest_induce_inner_eta_col_zero hG hnoV chief i θ hθ hθP
  mu_col_tau1_eta_col_one := by
    obtain ⟨j, δ, θold, hj, hδ, -, -, -, hform⟩ :=
      hyp.tau1S_ofHonest_mu_col_eta_col_one hG hnoV chief
    obtain ⟨θ, hθirr, hθ1, hμeq, hθP⟩ := hyp.mu_j_isIndPC_not_ker hG j hj
    exact ⟨j, δ, θ, hj, hδ, hθirr, hθ1, hθP, hμeq, hform⟩
  mu_j_linear_induced := fun j hj => by
    obtain ⟨θ, hθirr, hθ1, hμeq, hθP⟩ := hyp.mu_j_isIndPC_not_ker hG j hj
    exact ⟨θ, hθirr, hθ1, hθP, hμeq⟩
  delta_eq_one := fun j => hyp.delta_eq_one_S hG j
  mu_tau1_formula := hyp.tau1S_ofHonest_muColumn_formula hG hnoV chief

/-- **The λ-free core, unconditionally** (issue 9094 RULING 案 A): `CharacterDegreeCore` is
inhabited for every (13.1) hypothesis — the (12.x) no-type-V fact supplies `hnoV`, and a chief
factor datum always exists. -/
theorem Hypothesis.characterDegreeCore_nonempty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (CharacterDegreeCore hyp) := by
  have := hyp.finiteG
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.toTypesIIIIIIVSetupS hG)
  exact ⟨hyp.characterDegreeCore hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG) chief⟩

open scoped FiniteInduce in
/-- **The conditional λ-cluster producer** (issue 9094 RULING 案 A, the (13.3.b) conditional
branch): a linear `θ ∈ Irr H` (`H = PC`) with `P ⊄ Ker θ` whose induction `Ind_{PC}^S θ` is
irreducible packages into `LambdaClusterData` — the degree is `[S:H]·1 = uq`
(`H_index_eq_uq`). -/
theorem Hypothesis.lambdaClusterData_of_irr_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ) (hθ1 : θ 1 = 1)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) :
    Nonempty (LambdaClusterData hyp) := by
  have := hyp.finiteG
  refine ⟨⟨ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ, hind, ?_, θ, hθ, hθ1, rfl, ?_⟩⟩
  · rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one,
      hyp.H_index_eq_uq hG]
  · obtain ⟨x, hxP, hxker⟩ := Set.not_subset.mp hθP
    exact ⟨x, Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxP), hxker⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayerCore.lean =====
namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

section

/-- **Peterfalvi (13.12), Core form**: the centralizer parameter `c` is one, using the
Core analytic inequality instead of the legacy norm-cascade carrier. -/
theorem CharacterDegreeCore.c_eq_one_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    hyp.c = 1 := by
  exact c_eq_one_of_analytic_inequality hG hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm pins)

/-- **Peterfalvi (13.13), Core form**: Clifford case (9.7.a) forces the sharp parameters,
with (13.10) supplied by the Core character-degree analysis. -/
theorem CharacterDegreeCore.caseA_parameters_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp)
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief)) :
    hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  exact caseA_parameters_of_analytic_inequality hG hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm pins) caseA

/-- **Peterfalvi (13.15), Core form**: Clifford case (9.7.b) determines the Singer
cyclotomic order of `u`, with (13.10) supplied by the Core character-degree analysis. -/
theorem CharacterDegreeCore.caseB_order_u_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp)
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief)) :
    (hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
      (¬ hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  exact caseB_order_u_of_analytic_inequality hG hyp
    (core.analytic_inequality_of_caseB_facts hG lam hD hv hQcomm pins) caseB

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The no-λ (Galois) branch of the `S`-side (13.3.b) facts** (issue 9094 RULING §2, faithful
bridging — introduced sorried, since proved): if `𝒮` contains no `uq`-degree `PC`-induced
irreducible (`¬ LambdaWitness`),
then by Pf (13.3.b) `M = S` is in case (9.7.b) with `C = ⊥` and `u = (p^q−1)/(p−1)` — the Galois
case.

Assembled from the §9-generic `caseB_of_no_irreducible_sOf_H0Cprime` (sorry-free) through the
S15↔S11 `Section11CharacterData` SOf-identification: an irreducible member of the `S`-instance
family `𝒮(H₀ ⊔ C')` is (13.3.a-style) a `uq`-degree `PC`-linear induced irreducible, i.e. a
`LambdaWitness`, and the `chars.C`/`chars.u` conclusion transports to `hyp.C`/`hyp.u`
(`toTypesIIIIIIVSetupS_cSub_eq_C`).  That identification is the deep (13.3.b) forward bridge
(S15↔S11, multi-session); until it lands this is the honest, precisely-named gate. -/
theorem S_caseB_facts_no_lambda [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hnolam : ¬ LambdaWitness hyp) :
    hyp.C = ⊥ ∧ hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1) := by
  have := hyp.finiteG
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  -- **(13.3.b) forward, the one isolated genuine gate**: an irreducible member of the `S`-instance
  -- family `𝒮(H₀ ⊔ C')` is a `uq`-degree `PC`-linear induced irreducible — a `LambdaWitness`.
  -- (The reducible members are `Ind_{HC}` linear by `caseB_reducible_sOf_H0_isIndHC`; the
  -- irreducible ones — the `λ`-candidates — need the (13.3.a)-for-irr characterization, the
  -- multi-session S15↔S11 assembly.)
  have hbridge : ∀ χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ → LambdaWitness hyp := by
    intro χ _hχmem _hχirr
    -- `set`-free case split: a `set data`/`set chars` here would split the (externally obtained)
    -- `chief` into a folded copy plus a stray `chief✝`, desyncing `_hχmem` from `caseB`.  Both
    -- branches are `set`-free standalone witnesses (`lambdaWitness_of_caseA` / `_of_caseB_member`),
    -- each doing its own `let data` internally, so hbridge passes one pristine `chief`.
    rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataS hG chief) with hA | hB
    · -- **caseA**: a `LambdaWitness` exists unconditionally (ignore `χ`) — the (9.8.c) degree-`qu`
      -- irreducible `Ind_{HU}^S(Ind_{HC}(hcPsi θ̄))` is `Ind_{PC}^S(linear irr)`.
      obtain ⟨caseA⟩ := hA
      exact lambdaWitness_of_caseA hG hyp chief caseA
    · -- **caseB** (Singer/Galois, `U` irreducible on `H̄`): the given irreducible `χ = Ind_{HU} ζ`
      -- (`ζ ∈ 𝒳(H₀C')`) is `Ind_{HC}(hcPsiPair θ̄ λ)` for a linear pair character
      -- (`caseB_xiOf_H0Cprime_eq_induce_hcPsiPair`); `lambdaWitness_of_caseB_member` flattens and
      -- transports it to the `Ind_{PC}(linear irr)` = `LambdaWitness` shape.
      obtain ⟨caseB⟩ := hB
      exact lambdaWitness_of_caseB_member hG hyp chief caseB _hχmem _hχirr
  have hno : ¬ ∃ χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    fun ⟨χ, hmem, hirr⟩ => hnolam (hbridge χ hmem hirr)
  obtain ⟨-, hCbot, hufull⟩ :=
    caseB_of_no_irreducible_sOf_H0Cprime hG
      (hyp.mkSection11CharacterDataS hG chief) hno
  refine ⟨?_, ?_⟩
  · -- `chars.C = cSub = hyp.C` (`toTypesIIIIIIVSetupS_cSub_eq_C`)
    rw [← hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]
    exact hCbot
  · -- transport `chars.u = (chief.p^data.q − 1)/(chief.p − 1)` to `hyp.u = (p^q − 1)/(p − 1)`
    rw [← hyp.mkSection11CharacterDataS_u_eq hG chief, hufull, hyp.chiefFactorS_p_eq hG chief,
      hyp.toTypesIIIIIIVSetupS_q_eq hG]

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.b) dichotomy, the `S`-side keystone producer** (issue 9094 RULING 案 A/§2):
either `𝒮` contains the honest λ-cluster (`Nonempty (LambdaClusterData hyp)`), or `M = S` is in
the Galois case (`C = ⊥`, `u = (p^q−1)/(p−1)`).  This is the producer every λ-independent
consumer of the legacy `character_degree_analysis` threads: the λ-branch supplies the
`LambdaClusterData` (against the unconditional `CharacterDegreeCore`), the no-λ branch supplies
the (13.10)-arithmetic inputs `C = ⊥ ∧ u = full`.

The case-split is `LambdaWitness hyp` (`Classical.em`): the λ-branch is
`lambdaClusterData_of_irr_witness`, the no-λ branch is `S_caseB_facts_no_lambda`. -/
theorem lambdaCluster_or_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (LambdaClusterData hyp) ∨
      (hyp.C = ⊥ ∧ hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  by_cases hlam : LambdaWitness hyp
  · obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := hlam
    exact Or.inl (hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind)
  · exact Or.inr (S_caseB_facts_no_lambda hG hyp hlam)

open scoped FiniteInduce in
/-- **Peterfalvi (13.12), swapped Core form**: `d = 1` without the legacy unconditional
character-degree carrier.  The swap's `ν`-grid is supplied honestly by the original `μ`-grid;
the λ-branch uses Core (13.10), while the no-λ branch already has the swap's `C = ⊥`. -/
theorem Hypothesis.d_eq_one_of_swapped_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) :
    hyp.d = 1 := by
  have hV : IsMulCommutative ↥hyp.V := hyp.isMulCommutative_V_unconditional hG
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T hG hyp
  let hyp' : Hypothesis (G := G) := hyp.swap hV Tdata hU hW1 hW2 pins
  have pins' : NuGridSupplyData hyp' :=
    hyp.nuGridSupply_swap hV Tdata hU hW1 hW2 pins
  obtain ⟨core'⟩ := hyp'.characterDegreeCore_nonempty hG
  have hc1 : hyp'.c = 1 := by
    rcases lambdaCluster_or_caseB hG hyp' with hlam | ⟨hCbot, _hu⟩
    · obtain ⟨lam'⟩ := hlam
      obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core' lam' pins'
      have hQcomm : IsMulCommutative ↥hyp'.Q :=
        IsMulCommutative.of_comm (hyp'.Q_elementaryAbelian hG).comm
      exact core'.c_eq_one_of_caseB_facts hG lam' hD hv hQcomm pins'
    · exact hyp'.c_eq_card_C.trans (Subgroup.card_eq_one.mpr hCbot)
  exact hc1

/-- **Peterfalvi (13.12), swapped Core subgroup form**: `D = ⊥`. -/
theorem Hypothesis.T_side_D_eq_bot_of_swapped_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) :
    hyp.D = ⊥ := by
  have hd := hyp.d_eq_one_of_swapped_lambda_dichotomy hG pins
  rw [hyp.d_eq_card_D] at hd
  exact Subgroup.card_eq_one.mp hd

open scoped FiniteInduce in
/-- **Peterfalvi (13.13)/(13.15) at the swap**: under `q < p`, the `T`-side Singer
parameter has the full order, using only the Core analytic relayer. -/
theorem Hypothesis.T_caseB_v_eq_full_of_swapped_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hqp : hyp.q < hyp.p) (pins : NuGridSupplyData hyp) :
    hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) := by
  have hV : IsMulCommutative ↥hyp.V := hyp.isMulCommutative_V_unconditional hG
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T hG hyp
  let hyp' : Hypothesis (G := G) := hyp.swap hV Tdata hU hW1 hW2 pins
  have pins' : NuGridSupplyData hyp' :=
    hyp.nuGridSupply_swap hV Tdata hU hW1 hW2 pins
  obtain ⟨core'⟩ := hyp'.characterDegreeCore_nonempty hG
  obtain ⟨chief', -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp'.toTypesIIIIIIVSetupS hG)
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
      (hyp'.mkSection11CharacterDataS hG chief') with hA | hB
  · obtain ⟨caseA⟩ := hA
    obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := lambdaWitness_of_caseA hG hyp' chief' caseA
    obtain ⟨lam'⟩ := hyp'.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind
    obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core' lam' pins'
    have hQcomm : IsMulCommutative ↥hyp'.Q :=
      IsMulCommutative.of_comm (hyp'.Q_elementaryAbelian hG).comm
    obtain ⟨hq3, -⟩ :=
      core'.caseA_parameters_of_caseB_facts hG lam' hD hv hQcomm pins' caseA
    have hp3 : hyp.p = 3 := hq3
    have h3q : 3 ≤ hyp.q := hyp.three_le_q
    omega
  · obtain ⟨caseB⟩ := hB
    have hnotmod : ¬ hyp'.p ≡ 1 [MOD hyp'.q] := by
      change ¬ hyp.q ≡ 1 [MOD hyp.p]
      intro hmod
      have hq_mod : hyp.q % hyp.p = hyp.q := Nat.mod_eq_of_lt hqp
      have h1_mod : 1 % hyp.p = 1 :=
        Nat.mod_eq_of_lt (lt_of_lt_of_le (by norm_num) hyp.three_le_p)
      have h3q : 3 ≤ hyp.q := hyp.three_le_q
      have := hmod
      unfold Nat.ModEq at this
      omega
    rcases lambdaCluster_or_caseB hG hyp' with hlam | ⟨_hCbot, hufull⟩
    · obtain ⟨lam'⟩ := hlam
      obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core' lam' pins'
      have hQcomm : IsMulCommutative ↥hyp'.Q :=
        IsMulCommutative.of_comm (hyp'.Q_elementaryAbelian hG).comm
      exact (core'.caseB_order_u_of_caseB_facts hG lam' hD hv hQcomm pins' caseB).2 hnotmod
    · exact hufull

/-- **The `T`-side (13.4)/(14.4) facts under `q < p`, Core-only form**. -/
theorem T_caseB_facts_of_q_lt_p_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hqp : hyp.q < hyp.p) (pins : NuGridSupplyData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p :=
  ⟨hyp.T_side_D_eq_bot_of_swapped_lambda_dichotomy hG pins,
    hyp.T_caseB_v_eq_full_of_swapped_lambda_dichotomy hG hqp pins,
    hyp.card_Q_eq_qp hG⟩

open scoped FiniteInduce in
/-- **Peterfalvi (13.4)/(14.4), `T`-side case (9.7.b), unconditional via the (13.3.b) dichotomy**
(issue 9094 RULING 案 A + §4): `D = ⊥`, `v = (q^p−1)/(q−1)` and `|Q| = q^p`, obtained **without**
the overstated unconditional λ-cluster of the legacy `character_degree_analysis`.

Case-splits on `LambdaWitness hyp` (Pf (13.3.b) dichotomy): the λ-branch builds the honest
`LambdaClusterData` (`lambdaClusterData_of_irr_witness`) and runs `lambda_forces_T_caseB_core`
against the unconditional `CharacterDegreeCore`; the no-λ branch is the (Galois) T-mirror
`T_caseB_facts_no_lambda`.  This is the b-side export the (14.9) type-II endpoint
(`S16 … T_side_caseB_facts`) cites in place of the uninhabitable monolithic producer. -/
theorem T_caseB_facts_unconditional [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hqp : hyp.q < hyp.p)
    (pins : NuGridSupplyData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  by_cases hlam : LambdaWitness hyp
  · obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := hlam
    obtain ⟨lam⟩ := hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind
    exact lambda_forces_T_caseB_core hG core lam pins
  · exact T_caseB_facts_of_q_lt_p_core hG hyp hqp pins

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayer.lean =====
namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

section

/-- **Peterfalvi (13.12), honest dichotomy form**: `c = 1`.

This is the unconditional replacement for the legacy monolithic character-degree carrier.
If the (13.3.b) λ-cluster exists, `lambda_forces_T_caseB_core` supplies the `T`-side case-B
facts and the general type-`P` theorem `Q_elementaryAbelian` supplies the commutativity needed
by the Core analytic endpoint.  This avoids the circular route through the later (14.9)
`T_typeII`, whose character proof itself consumes (13.12).  If no λ-cluster exists, the
faithful Galois branch already gives `C = ⊥`. -/
theorem Hypothesis.c_eq_one_of_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) :
    hyp.c = 1 := by
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  rcases lambdaCluster_or_caseB hG hyp with hlam | ⟨hCbot, _hu⟩
  · obtain ⟨lam⟩ := hlam
    obtain ⟨hD, hv, _hQ⟩ := lambda_forces_T_caseB_core hG core lam pins
    have hQcomm : IsMulCommutative ↥hyp.Q :=
      IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
    exact core.c_eq_one_of_caseB_facts hG lam hD hv hQcomm pins
  · exact hyp.c_eq_card_C.trans (Subgroup.card_eq_one.mpr hCbot)

/-- **Peterfalvi (13.13), honest Clifford-case form**: an actual case-(9.7.a)
certificate supplies its own λ-witness, so the Core analytic relayer gives the sharp
parameters without the legacy monolithic character-degree carrier. -/
theorem Hypothesis.caseA_parameters_of_clifford_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (pins : NuGridSupplyData hyp) :
    hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := lambdaWitness_of_caseA hG hyp chief caseA
  obtain ⟨lam⟩ := hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core lam pins
  have hQcomm : IsMulCommutative ↥hyp.Q :=
    IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
  exact core.caseA_parameters_of_caseB_facts hG lam hD hv hQcomm pins caseA

/-- **Peterfalvi (13.15), honest λ-dichotomy form**: an actual Clifford case-(9.7.b)
certificate has the two Singer-order alternatives without using the legacy character-degree
carrier.  In the λ-branch the Core analytic relayer proves (13.15).  In the no-λ Galois branch
`u` already has the full Singer order; the `p ≡ 1 (mod q)` alternative is impossible because
that congruence makes `q` divide the Singer quotient while the Frobenius congruence
`u ≡ 1 (mod q)` gives `q ∤ u`. -/
theorem Hypothesis.caseB_order_u_of_lambda_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief))
    (pins : NuGridSupplyData hyp) :
    (hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
      (¬ hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  have hq_not_dvd_u : ¬ hyp.q ∣ hyp.u := by
    intro hqu
    have hmod : hyp.u % hyp.q = 1 % hyp.q := hyp.u_modEq_one hG
    obtain ⟨k, hk⟩ := hqu
    have hq2 : 2 ≤ hyp.q := hyp.q_prime.two_le
    have h1q : 1 % hyp.q = 1 := Nat.one_mod_eq_one.mpr (by omega)
    rw [hk, Nat.mul_mod_right, h1q] at hmod
    omega
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  rcases lambdaCluster_or_caseB hG hyp with hlam | ⟨_hCbot, hufull⟩
  · obtain ⟨lam⟩ := hlam
    obtain ⟨hD, hv, -⟩ := lambda_forces_T_caseB_core hG core lam pins
    have hQcomm : IsMulCommutative ↥hyp.Q :=
      IsMulCommutative.of_comm (hyp.Q_elementaryAbelian hG).comm
    exact core.caseB_order_u_of_caseB_facts hG lam hD hv hQcomm pins caseB
  · refine ⟨?_, fun _ => hufull⟩
    intro hmod
    have hqdvd : hyp.q ∣ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) :=
      cyclotomic_quotient_dvd_of_modEq_one hyp.p_prime hmod
    have hqu : hyp.q ∣ hyp.u := by rwa [hufull]
    exact (hq_not_dvd_u hqu).elim

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (11.9)/(14.9), the Type-IV exclusion** — the deep content of the type
determination, now discharged.  Coq `FTtype34_structure` (Peterfalvi (11.9), `PFsection11.v:1001`,
consumed at `PFsection14.v:735`) pins a non-type-II type-`P` maximal `T` to Type III (not IV) via
the character/Galois argument `suffices galM : typeP_Galois MtypeP` (`PFsection11.v:1139`) — the
`η`-grid projection computation `a₁₁ = a₁₀ = 0`.

Formalised as the universal (11.9.c) Type-IV exclusion `not_isTypeIV_of_mem_maximalSubgroups`
(`S13_NonGaloisExclusion`, sorry-free): the `IsMulCommutative V` residual that used to live here
follows from `cyclic V ⟸ typeP_Galois T`, whose full §5–§13 chain
(`not_isTypeIV_of_hypothesis`/`U_isCyclic_of_hypothesis`) is landed.  The direct cite became
possible once the §12–16 import inversion (issue 9093) removed `S13_NonGaloisExclusion`'s
transitive dependency on §16. -/
theorem T_not_isTypeIV_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    ¬ OddOrder.GroupTheory.IsTypeIV hyp.base.T :=
  OddOrder.Peterfalvi.S13.not_isTypeIV_of_mem_maximalSubgroups hG hyp.base.T_maximal

/-- **Peterfalvi (14.9), the type determination** — Coq `PFsection14`
`have [_ _ [Ttype3 _]] := FTtype34_structure maxT TtypeP notTtype2` (line 735): a type-`P` maximal
subgroup that is *not* type II is type III.  In σ-theoretic terms, `IsTypeP1 T` (equivalently
`¬ IsTypeP2 T` given `IsTypeP T`) forces `T` to be structurally Type III.

**Fully reduced to the single (11.9) residual `T_not_isTypeIV_of_isTypeP1`.**  The type dictionary
`proposition_type_classification` (BG Prop 16.1, proven) gives, from `IsTypeP1 T`, either Type
III/IV
(if `M_F ≠ M_σ`) or Type V (if `M_F = M_σ`).  **Type V is excluded outright** by the (10.10)
hypothesis `hnoV` (instantiate with the axiom-clean `no_typeV_maximal_unconditional`,
`S12_Noncoherence`; issue 9087), so `M_F ≠ M_σ` and `T` is Type III or IV. Excluding Type IV — the
genuine (11.9) Galois/character
content — is the isolated residual `T_not_isTypeIV_of_isTypeP1`.  The Type-V exclusion and the
III/IV
structural wiring (incl. the `TypeIIIData.normalizer_le` field, bundled into the clause-(c)
disjunction) are proven here. -/
theorem T_isTypeIII_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    OddOrder.GroupTheory.IsTypeIII hyp.base.T := by
  -- Type dictionary (BG Prop 16.1): `IsTypeP1 T` ⟹ III/IV (`M_F ≠ M_σ`) or V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.base.T_maximal
  -- Type V excluded universally by the (10.10) hypothesis `hnoV`, so `M_F ≠ M_σ`.
  have hMF : OddOrder.BG.Ch4.S15.MF hyp.base.T ≠ OddOrder.BG.Ch3.S10.Msigma hyp.base.T := fun h =>
    hnoV ⟨hyp.base.T, hyp.base.T_maximal, hdV.mpr ⟨hP1, h⟩⟩
  -- `T` is Type III or IV; exclude IV by the (11.9) residual.
  exact (hcIII_IV.mpr ⟨hP1, hMF⟩).resolve_right (T_not_isTypeIV_of_isTypeP1 hG hyp hP1)

/-- **Peterfalvi (14.9), reduced to its canonical residual.**  Starting from the symmetric
(13.1) non-type-I carrier, `T` is sharpened to BG type `P₂` (`κ(T) ≠ σ'(T)`; Coq `PFsection14`
`FTtypeP_min_typeII : FTtype T == 2`).  The `IsTypeP T` conjunct is discharged honestly from
`T_nonI` (`isTypeP_of_isTypeNonI`).

The residual `κ(T) ≠ σ'(T)` is proved by the (14.9) contradiction, following Coq
`FTtypeP_min_typeII` (`apply: contraLR v1p_gt_u1q => notTtype2`): were `κ(T) = σ'(T)` (i.e.
`IsTypeP1 T`), then `T` is Type III (`T_isTypeIII_of_isTypeP1`, the `FTtype34_structure`
determination), whence the character body forces `(v − 1)/p ≤ (u − 1)/q` (`T_typeIII_ratio_le`) —
contradicting (14.8) `key_inequality`'s `(v − 1)/p > (u − 1)/q`.

The two deep pieces are isolated as `T_typeIII_ratio_le` (character body) and
`T_isTypeIII_of_isTypeP1` (type determination), both consumed below.  The `>` half is (14.8): its
pure cyclotomic comparison lives upstream in `KeyInequalityArithmetic`, while the two
group-theoretic
order inputs are the direct (13.4) producer `T_side_caseB_facts` and the (13.15) producer
`Hypothesis.u_le_cyclotomicQuotient`.  Thus no forward reference through the later
`key_inequality` theorem is needed. -/
theorem T_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP2 hyp.base.T := by
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.base.T_maximal hyp.base.T_nonI
  refine ⟨hP, ?_⟩
  -- (14.9), by contradiction (Coq `contraLR v1p_gt_u1q => notTtype2`): assume `κ(T) = σ'(T)`.
  intro hκeq
  -- Then `T` is type `P₁`, hence (Coq `FTtype34_structure`) structurally Type III.
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := ⟨hP, hκeq⟩
  have hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T := T_isTypeIII_of_isTypeP1 hG hnoV hyp hP1
  -- The character body then gives the type-III Γ-bridge estimate `(v − 1)/p ≤ (u − 1)/q`.
  have hle : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) :=
    T_typeIII_ratio_le hG hnoV hncH0C hyp hIII
  -- The arithmetic half of (14.8), separated from the later `key_inequality` packaging.
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  -- Its T-side order input is the direct (13.4) producer, which is upstream of `T_isTypeP2`.
  have hvfull := (T_side_caseB_facts hG hyp).2
  -- The required S-side upper bound is the unconditional cyclotomic quotient estimate.
  have hu_le_full :
      hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    hyp.base.u_le_cyclotomicQuotient hG
  have hqpos : (0 : ℚ) < hyp.base.q := by
    exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right hu_le_full 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  have hgt : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
    rw [hvfull]
    exact lt_of_le_of_lt hu_div hratio
  exact absurd hle (not_le.mpr hgt)

/-- **Peterfalvi (14.9)**: the subgroup `T` is of Type II.  `T` is of type `P₂`
(`T_isTypeP2`), and *every* type-`P₂` maximal subgroup is type II by the proven BG bridge
`isTypeII_of_isTypeP2`.  That bridge discharges
the deep `M'`-type-`F` structure — `IsTypeF (derivedInG T)` and `(T')_F = T_F` — internally
(`isTypeF_derivedInG_of_isTypeP2`), so the sole residual of (14.9) is the type-`P₂` fact
`T_isTypeP2`.
(Placed ahead of `exists_LHypothesis` so the §14 `T`-side chain — `typeII_overNormalizer_frobenius`
etc. — can cite `IsTypeII T` locally.) -/
theorem T_typeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    IsTypeII hyp.base.T :=
  OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.T_maximal (T_isTypeP2 hG hnoV hncH0C hyp)

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.4)**: case (9.7.b) holds for `T`, and `v = (q^p - 1) / (q - 1)`.  The numeric
content (`D = ⊥`, `v` full) is the named §13 obligation `T_side_caseB_facts`; the case-(9.7.b)
proposition is carried trivially (no consumer reads it). -/
theorem caseB_for_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧
        hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
  ⟨⟨True, trivial, (T_side_caseB_facts _hG hyp).1, (T_side_caseB_facts _hG hyp).2⟩,
    trivial, (T_side_caseB_facts _hG hyp).2⟩

namespace CaseBForSData

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
`p ≡ 1 mod q` branch gives the divided cyclotomic value of `u`. -/
theorem u_eq_of_p_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) :=
  data.order_u_eq_of_p_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
non-`p ≡ 1 mod q` branch gives the full cyclotomic value of `u`. -/
theorem u_eq_of_not_modEq_one {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  data.order_u_eq_of_not_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, `u` is at
most the full cyclotomic quotient.  The `p ≡ 1 mod q` branch divides that
quotient by the additional factor `q`; the other branch is equality. -/
theorem u_le_full_cyclotomic {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hp1_pos : 0 < hyp.base.p - 1 := by
      have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
      omega
    have hden_le : hyp.base.p - 1 ≤ hyp.base.q * (hyp.base.p - 1) := by
      have hqpos : 1 ≤ hyp.base.q := hyp.base.q_prime.one_le
      nlinarith [Nat.mul_le_mul_right (hyp.base.p - 1) hqpos]
    exact Nat.div_le_div_left hden_le hp1_pos
  · rw [data.u_eq_of_not_modEq_one hmod]

end CaseBForSData

/-- **Peterfalvi (14.6)**: case (9.7.b) holds for `S`.

The Clifford dichotomy supplies either case (9.7.a) or an actual `CliffordCaseBData`
certificate.  The case-A branch is impossible by the completed type-I-over-normalizer
contradiction, using the `(13.13)` parameters and `c = 1`.  In the remaining branch,
the Core λ-dichotomy order endpoint supplies the two alternatives for `u`; the qualitative field
stores the genuine nonempty case-B certificate rather than an opaque compatibility proposition. -/
theorem caseB_for_S [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ data : CaseBForSData hyp, data.caseB_formula := by
  classical
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData _hG
      (hyp.base.toTypesIIIIIIVSetupS _hG)
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy _hG
      (hyp.base.mkSection11CharacterDataS _hG chief) with hA | hB
  · obtain ⟨caseA⟩ := hA
    obtain ⟨hq, hu⟩ := hyp.base.caseA_parameters_of_clifford_caseA
      _hG caseA (pins := hyp.nuGridSupply)
    exact (OddOrder.Peterfalvi.S15.caseA_false_of_parameters_and_typeIOverNormalizerData
      _hG hyp.base caseA
        (hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply) hq hu
      Ldata.typeI_data).elim
  · obtain ⟨caseB⟩ := hB
    let caseB_formula : Prop := Nonempty
      (OddOrder.Peterfalvi.S11.CliffordCaseBData
        (hyp.base.mkSection11CharacterDataS _hG chief))
    have hcaseB : caseB_formula := ⟨caseB⟩
    obtain ⟨hu_mod, hu_not_mod⟩ :=
      hyp.base.caseB_order_u_of_lambda_dichotomy
        _hG caseB (pins := hyp.nuGridSupply)
    exact ⟨⟨caseB_formula, hcaseB, hu_mod, hu_not_mod, True, trivial⟩, hcaseB⟩

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- Arithmetic bridge for **Peterfalvi (14.8)**: under the Section 16 prime
ordering `q < p`, the T-side full cyclotomic quotient gives a strictly larger
`(v - 1) / p` ratio than the S-side full cyclotomic quotient gives for
`(u - 1) / q`. -/
theorem key_ratio_inequality_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) :
    (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  have hqpos : (0 : ℚ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right Sdata.u_le_full_cyclotomic 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  rw [Tdata.v_eq]
  exact lt_of_le_of_lt hu_div hratio

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace MHypothesis

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

theorem h78_H_eq [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.h78.hyp76.H = Mdata.K := by
  calc Mdata.h78.hyp76.H = Mdata.coherent78.kernel :=
        Mdata.coherent78.h78_H_eq Mdata.hG
    _ = maxNilpotentNormalHall Mdata.M := Mdata.typeIHyp.typeI.typeF.H_eq
    _ = Mdata.K := Mdata.K_eq_MF.symm

/-- The complement index of the canonical (7.8) bundle is the concrete index `e = |M : K|`
carried by `MHypothesis`. -/
theorem h78_complementIndex_eq_e [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) : Mdata.h78.complementIndex = Mdata.e := by
  have hKleM : Mdata.K ≤ Mdata.M :=
    Mdata.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le Mdata.M
  have hko : Mdata.h78.kernelOrder = Mdata.k := by
    rw [Mdata.k_eq_card_K]
    change Nat.card ↥(Mdata.h78.hyp76.H) = Nat.card ↥Mdata.K
    rw [Mdata.h78_H_eq]
  have hmul := Mdata.h78.kernelOrder_mul_complementIndex_eq_card_L
  rw [hko, Mdata.k_eq_card_K] at hmul
  have hcardK : Nat.card ↥(Mdata.K.subgroupOf Mdata.M) = Nat.card ↥Mdata.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
  have hidx : Nat.card ↥Mdata.K * (Mdata.K.subgroupOf Mdata.M).index = Nat.card ↥Mdata.M := by
    rw [← hcardK]
    exact Subgroup.card_mul_index _
  rw [← Mdata.e_eq_index] at hidx
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hmul.trans hidx.symm)

theorem psi_tau1_norm_one [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    ClassFunction.inner (Mdata.tau1 Mdata.psi) (Mdata.tau1 Mdata.psi) = 1 := by
  simpa using Mdata.coherent78.nu_zeta_norm_one Mdata.hG
    (i := Mdata.h78.zetaDistinct) Mdata.h78.zetaDistinct_ne_ind1H

theorem h78_zetaNuRho_normSq_ge [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    1 - (Mdata.h78.complementIndex : ℝ) / (Mdata.h78.kernelOrder : ℝ) ≤
      Mdata.h78.zetaNuRhoNormSq :=
  (Mdata.coherent78.normEstimates Mdata.hG).zetaNuRho_norm_sq_ge
    (Mdata.coherent78.smallIndex Mdata.hG)

end MHypothesis

/-- **Peterfalvi (13.17.c), V-side dual complement alternatives**:
`e = |M : K| = p` or `e = p q`.

The alternatives are supplied by lane b's corrected `exists_M_structural_dichotomy` and stored
faithfully on the (14.10) witness. -/
theorem MHypothesis.complementIndex_eq_p_or_pq [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    Mdata.e = hyp.base.p ∨ Mdata.e = hyp.base.p * hyp.base.q := by
  exact Mdata.complementIndex_cases

/-- **Peterfalvi (13.17.c), V-side dual input for (14.11.1)**:
`e = |M : K| ≤ p q`, without choosing the `p q` branch. -/
theorem MHypothesis.complementIndex_le_pq [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    Mdata.e ≤ hyp.base.p * hyp.base.q := by
  rcases Mdata.complementIndex_eq_p_or_pq _hG with he | he
  · rw [he]
    exact Nat.le_mul_of_pos_right _ hyp.base.q_prime.pos
  · exact he.le

/-- **Peterfalvi (14.11.1)**: if `K != V`, then `k` is large and the first quotient is
strictly greater than `(v - 1) / p`.

The third conjunct `(v − 1) / p > (u − 1) / q` is now a genuine proof: it is the arithmetic
ratio comparison `key_ratio_inequality_of_caseB_data` (14.8), fed by the (14.4)/(14.6) case-(9.7.b)
cyclotomic data.  The two structural bounds remain the named §13/§14 obligation
`main_size_bounds_structural`. -/
theorem main_size_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hnoV hncH0C hyp
  obtain ⟨Tdata, _⟩ := caseB_for_T _hG hyp
  obtain ⟨Sdata, _⟩ := caseB_for_S _hG hyp Ldata
  obtain ⟨hk, hke⟩ :=
    main_size_bounds_structural _hG hnoV hncH0C hyp Mdata hne (Mdata.complementIndex_le_pq _hG)
  exact ⟨hk, hke, key_ratio_inequality_of_caseB_data Tdata Sdata⟩

/-- Pointwise evaluation of a finite sum of class functions: `(∑ i ∈ s, f i) g = ∑ i ∈ s, f i g`.
General-purpose `ClassFunction` plumbing (hoistable to `ClassFunction.lean`). -/
theorem classFunction_sum_apply {ι : Type*} {k : Type*} [CommRing k]
    (s : Finset ι) (f : ι → ClassFunction G k) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ClassFunction.add_apply, ih, Finset.sum_insert ha]

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **The (9.7.b) `S`-side field-model package** (Coq `typeP_Galois_P` for `S` with the §13
trivial kernels `Ptype_Fcore_kernel_trivial`/`Ptype_Fcompl_kernel_trivial`,
`PFsection14.v:115-118`): an additive isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}` and an
injective character `μ : U ↪ 𝔽_{p^q}^×` linearizing the conjugation action of `U` on `P`.

This is the **branch-independent** honest (9.7.b) gate — it deliberately does *not* posit the
`u`-value `|U| = (p^q−1)/(p−1)`: by (13.15) that value holds only in the `p ≢ 1 (mod q)`
branch (in the other branch `qu = (p^q−1)/(p−1)`), so positing it unconditionally was a
statement-level overclaim (issue 0115 audit).  The package itself is what `typeP_Galois S`
supplies in **both** branches (Schur: an abelian group acting faithfully and irreducibly on
`𝔽_p^q` lies in a Singer torus `𝔽_{p^q}^×`).

The branch-independent package is assembled from the unconditional (10.10) exclusion of type V,
the unconditional (11.3) `H₀C` noncoherence refuter, and the canonical (14.3)/(14.5)
`LHypothesis.typeI_data`.  The S-side dispatcher then uses (13.12) `c = 1`; only an actual
Clifford case-(a) certificate requests the (13.13) sharp parameters, while case (b) returns the
transported §9 Singer realization directly (issue 0117). -/
theorem s_side_field_repr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
      (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
      Function.Injective μ ∧
      ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
        e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
            ↥hyp.base.P))
          = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x) := by
  have hnoV := OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG
  have hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G :=
    fun s13 =>
      OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13
  obtain ⟨Ldata⟩ := exists_LHypothesis hG hnoV hncH0C hyp
  simpa using
    OddOrder.Peterfalvi.S15.sSide_galoisField_repr_of_c_eq_one_and_caseA_parameters
      hG hyp.base
        (hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply)
        (fun caseA =>
          hyp.base.caseA_parameters_of_clifford_caseA
            hG caseA (pins := hyp.nuGridSupply))
        Ldata.typeI_data

/-- **Peterfalvi (14.6)+(13.12), the S-side Frobenius kernel** — `C_{S'}(x) ≤ P` for
`x ∈ P#`.  Follows Coq `PFsection14.v:111-141` *exactly*: the (9.7.b) resolution for `S`
(`typeP_Galois S`, via `typeP_Galois_P` and the §13 (13.12) structure) makes
`S' = P ⋊ U` a **Frobenius group with kernel `P`** (Coq `frobPU`), and the containment is
the standard Frobenius kernel-centralizer property `Frobenius_cent1_ker` — here the proven
Isaacs Thm 6.4 transport `IsFrobeniusGroup.centralizer_kernel_le`.

The `typeP_Galois_P` package is the theorem `s_side_field_repr` above, assembled upstream from
the §9 realization and the §13–§14 structural producers.  The remaining argument is Coq's
`frobPU` semiregularity plus the `↥S'`-coordinate transport.  (The alternative route through the
(14.2) field model `FieldNormalizerData` is *not* used here: `field_normalizer_structure` sits
downstream of `exists_MHypothesis`, which consumes (14.11.3) and hence this very lemma.) -/
theorem s_side_frobenius_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ x ∈ sharpSubgroup hyp.base.P,
      derivedInG hyp.base.S ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.base.P := by
  intro x hx
  rw [sharpSubgroup, Set.mem_sdiff_singleton] at hx
  obtain ⟨hxP, hx1⟩ := hx
  have frobPU : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG hyp.base.S)
      (hyp.base.P.subgroupOf (derivedInG hyp.base.S))
      (hyp.base.U.subgroupOf (derivedInG hyp.base.S)) :=
    frobenius_PU_of_field_repr hG hyp (s_side_field_repr hG hyp)
  -- `P ≤ S'` (carrier: `S' = P ⊔ U`)
  have hP_le : hyp.base.P ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU]; exact le_sup_left
  -- transport the Isaacs 6.4 kernel-centralizer containment from `↥S'`-coordinates
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgS', hgC⟩ := hg
  have hkey := frobPU.centralizer_kernel_le
    (⟨x, hP_le hxP⟩ : ↥(derivedInG hyp.base.S)) (Subgroup.mem_subgroupOf.mpr hxP)
    (fun hc => hx1 (by simpa using congrArg Subtype.val hc))
  have hgP : (⟨g, hgS'⟩ : ↥(derivedInG hyp.base.S))
      ∈ hyp.base.P.subgroupOf (derivedInG hyp.base.S) := by
    apply hkey
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : g * x = x * g := by
      have := Subgroup.mem_centralizer_iff.mp hgC x rfl
      -- `mem_centralizer_iff` gives `∀ h ∈ {x}, h * g = g * h`; normalize orientation
      exact this.symm
    exact Subtype.ext (by simpa using hcomm)
  exact Subgroup.mem_subgroupOf.mp hgP

/-- **The `(9.7.b)` T-side field model** (issue 9078 / 9000 sphere, issue 0115 Campaign B): the
T-side field-algebra package assembled into a `TFieldModelData hyp.base` via the proven producer
`tFieldModelData_of_repr` (`SemidirectFieldModel.fieldModelEmbedding`, `E = Q`, `C = V`).

**Now proven** by instantiating the lane-a shared adapter
`ConjugationFieldModel.exists_normOne_galoisField_conjugation_repr` (issue 9097) at
`(r, s, E, C) = (q, p, Q, V)`.  Its inputs are supplied as follows:

* `D = ⊥`, the `v`-value `v = (q^p−1)/(q−1)`, and `|Q| = q^p` — the (13.4)/(14.4) case-(9.7.b)
  facts `S15.T_caseB_facts_unconditional`; via `D_eq`/`d_eq_card_D`/`card_V_eq_vd` these give the
  faithfulness `V ⊓ C_G(Q) = ⊥` and `|V| = (q^p−1)/(q−1)` (no branch issue on the `T`-side:
  `q ≡ 1 (mod p)` is impossible for `q < p`);
* `V` abelian — the unconditional (13.2.a)-for-`T` `isMulCommutative_V_unconditional`;
* `Q` elementary abelian — `Q_elementaryAbelian_T` from the (14.9) `T_typeII` (the one input
  still threading the type-II structure, hence the `hnoV`/`hncH0C` parameters);
* `V ≤ N_G(Q)` — `V ≤ T' ≤ T = N_G(Q)` (`normalizer_Q_eq_T`). -/
theorem t_side_caseB_fieldModel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) : Nonempty (TFieldModelData hyp.base) := by
  let : Fact hyp.base.q.Prime := ⟨hyp.base.q_prime⟩
  -- `V` normalizes `Q`: `V ≤ T' ≤ T = N_G(Q)` (`normalizer_Q_eq_T`).
  have hVN : hyp.base.V ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    intro g hg
    rw [OddOrder.Peterfalvi.S15.normalizer_Q_eq_T hG hyp.base]
    exact ((show hyp.base.V ≤ derivedInG hyp.base.T by
      rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right).trans (Subgroup.map_subtype_le _)) hg
  have hVQ : ∀ (v : ↥hyp.base.V) (x : ↥hyp.base.Q),
      (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.Q := by
    intro v x
    exact (Subgroup.mem_set_normalizer_iff.mp (hVN v.2) (x : G)).mp x.2
  -- `(9.7.b)` field-algebra package `(e, μ, hcompat)` for `T`, via the 9097 adapter
  obtain ⟨e, μ, hμ_inj, hμ_range, hcompat⟩ :
      ∃ (e : Additive ↥hyp.base.Q ≃+ GaloisField hyp.base.q hyp.base.p)
        (μ : ↥hyp.base.V →* (GaloisField hyp.base.q hyp.base.p)ˣ)
        (_ : Function.Injective μ)
        (_ : μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.q hyp.base.p),
        ∀ (v : ↥hyp.base.V) (x : ↥hyp.base.Q),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hVQ v x⟩ : ↥hyp.base.Q))
            = ((μ v : (GaloisField hyp.base.q hyp.base.p)ˣ) : GaloisField hyp.base.q hyp.base.p) *
                e (Additive.ofMul x) := by
    -- (13.4)/(14.4): `D = ⊥`, the `v`-value, `|Q| = q^p`.
    obtain ⟨hDbot, hv, hcardQ⟩ :=
      OddOrder.Peterfalvi.S15.T_caseB_facts_unconditional hG hyp.base hyp.q_lt_p
        (pins := hyp.nuGridSupply)
    have hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q :=
      OddOrder.Peterfalvi.S15.Q_elementaryAbelian_T hG hyp.base (T_typeII hG hnoV hncH0C hyp)
    have hVcomm : IsMulCommutative ↥hyp.base.V :=
      hyp.base.isMulCommutative_V_unconditional hG
    -- faithfulness `V ⊓ C_G(Q) = ⊥` and `|V| = v` from `D = ⊥` (`d = 1`).
    have hfaith : hyp.base.V ⊓ Subgroup.centralizer (hyp.base.Q : Set G) = ⊥ := by
      rw [← hyp.base.D_eq]; exact hDbot
    have hd1 : hyp.base.d = 1 := by
      rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
    have hcardV : Nat.card ↥hyp.base.V =
        (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
      rw [hyp.base.card_V_eq_vd, hd1, mul_one, hv]
    obtain ⟨e, μ, hμinj, hμrange, hcompat₀⟩ :=
      ConjugationFieldModel.exists_normOne_galoisField_conjugation_repr
        hyp.base.q_prime hyp.base.p_prime hyp.base.p_odd hQ_elemAb hVcomm hVN hcardQ hcardV hfaith
    refine ⟨e, μ, hμinj, hμrange, fun v x => ?_⟩
    have h := hcompat₀ v x
    rwa [show OddOrder.RepresentationTheory.ConjugationFieldModel.conjugate hVN v x
        = (⟨(v : G) * (x : G) * (v : G)⁻¹, hVQ v x⟩ : ↥hyp.base.Q) from
      Subtype.ext (by simp)] at h
  exact tFieldModelData_of_repr hyp.base e μ hμ_inj hμ_range hVQ hcompat

/-- **Peterfalvi (14.4)+(13.12), the T-side Frobenius kernel** — `C_{T'}(x) ≤ Q` for
`x ∈ Q#` (dual of `s_side_frobenius_kernel`: (14.4) puts `T` in case (9.7.b), and the
T-side field model has Frobenius kernel `Q`).  Discharged (engine proven, `S16_G0Coprime`) by the
minimal (14.4) carrier `TFieldModelData` from `t_side_caseB_fieldModel` (injective
`σ : F_{q^p} ⋊ V* →* G` with kernel `Q`, complement `V`) through the proven transport
`TFieldModelData.derived_inf_centralizer_le_Q`. -/
theorem t_side_frobenius_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    ∀ x ∈ sharpSubgroup hyp.base.Q,
      derivedInG hyp.base.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.base.Q := by
  intro x hx
  obtain ⟨data⟩ := t_side_caseB_fieldModel hG hnoV hncH0C hyp
  exact data.derived_inf_centralizer_le_Q hx

/-- **Peterfalvi (14.11.3), support half**: every element of the generic set `G₀` has order
prime to `pq`.  The avoidance fields of `MHypothesis` (`G0_avoid`) feed the proven
(14.11.3) chain `orderOf_coprime_pq_of_not_mem_conj` (W-orbit bridge + per-side
Sylow/TI/(2.1) coset collapse, `S16_G0Coprime`), with the two case-(9.7.b) Frobenius-kernel
inputs supplied by `s_side_frobenius_kernel`/`t_side_frobenius_kernel`. -/
theorem MHypothesis.G0_orderOf_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) {g : G} (hg : g ∈ Mdata.G0) :
    Nat.Coprime (orderOf g) (hyp.base.p * hyp.base.q) := by
  obtain ⟨hreg, hP, hQ⟩ := Mdata.G0_avoid g hg
  exact orderOf_coprime_pq_of_not_mem_conj hG hyp.base (T_typeII hG hnoV hncH0C hyp)
    (s_side_frobenius_kernel hG hyp) (t_side_frobenius_kernel hG hnoV hncH0C hyp) hreg hP hQ

/-- **Peterfalvi (3.9.a/c), the Galois half of the `η`-grid facts** — the genuine §3/§5
obligation still gated on the `τ₃`-Galois-equivariance (issue 3002 follow-up; the carried
grid primitives determine `η` on `W`-regular values but not its Galois behaviour off `W`):
on the generic set `G₀`, the `η`-grid takes integer values (3.9.c) and pairs under the
negation involution (3.9.a). -/
theorem eta_grid_galois_facts_on_G0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) :
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)) ∧
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
        = hyp.base.eta i j g) := by
  -- Now **proven** by citing the issue-3002 keystone fields threaded into `S15.Hypothesis`
  -- by lane b (`eta_intCast_of_coprime` = (3.9.c), `eta_pair_of_coprime` = (3.9.a)), which apply
  -- to every `g` of order coprime to `pq` — and `G₀` elements are exactly such
  -- (`MHypothesis.G0_orderOf_coprime`).
  refine ⟨fun g hg i j => ?_, fun g hg i j => ?_⟩
  · exact hyp.base.eta_intCast_of_coprime g (Mdata.G0_orderOf_coprime hG hnoV hncH0C hg) i j
  · exact hyp.base.eta_pair_of_coprime g (Mdata.G0_orderOf_coprime hG hnoV hncH0C hg) i j

/-- **Peterfalvi (3.9.a/c) `η`-grid facts on `G₀`**: on the generic set `G₀`, the `η`-grid
takes integer values (3.9.c), pairs under the negation involution (3.9.a), and has principal
entry `η₀₀ = 1`.  The principal entry is now genuine (`eta_principal_apply_eq_one`, the
issue-2033 grid-semantics payoff, `S16_GridExpansion`); the Galois half remains the named
obligation `eta_grid_galois_facts_on_G0`. -/
theorem eta_grid_facts_on_G0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)) ∧
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
        = hyp.base.eta i j g) ∧
    (∀ g ∈ Mdata.G0,
      hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ g = 1) := by
  obtain ⟨hint, hpair⟩ := eta_grid_galois_facts_on_G0 hG hnoV hncH0C hyp Mdata
  exact ⟨hint, hpair, fun g _ => eta_principal_apply_eq_one hyp.base g⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.9)/(14.10) generic-set producer.**  The `η`-grid integrality/symmetry on `G₀`
(`eta_grid_facts_on_G0`, the §3/§5 grid obligation) together with the **now-genuine** support
vanishing `β_M^τ = 0` on `G₀`: `β_M = β` is a Dade image, so its support lies in `Ã(M)`
(`beta_support_subset_dadeSupport`), while `G₀` avoids `Ã(M)` (`G0_off_dadeSupport`). -/
theorem eta_generic_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    EtaGenericData hyp Mdata := by
  obtain ⟨hint, hpair, hprinc⟩ := eta_grid_facts_on_G0 hG hnoV hncH0C hyp Mdata
  refine { eta_int := hint, eta_pair := hpair, eta_principal := hprinc, betaM_vanish := ?_ }
  -- **Peterfalvi (14.11.3)**: `β_M^τ` vanishes off its Dade support `Ã(M)`, and `G₀ ⊆ G ∖ Ã(M)`.
  intro g hg
  rw [Mdata.betaM_eq]
  by_contra hne
  have hmem := Mdata.h78.beta_support_subset_dadeSupport (Function.mem_support.mpr hne)
  rw [Mdata.h78_hyp_eq] at hmem
  exact Mdata.G0_off_dadeSupport g hg hmem

/-- **Peterfalvi (14.11.3)**: on the generic set `G_0`, the extended character `ψ^{τ₁}` has
absolute value at least one: `|ψ^{τ₁}(g)| ≥ 1` for `g ∈ G_0`.

De-opacified (lane-c §16 char-endpoint): the former opaque carrier field
`generic_bound_formula : G → Prop` is replaced by this concrete inequality on the `ℤ`-linear
Dade extension `τ₁` applied to `ψ`.  Proof recipe (Pf p.89): for `g ∈ G_0`, `β_M^τ(g) = 0` (as
`g ∉ Ã(M)`), so by (14.11.2) `ψ^{τ₁}(g) = ±Σ_{i,j}(±η_ij(g))`; `g` has order prime to `pq`, so by
(3.9.c) each `η_ij(g) ∈ ℤ` and by (3.9.a) they pair under conjugation, and `η₀₀(g) = 1`, whence
`Σ(±η_ij(g)) ∈ 2ℤ+1`, giving absolute value `≥ 1`.  Depends on `betaM_expansion` (14.11.2). -/
theorem generic_character_bound [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    ∀ g : G, g ∈ Mdata.G0 → 1 ≤ ‖(Mdata.tau1 Mdata.psi) g‖ := by
  classical
  -- (14.11.2): the signed `η`-grid expansion of `β_M^τ`.
  obtain ⟨_he, ε, hε, χ, hχnorm, hexp⟩ := betaM_expansion _hG hnoV hncH0C hyp Mdata hne
  -- (3.9)/(14.10): the `η`-grid is integral and conjugation-symmetric on `G₀`, and `β_M^τ`
  -- vanishes there.
  have hdata := eta_generic_data _hG hnoV hncH0C hyp Mdata
  intro g hg
  -- (3.9.c) integer values of the `η`-grid at `g`.
  choose n hn using hdata.eta_int g hg
  -- Evaluate the (14.11.2) expansion at `g` pointwise.
  have happ : Mdata.betaM g
      = (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
          (ε i j : ℂ) * (hyp.base.eta i j g)) - χ g := by
    rw [hexp, ClassFunction.sub_apply, classFunction_sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [classFunction_sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ClassFunction.smul_apply]
  -- `β_M^τ(g) = 0` gives `χ(g) = Σ ε_ij η_ij(g) = Σ ε_ij (n_ij : ℂ)`.
  have hχ2 : χ g = ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (ε i j : ℂ) * (n i j : ℂ) := by
    have h0 : (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
        (ε i j : ℂ) * (hyp.base.eta i j g)) - χ g = 0 := by
      rw [← happ]; exact hdata.betaM_vanish g hg
    rw [(sub_eq_zero.mp h0).symm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hn i j]
  -- (3.9.a) the integer grid pairs under negation with principal value `1`.
  have hpair : ∀ i j,
      n (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) = n i j := by
    intro i j
    have he := hdata.eta_pair g hg i j
    rw [hn, hn] at he
    exact_mod_cast he
  have h00 : n ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 := by
    have he := hdata.eta_principal g hg
    rw [hn] at he
    exact_mod_cast he
  -- The signed paired sum has norm `≥ 1` (14.11.3 arithmetic core), and `‖χ‖ = ‖ψ^{τ₁}‖`.
  calc (1 : ℝ)
      ≤ ‖∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (ε i j : ℂ) * (n i j : ℂ)‖ :=
        one_le_norm_eta_grid_signed_sum hyp.base.q_prime.pos hyp.base.p_prime.pos
          hyp.base.q_odd hyp.base.p_odd n ε hε hpair h00
    _ = ‖χ g‖ := by rw [hχ2]
    _ = ‖(Mdata.tau1 Mdata.psi) g‖ := hχnorm g

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), line-83 upper-bound step** — the V-side `M`-analogue of
`S12.Hypothesis.chiRhoNormSq_zeta_le_line83`.  Applying the family inequality (7.5)
`S09.family_inequality` to the norm-one character `ψ^{τ₁}` (`psi_tau1_norm_one`) and dropping the
`G₀`-part of the sum via (14.11.3) `generic_character_bound` (`|ψ^{τ₁}(g)| ≥ 1` on `G₀`) together
with the inclusion `G₀ ⊆ famG₀` (`G0_off_dadeSupport`) gives
`‖ψ^{τ₁ρ}‖² ≤ |A(M)|/|M| + (1/|G|)(|famG₀| − |G₀|)`.

This is the first step of (14.11.4)'s upper bound; the remaining passage to the displayed
`1 − 1/p − 1/q + …` is the `|K#|/|M|` evaluation and the §8 TI-counting of the `(W#)^G`/`(P#)^G`/
`(Q#)^G` contributions, isolated for the cascade producer `normCascadeData`.  `famG₀ =
(toFamilyHypothesis71).G0 = G − Ã(M)` and `G₀ = Mdata.G0`. -/
theorem MHypothesis.chiRhoNormSq_psi_le_line83 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
      ≤ (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
          / (Nat.card ↥Mdata.M : ℝ)
        + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
          - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)) := by
  have := Mdata.finiteG
  have hA0 : (Mdata.toFamilyHypothesis71).A 0
      = OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI := rfl
  have hL0 : (Mdata.toFamilyHypothesis71).L 0 = Mdata.M := rfl
  -- (7.5) line 81 (single member, `k = 1`).
  have h81 := OddOrder.Peterfalvi.S09.family_inequality (Mdata.toFamilyHypothesis71)
    (Mdata.tau1 Mdata.psi) Mdata.psi_tau1_norm_one
  rw [Fin.sum_univ_one, hA0, hL0] at h81
  -- `G₀ ⊆ famG₀`: every `g ∈ G₀` is off the Dade support `Ã(M)`.
  have hsub : Finset.univ.filter (fun g : G => g ∈ Mdata.G0)
      ⊆ Finset.univ.filter (fun g : G => g ∈ (Mdata.toFamilyHypothesis71).G0) := by
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ g, fun _ => Mdata.G0_off_dadeSupport g hg.2⟩
  -- Drop the `G₀`-part: `|G₀| ≤ Σ_{G₀} ‖ψ^{τ₁}‖² ≤ Σ_{famG₀} ‖ψ^{τ₁}‖²`.
  have hge : ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0),
          ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 := by
    calc ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
        = ∑ _g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0), (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0),
            ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 := by
          refine Finset.sum_le_sum (fun g hg => ?_)
          have hg2 : g ∈ Mdata.G0 := (Finset.mem_filter.mp hg).2
          have h1 := generic_character_bound _hG hnoV hncH0C hyp Mdata hne g hg2
          nlinarith [h1, norm_nonneg ((Mdata.tau1 Mdata.psi : G → ℂ) g)]
  have hdrop : ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ (Mdata.toFamilyHypothesis71).G0),
          ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 :=
    le_trans hge (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by positivity))
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hcS := mul_le_mul_of_nonneg_left hdrop hGinv
  rw [mul_sub] at h81 ⊢
  linarith [h81, hcS]

/-- **`S09.Hypothesis71.chiRho` depends only on the support hypothesis `H71.hyp`.**  Two `(7.1)`
data with the same underlying `S04.Hypothesis` (the same `H(a)`-family) induce the same `ρ`-image
of any `χ`, even if their chosen Dade maps `τ` differ — `chiRho` never mentions `τ`.  Used to
identify the family-inequality `ρ`-norm of (14.11.4) with the (7.8.b) `ρ`-norm of `h78`. -/
theorem chiRhoCF_congr_hyp [Fintype G] {A : Set G} {L : Subgroup G}
    {H71a H71b : OddOrder.Peterfalvi.S09.Hypothesis71 G A L}
    (h : H71a.hyp = H71b.hyp) (χ : ClassFunction G ℂ) :
    H71a.chiRhoCF χ = H71b.chiRhoCF χ := by
  apply ClassFunction.ext
  intro a
  simp only [OddOrder.Peterfalvi.S09.Hypothesis71.chiRhoCF_apply]
  unfold OddOrder.Peterfalvi.S09.Hypothesis71.chiRho
  rw [h]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4) norm bridge.**  The family-inequality `ρ`-norm of `ψ^{τ₁}` (the LHS of
the line-83 bound) equals the (7.8.b) `ρ`-norm `h78.zetaNuRhoNormSq`.  Both are `‖(ψ^{τ₁})^ρ‖²` for
the `(M, A(M))` map `ρ`: `psi_tau1_eq` (`ψ^{τ₁} = ζ^ν`) matches the characters, and `h78_hyp_eq`
(same Dade support hypothesis) plus `chiRhoCF_congr_hyp` (independence of `chiRho` from `τ`) matches
the `ρ`-images.  This is the linchpin tying the (7.5) family-inequality layer to the (7.8.b)
coherence-norm layer of (14.11.4). -/
theorem MHypothesis.chiRhoNormSq_eq_zetaNuRhoNormSq [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
      = Mdata.h78.zetaNuRhoNormSq := by
  have hcf : ((Mdata.toFamilyHypothesis71).hyp71 0).chiRhoCF (Mdata.tau1 Mdata.psi)
      = Mdata.h78.zetaNuRho := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRho, Mdata.psi_tau1_eq]
    exact chiRhoCF_congr_hyp Mdata.h78_hyp_eq.symm _
  simp only [OddOrder.Peterfalvi.S09.FamilyHypothesis71.chiRhoNormSq,
    OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRhoNormSq, hcf]
  congr 1

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (7.8.b), the unconditional lower bound**
`1 − e/k ≤ ‖ψ^{τ₁ρ}‖²`.  Combines the coherence-norm estimate for the type-I `M`
(`h78_zetaNuRho_normSq_ge`) with `h78.kernelOrder = |K| = k` and
`h78.complementIndex = |M:K| = e` (`h78_H_eq`, `e_eq_index`) via
`chiRhoNormSq_eq_zetaNuRhoNormSq`.  The conditional producer `normCascadeData` rewrites
`e = p q` only after (14.11.2). -/
theorem MHypothesis.rhoNormSq_ge_lower [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    1 - (Mdata.e : ℝ) / (Mdata.k : ℝ)
      ≤ (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0 := by
  rw [Mdata.chiRhoNormSq_eq_zetaNuRhoNormSq]
  -- `h78.kernelOrder = |K| = k`.
  have hko : Mdata.h78.kernelOrder = Mdata.k := by
    rw [Mdata.k_eq_card_K]
    change Nat.card ↥(Mdata.h78.hyp76.H) = Nat.card ↥Mdata.K
    rw [Mdata.h78_H_eq]
  -- Rewrite the (7.8.b) carrier into `e`/`k` and conclude.
  have key := Mdata.h78_zetaNuRho_normSq_ge
  rw [Mdata.h78_complementIndex_eq_e, hko] at key
  exact key

/-- **Faithful §7 carrier for the `ρ`-norm two-sided bound of Peterfalvi (14.11.4).**

The character theory of (14.11.4) reduces to a two-sided bound on `‖ψ^{τ₁ρ}‖²`, where `ρ` is the
Hypothesis (7.1) map for `(M, A(M))` (Pf (14.11.4), p.90):

* `lower` — **(7.8.b)** (Pf 04.16 line 113): the §7 coherence-norm formula `‖ζ^{νρ}‖² ≥ 1 − e/h`
  for the coherent type-I `M` (with `e = |M:K| = pq`, `h = |K| = k`) gives `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²`.
  **Proven** (`MHypothesis.rhoNormSq_ge_lower`), via the `h78` coherence carrier and the norm bridge
  `chiRhoNormSq_eq_zetaNuRhoNormSq`.
* `upper` — **(7.5) + (14.11.3) + §8 TI-counting**: the (7.5) family inequality applied to the
  norm-one `ψ^{τ₁}`, dropping the `G_0`-part via `|ψ^{τ₁}(g)| ≥ 1` (`generic_character_bound`,
  14.11.3) to line 83 (`chiRhoNormSq_psi_le_line83`), then the §8 TI-counting of the
  `(W#)^G`/`(P#)^G`/`(Q#)^G` orbit contributions giving the raw estimate, loosened by
  `(|P|−1)/|P| ≤ 1`, `(|Q|−1)/|Q| ≤ 1`, `(k−1)/k ≤ 1` (`normCascade_upper_loosen`) to the
  `normCascadeBound` error terms `2/(pq) + 1/(uq) + 1/(vp)`.

The two-sided structure mirrors the textbook's two-step derivation; the `lower` (7.8.b) bound is
proven, and the remaining genuine obligation is the upper §8 TI-counting, isolated in
`normCascadeData`. -/
structure NormCascadeData (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  /-- `‖ψ^{τ₁ρ}‖²`, the squared `L`-norm of the Hypothesis (7.1) `ρ`-image of `ψ^{τ₁}`.
  Real-valued (matching `S09.FamilyHypothesis71.chiRhoNormSq : ℝ`), so the (7.5)/(7.8.b)
  derivation lives in `ℝ`; the passage to the rational `normCascadeBound` is a final cast. -/
  rhoNormSq : ℝ
  /-- **(7.8.b)** lower bound: `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²`
  (proven, `MHypothesis.rhoNormSq_ge_lower`). -/
  lower :
    (1 : ℝ) - ((hyp.base.p * hyp.base.q : ℕ) : ℝ) / (Mdata.k : ℝ) ≤ rhoNormSq
  /-- **(7.5) + (14.11.3) + §8 TI-counting** upper bound (loosened to the `normCascadeBound`
  error terms). -/
  upper :
    rhoNormSq ≤ 1 - (1 : ℝ) / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
      + 2 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
      + 1 / ((hyp.base.u * hyp.base.q : ℕ) : ℝ)
      + 1 / ((hyp.base.v * hyp.base.p : ℕ) : ℝ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §7 Dade producer for (14.11.4).**  The `ρ`-norm is the concrete family-inequality
norm `(toFamilyHypothesis71).chiRhoNormSq (ψ^{τ₁}) 0` for the `(M, A(M))` map `ρ`.

* `lower` uses the **proven** unconditional estimate `1 − e/k ≤ ‖ψ^{τ₁ρ}‖²`
  (`MHypothesis.rhoNormSq_ge_lower`, via `h78` and `chiRhoNormSq_eq_zetaNuRhoNormSq`) and rewrites
  `e = p q` only after the conditional (14.11.2) producer.
* `upper` is the remaining genuine obligation: the **§8 TI-counting** of the `(W#)^G`/`(P#)^G`/
  `(Q#)^G` orbit contributions that turns the line-83 bound (`chiRhoNormSq_psi_le_line83`, proven)
  into the raw estimate, which `normCascade_upper_loosen` (proven) then loosens to the displayed
  `normCascadeBound` error terms.  Both arithmetic ends of `upper` are honest; the gap is the §8
  orbit cardinality `|K#|/|M|`, `|(W#)^G|`/`|(P#)^G|`/`|(Q#)^G|` count. -/
noncomputable def normCascadeData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    NormCascadeData hyp Mdata := by
  have hepq := (betaM_expansion _hG hnoV hncH0C hyp Mdata hne).1
  refine {
    rhoNormSq := (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
    lower := ?_
    upper := ?_
  }
  · rw [← hepq]
    exact Mdata.rhoNormSq_ge_lower
  · -- line-83 (`chiRhoNormSq_psi_le_line83`, proven) chained with the §8 TI-counting step
    -- (`line83_le_displayed_upper`, the single remaining gate).
    exact le_trans (Mdata.chiRhoNormSq_psi_le_line83 _hG hnoV hncH0C hne)
      (Mdata.line83_le_displayed_upper _hG hnoV hepq)

/-- **Peterfalvi (14.11.4)**: the character-theoretic norm calculation produces the displayed
rational inequality `normCascadeBound hyp k`.

De-opacified (W4 §16→§7 bridge, lane-h): the genuine character theory is the two-sided `ρ`-norm
bound `NormCascadeData` (the (7.5) family inequality + (14.11.3)/(7.8.b) norm estimates); the
passage to `normCascadeBound` is then the pure rational rearrangement
`1 − pq/k ≤ ‖ψ^{τ₁ρ}‖² ≤ 1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)` ⟹
`1/p + 1/q ≤ pq/k + 2/(pq) + 1/(uq) + 1/(vp)` (`linarith`).  Everything downstream of
`normCascadeBound` is the arithmetic cascade already discharged in `norm_cascade_contradiction`. -/
theorem normCascadeBound_of_charData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    normCascadeBound hyp Mdata.k := by
  obtain ⟨R, hlower, hupper⟩ := normCascadeData _hG hnoV hncH0C hyp Mdata hne
  unfold normCascadeBound
  -- The two-sided `ℝ` bound `1 − pq/k ≤ R ≤ 1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)` gives the
  -- displayed rational inequality; lift the `ℚ` goal to `ℝ` and close by `linarith`.
  rw [← Rat.cast_le (K := ℝ)]
  push_cast at hlower hupper ⊢
  linarith [hlower, hupper]

/-- **Peterfalvi (14.11.4)**: the norm inequality cascade contradicts `K != V`.

This is now a transparent composition rather than an opaque obligation: the
case-(9.7.b) outputs of `caseB_for_T` (14.4) and `caseB_for_S` (14.6) supply the
T-side/S-side cyclotomic size data, `main_size_bounds` (14.11.1) supplies
`k > 2 p v`, and `normCascadeBound_of_charData` (14.11.2)--(14.11.3) supplies the
displayed norm inequality.  The arithmetic consumer
`norm_cascade_contradiction_of_caseB_outputs_main_size_bounds` then closes the
cascade.  The named producers above carry the substance. -/
theorem contradiction_of_K_ne_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    False :=
  norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    (caseB_for_T _hG hyp) (caseB_for_S _hG hyp Ldata) Mdata
    (main_size_bounds _hG hnoV hncH0C hyp Mdata hne)
    (normCascadeBound_of_charData _hG hnoV hncH0C hyp Mdata hne)

/-- **Peterfalvi (13.17.c)-dual specialised in the §14 context.**  Once `K = V`, the
alternative complement branch `e = p` is excluded by (14.9), leaving `e = p q`.

This is the second named hand-off boundary from issue 3004.  It deliberately depends on the
proved kernel equality instead of restoring an unconditional `e = p q` field on
`MHypothesis`. -/
theorem MHypothesis.complementIndex_eq_pq_of_K_eq_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) (_hKV : Mdata.K = hyp.base.V)
    (_hcases : Mdata.e = hyp.base.p ∨ Mdata.e = hyp.base.p * hyp.base.q) :
    Mdata.e = hyp.base.p * hyp.base.q := by
  classical
  rcases _hcases with hp | hpq
  · exfalso
    have hMI : IsTypeI Mdata.M := ⟨Mdata.typeIHyp.typeI⟩
    obtain ⟨frob, _hker, hW2E⟩ :=
      OddOrder.Peterfalvi.S15.exists_typeIFrobeniusData_W2_le
        _hG hnoV hyp.base Mdata.M_maximal hMI Mdata.normalizer_V_le_M
    have hEcard : Nat.card ↥(frob.complement.map Mdata.M.subtype) =
        Nat.card ↥frob.complement :=
      Subgroup.card_map_of_injective (K := frob.complement) Mdata.M.subtype_injective
    have hCcard : Nat.card ↥frob.complement = Mdata.e := by
      rw [← OddOrder.Peterfalvi.S15.typeIFrobenius_kernel_index_eq_complement frob,
        ← Mdata.K_eq_MF, ← Mdata.e_eq_index]
    have hEW2 : frob.complement.map Mdata.M.subtype = hyp.base.W2 := by
      apply Eq.symm
      apply Subgroup.eq_of_le_of_card_ge hW2E
      rw [hEcard, hCcard, hp, hyp.base.p_eq_card_W2]
    have hH_V : frob.typeI.typeF.H = hyp.base.V := by
      rw [frob.typeI.typeF.H_eq, ← Mdata.K_eq_MF, _hKV]
    have hdecomp :
        frob.typeI.typeF.H ⊔ frob.complement.map Mdata.M.subtype = Mdata.M := by
      have hmap := congrArg (Subgroup.map Mdata.M.subtype)
        frob.frobenius.isComplement.sup_eq_top
      rwa [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le frob.typeI.typeF.H_le,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    have hM_eq : Mdata.M = hyp.base.V ⊔ hyp.base.W2 := by
      rw [hH_V, hEW2] at hdecomp
      exact hdecomp.symm
    have hVleT : hyp.base.V ≤ hyp.base.T :=
      (le_sup_right.trans hyp.base.T_deriv_eq_QV.ge).trans (Subgroup.map_subtype_le _)
    have hW2leW : hyp.base.W2 ≤ hyp.base.W := by
      rw [hyp.base.W_eq_join]
      exact le_sup_right
    have hWleT : hyp.base.W ≤ hyp.base.T := by
      rw [hyp.base.W_eq_inter]
      exact inf_le_right
    have hMleT : Mdata.M ≤ hyp.base.T := by
      rw [hM_eq]
      exact sup_le hVleT (hW2leW.trans hWleT)
    obtain ⟨tdata⟩ := T_typeII _hG hnoV hncH0C hyp
    have hcop := OddOrder.Peterfalvi.S15.coprime_card_V_card_Q_of_disjoint
      hyp.base tdata hyp.base.Q_inf_V_eq_bot
    have hNVT : ¬ Subgroup.normalizer (hyp.base.V : Set G) ≤ hyp.base.T :=
      OddOrder.Peterfalvi.S15.not_normalizer_V_le_T _hG hyp.base tdata
        (OddOrder.Peterfalvi.S15.exists_conj_typeP_V_of_coprime
          _hG hyp.base tdata hcop)
    exact hNVT (Mdata.normalizer_V_le_M.trans hMleT)
  · exact hpq

/-- **Peterfalvi (14.11)**: `K = V` and `|M : K| = p q`.

The `K = V` half is now a genuine consequence of the (14.11.1)--(14.11.4)
contradiction: assuming `K ≠ V` invokes `contradiction_of_K_ne_V`.  The index
computation `|M : K| = p q` (here `Mdata.e = p q`) is the remaining genuine
obligation; note `betaM_expansion`'s `e = p q` is unavailable here because it
is conditioned on `K ≠ V`, so the equal-index value under `K = V` needs the
type-I structure of `M` directly. -/
theorem _root_.solution [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp) :
    Mdata.K = hyp.base.V ∧ Mdata.e = hyp.base.p * hyp.base.q := by
  have hKV : Mdata.K = hyp.base.V := by
    -- (14.11.1)--(14.11.4): `K ≠ V` is contradictory.
    by_contra hne
    exact contradiction_of_K_ne_V _hG hnoV hncH0C hyp Ldata Mdata hne
  have hcases := Mdata.complementIndex_eq_p_or_pq _hG
  exact ⟨hKV, Mdata.complementIndex_eq_pq_of_K_eq_V _hG hnoV hncH0C hKV hcases⟩

end OddOrder.Peterfalvi.S16
