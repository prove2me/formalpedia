-- Prove2me | solution 1 for OddOrder.noMinimalSimpleOdd_of_section16
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:43:37.157094+00:00
-- url     : https://prove2.me/submissions/33e884e4-5bda-4c2e-b943-983ce7daea89

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/TISubset.lean
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
--   OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
--   OddOrder/Peterfalvi/S10_CoherenceWiring.lean
--   OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructureBasic.lean
--   OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructure.lean
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S14_MaximalI/NormPackage.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean
--   OddOrder/Peterfalvi/S11_CaseAOddPartBound.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean
--   OddOrder/Peterfalvi/S15_SAndTDefs.lean
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
--   OddOrder/Peterfalvi/S15_ComplementStructure.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S16_PairingBessel.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean
--   OddOrder/Peterfalvi/S15_CaseBReducibleCoherence.lean
--   OddOrder/Peterfalvi/S15_CaseACoherence.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayerCore.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayer.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLMBasic.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLM.lean
--   OddOrder/BG/AppC_FinalContradiction.lean
--   OddOrder/FeitThompsonSection16Core.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_FeitThompsonSection16Core
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Theorems.Thm_OddOrder_BG_AppC_theoremC
import Theorems.Thm_OddOrder_Isaacs_Ch06_IsFrobeniusGroup_conjComplement
import Theorems.Thm_OddOrder_Isaacs_Ch06_normal_of_card_prime_of_isFrobeniusAction_of_odd
import Theorems.Thm_OddOrder_Peterfalvi_S09_Hypothesis79_zetaImage_cross_eq_zero_of_conjIndex
import Theorems.Thm_OddOrder_RepresentationTheory_cfdot_real_vchar_even
import Theorems.Thm_OddOrder_Peterfalvi_S11_caseA_blockScalarFacts
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_S
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_false_of_parameters_and_typeIOverNormalizerData
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_analytic_inequality_of_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_sSet_irr
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_forces_T_caseB_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseB_member
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseA
import Theorems.Thm_OddOrder_Peterfalvi_S15_exists_typeI_maximal_overNormalizer_V
import Theorems.Thm_OddOrder_Peterfalvi_S15_card_LF_coprime_pq
import Theorems.Thm_OddOrder_Peterfalvi_S15_Q_elementaryAbelian_T
import Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_P_card_UW1
import Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_W2_within_S_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseB_order_u_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S15_numeric_bounds_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_c_eq_one_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_numeric_parameters
import Theorems.Thm_OddOrder_Peterfalvi_S16_V_cyclic
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_caseA_contradiction_of_nonfull_fpf_card_congruences
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_caseA_contradiction_of_full_u_card_congruences
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_mSide_dadeSupport_avoids_regular
import Theorems.Thm_OddOrder_Peterfalvi_S16_Hypothesis_caseB_forces_q_three_and_p_five
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_lSide_expansion_classification
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_typeICoherent78_complementIndex_eq_pq
import Theorems.Thm_OddOrder_Peterfalvi_S16_cyclotomic_ratio_gt_of_q_lt_p
import Theorems.Thm_OddOrder_Peterfalvi_S16_exists_LHypothesis
import Theorems.Thm_OddOrder_Peterfalvi_S16_fieldNormalizerData_of_repr
import Theorems.Thm_OddOrder_Peterfalvi_S16_exists_pu_field_repr
import Theorems.Thm_OddOrder_Peterfalvi_S16_field_repr_rescale_to_W2
import Theorems.Thm_OddOrder_Peterfalvi_S16_K_eq_V_index_pq
import Theorems.Thm_OddOrder_Peterfalvi_S16_card_modEq_one_of_prime_normalizing_fpf
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_side_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_ratio_le
import Theorems.Thm_OddOrder_Peterfalvi_S16_bessel_bound_of_inner_beta_zeta_ne_zero
import Theorems.Thm_OddOrder_Peterfalvi_S16_pair_cross_orthogonal

-- ===== OddOrder/GroupTheory/TISubset.lean =====
namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

variable {A : Set G} {L : Subgroup G}

/-- ホスト部分群を緩めても TI: `L ≤ L'` なら `A` は `L'` 相対でも TI. -/
theorem mono {L' : Subgroup G} (hA : IsTISubset A L) (hLL' : L ≤ L') :
    IsTISubset A L' :=
  fun g hg => hLL' (hA g hg)

end IsTISubset

end OddOrder.GroupTheory

-- ===== OddOrder/BG/AppC_NormSetBasic.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- **BG Appendix C, Remark (VII)**: `|U| = (p^q - 1)/(p - 1)` for the
norm-one subgroup `U ≤ 𝔽_{p^q}ˣ`.  This is the `|U|` used in the `q ≥ 5`
character-sum branch of Lemma C.2. -/
theorem normOneUnits_card [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneUnits p q) = (p ^ q - 1) / (p - 1) := by
  classical
  let f : (GaloisField p q)ˣ →* (ZMod p)ˣ :=
    Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
  have hf_surj : Function.Surjective f :=
    FiniteField.unitsMap_norm_surjective (ZMod p) (GaloisField p q)
  have hker : normOneUnits p q = f.ker := rfl
  have hcod : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdom : Nat.card (GaloisField p q)ˣ = p ^ q - 1 := by
    rw [Nat.card_units, GaloisField.card p q hq]
  have hindex : f.ker.index = p - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf_surj, Subgroup.card_top, hcod]
  have hmul : Nat.card (normOneUnits p q) * (p - 1) = p ^ q - 1 := by
    rw [hker, ← hindex, f.ker.card_mul_index, hdom]
  exact Nat.eq_div_of_mul_eq_right (ne_of_gt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
    (by simpa [mul_comm] using hmul)

end OddOrder.BG.AppC.NormSet

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

/-- The source difference `Ind 1_H - ζ` is virtual when the `Ind 1_H`
source term is virtual and the distinguished `ζ` is irreducible. -/
theorem sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L :=
  Submodule.sub_mem _ hindZ hzeta_irr.mem_ZIrr

/-- Virtuality of `Ind 1_H` and irreducibility of `ζ` supply the
virtual-character input needed by the Dade bridge for `β`. -/
theorem beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.beta ∈ ZIrr G :=
  H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr
    (H78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

/-- The Dade image defining `β` is supported on the corresponding Dade support. -/
theorem beta_support_subset_dadeSupport (H78 : Hypothesis78 G A L) :
    H78.beta.support ⊆ H78.hyp76.hyp71.hyp.dadeSupport := by
  intro g hg
  by_contra hnot
  exact hg (by
    rw [H78.beta_def]
    exact H78.hyp76.hyp71.isDadeMap.map_eq_zero_of_not_mem_dadeSupport
      H78.indMinusZetaSupp g hnot)

/-- If `β` is a virtual character and `ν` is a concrete coherent extension on
`S = T \ {Ind 1_H}`, then the residual `Δ = β - 1_G + νζ` is virtual. -/
theorem delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hbeta : H78.beta ∈ ZIrr G) :
    H78.delta ∈ ZIrr G := by
  have hconst : Hypothesis71.constOne G ∈ ZIrr G := by
    have htriv : OddOrder.RepresentationTheory.trivialClassFunction G ∈ ZIrr G :=
      OddOrder.RepresentationTheory.trivialClassFunction_isIrreducible.mem_ZIrr
    simpa [Hypothesis71.constOne, OddOrder.RepresentationTheory.trivialClassFunction]
      using htriv
  have hzeta : H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G :=
    H78.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh hnu
  simpa [delta] using Submodule.add_mem (ZIrr G)
    (Submodule.sub_mem (ZIrr G) hbeta hconst) hzeta

/-- If the `Ind 1_H` source term is virtual and the distinguished `ζ` is
irreducible, then coherence supplies the residual virtual character `Δ`. -/
theorem delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.delta ∈ ZIrr G :=
  H78.delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent hcoh hnu
    (H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

/-- The defining rearrangement `β = 1_G - ζ^ν + Δ`. -/
theorem beta_eq_constOne_sub_zetaImage_add_delta (H78 : Hypothesis78 G A L) :
    H78.beta =
      Hypothesis71.constOne G - H78.nu (H78.hyp76.zeta H78.zetaDistinct) +
        H78.delta := by
  rw [delta]
  abel

/-- If `χ` is orthogonal to both `1_G` and the distinguished `ζ^ν`, then
`(β,χ) = (Δ,χ)`. -/
theorem beta_inner_eq_delta_inner_of_orthogonal
    (H78 : Hypothesis78 G A L) (χ : ClassFunction G ℂ)
    (hone : ClassFunction.inner (Hypothesis71.constOne G) χ = 0)
    (hzeta : ClassFunction.inner
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) χ = 0) :
    ClassFunction.inner H78.beta χ = ClassFunction.inner H78.delta χ := by
  rw [H78.beta_eq_constOne_sub_zetaImage_add_delta, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, hone, hzeta]
  ring

/-- Right-hand variant: if `χ` is orthogonal on the left to `1_G` and the
 distinguished `ζ^ν`, then `(χ,β) = (χ,Δ)`. -/
theorem inner_beta_eq_inner_delta_of_orthogonal
    (H78 : Hypothesis78 G A L) (χ : ClassFunction G ℂ)
    (hone : ClassFunction.inner χ (Hypothesis71.constOne G) = 0)
    (hzeta : ClassFunction.inner χ
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0) :
    ClassFunction.inner χ H78.beta = ClassFunction.inner χ H78.delta := by
  rw [H78.beta_eq_constOne_sub_zetaImage_add_delta, ClassFunction.inner_add_right,
    ClassFunction.inner_sub_right, hone, hzeta]
  ring

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

/-- `BetaDecomp` identifies the (7.9) residual `Δ` with the weighted part plus
`Γ`. -/
theorem delta_eq_weightedNuSum_add_gamma
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    H78.delta = (hBD.a : ℂ) • H78.weightedNuSum + hBD.Gamma := by
  rw [delta, hBD.beta_eq]
  abel

/-- The residual `Δ` is orthogonal to `1_G`. -/
theorem delta_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.delta (Hypothesis71.constOne G) = 0 := by
  rw [H78.delta_eq_weightedNuSum_add_gamma hBD, ClassFunction.inner_add_left,
    ClassFunction.inner_smul_left, H78.weightedNuSum_orth_one hBD,
    hBD.Gamma_orth_one, mul_zero, add_zero]

/-- Hermitian-symmetric form of `delta_orth_one`. -/
theorem constOne_orth_delta (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G) H78.delta = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.delta_orth_one hBD, star_zero]

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_9

namespace Hypothesis79

variable {G : Type*} [Group G] [Fintype G]

variable {A₁ : Set G} {L₁ : Subgroup G} [Fintype L₁]

variable [Invertible (Nat.card L₁ : ℂ)]

variable {A₂ : Set G} {L₂ : Subgroup G} [Fintype L₂]

variable [Invertible (Nat.card L₂ : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- Coherence supplies virtual-character membership for the two distinguished
`ζ` images used in (7.9). -/
theorem zetaImages_mem_ZIrr_of_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension) :
    H79.firstZetaImage ∈ ZIrr G ∧ H79.secondZetaImage ∈ ZIrr G := by
  constructor
  · simpa [firstZetaImage] using
      H79.first.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh₁ hnu₁
  · simpa [secondZetaImage] using
      H79.second.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh₂ hnu₂

/-- Coherence plus virtual `Ind 1_H` sources package the four virtual-character
memberships used by the residual cross-term consumers. -/
theorem delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct)) :
    H79.first.delta ∈ ZIrr G ∧ H79.second.delta ∈ ZIrr G ∧
      H79.firstZetaImage ∈ ZIrr G ∧ H79.secondZetaImage ∈ ZIrr G := by
  have hδ₁ : H79.first.delta ∈ ZIrr G :=
    H79.first.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hind₁Z hzeta₁_irr
  have hδ₂ : H79.second.delta ∈ ZIrr G :=
    H79.second.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₂ hnu₂ hind₂Z hzeta₂_irr
  obtain ⟨hζ₁, hζ₂⟩ := H79.zetaImages_mem_ZIrr_of_isCoherent hcoh₁ hnu₁ hcoh₂ hnu₂
  exact ⟨hδ₁, hδ₂, hζ₁, hζ₂⟩

/-- The two `β` functions are orthogonal when their Dade supports are disjoint. -/
theorem beta_inner_beta_eq_zero (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    ClassFunction.inner H79.first.beta H79.second.beta = 0 := by
  have hdisj : Disjoint H79.first.beta.support H79.second.beta.support := by
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp H79.dadeSupport_disjoint
      (H79.first.beta_support_subset_dadeSupport hg₁)
      (H79.second.beta_support_subset_dadeSupport hg₂)
  exact ClassFunction.inner_eq_zero_of_disjoint_support hdisj

/-- Expanding `β₁ = 1_G - ζ₁^ν + Δ₁` and `β₂ = 1_G - ζ₂^ν + Δ₂`
gives the displayed algebraic identity used in Peterfalvi (7.9). -/
theorem beta_inner_beta_expand_delta (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0) :
    ClassFunction.inner H79.first.beta H79.second.beta =
      1 - ClassFunction.inner H79.firstZetaImage H79.second.delta -
        ClassFunction.inner H79.first.delta H79.secondZetaImage +
          ClassFunction.inner H79.first.delta H79.second.delta := by
  have hzeta_cross' :
      ClassFunction.inner
        (H79.first.nu (H79.first.hyp76.zeta H79.first.zetaDistinct))
        (H79.second.nu (H79.second.hyp76.zeta H79.second.zetaDistinct)) = 0 := by
    simpa [firstZetaImage, secondZetaImage] using hzeta_cross
  rw [H79.first.beta_eq_constOne_sub_zetaImage_add_delta,
    H79.second.beta_eq_constOne_sub_zetaImage_add_delta]
  simp only [firstZetaImage, secondZetaImage, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, ClassFunction.inner_add_right,
    ClassFunction.inner_sub_right]
  rw [Hypothesis71.constOne_inner_self_eq_one,
    H79.second.constOne_orth_zetaImage hBD₂,
    H79.second.constOne_orth_delta hBD₂,
    H79.first.zetaImage_orth_one hBD₁,
    H79.first.delta_orth_one hBD₁,
    hzeta_cross']
  ring

/-- The support and `ζ`-orthogonality inputs reduce Peterfalvi (7.9) to the
parity/nonzero statement for the two residual cross terms. -/
theorem delta_cross_equation (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0) :
    0 = 1 - ClassFunction.inner H79.firstZetaImage H79.second.delta -
        ClassFunction.inner H79.first.delta H79.secondZetaImage +
          ClassFunction.inner H79.first.delta H79.second.delta := by
  rw [← H79.beta_inner_beta_expand_delta hBD₁ hBD₂ hzeta_cross,
    H79.beta_inner_beta_eq_zero]

/-- If one of the residual cross terms is nonzero, then the original (7.9)
non-orthogonality conclusion follows. -/
theorem conclusion_of_delta_cross_nonzero (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hdelta : ClassFunction.inner H79.first.delta H79.secondZetaImage ≠ 0 ∨
      ClassFunction.inner H79.firstZetaImage H79.second.delta ≠ 0) :
    H79.conclusion := by
  rcases hdelta with hdelta | hdelta
  · left
    rw [H79.first.beta_inner_eq_delta_inner_of_orthogonal H79.secondZetaImage
      (H79.second.constOne_orth_zetaImage hBD₂) hzeta_cross]
    exact hdelta
  · right
    have hleft : ClassFunction.inner H79.firstZetaImage H79.second.beta ≠ 0 := by
      rw [H79.second.inner_beta_eq_inner_delta_of_orthogonal H79.firstZetaImage
        (H79.first.zetaImage_orth_one hBD₁) hzeta_cross]
      exact hdelta
    intro hzero
    apply hleft
    rw [Hypothesis71.ClassFunction.inner_symm H79.second.beta H79.firstZetaImage,
      hzero, star_zero]

/-- Virtual-character residuals make the three residual cross terms integral. -/
theorem delta_cross_integral_of_ZIrr
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hδ₁ : H79.first.delta ∈ ZIrr G)
    (hδ₂ : H79.second.delta ∈ ZIrr G)
    (hζ₁ : H79.firstZetaImage ∈ ZIrr G)
    (hζ₂ : H79.secondZetaImage ∈ ZIrr G) :
    (∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ)) ∧
    (∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ)) ∧
    (∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ)) := by
  exact ⟨ClassFunction.inner_mem_ZIrr_int hδ₁ hζ₂,
    ClassFunction.inner_mem_ZIrr_int hζ₁ hδ₂,
    ClassFunction.inner_mem_ZIrr_int hδ₁ hδ₂⟩

/-- Integer-parity form of the last step of Peterfalvi (7.9): once the two
residual cross terms are integers and `(Δ₁,Δ₂)` is an even integer, the displayed
`0 = 1 - ... + ...` equation forces one cross term to be nonzero. -/
theorem conclusion_of_delta_cross_integral_parity
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hx : ∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ))
    (hy : ∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ))
    (hz : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion := by
  rcases hx with ⟨x, hx⟩
  rcases hy with ⟨y, hy⟩
  rcases hz with ⟨z, hz, hz_even⟩
  have heqC := H79.delta_cross_equation hBD₁ hBD₂ hzeta_cross
  rw [hx, hy, hz] at heqC
  have heqZ : (0 : ℤ) = 1 - y - x + z := by
    have hcast : ((0 : ℤ) : ℂ) = ((1 - y - x + z : ℤ) : ℂ) := by
      simpa [Int.cast_sub, Int.cast_add] using heqC
    exact_mod_cast hcast
  have hnonzero : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hnot
    push Not at hnot
    rcases hz_even with ⟨t, ht⟩
    omega
  apply H79.conclusion_of_delta_cross_nonzero hBD₁ hBD₂ hzeta_cross
  rcases hnonzero with hx_ne | hy_ne
  · left
    rw [hx]
    exact_mod_cast hx_ne
  · right
    rw [hy]
    exact_mod_cast hy_ne

/-- Virtual-character inputs supply the two integer cross terms needed by the
parity form of Peterfalvi (7.9). -/
theorem conclusion_of_delta_cross_even_of_ZIrr
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hδ₁ : H79.first.delta ∈ ZIrr G)
    (hδ₂ : H79.second.delta ∈ ZIrr G)
    (hζ₁ : H79.firstZetaImage ∈ ZIrr G)
    (hζ₂ : H79.secondZetaImage ∈ ZIrr G)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion := by
  obtain ⟨hx, hy, _hz⟩ := H79.delta_cross_integral_of_ZIrr hδ₁ hδ₂ hζ₁ hζ₂
  exact H79.conclusion_of_delta_cross_integral_parity hBD₁ hBD₂ hzeta_cross hx hy
    hdelta_even

/-- Coherence, virtual `Ind 1_H` sources, and irreducible distinguished source
terms supply the integer cross terms needed by the parity form of Peterfalvi
(7.9). -/
theorem conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion := by
  obtain ⟨hδ₁, hδ₂, hζ₁, hζ₂⟩ :=
    H79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁Z hzeta₁_irr hind₂Z hzeta₂_irr
  exact H79.conclusion_of_delta_cross_even_of_ZIrr hBD₁ hBD₂ hzeta_cross hδ₁ hδ₂
    hζ₁ hζ₂ hdelta_even

end Hypothesis79

end Section_7_9

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

/-- **Z-group property, subgroup-pair form** (Step 1 for a bundled Frobenius group): in a finite
Frobenius group `G = N ⋊ A` whose complement `A` has **odd order**, `A` is a Z-group — every
Sylow subgroup of `A` is cyclic ([BG] Proposition 3.9 for the complement; the conjugation action
of `A` on the kernel `N` is Frobenius, and `isZGroup_of_isFrobeniusAction_of_odd` applies).
Combined with mathlib's `IsPGroup.isCyclic_of_isZGroup` (and the `Subgroup` instance), every
prime-power-order subgroup of `A` is cyclic. -/
theorem isZGroup_complement_of_isFrobeniusGroup_of_odd
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G}
    (hFrob : IsFrobeniusGroup G N A) (hodd : Odd (Nat.card ↥A)) :
    IsZGroup ↥A := by
  let : N.Normal := hFrob.isNormal
  let : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hFrob.ne_bot_kernel
  exact isZGroup_of_isFrobeniusAction_of_odd hFrob.toFrobeniusAction hodd

/-- **Huppert V.8.18 b), subgroup-pair form.**  In a finite Frobenius group `G = N ⋊ A` whose
complement `A` has **odd order**, every subgroup `R ≤ A` of prime order is normal in `A`. -/
theorem normal_of_card_prime_of_isFrobeniusGroup_of_odd
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G}
    (hFrob : IsFrobeniusGroup G N A) (hodd : Odd (Nat.card ↥A))
    {R : Subgroup ↥A} {r : ℕ} (hr : r.Prime) (hRcard : Nat.card ↥R = r) :
    R.Normal := by
  let : N.Normal := hFrob.isNormal
  let : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hFrob.ne_bot_kernel
  exact normal_of_card_prime_of_isFrobeniusAction_of_odd hFrob.toFrobeniusAction hodd hr hRcard

end OddOrder.Isaacs.Ch06

-- ===== OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

/-- **The residual `Δ = β − 1_G + νζ` is real** (Peterfalvi (7.9), delta-reality — pure algebra).
Given `β̄ − β = νζ − νζ̄` (`hbeta_conj_sub`, itself (A) `dadeMap_conj` + agreement + Dade linearity)
and `(νζ)‾ = ν(ζ̄)` (`hnu_conj`, (B) `coherence_extension_conj`), the two conjugate-difference terms
cancel: `Δ̄ − Δ = (β̄−β) + ((νζ)‾−νζ) = (νζ−νζ̄) + (νζ̄−νζ) = 0`.  `1_G` is real, so it drops out.
Feeds `cfdot_real_vchar_even` for the (7.9) `hdelta_even`. -/
theorem delta_isReal {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L)
    (hnu_conj : (H78.nu (H78.hyp76.zeta H78.zetaDistinct)).conj
        = H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj)
    (hbeta_conj_sub : H78.beta.conj - H78.beta
        = H78.nu (H78.hyp76.zeta H78.zetaDistinct)
          - H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj) :
    ClassFunction.IsReal H78.delta := by
  have hd : H78.delta = H78.beta - Hypothesis71.constOne G
      + H78.nu (H78.hyp76.zeta H78.zetaDistinct) := rfl
  have hconstOne : (Hypothesis71.constOne G).conj = Hypothesis71.constOne G := by
    ext g; simp [ClassFunction.conj_apply, Hypothesis71.constOne_apply]
  have hbeta : H78.beta.conj = (H78.nu (H78.hyp76.zeta H78.zetaDistinct)
      - H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj) + H78.beta := by
    rw [← hbeta_conj_sub]; abel
  rw [ClassFunction.IsReal, hd, ClassFunction.conj_add, ClassFunction.conj_sub, hconstOne,
    hnu_conj, hbeta]
  abel

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

-- ===== OddOrder/Peterfalvi/S10_CoherenceWiring.lean =====
namespace OddOrder.Peterfalvi.CoherenceWiring

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **Peterfalvi (6.8) coherence-wiring bridge.**

Let `L` be a maximal subgroup (used here as the ambient group of the character theory) and
`H ◁ L` the kernel of its Sibley Dade setup.  Given a faithful Sibley hypothesis `sib`
(`S08.SibleyDadeHypothesis`) for `(G, L, H)` and identifications

* `htau : sib.tau = τ`   — its §4 Dade isometry is the spine's integral character map,
* `hS   : sib.S = S`      — its base family `{Ind_H^L θ}` is the spine's family,
* `hA0  : H^#(supported in L) = A₀` — its `H^#`-support is the spine's `A₀`,

the family `S` is coherent for `τ` on `A₀`.

The proof is the (6.8) capstone `S08.sibleySetup_is_coherent` transported along the three
identifications; it carries no `sorry`.  All the maximal-subgroup content is concentrated in
the `sib` witness (the §14 structure theory), exactly as in Peterfalvi's text, where (13.2.d)
etc. read off "(6.8) applies". -/
noncomputable def coherent_of_sibley {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (sib : S08.SibleyDadeHypothesis G L H)
    {τ : S07.IntegralCharacterMap ↥L G} {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L}
    (htau : sib.tau = τ) (hS : sib.S = S)
    (hA0 : S04.supportInSubgroup (S08.sharpImage H) L = A0) :
    S07.IsCoherent τ S A0 := by
  subst htau; subst hS; subst hA0
  exact S08.sibleySetup_is_coherent sib

/-- `Nonempty`-wrapped form of `coherent_of_sibley`, for the spine riders phrased as
`Nonempty (S07.IsCoherent …)` (e.g. Peterfalvi (10.4), (13.2.d)). -/
theorem nonempty_coherent_of_sibley {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (sib : S08.SibleyDadeHypothesis G L H)
    {τ : S07.IntegralCharacterMap ↥L G} {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L}
    (htau : sib.tau = τ) (hS : sib.S = S)
    (hA0 : S04.supportInSubgroup (S08.sharpImage H) L = A0) :
    Nonempty (S07.IsCoherent τ S A0) :=
  ⟨coherent_of_sibley sib htau hS hA0⟩

/-- Discharge an opaque coherence rider `Nonempty (S07.IsCoherent τ S A₀)` from a
`SibleyTarget` witness, via (6.8).  `sorry`-free. -/
theorem coherent_of_sibleyTarget {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {τ : S07.IntegralCharacterMap ↥L G}
    {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L} (w : SibleyTarget τ S A0) :
    Nonempty (S07.IsCoherent τ S A0) :=
  letI := w.invH
  nonempty_coherent_of_sibley w.sib w.tau_eq w.S_eq w.A0_eq

end OddOrder.Peterfalvi.CoherenceWiring

-- ===== OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructureBasic.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Transporting a §4 Dade datum along an equality of its support set preserves the Dade isometry
`dadeIntegralCharacterMap`.**  The isometry's codomain `IntegralCharacterMap ↥L G` does not mention
the support `A`, so rewriting `A` to `A'` in the datum leaves the map unchanged (`subst` + `rfl`).
This lets the (6.8) `SibleyDadeHypothesis` (Dade datum on `sharpImage H`) carry *exactly* the (12.1)
isometry `hyp.tau` (Dade datum on `A(L)`) after the ambient identification `sharpImage H = A(L)` —
the map is an *arbitrary* linear extension off the supported lattice
(`dadeIntegralCharacterMap_apply_of_support`), so only the identical datum (transported), not a
re-construction via `of_isTISubset`, reproduces `hyp.tau`. -/
theorem dadeIntegralCharacterMap_transport_ambient {L : Subgroup G} [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {A A' : Set G} (hEq : A = A')
    (dade : OddOrder.Peterfalvi.S04.Hypothesis G A L) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hEq ▸ dade)
        ((hEq ▸ dade).fullDadeIsometryData)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap dade
        (dade.fullDadeIsometryData) := by
  subst hEq; rfl

/-- **The centralizer-support of `N^#` collapses to `N^#` for a Frobenius `L` with kernel `N`.**
The (12.1) type-I Dade support is `A(L) = centralizerSupport (N^#) L`; when `L` is a Frobenius group
with kernel `N` (`N.subgroupOf L`), the extra centralizer condition is vacuous — a `y` centralizing
a nontrivial `x ∈ N` lands in the kernel `N` (`IsFrobeniusGroup.centralizer_kernel_le`), so the
support is just `N^#`.  This is the **non-circular** upstream twin of the §16
`centralizerSupport_sharpSubgroup_eq_of_frobenius`: it takes the Frobenius structure as a hypothesis
(supplied for the (12.16) witness by (12.10) `witness_L_frobenius`) rather than routing through the
final (12.7), so it is available before the minimal-counterexample machinery. -/
theorem centralizerSupport_sharp_eq_of_frobenius [Finite G] {M N : Subgroup G} {C : Subgroup ↥M}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (N.subgroupOf M) C) (hNM : N ≤ M) :
    OddOrder.GroupTheory.centralizerSupport (OddOrder.GroupTheory.sharpSubgroup N) M
      = OddOrder.GroupTheory.sharpSubgroup N := by
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyM, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxM : x ∈ M := hNM hxN
    have hxMsub : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyM⟩ : ↥M) ∈ N.subgroupOf M :=
      hfrob.centralizer_kernel_le _ hxMsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hNM hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

/-- **Ambient match for the (6.8) Sibley setup**: the `H^#`-image `sharpImage (H.subgroupOf L)` of
the Fitting kernel (`H = L_F`), pushed back to `G`, is exactly the type-I Dade support
`A(L) = typeIA L`.  Here `A(L) = centralizerSupport (H^#) L` (`typeIA` def) collapses to `H^#` for
the **Frobenius** `L` (`centralizerSupport_sharp_eq_of_frobenius`, non-circular from `hfrob`), and
`(H.subgroupOf L).map L.subtype = H ⊓ L = H` (`subgroupOf_map_subtype`, `H ≤ L`) matches the two
`H^#` descriptions.  This is the ambient identification that lets the (6.8) `SibleyDadeHypothesis`
(Dade datum on `sharpImage H`) reuse the (12.1) datum `hyp.dadeData.dade` (on `A(L)`), preserving
the isometry `hyp.tau` exactly. -/
theorem sharpImage_H_subgroupOf_eq_typeIA [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L) = typeIA L hyp.typeI := by
  have hmap : (hyp.H.subgroupOf L).map L.subtype = hyp.typeI.typeF.H := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hyp.typeI.typeF.H_le
  rw [show typeIA L hyp.typeI
        = OddOrder.GroupTheory.centralizerSupport
          (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H) L from rfl,
    centralizerSupport_sharp_eq_of_frobenius (N := hyp.typeI.typeF.H) hfrob hyp.typeI.typeF.H_le]
  simp only [OddOrder.Peterfalvi.S08.sharpImage, OddOrder.GroupTheory.sharpSubgroup, hmap]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Structural input for Peterfalvi (12.6) — TI-kernel Frobenius case (6.8)(c1).**

For the (6.8) case-(c1) route, `L` is Frobenius **and** `H^#` is a TI-subset of `G`
(Peterfalvi (6.8)(a) requires *both*: being Frobenius is (c1), but the ambient TI-ness is a
separate hypothesis).  Under TI, the §4 Dade datum's local subgroups vanish
(`dade.H a = ⊥`), which is exactly the `SibleyDadeHypothesis.dade_H_eq_bot` field, so a
`SibleyTarget` is available.

**Note (2026-07-01, issue 2032):** the earlier `_hfrob`-only signature was *unsound* — the (12.16)
witness `L` is Frobenius but its `H^#` is **not** TI in `G` (Peterfalvi (12.10): "By (12.9), `H^#`
is
not a TI-subset of `G`"), so `dade_H_eq_bot` fails there.  The `_hTI` hypothesis restores soundness;
the witness (non-TI) is handled by the case-(b)/(c) routes of `frobenius_typeI_coherent`, not by
this
TI-only carrier.

**Construction (2026-07-14, carve-out issue 9077)**: kernel `H = (L_F).subgroupOf L`; the Frobenius
witness supplies the split/nontriviality fields, `L_F = maxNilpotentNormalHall` the nilpotency.  The
TI bound `N_G(H)` collapses to `L` through the (8.15) normalizer identification
`hyp.dadeData.normalizer_eq` (`N_G(A(L)) = L`) and `A(L) = H^#` for Frobenius `L`
(`typeIA_eq_sharp_of_frobenius`, `normalizer_sharpSubgroup`).  The §4 Dade datum is the (12.1)
`hyp.dadeData.dade` recoordinated along `sharpImage H = A(L)`
(`sharpImage_H_subgroupOf_eq_typeIA`), so the Sibley map *is* `hyp.tau` exactly
(`dadeIntegralCharacterMap_transport_ambient`), and its local subgroups vanish by the (2.3) reverse
direction (`H_eq_bot_of_isTISubset`).  The `hodd` hypothesis feeds `card_L_odd` (Peterfalvi works
throughout with odd-order `G`; the earlier `hodd`-less signature was statement-level unprovable —
counter-model `G = S₄`, `L = S₃` — cf. the `hG.odd`-fed `card_L_odd` of
`typeVSibleyDadeHypothesis`; faithfulness fix approved by issue 9077 HUB RULING #4′). -/
noncomputable def sibleyTarget_frobI [Fintype G] {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis L)
    (hodd : Odd (Nat.card G))
    (_hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (_hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H)
      (Subgroup.normalizer (hyp.typeI.typeF.H : Set G))) :
    CoherenceWiring.SibleyTarget hyp.tau hyp.Sset hyp.A := by
  -- Reconcile the four instance binders with the scoped `FiniteInduce` instances baked into
  -- `hyp.tau`/`hyp.Sset`/`hyp.A` (all four classes are subsingletons; `Finite G` proofs are
  -- definitionally irrelevant), so the whole construction lives in one instance world.
  rename_i iFG iFL iIL iIG
  haveI hFin : Finite G := hyp.finiteG
  obtain rfl : iFG = OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype :=
    Subsingleton.elim _ _
  obtain rfl : iFL = OddOrder.Peterfalvi.S12.FiniteInduce.finiteSubFintype L :=
    Subsingleton.elim _ _
  obtain rfl : iIL = OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC L :=
    Subsingleton.elim _ _
  obtain rfl : iIG = OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG :=
    Subsingleton.elim _ _
  -- The target lives in `Type`, so extract the Frobenius complement by choice.
  let C : Subgroup ↥L := _hfrob.choose
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C :=
    _hfrob.choose_spec
  -- Support-set identifications: `sharpImage ((L_F).subgroupOf L) = A(L) (= (L_F)^#)`.
  have hset : OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L)
      = typeIA L hyp.typeI := sharpImage_H_subgroupOf_eq_typeIA hyp hfrob
  have hEq : typeIA L hyp.typeI
      = OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L) := hset.symm
  -- `A(L) = (L_F)^#` for the Frobenius `L` (the non-circular upstream twin of
  -- `typeIA_eq_sharp_of_frobenius`, which is defined only later in this file).
  have hsharp : typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H :=
    centralizerSupport_sharp_eq_of_frobenius hfrob hyp.typeI.typeF.H_le
  -- The (6.8.a) TI in the `L`-relative form: the TI bound `N_G(H)` collapses to `L`
  -- through the (8.15) normalizer identification `N_G(A(L)) = L`.
  have hNeq : Subgroup.normalizer (hyp.typeI.typeF.H : Set G) = L := by
    rw [← OddOrder.Peterfalvi.S12.normalizer_sharpSubgroup, ← hsharp]
    exact hyp.dadeData.normalizer_eq
  have hTI_L : OddOrder.GroupTheory.IsTISubset
      (OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L)) L := by
    rw [hset, hsharp]
    exact _hTI.mono hNeq.le
  -- The (12.1) Dade datum recoordinated to the Sibley support: the *identical* datum
  -- transported along `hEq`, so the Dade isometry is preserved exactly.
  have hconj' : (hEq ▸ hyp.dadeData.dade :
      OddOrder.Peterfalvi.S04.Hypothesis G
        (OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L)) L).HConjInvariant :=
    OddOrder.Peterfalvi.S04.Hypothesis.hConjInvariant _
  have hoddL : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  refine
    { H := hyp.H.subgroupOf L
      invH := inferInstance
      sib :=
        { W1 := C
          H_ne_bot := hfrob.ne_bot_kernel
          H_normal := hfrob.isNormal
          H_nilpotent := ?_
          split := hfrob.isComplement
          W1_nontrivial := hfrob.ne_bot_complement
          card_L_odd := hoddL
          H_sharp_ti := hTI_L
          dade := hEq ▸ hyp.dadeData.dade
          dade_H_eq_bot := fun a =>
            OddOrder.Peterfalvi.S04.Hypothesis.H_eq_bot_of_isTISubset _ hTI_L a
          S := hyp.Sset
          S_eq := rfl
          cases := Or.inl hfrob }
      tau_eq :=
        dadeIntegralCharacterMap_transport_ambient hEq hyp.dadeData.dade
      S_eq := rfl
      A0_eq := by rw [hset]; rfl }
  -- `H = L_F` is nilpotent: `maxNilpotentNormalHall` nilpotency transported to the
  -- `↥L`-coordinate along `subgroupOfEquivOfLe`.
  have : Group.IsNilpotent ↥(hyp.typeI.typeF.H) := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.H_le).symm

end OddOrder.Peterfalvi.S14

-- ===== OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructure.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6)**: if `L` is Frobenius with kernel `H = L_F`, then `S` is coherent.

The textbook proof **case-splits** on the type-I trichotomy `Definition (8.3)` (carried by
`hyp.typeI.alternative`): (a) `H^#` TI in `G` → (6.8) (`sibleyTarget_frobI`); (b) `H` abelian rank 2
→ equal-degree (5.7) (`frobenius_typeI_coherent_of_abelianKernel`); (c) `|L/H| ∣ p−1` → (6.5.c)
(`frobenius_typeI_coherent_of_cyclicQuotient`).  The (12.16) witness lands in case (b) or (c)
(Peterfalvi (12.10): its `H^#` is *not* TI), so the (6.8) route alone is insufficient — the earlier
single-`sibleyTarget_frobI` proof was unsound (issue 2032).  This assembly carries no `sorry` of its
own.  Cases (b) `frobenius_typeI_coherent_of_abelianKernel` and (c)
`frobenius_typeI_coherent_of_cyclicQuotient` are `sorry`-free, as is case (a) via the (6.8) target
`sibleyTarget_frobI` (its (8.18.c) obligation `nonconjugate_diffImage_inner_zero` was closed by the
(12.3) bar-trick descent, 2026-07-03). -/
theorem frobenius_typeI_coherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  rcases hyp.typeI.alternative with hTI | hab | hexp
  · exact CoherenceWiring.coherent_of_sibleyTarget (sibleyTarget_frobI hyp hG.odd hfrob hTI)
  · exact frobenius_typeI_coherent_of_abelianKernel hG hyp hfrob hab
  · exact frobenius_typeI_coherent_of_cyclicQuotient hG hyp hfrob hexp

end OddOrder.Peterfalvi.S14

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

-- ===== OddOrder/Peterfalvi/S14_MaximalI/NormPackage.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **The type-I Dade support is `H#`** (Peterfalvi (8.3)/(12.1) for the witness subgroup `L`).
`typeIA L = centralizerSupport (H#) L` collapses to `H# = (H : Set G) \ {1}` (`H = L_F`): the
Frobenius structure of `L` (from (12.7) `typeI_frobenius`) makes the centralizer condition vacuous
on `H#` (`IsFrobeniusGroup.centralizer_kernel_le`).  This supplies the `A = H#` shape that
`S09.Cert.hypothesis78OfDade` needs (the `hAH` argument of the §12→§7 Dade bridge).

Re-derives the `centralizerSupport = sharp` argument of
`S16.centralizerSupport_sharpSubgroup_eq_of_frobenius` — which lives downstream of `S14` and so
cannot be cited here; a hub dedup hoisting that pure-group-theory fact to a shared file (e.g.
`MaximalSubgroupType`) is tracked in issue 1013. -/
theorem Hypothesis.typeIA_eq_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.GroupTheory.typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H := by
  obtain ⟨fdata, _⟩ := typeI_frobenius hG hnoV hyp.maximal ⟨hyp.typeI⟩
  have hKf : fdata.typeI.typeF.H = hyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, hyp.typeI.typeF.H_eq]
  exact hyp.typeIA_eq_sharp_of_frobenius (hKf ▸ fdata.frobenius)

end OddOrder.Peterfalvi.S14

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

/-- The coprimality part of **Peterfalvi (13.14)** when `p` is not `1 mod q`. -/
theorem cyclotomic_quotient_coprime_of_not_modEq_one {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.coprime_iff_gcd_eq_one]
  have hpmod : p ≡ 1 [MOD p - 1] := Nat.modEq_sub (le_of_lt hp.one_lt)
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD p - 1] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpmod
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  have hmod : (∑ k ∈ Finset.range q, p ^ k) ≡ q [MOD p - 1] := by
    exact hterms.trans (by rw [hsum_one])
  rw [hmod.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp <|
    hq.coprime_iff_not_dvd.mpr fun hdiv => hpq <| by
      exact ((Nat.modEq_iff_dvd'
        (show 1 ≤ p from le_of_lt hp.one_lt)).mpr hdiv).symm

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

-- ===== OddOrder/Peterfalvi/S15_SAndTDefs.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.16), TI reduction for the `W₂`-side**: `N_G(W₂) ≤ S`.

`W₂ ≤ P = S_F ≤ F(S)` (`W2_le_P` + `maxNilpotentNormalHall_le_fittingInG`), and `F(S)^#` is a
TI-subset whose normalizer is `S` (BG Theorem 15.7(a), in the type-uniform form
`S13.fittingIsTI_of_isTypeNonI`; the normalizer identity
`normalizer_fittingInAmbient_eq_self`).  Any `g` normalizing `W₂` sends a
nonidentity `a ∈ W₂ ⊆ F(S)^#` to `g a g⁻¹ ∈ W₂ ⊆ F(S)^#`, so the TI condition places
`g ∈ N_G(F(S)) = S`.  This is the first (TI) half of the (13.16) `W₂`-confinement; the residual
`N_G(W₂) ⊓ S ≤ P ⊔ W₁` is the Maschke/Wielandt core (`normalizer_W2_within_S`). -/
theorem normalizer_W2_le_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.W2 : Set G) ≤ hyp.S := by
  have hTI := OddOrder.Peterfalvi.S13.fittingIsTI_of_isTypeNonI
    hG hyp.S_maximal hyp.S_nonI
  have hNorm := OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.S_maximal
  -- `W₂ ≤ P ≤ F(S)`.
  have hW2F : hyp.W2 ≤ OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S := by
    refine (W2_le_P hG hyp).trans ?_
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_fittingInG hyp.S
  -- a nonidentity element `a ∈ W₂` (`|W₂| = p ≥ 3`).
  have hW2ne : hyp.W2 ≠ ⊥ := by
    intro hbot
    have hp1 : hyp.p = 1 := by rw [hyp.p_eq_card_W2, hbot, Subgroup.card_bot]
    exact hyp.p_prime.one_lt.ne' hp1
  have : Nontrivial ↥hyp.W2 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW2ne
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥hyp.W2)
  set a : G := (x : G) with ha
  have haW2 : a ∈ hyp.W2 := x.2
  have hane : a ≠ 1 := fun h => hx1 (OneMemClass.coe_eq_one.mp (ha ▸ h))
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg
  have hgaW2 : g * a * g⁻¹ ∈ hyp.W2 := (hg a).mp haW2
  have hgane : g * a * g⁻¹ ≠ 1 := by
    intro h
    have key : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [h] at key; simp only [mul_one, inv_mul_cancel] at key
    exact hane key
  have ha_sharp : a ∈ OddOrder.BG.Ch4.S15.fittingSharp hyp.S := by
    change a ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) \ {1}
    exact ⟨hW2F haW2, hane⟩
  have hga_sharp : g * a * g⁻¹ ∈ OddOrder.BG.Ch4.S15.fittingSharp hyp.S := by
    change g * a * g⁻¹ ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) \ {1}
    exact ⟨hW2F hgaW2, hgane⟩
  have hgN : g ∈ Subgroup.normalizer
      (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) :=
    hTI g ⟨a, ha_sharp, hga_sharp⟩
  rwa [hNorm] at hgN

/-- **Peterfalvi (13.16), structural core for the `W₂`-side**: the Frobenius/Wielandt containment
`N_G(W₂) ≤ P ⊔ W₁`.  Assembled from the TI reduction `N_G(W₂) ≤ S` (`normalizer_W2_le_S`, proven)
and the Maschke/Wielandt core `N_G(W₂) ⊓ S ≤ P ⊔ W₁` (`normalizer_W2_within_S`, the isolated
residual): every `g ∈ N_G(W₂)` lies in `S`, hence in `N_G(W₂) ⊓ S ≤ P ⊔ W₁`. -/
theorem normalizer_W2_structure_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    Subgroup.normalizer (hyp.W2 : Set G) ≤ hyp.P ⊔ hyp.W1 := by
  intro g hg
  have hgS : g ∈ hyp.S := normalizer_W2_le_S hG hyp hg
  exact normalizer_W2_within_S_of_c_eq_one hG hyp hc1 (Subgroup.mem_inf.mpr ⟨hg, hgS⟩)

/-- **Peterfalvi (13.16), `W₂`-side**: `N_G(W₂) = C_G(W₂) = P ⊔ W₁` (the `S↔T`, `W₁↔W₂`, `P↔Q`
dual of `normalizer_W1_of_D_eq_bot`; the form stated directly in Coq
`FTtypeP_norm_cent_compl`).

Proved from `normalizer_W2_structure` by the antisymmetric chain
`P ⊔ W₁ ≤ C_G(W₂) ≤ N_G(W₂) ≤ P ⊔ W₁`:

* `W₁ ≤ C_G(W₂)` because `W = W₁ × W₂` is abelian (`W1_commutes_W2`);
* `P ≤ C_G(W₂)` because `W₂ ≤ P` (`W2_le_P`) and `P` is elementary abelian (`basic_structure`);
* `C_G(W₂) ≤ N_G(W₂)` always (`centralizer_le_normalizer`);
* `N_G(W₂) ≤ P ⊔ W₁` is the Frobenius/Wielandt containment (`normalizer_W2_structure`).

Supplies the `W₂`-side of the (13.17.c) Huppert step (`E ≤ P W₁`). -/
theorem normalizer_W2_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    Subgroup.normalizer (hyp.W2 : Set G) = Subgroup.centralizer (hyp.W2 : Set G) ∧
      Subgroup.centralizer (hyp.W2 : Set G) = hyp.P ⊔ hyp.W1 := by
  have hN_le : Subgroup.normalizer (hyp.W2 : Set G) ≤ hyp.P ⊔ hyp.W1 :=
    normalizer_W2_structure_of_c_eq_one hG hyp hc1
  -- `W₁ ≤ C_G(W₂)`: `W = W₁ × W₂` is abelian.
  have hW1_le_C : hyp.W1 ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hyp.W1_commutes_W2 x hx y (SetLike.mem_coe.mp hy)).symm
  -- `P ≤ C_G(W₂)`: `W₂ ≤ P` and `P` elementary abelian give `P` centralizes `W₂`.
  have hP_le_C : hyp.P ≤ Subgroup.centralizer (hyp.W2 : Set G) := by
    obtain ⟨_, _, hP_elemAb, _, _, _⟩ := basic_structure hG hyp
    have hW2P := W2_le_P hG hyp
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyP : y ∈ hyp.P := hW2P (SetLike.mem_coe.mp hy)
    have h := hP_elemAb.comm (⟨y, hyP⟩ : ↥hyp.P) (⟨g, hg⟩ : ↥hyp.P)
    have h2 := congrArg (Subgroup.subtype hyp.P) h
    simpa using h2
  have hPW1_le_C : hyp.P ⊔ hyp.W1 ≤ Subgroup.centralizer (hyp.W2 : Set G) :=
    sup_le hP_le_C hW1_le_C
  have hC_le_N : Subgroup.centralizer (hyp.W2 : Set G) ≤
      Subgroup.normalizer (hyp.W2 : Set G) := Subgroup.centralizer_le_normalizer _
  exact ⟨le_antisymm (hN_le.trans hPW1_le_C) hC_le_N,
    le_antisymm (hC_le_N.trans hN_le) hPW1_le_C⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`T`-side Fitting-TI source** (Pf (13.16), dual of the `S`-side type-uniform TI result):
`F(T)^#` is a TI-subset of `G` (with normalizer `T`).

On the `W₂`-side, `normalizer_W2_le_S` reduces `N_G(W₂) ≤ S` using the type-uniform
`S13.fittingIsTI_of_isTypeNonI`.  The `W₁`-side dual applies BG Theorem 15.7(a) to `T`: the
(14.9) conclusion `IsTypeII T`, together with the BG type dictionary
`proposition_type_classification` (`IsTypeII M ↔ IsTypeP2 M`), makes `T` **type-`P₂`**, so
`fittingIsTI_of_isTypeP2` applies directly.  (The `q < p` κ-Hall ordering pins the *matched-pair*
labelling `S`/`T`, not the type: both members of a type-`P₂` pair are type-`P₂` — the earlier belief
that `T` is type-`P₁` and needed the `M_F ≠ M_σ` route was mistaken.) -/
theorem fittingIsTI_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    OddOrder.BG.Ch4.S15.FittingIsTI hyp.T := by
  have hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T :=
    ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.T_maximal).2.1).mp hTTypeII
  exact OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hyp.T_maximal hP2

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

/-- **Peterfalvi (13.17.c), V-side dual — faithful dichotomy form, proven** (hub issue 3004,
ruling 3): for the `W₂`-containing Frobenius complement `E` of the type-I maximal `L` over
`N_G(V)`, either `E = W₂` (the `L = H ⋊ W₂` branch, `e = p`), or `E ⊓ P = W₂` and `E ⊄ P` (the
`L = H ⋊ (W₂W₁^y)` branch, leading to `e = pq`).  Unlike the S-side
(`complement_inf_Q_eq_W1`/`complement_not_le_Q`, whose small branch is excluded by (14.5)), both
branches are live here; the resolution to `e = pq` happens only inside (14.11).

*Proof.*  `E ⊓ P = W₂` holds unconditionally, by the mirror of `complement_inf_Q_eq_W1`:
`W₂ ≤ E ⊓ P` (`hW2E` + `W2_le_P`), and conversely `E ⊓ P` is a `p`-subgroup of the elementary
abelian `P` (`P_elementaryAbelian`, (13.2.a)) inside the Z-group `E`
(`isZGroup_complement_of_isFrobeniusGroup_of_odd`), hence cyclic of exponent `p`, so of order
`p = |W₂|`.  The dichotomy is then `by_cases` on `E ≤ P`: if so, `E = E ⊓ P = W₂`. -/
theorem complement_inf_P_structure_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype = hyp.W2 ∨
      (frob.complement.map L.subtype ⊓ hyp.P = hyp.W2 ∧
        ¬ frob.complement.map L.subtype ≤ hyp.P) := by
  classical
  set Em := frob.complement.map L.subtype with hEm
  have hInf : Em ⊓ hyp.P = hyp.W2 := by
    have hW2le : hyp.W2 ≤ Em ⊓ hyp.P := le_inf hW2E (W2_le_P _hG hyp)
    have hodd : Odd (Nat.card ↥frob.complement) := _hG.odd.of_dvd_nat
      ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L))
    have hZE : _root_.IsZGroup ↥frob.complement :=
      OddOrder.Isaacs.Ch06.isZGroup_complement_of_isFrobeniusGroup_of_odd frob.frobenius hodd
    have hZEm : _root_.IsZGroup ↥Em := _root_.IsZGroup.of_injective
      (f := ((Subgroup.equivMapOfInjective frob.complement L.subtype
        Subtype.coe_injective).symm : ↥Em ≃* ↥frob.complement).toMonoidHom)
      (MulEquiv.injective _)
    have hPeA := hyp.P_elementaryAbelian _hG
    set R : Subgroup ↥Em := (Em ⊓ hyp.P).subgroupOf Em with hRdef
    have hexp : ∀ x : ↥R, x ^ hyp.p = 1 := by
      intro x
      have hgP : ((x : ↥Em) : G) ∈ hyp.P := (Subgroup.mem_subgroupOf.mp x.2).2
      have hp1 := hPeA.2 (⟨((x : ↥Em) : G), hgP⟩ : ↥hyp.P)
      have hg1 : (((x : ↥Em) : G)) ^ hyp.p = 1 := by
        simpa using congrArg Subtype.val hp1
      apply Subtype.ext; apply Subtype.ext
      push_cast
      exact hg1
    have hpg : IsPGroup hyp.p ↥R := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
    have hFp : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
    have hcyc : IsCyclic ↥R := hpg.isCyclic_of_isZGroup
    obtain ⟨g, hgen⟩ := hcyc.exists_generator
    have hcard_dvd : Nat.card ↥R ∣ hyp.p := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hgen]
      exact orderOf_dvd_of_pow_eq_one (hexp g)
    have hcardR : Nat.card ↥(Em ⊓ hyp.P) = Nat.card ↥R :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Em ⊓ hyp.P ≤ Em)).toEquiv).symm
    have hple : hyp.p ≤ Nat.card ↥(Em ⊓ hyp.P) := by
      rw [hyp.p_eq_card_W2]
      exact Subgroup.card_le_of_le hW2le
    have hcard_eq : Nat.card ↥(Em ⊓ hyp.P) = hyp.p :=
      le_antisymm (hcardR ▸ Nat.le_of_dvd hyp.p_prime.pos hcard_dvd) hple
    exact (Subgroup.eq_of_le_of_card_ge hW2le
      (by rw [hcard_eq, hyp.p_eq_card_W2])).symm
  by_cases hle : Em ≤ hyp.P
  · left
    rw [← hInf, inf_eq_left.mpr hle]
  · right
    exact ⟨hInf, hle⟩

/-- **`S`-side dual of `complement_le_QW2_of_D_eq_bot`** (V-side Huppert step): the
`W₂`-containing Frobenius complement `E` satisfies `E ≤ P W₁`.  Mirror of
`complement_le_QW2_of_D_eq_bot` with `W₁/Q ↔ W₂/P`: `W₂` (of
prime order `p`) is normal in the Frobenius complement `E` (Huppert V.8.18b,
`normal_of_card_prime_of_isFrobeniusGroup_of_odd`), so `E ≤ N_G(W₂)`, and (13.16) `normalizer_W2`
gives `N_G(W₂) = P ⊔ W₁`.  (The Frobenius/Wielandt content of (13.16) is isolated in
`normalizer_W2_structure`.) -/
theorem complement_le_PW1_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1)
    {L : Subgroup G} (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ≤ hyp.P ⊔ hyp.W1 := by
  set E := frob.complement with hEdef
  -- `W₂ ≤ L`, and `W₂` (as a subgroup of `↥L`) is contained in `E`.
  have hEleL : E.map L.subtype ≤ L := Subgroup.map_subtype_le E
  have hW2L : hyp.W2 ≤ L := hW2E.trans hEleL
  have hW2L_le_E : hyp.W2.subgroupOf L ≤ E := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨e, he, hee⟩ := hW2E hx
    have hex : e = x := Subtype.coe_injective (by simpa using hee)
    rw [← hex]; exact he
  -- `R := W₂` viewed inside `E`, of prime order `p`.
  set R : Subgroup ↥E := (hyp.W2.subgroupOf L).subgroupOf E with hRdef
  have hRcard : Nat.card ↥R = hyp.p := by
    rw [hRdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L_le_E).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L).toEquiv]
    exact hyp.p_eq_card_W2.symm
  have hEdvd : Nat.card ↥E ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card E).trans (Subgroup.card_subgroup_dvd_card L)
  have hodd : Odd (Nat.card ↥E) := _hG.odd.of_dvd_nat hEdvd
  -- Huppert V.8.18 b): `W₂` is normal in `E`, so `E` normalizes `W₂` in `↥L`.
  have hRnormal : R.Normal :=
    OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusGroup_of_odd
      frob.frobenius hodd hyp.p_prime hRcard
  have hEnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hW2L_le_E).mp hRnormal
  -- Lift to `G`: `E.map L.subtype ≤ N_G(W₂)`.
  have hEN : E.map L.subtype ≤ Subgroup.normalizer (hyp.W2 : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have heN := hEnorm he
    rw [Subgroup.mem_normalizer_iff] at heN ⊢
    intro w
    constructor
    · intro hw
      have hwL : w ∈ L := hW2L hw
      have hw' : (⟨w, hwL⟩ : ↥L) ∈ hyp.W2.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; exact hw
      have hconj := ((heN ⟨w, hwL⟩).mp hw')
      rw [Subgroup.mem_subgroupOf] at hconj
      simpa using hconj
    · intro hw
      have he' : (L.subtype e : G) ∈ L := e.2
      have hwL : w ∈ L := by
        have hrw : w = (L.subtype e)⁻¹ * ((L.subtype e) * w * (L.subtype e)⁻¹) * (L.subtype e) := by
          group
        rw [hrw]
        exact L.mul_mem (L.mul_mem (L.inv_mem he') (hW2L hw)) he'
      have hconjmem : (e * ⟨w, hwL⟩ * e⁻¹) ∈ hyp.W2.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; simpa using hw
      have hfin := (heN ⟨w, hwL⟩).mpr hconjmem
      rw [Subgroup.mem_subgroupOf] at hfin
      simpa using hfin
  -- (13.16): `N_G(W₂) = C_G(W₂) = P W₁`.
  have h1316 := normalizer_W2_of_c_eq_one _hG hyp hc1
  calc E.map L.subtype ≤ Subgroup.normalizer (hyp.W2 : Set G) := hEN
    _ = Subgroup.centralizer (hyp.W2 : Set G) := h1316.1
    _ = hyp.P ⊔ hyp.W1 := h1316.2

/-- **`S`-side of the (13.17.c) `W₁`-structure**: `W₁ ≤ N_G(P)`, `P ⊓ W₁ = ⊥`, and `q ∤ |P|`.

All three are ungated `S`-side facts: `W₁ ≤ S ≤ N_G(P)` (`P = S_F ⊴ S`); `P ⊓ W₁ ≤ M' ⊓ W₁ = ⊥`
(`P ≤ M' = derivedInG S`, `M_complement` disjointness); and `q ∤ |P|` from
`Coprime |P| |U ⋊ W₁|` (`coprime_card_P_card_UW1`) with `|W₁| = q ∣ |U ⋊ W₁|`. -/
theorem P_W1_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ Subgroup.normalizer (hyp.P : Set G) ∧ hyp.P ⊓ hyp.W1 = ⊥ ∧
      ¬ hyp.q ∣ Nat.card ↥hyp.P := by
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  refine ⟨hW1_le_S.trans hS_norm_P, ?_, ?_⟩
  · rw [eq_bot_iff]; intro x hx
    obtain ⟨hxP, hxW1⟩ := Subgroup.mem_inf.mp hx
    have hxm : x ∈ derivedInG hyp.S ⊓ hyp.W1 := Subgroup.mem_inf.mpr ⟨hP_le_M' hxP, hxW1⟩
    rwa [hM'W1] at hxm
  · intro hq
    have hcop := coprime_card_P_card_UW1 hG hyp
    have hW1dvd : Nat.card ↥hyp.W1 ∣ Nat.card ↥(hyp.U ⊔ hyp.W1) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have hcopPW1 : Nat.Coprime (Nat.card ↥hyp.P) (Nat.card ↥hyp.W1) :=
      hcop.coprime_dvd_right hW1dvd
    rw [← hyp.q_eq_card_W1] at hcopPW1
    have hqdvd1 : hyp.q ∣ 1 := hcopPW1 ▸ Nat.dvd_gcd hq (dvd_refl hyp.q)
    exact hyp.q_prime.one_lt.ne' (Nat.dvd_one.mp hqdvd1)

/-- **The `e = pq` branch computation** (V-side): from the (13.17.c)-dual second-branch facts
`E ⊓ P = W₂` and `E ⊄ P`, the complement order is `p q`.  This is the sorry-free arithmetic core
of `complement_card_p_or_pq_V` (the faithful dichotomy form; the deprecated unconditional
`complement_card_eq_pq_V` family was deleted per hub issue 3004 ruling 3). -/
theorem complement_card_eq_pq_V_of_structure_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype)
    (hInf : frob.complement.map L.subtype ⊓ hyp.P = hyp.W2)
    (hnle : ¬ frob.complement.map L.subtype ≤ hyp.P) :
    Nat.card ↥frob.complement = hyp.p * hyp.q := by
  set Em := frob.complement.map L.subtype with hEm
  set Hg := hyp.P ⊔ hyp.W1 with hHg
  have hEH : Em ≤ Hg := complement_le_PW1_of_c_eq_one _hG hyp hc1 frob hW2E
  obtain ⟨hWnorm, hdisj, _⟩ := P_W1_structure _hG hyp
  have hPleH : hyp.P ≤ Hg := le_sup_left
  have hInfCard : Nat.card ↥(Em ⊓ hyp.P) = hyp.p := by rw [hInf]; exact hyp.p_eq_card_W2.symm
  have hPnorm : (hyp.P.subgroupOf Hg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleH).mpr (sup_le Subgroup.le_normalizer hWnorm)
  have hHcard : Nat.card ↥Hg = Nat.card ↥hyp.P * hyp.q := by
    have h := OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
      (show hyp.W1 ⊓ hyp.P = ⊥ by rw [inf_comm]; exact hdisj)
    rw [hHg, sup_comm, h, ← hyp.q_eq_card_W1]
    exact mul_comm _ _
  have hPpos : 0 < Nat.card ↥hyp.P := Nat.card_pos
  have hindexH : (hyp.P.subgroupOf Hg).index = hyp.q := by
    have hmul := Subgroup.card_mul_index (hyp.P.subgroupOf Hg)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleH).toEquiv, hHcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hPpos hmul
  have hdvd : hyp.P.relIndex Em ∣ hyp.q := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := hyp.P.subgroupOf Hg)
      (K := Em.subgroupOf Hg)
    rwa [Subgroup.relIndex_subgroupOf hEH, hindexH] at h1
  have hne1 : hyp.P.relIndex Em ≠ 1 := fun h => hnle (Subgroup.relIndex_eq_one.mp h)
  have hrel : hyp.P.relIndex Em = hyp.q :=
    (hyp.q_prime.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  have hEmcard : Nat.card ↥Em = hyp.p * hyp.q := by
    have hmul := Subgroup.card_mul_index (hyp.P.subgroupOf Em)
    rw [show (hyp.P.subgroupOf Em).index = hyp.q from hrel, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.P ≤ Em)).toEquiv,
      hInfCard] at hmul
    exact hmul.symm
  rw [show Nat.card ↥frob.complement = Nat.card ↥Em from
    Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hEmcard]

/-- **Peterfalvi (13.17.c), V-side dual — the complement-order dichotomy** (hub issue 3004,
ruling 3): the `W₂`-containing Frobenius complement of the type-I maximal `L` over `N_G(V)` has
order `p` (the `L = H ⋊ W₂` branch) or `p q` (the `L = H ⋊ (W₂W₁^y)` branch).  The faithful
V-side export: unlike the S-side, the small branch cannot be excluded before (14.11). -/
theorem complement_card_p_or_pq_V_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p ∨ Nat.card ↥frob.complement = hyp.p * hyp.q := by
  rcases complement_inf_P_structure_dichotomy _hG hyp frob hW2E with hW2 | ⟨hInf, hnle⟩
  · left
    rw [Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hW2]
    exact hyp.p_eq_card_W2.symm
  · exact Or.inr
      (complement_card_eq_pq_V_of_structure_of_c_eq_one _hG hyp hc1 frob hW2E hInf hnle)

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

/-- **Peterfalvi (14.10), structural foundation — faithful dichotomy form** (hub issue 3004,
ruling 3): for `T` of type II, there is a type-I maximal subgroup `M` over `N_G(V)` carrying a §14
`S14.Hypothesis`, with Fitting-kernel index `|M : M_F| = p` or `= p q` (the (13.17.c)-dual
complement dichotomy `complement_card_p_or_pq_V`; the resolution to `p q` happens only inside
(14.11): the `K ≠ V` branch by the (14.11.2) character argument, the `K = V` branch by excluding
`E = W₂` in the §14 context).  The restructured §16 `exists_MHypothesis` cites this form. -/
theorem exists_M_structural_dichotomy_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) (hTII : IsTypeII hyp.T) :
    ∃ (M : Subgroup G) (_typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M),
      M ∈ maximalSubgroups G ∧
        Subgroup.normalizer (hyp.V : Set G) ≤ M ∧
          (((maxNilpotentNormalHall M).subgroupOf M).index = hyp.p ∨
            ((maxNilpotentNormalHall M).subgroupOf M).index = hyp.p * hyp.q) := by
  obtain ⟨L, hLmax, hLtypeI, hNVL, _hVH⟩ :=
    exists_typeI_maximal_overNormalizer_V hG hnoV hyp hTII
  obtain ⟨frob, _hker, hW2E⟩ := exists_typeIFrobeniusData_W2_le hG hnoV hyp hLmax hLtypeI hNVL
  obtain ⟨typeIHyp⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis hG hLmax hLtypeI
  refine ⟨L, typeIHyp, hLmax, hNVL, ?_⟩
  rw [typeIFrobenius_kernel_index_eq_complement frob]
  exact complement_card_p_or_pq_V_of_c_eq_one hG hyp hc1 frob hW2E

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

/-- The coherent extension of `h78` is the bundle's coherence extension
(definitional). -/
theorem h78_nu_eq : (data.h78 hG).nu = data.coh.extension := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is irreducible** (Frobenius kernel induction,
[Is] Thm 6.34). -/
theorem h78_zeta_irreducible :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) := by
  have := data.kernelIn_normal
  rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **The induced principal `ζ_{ind1H} = Ind 1_H` is a virtual character.** -/
theorem h78_ind_mem_ZIrr :
    (data.h78 hG).hyp76.zeta (data.h78 hG).ind1H ∈ ZIrr ↥L := by
  have := data.kernelIn_normal
  rw [data.h78_ind1H_eq, data.h78_zeta_eq]
  exact ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr

/-- **The `(7.8)` coherent source set equals the (12.1) family `S`.** -/
theorem h78_sourceSet_eq : (data.h78 hG).sourceSet = data.typeIHyp.Sset := by
  have := data.kernelIn_normal
  ext φ
  constructor
  · rintro ⟨idx, hidx, rfl⟩
    exact data.zeta_mem_Sset hidx
  · rintro ⟨θ', hθ'_ne, rfl⟩
    obtain ⟨j, hj⟩ := data.cover θ'
    have hj' : data.zeta j = ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ) := hj
    refine ⟨j, ?_, hj'⟩
    intro hjind
    apply induce_ne_trivialChar_induce data.kernelIn θ' hθ'_ne
    rw [← hj', show j = data.ind1H from hjind]
    change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
      = ClassFunction.induce data.kernelIn
        ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
          ClassFunction _ ℂ)
    rw [data.triv]

/-- **The bundle coherence as an `IsCoherent` over the `(7.8)` `sourceSet`** (transport along
`h78_sourceSet_eq`, keeping the same extension `ν`). -/
noncomputable def isCoherentSourceSet :
    OddOrder.Peterfalvi.S07.IsCoherent data.typeIHyp.tau (data.h78 hG).sourceSet
      data.typeIHyp.A where
  nonzero := (data.h78_sourceSet_eq hG).symm ▸ data.coh.nonzero
  extension := data.coh.extension
  extension_inner_eq := fun φ ψ hφ hψ => data.coh.extension_inner_eq φ ψ
    (data.h78_sourceSet_eq hG ▸ hφ) (data.h78_sourceSet_eq hG ▸ hψ)
  extends_on_supported := fun φ hφ => data.coh.extends_on_supported φ
    (data.h78_sourceSet_eq hG ▸ hφ)
  extension_mem_ZIrr := fun φ hφ => data.coh.extension_mem_ZIrr φ
    (data.h78_sourceSet_eq hG ▸ hφ)

set_option backward.isDefEq.respectTransparency false in
/-- **The conjugate `ζ̄_0` is a family member**: there is `j₁ ≠ ind1H` with
`ζ_{j₁} = ζ̄_0` (`conjPerm` of the distinguished source is covered). -/
theorem exists_conjIndex :
    ∃ j₁, j₁ ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta j₁
        = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  have := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ 0)) : ClassFunction _ ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ 0)).symm
  obtain ⟨j₁, hj₁_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ 0))
  have hj₁_conj : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hj₁_range
  refine ⟨j₁, ?_, hj₁_conj⟩
  intro hj1
  apply data.ind1H_ne_zero
  have hzeta_inj : Function.Injective (data.h78 hG).hyp76.zeta := data.inj
  refine (hzeta_inj ?_).symm
  -- `ζ_{ind1H}` is real (`Ind 1_H`), and `ζ_{ind1H} = ζ_{j₁} = ζ̄_0`.
  have e1 : (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [← show j₁ = (data.h78 hG).ind1H from hj1]; exact hj₁_conj
  have e2 : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  calc (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
      = ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj := by
        rw [e1, ClassFunction.conj_conj]
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := e2

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is not real** (odd order): it is a nontrivial irreducible
(degree `[L:H] > 1`) of the odd-order group `L`. -/
theorem h78_zeta_ne_conj (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ≠ ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  have := data.kernelIn_normal
  have hirr := data.h78_zeta_irreducible hG
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  -- The kernel is proper (complement nontrivial), so `[L:H] > 1`.
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  have hdeg : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.kernelIn).index : ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
    exact data.deg0
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct), hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
        = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : (((data.kernelIn).index : ℂ)) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    exact absurd (by exact_mod_cast hone : (data.kernelIn).index = 1) (by omega)
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **`ζ_0 − ζ̄_0` is supported on `A(L)`** (equal degree; both vanish off `H`). -/
theorem zeta_sub_conj_support (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {j₁ : Fin (data.n + 1)}
    (hj₁ : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj) :
    ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
        - (data.h78 hG).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  have := data.kernelIn_normal
  have hdeg : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.kernelIn).index : ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
    exact data.deg0
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hj₁, ClassFunction.conj_apply] at hx
  refine (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨?_, ?_⟩
  · -- `x ∈ kernelIn`: else `ζ_0 x = 0`, so the difference vanishes.
    by_contra hxH
    apply hx
    rw [(data.h78 hG).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH, star_zero, sub_zero]
  · -- `x ≠ 1`: at `1`, `ζ_0(1) = [L:H]` is real.
    intro hx1
    apply hx
    rw [hx1, hdeg]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- **`ζ_0^ν − ζ̄_0^ν` is supported in the Dade support** (the coherent extension agrees
with the Dade isometry on the equal-degree difference). -/
theorem nu_zeta_sub_conj_support (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {j₁ : Fin (data.n + 1)} (hj₁ne_ind : j₁ ≠ (data.h78 hG).ind1H)
    (hj₁ : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj) :
    ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)
        - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta j₁)).support
      ⊆ (data.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  have := data.kernelIn_normal
  have hzd_mem : (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ∈ data.typeIHyp.Sset := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
    exact data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)
  have hj₁_mem : (data.h78 hG).hyp76.zeta j₁ ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]
    exact data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hj₁ne_ind)
  have hsupp' : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support hG hj₁
  have hagree := coherence_hagree_dadeMap data.typeIHyp.dadeData.dade
    data.coh hzd_mem hj₁_mem (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  have heq : (data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)
      - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta j₁)
      = (data.typeIHyp.dadeData.dade.fullDadeIsometryData).toDadeMap
          ⟨_, (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [data.h78_nu_eq,
      ← one_smul ℂ (data.coh.extension ((data.h78 hG).hyp76.zeta j₁))]
    exact hagree.symm
  rw [heq]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  have hdade := (data.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeMap
  exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)

/-- **Members of `ℤ[S]` vanishing at `1` are `A(L)`-supported** (the `hspan` input of
`extension_mapRingEquiv_comm`): each `Ind θ ∈ S` vanishes off the normal kernel
(`Sset_vanishes_off_H`), so `ℤ[S] ⊆ {ψ | supp ψ ⊆ H}` by span induction; vanishing at `1`
then lands the support in `H^# = A(L)`. -/
theorem zSpan_Sset_support_subset (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan data.typeIHyp.Sset) (h1 : φ 1 = 0) :
    φ.support ⊆ data.typeIHyp.A := by
  have := data.kernelIn_normal
  -- `ℤ[S] ⊆ {ψ | ψ.support ⊆ kernelIn}` by span induction.
  have hsuppH : ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan data.typeIHyp.Sset,
      ψ.support ⊆ (data.kernelIn : Set ↥L) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        intro g hg
        rw [ClassFunction.mem_support] at hg
        by_contra hgK
        exact hg (OddOrder.Peterfalvi.S14.Sset_vanishes_off_H data.typeIHyp hx
          (fun hmem => hgK (Subgroup.mem_subgroupOf.mpr hmem)))
    | zero => intro g hg; rw [ClassFunction.mem_support] at hg; exact absurd rfl hg
    | add x y _ _ hx hy =>
        intro g hg
        rcases ClassFunction.support_add_subset x y hg with h | h
        · exact hx h
        · exact hy h
    | smul c x _ hx =>
        intro g hg
        refine hx ?_
        rw [ClassFunction.mem_support] at hg ⊢
        intro hxg
        apply hg
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hxg, mul_zero]
  intro g hg
  have hgH : g ∈ data.kernelIn := hsuppH φ hφ hg
  have hg1 : g ≠ 1 := by
    rintro rfl; exact (ClassFunction.mem_support.mp hg) h1
  change g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) g).mpr ⟨hgH, hg1⟩

/-- **The family `S` consists of irreducibles** (Frobenius kernel induction). -/
theorem Sset_subset_irreducible :
    data.typeIHyp.Sset ⊆ irreducibleCharacters ↥L := by
  have := data.kernelIn_normal
  rintro φ ⟨θ', hθ'_ne, rfl⟩
  exact mem_irreducibleCharacters.mpr
    (isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob θ' hθ'_ne)

/-- **The family `S` is closed under complex conjugation** (`Ind θ̄ = (Ind θ)‾`, and
`θ̄ ≠ 1` for `θ ≠ 1`). -/
theorem Sset_closedUnderConjugate {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ data.typeIHyp.Sset) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ ∈ data.typeIHyp.Sset := by
  have := data.kernelIn_normal
  obtain ⟨θ', hθ'_ne, rfl⟩ := hφ
  have hbridge : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ))
      = (ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ)).conj := by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  rw [hbridge, conj_induce]
  refine ⟨IrreducibleCharacter.conjPerm _ θ', ?_, ?_⟩
  · -- `θ̄' ≠ 1`: conjugating `θ̄' = 1` gives `θ' = 1̄ = 1`.
    intro hconj_triv
    refine hθ'_ne (IrreducibleCharacter.ext ?_)
    have hcoe := congrArg IrreducibleCharacter.toClassFunction hconj_triv
    rw [show (IrreducibleCharacter.conjPerm _ θ').toClassFunction
        = (θ' : ClassFunction ↥data.kernelIn ℂ).conj
      from IrreducibleCharacter.conjPerm_apply_coe θ'] at hcoe
    calc (θ' : ClassFunction ↥data.kernelIn ℂ)
        = ((θ' : ClassFunction ↥data.kernelIn ℂ).conj).conj := (ClassFunction.conj_conj _).symm
      _ = ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
            ClassFunction _ ℂ).conj := by rw [hcoe]
      _ = ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
            ClassFunction _ ℂ) := trivialClassFunction_isReal
  · exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe θ').symm

/-- **The coherent extension commutes with complex conjugation on `S`**
(Peterfalvi (5.9)(a) via `extension_mapRingEquiv_comm`). -/
theorem coherence_extension_conj (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ data.typeIHyp.Sset)
    (h2 : ∃ ψ ∈ data.typeIHyp.Sset, ψ ≠ χ) :
    (data.coh.extension χ).conj = data.coh.extension χ.conj := by
  have hbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hbridgeL : ∀ X : ClassFunction ↥L ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  rw [hbridgeG (data.coh.extension χ), hbridgeL χ]
  exact data.coh.extension_mapRingEquiv_comm subset_rfl data.Sset_subset_irreducible
    (fun φ hφ h1 => data.zSpan_Sset_support_subset hG hφ h1)
    Complex.conjAe.toRingEquiv (fun φ hφ => data.Sset_closedUnderConjugate hφ)
    (fun φ hφ => data.coh.extension_mem_ZIrr φ (Submodule.subset_span hφ)) hχS h2

/-- **`β̄ − β = ζ_0^ν − ζ̄_0^ν`** (the `hbeta_conj_sub` input of `delta_isReal`). -/
theorem beta_conj_sub (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).beta.conj - (data.h78 hG).beta
      = (data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)
        - (data.h78 hG).nu
            ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  classical
  have := data.kernelIn_normal
  set hyp := data.typeIHyp.dadeData.dade with hhyp
  set dade := hyp.fullDadeIsometryData with hdade
  obtain ⟨j₁, hj₁ne, hj₁⟩ := data.exists_conjIndex hG
  -- `ζ_ind = Ind 1_H` is real.
  have hind_real : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  -- `S`-memberships of `ζ_0` and `ζ̄_0 = ζ_{j₁}`.
  have hzd_mem : (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ∈ data.typeIHyp.Sset := data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)
  have hj₁_mem : (data.h78 hG).hyp76.zeta j₁ ∈ data.typeIHyp.Sset :=
    data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hj₁ne)
  have hsupp' : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support hG hj₁
  have hagree := coherence_hagree_dadeMap hyp data.coh hzd_mem hj₁_mem
    (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  -- `dade.toDadeMap` on supported functions is the ℤ-linear `dadeIntegralCharacterMap`.
  have hbridge : ∀ (φ : ClassFunction ↥L ℂ)
      (hφ : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (typeIA L data.typeIHyp.typeI) L),
      dade.toDadeMap ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
        = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade φ := by
    intro φ hφ
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp dade hφ]
    rfl
  have hiz_supp : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
        - (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L :=
    (data.h78 hG).diff_support
  have hbeta_eq : (data.h78 hG).beta
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade
          ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
            - (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)) := by
    rw [← hbridge _ hiz_supp]; rfl
  have hconjbridgeL : ∀ X : ClassFunction ↥L ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hconjbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hLHS : (data.h78 hG).beta.conj - (data.h78 hG).beta
      = dade.toDadeMap ⟨(data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
          - (1 : ℂ) • (data.h78 hG).hyp76.zeta j₁,
          (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [hbridge _ hsupp', hbeta_eq,
      hconjbridgeG (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade _),
      ← OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm hyp dade
        Complex.conjAe.toRingEquiv hiz_supp, ← hconjbridgeL, ← map_sub]
    congr 1
    rw [one_smul, ClassFunction.conj_sub, hind_real, ← hj₁]
    abel
  rw [hLHS, hagree, ← hj₁, data.h78_nu_eq, one_smul]

/-- **The (7.9) residual `Δ = β − 1_G + ζ_0^ν` is real** (odd order). -/
theorem delta_isReal (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ClassFunction.IsReal (data.h78 hG).delta := by
  obtain ⟨j₁, hj₁ne, hj₁⟩ := data.exists_conjIndex hG
  have hzd_mem : (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ∈ data.typeIHyp.Sset := data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)
  have hj₁_mem : (data.h78 hG).hyp76.zeta j₁ ∈ data.typeIHyp.Sset :=
    data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hj₁ne)
  have h2 : ∃ ψ ∈ data.typeIHyp.Sset,
      ψ ≠ (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct :=
    ⟨_, hj₁_mem, by rw [hj₁]; exact (data.h78_zeta_ne_conj hG hG.odd).symm⟩
  have hnu_conj : ((data.h78 hG).nu
        ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)).conj
      = (data.h78 hG).nu
        ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [data.h78_nu_eq]
    exact data.coherence_extension_conj hG hzd_mem h2
  exact _root_.OddOrder.Peterfalvi.S09.delta_isReal (data.h78 hG) hnu_conj
    (data.beta_conj_sub hG)

/-- **The residual `Δ` is a virtual character** (coherence + irreducible sources). -/
theorem delta_mem_ZIrr (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).delta ∈ ZIrr G :=
  (data.h78 hG).delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (data.isCoherentSourceSet hG) rfl (data.h78_ind_mem_ZIrr hG)
    (data.h78_zeta_irreducible hG)

/-- **The conjugate of any nontrivial family member is a family member**:
for `i ≠ ind1H` there is `i' ≠ ind1H` with `ζ_{i'} = ζ̄_i`. -/
theorem exists_conjIndex_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    ∃ i', i' ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
  have := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta i).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ i)) : ClassFunction _ ℂ) := by
    rw [data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ i)).symm
  obtain ⟨i', hi'_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ i))
  have hi'_conj : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hi'_range
  refine ⟨i', ?_, hi'_conj⟩
  intro hi'1
  -- else `ζ̄_i = ζ_{ind1H} = Ind 1_H` is real, so `ζ_i = Ind 1_H`, contra `i ≠ ind1H`.
  have hind_real : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  refine hi (data.inj ?_)
  have h1 : ((data.h78 hG).hyp76.zeta i).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    rw [← hi'_conj, hi'1]
  calc (data.h78 hG).hyp76.zeta i
      = (((data.h78 hG).hyp76.zeta i).conj).conj := (ClassFunction.conj_conj _).symm
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by rw [h1, hind_real]

/-- **No nontrivial family member is real** (odd order): `ζ_i ≠ ζ̄_i` for `i ≠ ind1H`. -/
theorem zeta_ne_conj_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta i ≠ ((data.h78 hG).hyp76.zeta i).conj := by
  have := data.kernelIn_normal
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial hi)
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  -- `ζ_i(1) = [L:H]·θ_i(1) ≥ [L:H] > 1`, so `ζ_i` is nontrivial.
  obtain ⟨di, hdi_pos, hdi⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  have hdeg : (data.h78 hG).hyp76.zeta i (1 : ↥L)
      = ((data.kernelIn).index : ℂ) * (di : ℂ) := by
    rw [data.h78_zeta_eq]
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) = _
    rw [ClassFunction.induce_apply_one, hdi]
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta i, hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta i = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : ((data.kernelIn).index : ℂ) * (di : ℂ) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    have : (data.kernelIn).index * di = 1 := by exact_mod_cast hone
    have h1 : (data.kernelIn).index = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_right this with h; omega
    omega
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **`ζ_i − ζ̄_i` is supported on `A(L)`** for any `i ≠ ind1H`. -/
theorem zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)}
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).hyp76.zeta i - (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  have := data.kernelIn_normal
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hi', ClassFunction.conj_apply] at hx
  refine (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨?_, ?_⟩
  · by_contra hxH
    apply hx
    rw [(data.h78 hG).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH, star_zero, sub_zero]
  · intro hx1
    apply hx
    rw [hx1]
    -- `ζ_i(1)` is real (`induce_apply_one_star`).
    have hreal : star ((data.h78 hG).hyp76.zeta i (1 : ↥L))
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) := by
      rw [data.h78_zeta_eq]
      exact induce_apply_one_star data.kernelIn (data.θ i)
    rw [hreal, sub_self]

/-- **`ζ_i^ν − ζ̄_i^ν` is supported in the Dade support** for any `i ≠ ind1H`. -/
theorem nu_zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
        - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')).support
      ⊆ (data.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  have := data.kernelIn_normal
  have hzi_mem : (data.h78 hG).hyp76.zeta i ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]; exact data.zeta_mem_Sset hi
  have hi'_mem : (data.h78 hG).hyp76.zeta i' ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]
    exact data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hsupp' : ((data.h78 hG).hyp76.zeta i
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support_at hG hi'
  have hagree := coherence_hagree_dadeMap data.typeIHyp.dadeData.dade
    data.coh hzi_mem hi'_mem (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  have heq : (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
      - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')
      = (data.typeIHyp.dadeData.dade.fullDadeIsometryData).toDadeMap
          ⟨_, (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [data.h78_nu_eq,
      ← one_smul ℂ (data.coh.extension ((data.h78 hG).hyp76.zeta i'))]
    exact hagree.symm
  rw [heq]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  have hdade := (data.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeMap
  exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)

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

/-- **`⟨ζ_i^ν, ζ̄_i^ν⟩ = 0`**: the conjugate pair is orthonormal (`ν`-isometry +
distinct irreducibles). -/
theorem nu_zeta_inner_nu_conj_eq_zero (hodd : Odd (Nat.card G))
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')) = 0 := by
  rw [(data.h78 hG).nu_isometry i i' hi hi'_ne]
  have hirr_i := data.zeta_irreducible_at hG hi
  have hirr_i' : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i') :=
    data.zeta_irreducible_at hG (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hne : (data.h78 hG).hyp76.zeta i ≠ (data.h78 hG).hyp76.zeta i' := by
    rw [hi']
    exact data.zeta_ne_conj_at hG hi hodd
  have h := irreducibleCharacter_inner_eq_ite
    (⟨_, hirr_i⟩ : IrreducibleCharacter ↥L) ⟨_, hirr_i'⟩
  rwa [if_neg (fun heq => hne (congrArg Subtype.val heq))] at h

/-- **Existence of the bundle for any type-I maximal subgroup** (Peterfalvi (12.1) +
(12.6) + (12.7)): the Dade setup from `exists_typeI_hypothesis`, the Frobenius witness
from the headline (12.7) `typeI_frobenius`, the coherence from
`frobenius_typeI_coherent`, and the placed family from
`exists_witness_placed_family`. -/
theorem nonempty (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G) (hLtypeI : IsTypeI L) :
    Nonempty (TypeICoherent78Data L) := by
  classical
  obtain ⟨typeIHyp⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis hG hLmax hLtypeI
  obtain ⟨fdata, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV hLmax hLtypeI
  -- Transport the Frobenius witness to `typeIHyp`'s kernel (both are `L_F`).
  have hHeq : fdata.typeI.typeF.H = typeIHyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, typeIHyp.typeI.typeF.H_eq]
  have hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((typeIHyp.typeI.typeF.H).subgroupOf L) fdata.complement := by
    rw [← hHeq]; exact fdata.frobenius
  obtain ⟨coh⟩ := OddOrder.Peterfalvi.S14.frobenius_typeI_coherent hG typeIHyp
    ⟨fdata.complement, hFrob⟩
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ :=
    OddOrder.Peterfalvi.S14.exists_witness_placed_family typeIHyp
  exact ⟨{ typeIHyp := typeIHyp
           C := fdata.complement
           hFrob := hFrob
           coh := coh
           n := n
           θ := θ
           ind1H := ind1H
           ind1H_ne_zero := hind1H
           deg0 := hdeg0
           triv := htriv
           inj := hinj
           cover := hcover
           typeIA_eq :=
             OddOrder.Peterfalvi.S14.Hypothesis.typeIA_eq_sharp hG hnoV typeIHyp }⟩

end TypeICoherent78Data

section Pairing

variable [Finite G] {L M : Subgroup G}

variable (dataL : TypeICoherent78Data L) (dataM : TypeICoherent78Data M)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- **The (7.9) cross-orthogonality for the pair**: `⟨ζ_L^ν, ζ_M^ν⟩ = 0`, via the
conjugate-index mechanism of both sides. -/
theorem hypothesis79OfNonconjugate_zetaImage_cross_eq_zero
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M) :
    ClassFunction.inner
        (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).firstZetaImage
        (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).secondZetaImage = 0 := by
  obtain ⟨j₁, hj₁ne, hj₁⟩ := dataL.exists_conjIndex hG
  obtain ⟨j₂, hj₂ne, hj₂⟩ := dataM.exists_conjIndex hG
  exact (hypothesis79OfNonconjugate dataL dataM hG hL hM
      hnc).zetaImage_cross_eq_zero_of_conjIndex
    (dataL.isCoherentSourceSet hG) rfl (dataM.isCoherentSourceSet hG) rfl
    (dataL.h78_zeta_irreducible hG) (dataM.h78_zeta_irreducible hG)
    hj₁ne hj₁ (dataL.h78_zeta_ne_conj hG hG.odd)
    hj₂ne hj₂ (dataM.h78_zeta_ne_conj hG hG.odd)
    (dataL.nu_zeta_sub_conj_support hG hj₁ne hj₁)
    (dataM.nu_zeta_sub_conj_support hG hj₂ne hj₂)

/-- **The `(Δ_L, Δ_M)` cross term is an even integer** (Peterfalvi (7.9) parity): both
residuals are real virtual characters orthogonal to `1_G`, so `cfdot_real_vchar_even`
applies with vanishing trivial components. -/
theorem hypothesis79OfNonconjugate_delta_cross_even
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M) :
    ∃ z : ℤ,
      ClassFunction.inner
          (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).first.delta
          (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).second.delta = (z : ℂ) ∧
        Even z := by
  obtain ⟨m, a, b, hm, ha, hb, heven⟩ := cfdot_real_vchar_even hG.odd
    (dataL.delta_mem_ZIrr hG) (dataL.delta_isReal hG)
    (dataM.delta_mem_ZIrr hG) (dataM.delta_isReal hG)
  refine ⟨m, hm.symm, ?_⟩
  -- `a = ⟨Δ_L, 1_G⟩ = 0` (`delta_orth_one`), so `Even (m − a·b) = Even m`.
  have ha0 : a = 0 := by
    have h := (dataL.h78 hG).delta_orth_one (dataL.betaDecomp hG)
    rw [show (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        = Hypothesis71.constOne G from rfl, h] at ha
    exact_mod_cast ha
  rw [ha0] at heven
  simpa using heven

/-- **The Peterfalvi (7.9) dichotomy for a non-conjugate type-I pair**:
`(β_L, ζ_M^ν) ≠ 0 ∨ (β_M, ζ_L^ν) ≠ 0`.  This is the character-theoretic heart of the
(14.14) orthogonality switch. -/
theorem pairing_dichotomy
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M) :
    (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).conclusion :=
  (hypothesis79OfNonconjugate dataL dataM hG hL hM
      hnc).conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    (dataL.isCoherentSourceSet hG) rfl (dataM.isCoherentSourceSet hG) rfl
    (dataL.h78_ind_mem_ZIrr hG) (dataL.h78_zeta_irreducible hG)
    (dataM.h78_ind_mem_ZIrr hG) (dataM.h78_zeta_irreducible hG)
    (dataL.betaDecomp hG) (dataM.betaDecomp hG)
    (hypothesis79OfNonconjugate_zetaImage_cross_eq_zero dataL dataM hG hL hM hnc)
    (hypothesis79OfNonconjugate_delta_cross_even dataL dataM hG hL hM hnc)

end Pairing

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

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace LHypothesis

/-- The subgroup `L` supplied in **Peterfalvi (14.3)** is type I, as witnessed
by the Frobenius data inherited from (13.17). -/
theorem isTypeI {hyp : Hypothesis (G := G)} (Ldata : LHypothesis hyp) :
    IsTypeI Ldata.L := by
  rw [← Ldata.typeI_data_L_eq]
  exact ⟨Ldata.typeI_data.frobenius.typeI⟩

end LHypothesis

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

/-- **Peterfalvi (13.12), `T`-side `d = 1` in the Section 16 context** (issue 9077):
`V ⊓ C_G(Q) = ⊥`.  The honest (13.4) character-degree producer supplies `D = ⊥`, and the
canonical identity `D = V ⊓ C_G(Q)` turns it into the faithful-action statement.  This downstream
placement avoids the genuine import cycle from `S15_SAndTBasic` to the character-degree layer. -/
theorem Hypothesis.V_inf_centralizer_Q_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.base.V ⊓ Subgroup.centralizer (hyp.base.Q : Set G) = ⊥ := by
  rw [← hyp.base.D_eq]
  exact (T_side_caseB_facts hG hyp).1

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

/-- **(14.7) `hPU_disj` input**: `P ∩ U = 1`.  Since `P` is elementary abelian it
centralizes itself, so `P ⊓ U ≤ U ⊓ C_G(P) = C = 1` by (13.12) `c = 1`, supplied by
the Core λ-dichotomy endpoint. -/
theorem P_inf_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.P ⊓ hyp.base.U = ⊥ := by
  obtain ⟨data, _⟩ := OddOrder.Peterfalvi.S15.basic_structure hG hyp.base
  have : IsMulCommutative ↥hyp.base.P :=
    IsMulCommutative.of_comm data.P_elementaryAbelian.comm
  have hP_le_cent : hyp.base.P ≤ Subgroup.centralizer (hyp.base.P : Set G) :=
    Subgroup.le_centralizer (H := hyp.base.P)
  have hC_bot : hyp.base.C = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [← hyp.base.c_eq_card_C,
      hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply]
  rw [eq_bot_iff, ← hC_bot, hyp.base.C_eq]
  exact le_inf inf_le_right (inf_le_left.trans hP_le_cent)

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

/-- **Peterfalvi (14.5)**: there is an element `y ∈ Q` such that `L = H ⋊ (W₁ W₂^y)`.
The downstream-relevant content of the split is that the conjugate `W₂^y` lands in the
Frobenius complement of `L` (the complement `W₁W₂^y`); this is the concrete form consumed by
`u_modEq_one_mod_p_of_LHypothesis` (the (14.7) fixed-point-free value argument) and, through it,
the part-(14.2.b) normalizer input `W₂^y ≤ N_G(U)`.  Its proof rules out the alternative
`L = H ⋊ W₁` of (13.17.c) via (13.19.c1)/(13.2.a). -/
theorem exists_y_L_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ y ∈ hyp.base.Q, (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Ldata.typeI_data.frobenius.complement.map (Ldata.typeI_data.L).subtype :=
  Ldata.typeI_data.exists_y_W2_conj_le_complement

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

/-- **(14.7) `hμ_range` input**: any injective `μ : U →* 𝔽_{p^q}ˣ` with `|U| = (p^q-1)/(p-1)`
has image exactly the norm-one units `U*`.  Both are subgroups of the cyclic group `𝔽_{p^q}ˣ`
of the same order `d = (p^q-1)/(p-1)`, hence both equal the unique subgroup `{x | x^d = 1}` of
that order (`= ker (powMonoidHom d)`, whose card is `gcd(p^q-1, d) = d`). -/
theorem mu_range_eq_normOneUnits {hyp : Hypothesis (G := G)}
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hinj : Function.Injective μ) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  set d := (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) with hd
  have hq0 : hyp.base.q ≠ 0 := hyp.base.q_prime.ne_zero
  have hGcard : Nat.card (GaloisField hyp.base.p hyp.base.q)ˣ = hyp.base.p ^ hyp.base.q - 1 := by
    rw [Nat.card_units, GaloisField.card hyp.base.p hyp.base.q hq0]
  have hpm1_dvd : (hyp.base.p - 1) ∣ (hyp.base.p ^ hyp.base.q - 1) := by
    have h1 : (1 : ℕ) ≡ hyp.base.p [MOD (hyp.base.p - 1)] :=
      (Nat.modEq_iff_dvd' (by have := hyp.base.p_prime.two_le; omega)).mpr dvd_rfl
    have hq1 : (1 : ℕ) ≡ hyp.base.p ^ hyp.base.q [MOD (hyp.base.p - 1)] := by
      simpa using h1.pow hyp.base.q
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by have := hyp.base.p_prime.two_le; omega))).mp
      hq1
  have hd_dvd : d ∣ (hyp.base.p ^ hyp.base.q - 1) :=
    ⟨hyp.base.p - 1, (Nat.div_mul_cancel hpm1_dvd).symm⟩
  have hkercard : Nat.card
      (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker = d := by
    rw [IsCyclic.card_powMonoidHom_ker, hGcard, Nat.gcd_eq_right hd_dvd]
  have hμcard : Nat.card (μ.range) = d := by
    have hcU := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hu_full] at hcU
    exact hcU
  have hncard :
      Nat.card (OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) = d :=
    OddOrder.BG.AppC.NormSet.normOneUnits_card hyp.base.p hyp.base.q hq0
  have hsub : ∀ (K : Subgroup (GaloisField hyp.base.p hyp.base.q)ˣ), Nat.card K = d →
      K ≤ (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker := by
    intro K hK x hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have hord : orderOf x ∣ d := by
      have h := orderOf_dvd_natCard (⟨x, hx⟩ : K)
      rw [hK] at h
      rwa [← orderOf_injective K.subtype (Subgroup.subtype_injective K) ⟨x, hx⟩] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hord
  have hμeq : μ.range =
      (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker :=
    Subgroup.eq_of_le_of_card_ge (hsub _ hμcard) (le_of_eq (hkercard.trans hμcard.symm))
  have hneq : OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q =
      (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker :=
    Subgroup.eq_of_le_of_card_ge (hsub _ hncard) (le_of_eq (hkercard.trans hncard.symm))
  rw [hμeq, hneq]

/-- **(14.7)/(14.2)(a) field model carrying the prime line to `W₂`.**  Chains the Singer
field model `exists_pu_field_repr` with the prime-line rescaling `field_repr_rescale_to_W2`,
producing the full `(e, μ)` package that `fieldNormalizerData_of_repr` consumes: an additive
isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}`, an injective character `μ : U →* 𝔽_{p^q}ˣ`, the
`U`-equivariance `hcompat`, and the prime-line/`W₂` identification `hW2`.  Cites the §13
producers `basic_structure` (`|P| = p^q`) and `c_eq_one` (`U` faithful) through
`exists_pu_field_repr`; its extra structural input is `W₂ ≤ P`. -/
theorem exists_pu_field_repr_W2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
      (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
      Function.Injective μ ∧
      (∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
              ↥hyp.base.P))
            = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x)) ∧
      (((Submodule.span (ZMod hyp.base.p)
            ({(1 : GaloisField hyp.base.p hyp.base.q)} :
              Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup).map
          (fieldNormalizerKernelTransport hyp e) = hyp.base.W2 := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  obtain ⟨e₀, μ, hμinj, hcompat₀⟩ := exists_pu_field_repr hG hyp hu_full
  obtain ⟨e, hcompat, hW2⟩ := field_repr_rescale_to_W2 hyp hW2_le_P e₀ μ hcompat₀
  exact ⟨e, μ, hμinj, hcompat, hW2⟩

/-- **(14.7) assembly engine.**  Given the §13/§14-gated structural facts as explicit
hypotheses — the cyclotomic value `|U| = (p^q-1)/(p-1)` (14.7), `U` cyclic (13), `W₂ ≤ P`
(13), the coprimality `gcd((p^q-1)/(p-1), p-1) = 1` (14.7), and part (14.2)(b)
(`Q` elementary abelian, `W₂ ≤ N_G(Q)`, and a `y ∈ Q` with `W₂^y ≤ N_G(U)`) — the concrete
`FieldNormalizerData` exists.  Every step is one of the proven (14.7) producers:
`exists_pu_field_repr_W2` (field model + prime line → `W₂`), `mu_range_eq_normOneUnits`
(`μ` onto `U*`), `conj_mem_P`/`P_inf_U_eq_bot` (the kernel/complement intersection), assembled
by the σ-bridge `fieldNormalizerData_of_repr`.  This engine carries no `sorry`; it is gated only
through the §13 producers `basic_structure`/`c_eq_one` cited inside `exists_pu_field_repr_W2`
and `P_inf_U_eq_bot` (Lane B), so it becomes unconditional exactly when those land. -/
theorem field_normalizer_of_U_characteristic_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P)
    (hcyc : Nat.Coprime
      ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) (hyp.base.p - 1))
    (hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q)
    (hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G))
    (yQ : G) (hyQ_mem : yQ ∈ hyp.base.Q)
    (hW2_conj_y : MulAut.conj yQ • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨e, μ, hμinj, hcompat, hW2⟩ := exists_pu_field_repr_W2 hG hyp hu_full hW2_le_P
  exact fieldNormalizerData_of_repr hyp e μ hμinj
    (mu_range_eq_normOneUnits hu_full μ hμinj) (conj_mem_P hyp) hcompat hW2
    (P_inf_U_eq_bot hG hyp) hcyc hQ_elemAb hW2_norm_Q yQ hyQ_mem hW2_conj_y

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem cyclotomic_quotient_modEq_one_mod_base {p q : ℕ}
    (hp2 : 2 ≤ p) (hqpos : 0 < q) :
    (p ^ q - 1) / (p - 1) ≡ 1 [MOD p] := by
  have hsum_eq : ∑ k ∈ Finset.range q, p ^ k = (p ^ q - 1) / (p - 1) :=
    Nat.geomSum_eq hp2 q
  rw [← hsum_eq]
  rw [show q = (q - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  have hzero : (∑ k ∈ Finset.range (q - 1), p ^ (k + 1)) ≡ 0 [MOD p] := by
    rw [Nat.modEq_zero_iff_dvd]
    refine Finset.dvd_sum fun k _hk => ?_
    exact dvd_pow_self p (Nat.succ_ne_zero k)
  simpa using hzero.add_right 1

/-- **Peterfalvi (14.7) value argument** (arithmetic core).  In case (9.7.b), the
`p ≡ 1 mod q` branch of (13.15) is incompatible with `u ≡ 1 mod p` — the congruence the
fixed-point-free action of `W₂^y` on `U` supplies in (14.7).  In that branch
`q · u = (p^q-1)/(p-1) ≡ 1 mod p` (geometric sum), so `q ≡ q·u ≡ 1 mod p` (using
`u ≡ 1 mod p`), forcing `p ∣ q - 1` against `q < p`.  Hence `u` takes its full cyclotomic
value and `q ∤ (p-1)` (i.e. `¬ p ≡ 1 mod q`).  Reduces the (14.7) value argument to the single
fixed-point-free congruence `u ≡ 1 mod p`; takes the case-(b) data `CaseBForSData` as a
hypothesis. -/
theorem u_eq_full_of_caseB_of_u_modEq_one_mod_p {hyp : Hypothesis (G := G)}
    (Sdata : CaseBForSData hyp) (hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p]) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) ∧
      ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] := by
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · exfalso
    have hqdvd : hyp.base.q ∣ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
      OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one hyp.base.p_prime hmod
    have hu_div : hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q := by
      rw [Sdata.u_eq_of_p_modEq_one hmod, Nat.div_div_eq_div_mul,
        Nat.mul_comm (hyp.base.p - 1) hyp.base.q]
    have hqu : hyp.base.q * hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
      rw [hu_div, Nat.mul_div_cancel' hqdvd]
    have hC_mod : (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) ≡ 1 [MOD hyp.base.p] :=
      cyclotomic_quotient_modEq_one_mod_base hyp.base.p_prime.two_le hyp.base.q_prime.pos
    have hqu_mod : hyp.base.q * hyp.base.u ≡ 1 [MOD hyp.base.p] := by rw [hqu]; exact hC_mod
    have hqu_mod2 : hyp.base.q * hyp.base.u ≡ hyp.base.q * 1 [MOD hyp.base.p] :=
      Nat.ModEq.mul_left hyp.base.q hu_mod_p
    have hq_mod : hyp.base.q ≡ 1 [MOD hyp.base.p] := by
      have h := hqu_mod2.symm.trans hqu_mod
      simpa using h
    have hp_dvd : hyp.base.p ∣ hyp.base.q - 1 :=
      (Nat.modEq_iff_dvd' hyp.base.q_prime.one_lt.le).mp hq_mod.symm
    have hqpos : 0 < hyp.base.q - 1 := by have := hyp.base.three_le_q; omega
    have hple : hyp.base.p ≤ hyp.base.q - 1 := Nat.le_of_dvd hqpos hp_dvd
    have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
    omega
  · exact ⟨Sdata.u_eq_of_not_modEq_one hmod, hmod⟩

/-- **(14.7) assembly from the fixed-point-free congruence.**  The tightest reduction of (14.7):
given the (14.7) fixed-point-free congruence `u ≡ 1 mod p` (the `W₂^y`-on-`U` input), `U` cyclic,
`W₂ ≤ P`, and part (14.2)(b), the field-normalizer data exists.  The value argument
`u_eq_full_of_caseB_of_u_modEq_one_mod_p` turns `u ≡ 1 mod p` into `u = (p^q-1)/(p-1)` and
`q ∤ (p-1)` (using the case-(b) certificate `caseB_for_S Ldata`), which then feed
`field_normalizer_of_U_characteristic_of_inputs`.  The cardinal substitution uses the Core
λ-dichotomy endpoint for (13.12). -/
theorem field_normalizer_of_U_characteristic_of_fpf [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp)
    (hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p])
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P)
    (hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q)
    (hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G))
    (yQ : G) (hyQ_mem : yQ ∈ hyp.base.Q)
    (hW2_conj_y : MulAut.conj yQ • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨Sdata, _⟩ := caseB_for_S hG hyp Ldata
  obtain ⟨hu_full, hnot_mod⟩ := u_eq_full_of_caseB_of_u_modEq_one_mod_p Sdata hu_mod_p
  -- bridge `|U| = u` via (13.12) `c = 1`
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc,
      hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply, mul_one]
  have hcyc : Nat.Coprime
      ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) (hyp.base.p - 1) :=
    OddOrder.Peterfalvi.S15.cyclotomic_quotient_coprime_of_not_modEq_one
      hyp.base.p_prime hyp.base.q_prime hnot_mod
  exact field_normalizer_of_U_characteristic_of_inputs hG hyp (hU_card.trans hu_full)
    hW2_le_P hcyc hQ_elemAb hW2_norm_Q yQ hyQ_mem hW2_conj_y

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (13.19.b), the M-side `η`-grid orthogonality of `ψ^{τ₁} = ζ_M^ν`.**

The distinguished coherent image `ψ^{τ₁} = ζ_M^ν` (`= (dataM.h78 hG).nu (ζ_{zetaDistinct})`)
is orthogonal to the entire `η`-grid.  This is the sorry-free (3.6)–(3.8)/(13.19.b) engine
`eta_orthogonal_of_norm_one_pair_vanish` (`S16_GridExpansion`) applied to the conjugate pair
`(ζ_M^ν, ζ̄_M^ν)`: the unit norms (`nu_zeta_norm_one`), the conjugate distinctness
`⟨ζ_M^ν, ζ̄_M^ν⟩ = 0` (`nu_zeta_inner_nu_conj_eq_zero`), and the `ℤ[Irr G]` memberships
(`coh.extension_mem_ZIrr` on `ζ ∈ 𝒮`) are all supplied by the `TypeICoherent78Data` coherence
bundle.  The single genuine §13/§14 input is `hDadeAvoid` = **Peterfalvi (13.19.a)**: the M-side
Dade support `Ã(M)` avoids the regular-set saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`, so the
conjugate difference `ζ_M^ν − ζ̄_M^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`)
vanishes on `Ŵ^G`. -/
theorem caseB_eta_orthogonal_psi [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)) = 0 := by
  classical
  -- distinctness datum for the distinguished index `zetaDistinct = 0` and its conjugate `i'`
  have hjne : (dataM.h78 hG).zetaDistinct ≠ dataM.ind1H := by
    have h := (dataM.h78 hG).zetaDistinct_ne_ind1H
    rwa [dataM.h78_ind1H_eq] at h
  obtain ⟨i', hi'_ne, hi'⟩ := dataM.exists_conjIndex_at hG hjne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)
      ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zetaDistinct_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset (Ne.symm dataM.ind1H_ne_zero)))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta i') ∈ ZIrr G := by
    have hi'ne_data : i' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hi'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hi'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG (dataM.h78 hG).zetaDistinct_ne_ind1H
  have hconj1 := dataM.nu_zeta_norm_one hG hi'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hjne hi'_ne hi'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hjne hi'_ne hi'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta i')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **A Frobenius complement acts fixed-point-freely on its kernel** (ambient-group form).
If `↥L` is a Frobenius group with kernel `H.subgroupOf L` and complement `compl`, and `H ≤ L`,
then every `a ≠ 1` lying — as a `G`-element — in the complement image `compl.map L.subtype`
conjugates no nontrivial `u ∈ H` to itself: `a * u * a⁻¹ ≠ u`.  This transports
`IsFrobeniusGroup.conj_frobenius` from `↥L` down to `G` through `L.subtype`. -/
theorem isFrobeniusGroup_conj_ne_of_mem_map_complement
    {L H : Subgroup G} {compl : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (H.subgroupOf L) compl)
    (hHL : H ≤ L) {a : G} (ha_mem : a ∈ compl.map L.subtype) (ha_ne : a ≠ 1)
    {u : G} (hu_mem : u ∈ H) (hu_ne : u ≠ 1) :
    a * u * a⁻¹ ≠ u := by
  obtain ⟨a', ha'_compl, ha'_eq⟩ := Subgroup.mem_map.mp ha_mem
  have ha'_ne : a' ≠ 1 := by
    intro h
    rw [h] at ha'_eq
    exact ha_ne (by simpa using ha'_eq.symm)
  have hmemL : u ∈ L := hHL hu_mem
  have hu'_ker : (⟨u, hmemL⟩ : ↥L) ∈ H.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]; exact hu_mem
  have hu'_ne : (⟨u, hmemL⟩ : ↥L) ≠ 1 := fun h => hu_ne (congrArg Subtype.val h)
  have hconj := hfrob.conj_frobenius a' ha'_compl ha'_ne ⟨u, hmemL⟩ hu'_ker hu'_ne
  intro hcontra
  apply hconj
  apply Subtype.coe_injective
  change ((a' * ⟨u, hmemL⟩ * a'⁻¹ : ↥L) : G) = ((⟨u, hmemL⟩ : ↥L) : G)
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, InvMemClass.coe_inv,
    show ((a' : G)) = a from ha'_eq]
  exact hcontra

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace NonConjugateHypothesis

/-- **Peterfalvi (14.13)**: since `h = |H|` and `H` is a subgroup of the
minimal odd-order group, `h` is odd. -/
theorem h_odd [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    Odd nc.h := by
  rw [nc.h_eq_card_H]
  exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card nc.Ldata.H)

/-- **Peterfalvi (14.5)** cardinal consequence: `u` divides `h = |H|`.
The subgroup `U` lies in the Fitting kernel `H` of the type-I subgroup over
`N_G(U)`, while (13.12) gives `c = 1`; hence `|U| = u` and `u ∣ |H|`. -/
theorem u_dvd_h [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    hyp.base.u ∣ nc.h := by
  rw [nc.h_eq_card_H]
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc,
      hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply, mul_one]
  have hU_le_H : hyp.base.U ≤ nc.Ldata.H := by
    rw [← nc.Ldata.typeI_data_H_eq]
    exact nc.Ldata.typeI_data.U_le_H
  have hdvd : Nat.card ↥hyp.base.U ∣ Nat.card ↥nc.Ldata.H :=
    Subgroup.card_dvd_of_le hU_le_H
  simpa [hU_card] using hdvd

/-- **Peterfalvi (14.5)** cardinal congruences for `h = |H|`.  The type-I
Frobenius structure has kernel `M_F = H`; by (14.5) its complement has order
`p q`.  Isaacs Lemma 6.1 gives `|H| ≡ 1 mod |C|`, hence both congruences
modulo `p` and modulo `q`. -/
theorem h_modEq_one_mod_p_and_q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    nc.h ≡ 1 [MOD hyp.base.p] ∧ nc.h ≡ 1 [MOD hyp.base.q] := by
  let H0 : Subgroup G := nc.Ldata.typeI_data.frobenius.typeI.typeF.H
  have hH0_eq_typeI_H : H0 = nc.Ldata.typeI_data.H := by
    dsimp [H0]
    rw [nc.Ldata.typeI_data.frobenius.typeI.typeF.H_eq,
      nc.Ldata.typeI_data.H_eq_LF]
  have hH0_eq_H : H0 = nc.Ldata.H :=
    hH0_eq_typeI_H.trans nc.Ldata.typeI_data_H_eq
  have hkernel_card :
      Nat.card ↥(H0.subgroupOf nc.Ldata.typeI_data.L) = Nat.card ↥nc.Ldata.H := by
    have hH0_card :
        Nat.card ↥(H0.subgroupOf nc.Ldata.typeI_data.L) = Nat.card ↥H0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
        dsimp [H0]
        exact nc.Ldata.typeI_data.frobenius.typeI.typeF.H_le)).toEquiv
    rw [hH0_card, hH0_eq_H]
  have hmod_pq : nc.h ≡ 1 [MOD hyp.base.p * hyp.base.q] := by
    have hmod := nc.Ldata.typeI_data.frobenius.frobenius.card_kernel_modEq_one
    rw [hkernel_card, nc.Ldata.typeI_complement_card_eq_pq] at hmod
    rwa [nc.h_eq_card_H]
  exact ⟨hmod_pq.of_dvd (dvd_mul_right hyp.base.p hyp.base.q),
    hmod_pq.of_dvd (dvd_mul_left hyp.base.q hyp.base.p)⟩

end NonConjugateHypothesis

namespace Hypothesis

/-- **Peterfalvi (14.5)** fixed-point-free cardinal consequence for `U`:
`u ≡ 1 mod q`.  The Frobenius action of `W₁` on `U` gives
`|U| ≡ 1 mod |W₁|`; using (13.12), `|U| = u`, and the definition
`q = |W₁|` gives the stated congruence. -/
theorem u_modEq_one_mod_q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.u ≡ 1 [MOD hyp.base.q] := by
  rcases OddOrder.Peterfalvi.S15.basic_structure _hG hyp.base with ⟨data, _hdata⟩
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc,
      hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply, mul_one]
  have hU_sub_card :
      Nat.card ↥(hyp.base.U.subgroupOf (hyp.base.U ⊔ hyp.base.W1)) =
        Nat.card ↥hyp.base.U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : hyp.base.U ≤ hyp.base.U ⊔ hyp.base.W1)).toEquiv
  have hW1_sub_card :
      Nat.card ↥(hyp.base.W1.subgroupOf (hyp.base.U ⊔ hyp.base.W1)) =
        Nat.card ↥hyp.base.W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : hyp.base.W1 ≤ hyp.base.U ⊔ hyp.base.W1)).toEquiv
  have hmod := data.UW1_frobenius.card_kernel_modEq_one
  rwa [hU_sub_card, hW1_sub_card, hU_card, ← hyp.base.q_eq_card_W1] at hmod

/-- **Peterfalvi (14.7)** fixed-point-free congruence for `U` modulo `p`.  The conjugate
`W₂^y` has order `p = |W₂|`; if it acts fixed-point-freely on `U` — as it does in (14.7), since
`W₂^y` lies in the complement of the type-I Frobenius subgroup `L ⊇ N_G(U)` whose kernel
contains `U` — then `|U| ≡ 1 mod p`, hence (using `|U| = u` by (13.12)) `u ≡ 1 mod p`.  This is
the mod-`p` analogue of `u_modEq_one_mod_q`; it discharges the `hu_mod_p` input of the (14.7)
value argument from the fixed-point-free action. -/
theorem u_modEq_one_mod_p_of_fpf [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {y : G}
    (hW2y_norm : (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Subgroup.normalizer (hyp.base.U : Set G))
    (hfpf : ∀ a ∈ (MulAut.conj y • hyp.base.W2 : Subgroup G), a ≠ 1 →
      ∀ u ∈ hyp.base.U, u ≠ 1 → a * u * a⁻¹ ≠ u) :
    hyp.base.u ≡ 1 [MOD hyp.base.p] := by
  have hW2y_card : Nat.card ↥(MulAut.conj y • hyp.base.W2 : Subgroup G) = hyp.base.p := by
    rw [hyp.base.p_eq_card_W2]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj y) hyp.base.W2).toEquiv).symm
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc,
      hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply, mul_one]
  have h := card_modEq_one_of_prime_normalizing_fpf hyp.base.p_prime hW2y_card hW2y_norm hfpf
  rwa [hU_card] at h

end Hypothesis

/-- **Part (14.2.b) normalizer conclusion `W₂^y ≤ N_G(U)`, from the structural carrier.**
The (14.5) complement membership of `W₂^y` already forces `W₂^y ≤ N_G(U)`: each element of `W₂^y`
lies in `L`, normalizes the Fitting kernel `H ◁ L` (`maxNilpotentNormalHall_le_normalizer`), and
`U` is characteristic in `H`, so it normalizes `U`
(`mem_normalizer_map_subtype_of_characteristic`).  Shared by the (14.7) value argument and the
final field-normalizer assembly. -/
theorem W2conj_le_normalizer_U_of_LHypothesis
    {hyp : Hypothesis (G := G)} (Ldata : LHypothesis hyp)
    (hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic)
    {y : G}
    (hW2y_compl : (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Ldata.typeI_data.frobenius.complement.map (Ldata.typeI_data.L).subtype) :
    (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Subgroup.normalizer (hyp.base.U : Set G) := by
  have : (hyp.base.U.subgroupOf Ldata.H).Characteristic := hchar
  have hU_le_H : hyp.base.U ≤ Ldata.H := by
    rw [← Ldata.typeI_data_H_eq]; exact Ldata.typeI_data.U_le_H
  intro a ha
  have ha_L : a ∈ Ldata.L := by
    obtain ⟨a', -, ha'eq⟩ := Subgroup.mem_map.mp (hW2y_compl ha)
    rw [← Ldata.typeI_data_L_eq, ← ha'eq]; exact a'.2
  have ha_normH : a ∈ Subgroup.normalizer (Ldata.H : Set G) := by
    have hLnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer Ldata.L ha_L
    rwa [← Ldata.H_eq_LF] at hLnorm
  have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
    (W := Ldata.H) (C := hyp.base.U.subgroupOf Ldata.H) ha_normH
  rwa [Subgroup.map_subgroupOf_eq_of_le hU_le_H] at hmem

/-- **Peterfalvi (14.7) value-argument input, assembled from (14.3)/(13.17)/(14.5).**
With the type-I-over-`N_G(U)` carrier `Ldata` — so `L ⊇ N_G(U)` is a Frobenius group (13.17.a)
with kernel `H ⊇ U` (13.17.b) — and `U` characteristic in `H` (the standing hypothesis of
(14.7)), the element `y ∈ Q` produced by (14.5) places `W₂^y` in the Frobenius complement of `L`.
Then `W₂^y` normalizes `U` (it normalizes `H ◁ L`, and `U` is characteristic in `H`) and acts
fixed-point-freely on `U` (it is a nontrivial complement element acting on the kernel), so by
`Hypothesis.u_modEq_one_mod_p_of_fpf`, `u ≡ 1 (mod p)`.  This discharges the fixed-point-free
input of the (14.7) value argument from the structural carrier, reducing it to the (14.5)
membership `W₂^y ≤ complement`. -/
theorem u_modEq_one_mod_p_of_LHypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp)
    (hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic)
    {y : G}
    (hW2y_compl : (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Ldata.typeI_data.frobenius.complement.map (Ldata.typeI_data.L).subtype) :
    hyp.base.u ≡ 1 [MOD hyp.base.p] := by
  -- `U ≤ H` (13.17.b)
  have hU_le_H : hyp.base.U ≤ Ldata.H := by
    rw [← Ldata.typeI_data_H_eq]; exact Ldata.typeI_data.U_le_H
  -- the Frobenius kernel base `typeI.typeF.H` is `H`
  have hH0_eq_typeIH : Ldata.typeI_data.frobenius.typeI.typeF.H = Ldata.typeI_data.H := by
    rw [Ldata.typeI_data.frobenius.typeI.typeF.H_eq, Ldata.typeI_data.H_eq_LF]
  have hH0_eq_H : Ldata.typeI_data.frobenius.typeI.typeF.H = Ldata.H :=
    hH0_eq_typeIH.trans Ldata.typeI_data_H_eq
  -- `W₂^y ≤ N_G(U)` (part (14.2.b)), shared with the final assembly
  have hW2y_norm := W2conj_le_normalizer_U_of_LHypothesis Ldata hchar hW2y_compl
  -- `W₂^y` acts fixed-point-freely on `U` (Frobenius complement on the kernel)
  have hfpf : ∀ a ∈ (MulAut.conj y • hyp.base.W2 : Subgroup G), a ≠ 1 →
      ∀ u ∈ hyp.base.U, u ≠ 1 → a * u * a⁻¹ ≠ u := by
    intro a ha ha_ne u hu hu_ne
    refine isFrobeniusGroup_conj_ne_of_mem_map_complement
      Ldata.typeI_data.frobenius.frobenius
      Ldata.typeI_data.frobenius.typeI.typeF.H_le (hW2y_compl ha) ha_ne ?_ hu_ne
    rw [hH0_eq_H]; exact hU_le_H hu
  exact Hypothesis.u_modEq_one_mod_p_of_fpf hG hyp hW2y_norm hfpf

/-- **Peterfalvi (13.2.b)/(14.2.a): `W₂ ≤ P`.**  `W₂` is a `p`-group (`|W₂| = p`) inside `S`
(`W₂ ≤ W = S ⊓ T`), while `P = S_F` is a normal Hall `p`-subgroup of `S` (normal by
`maxNilpotentNormalHall_subgroupOf_normal`, Hall by `maxNilpotentNormalHall_isHall`, and a
`p`-group of order `p^q` by `basic_structure`).  Hence `W₂ ≤ P` — the `F_p ⊆ F` identification of
(14.2.a). -/
theorem W2_le_P [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.base.W2 ≤ hyp.base.P :=
  OddOrder.Peterfalvi.S15.W2_le_P _hG hyp.base

/-- **Peterfalvi (13.2.b) for `T`**: `Q` is elementary abelian (13.2.b applied to the dual subgroup
`T`) — the canonical §15 obligation `Q_elementaryAbelian_T` (`T` type-II from `T_typeII` (14.9)). -/
theorem Q_elemAbelian_S [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.base.q ↥hyp.base.Q :=
  OddOrder.Peterfalvi.S15.Q_elementaryAbelian_T _hG hyp.base (T_typeII _hG hnoV hncH0C hyp)

/-- **Peterfalvi (13.2) `S`-side structural inputs for the (14.7) field model.**  The field-model
construction (14.2.a) needs two §13 structural facts about the type-`P` subgroup `S`: `W₂ ≤ P`
(the `F_p ⊆ F` identification) and `Q` elementary abelian (13.2.b for `T`).  `W₂ ≤ P` is proved
outright (`W2_le_P`); `Q` elementary abelian is the §15 obligation `Q_elemAbelian_S`.

The field model needs **no** cyclicity of `U`: the Singer representation `exists_pu_field_repr` is
built from `U` **abelian** (Peterfalvi (13.2.a): `UW₁` is Frobenius with abelian kernel `U`; coq
`PFsection14.v` `cUU : abelian U`) via the abelian Singer irreducibility
`isSimpleModule_of_abelian_faithful_card`, and the injection `μ : U ↪ 𝔽_{p^q}^×` into the cyclic
unit
group is a *consequence* — never a hypothesis. -/
theorem S_field_model_structural_inputs [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.W2 ≤ hyp.base.P ∧
      IsElementaryAbelian hyp.base.q ↥hyp.base.Q :=
  ⟨W2_le_P _hG hyp, Q_elemAbelian_S _hG hnoV hncH0C hyp⟩

/-- **Peterfalvi (14.7)**: if `U` is characteristic in `H`, then the field-normalizer
configuration (14.2) holds.  The value argument is assembled entirely from the structural
carrier: (14.5) `exists_y_L_structure` supplies `y ∈ Q` with `W₂^y` in the Frobenius complement
of `L`; the bridge `u_modEq_one_mod_p_of_LHypothesis` turns that into `u ≡ 1 mod p`; and
`W2conj_le_normalizer_U_of_LHypothesis` supplies `W₂^y ≤ N_G(U)`.  These feed the value-argument
engine `field_normalizer_of_U_characteristic_of_fpf`.  This theorem carries **no `sorry`**: the
remaining §13 structural facts are cited as the named obligation `S_field_model_structural_inputs`
(`U` cyclic / `W₂ ≤ P` / `Q` elementary abelian), while `W₂ ≤ N_G(Q)` is discharged outright
(`W₂ ≤ W ≤ T` and `Q = T_F`). -/
theorem field_normalizer_of_U_characteristic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp)
    (hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨y, hyQ, hW2y_compl⟩ := exists_y_L_structure hG hyp Ldata
  have hmod := u_modEq_one_mod_p_of_LHypothesis hG Ldata hchar hW2y_compl
  have hW2_conj_y := W2conj_le_normalizer_U_of_LHypothesis Ldata hchar hW2y_compl
  -- §13 structural inputs (13.2.a/b, companion to `basic_structure`; Lane B / §13 group theory)
  obtain ⟨hW2_le_P, hQ_elemAb⟩ := S_field_model_structural_inputs hG hnoV hncH0C hyp
  -- `W₂ ≤ N_G(Q)` is ungated: `W₂ ≤ W ≤ T` and `Q = T_F`
  have hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    have hW2_le_W : hyp.base.W2 ≤ hyp.base.W := by
      rw [hyp.base.W_eq_join]; exact le_sup_right
    have hW_le_T : hyp.base.W ≤ hyp.base.T := by
      rw [hyp.base.W_eq_inter]; exact inf_le_right
    rw [hyp.base.Q_eq_TF]
    exact (hW2_le_W.trans hW_le_T).trans
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T)
  exact field_normalizer_of_U_characteristic_of_fpf hG hyp Ldata hmod hW2_le_P
    hQ_elemAb hW2_norm_Q y hyQ hW2_conj_y

/-- **Every subgroup of a finite cyclic group is characteristic.**  A subgroup `K` equals the
`|K|`-torsion `ker (powMonoidHom |K|) = {x | x ^ |K| = 1}`: it is contained in it (Lagrange:
`x ^ |K| = 1` for `x ∈ K`) and has the same cardinality (`|ker| = gcd(|C|, |K|) = |K|` as
`|K| ∣ |C|`).  The torsion is preserved by every automorphism `φ` since `φ x ^ d = φ (x ^ d)`,
so `K` is characteristic.  Used for the (14.12) `L ≅ M` case where `H` is cyclic. -/
theorem characteristic_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (K : Subgroup C) : K.Characteristic := by
  let : CommGroup C := IsCyclic.commGroup
  have key : ∀ A : Subgroup C, A = (powMonoidHom (Nat.card A) : C →* C).ker := by
    intro A
    have hle : A ≤ (powMonoidHom (Nat.card A) : C →* C).ker := by
      intro a ha
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have h1 : (⟨a, ha⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
      have h2 := congrArg (Subtype.val) h1
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
      exact h2
    have hdvd : Nat.card A ∣ Nat.card C := Subgroup.card_subgroup_dvd_card A
    have hcard : Nat.card (powMonoidHom (Nat.card A) : C →* C).ker = Nat.card A := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdvd]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  have hcard_eq : Nat.card ↥(K.comap φ.toMonoidHom) = Nat.card ↥K :=
    Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv (fun a => Subgroup.mem_comap))
  conv_lhs => rw [key (K.comap φ.toMonoidHom)]
  conv_rhs => rw [key K]
  rw [hcard_eq]

/-- **Peterfalvi (14.11)/(14.4)/(13.12)**: the Fitting kernel `K = M_F` of the type-I maximal
subgroup `M` over `N_G(V)` is cyclic.

This realizes the textbook route directly: by (14.11) `K = V` (`K_eq_V_index_pq`, the
(14.11.1)--(14.11.4) norm cascade), and `V` is cyclic (`V_cyclic`, 13.2.a for `T`), so `K` is
cyclic.  The remaining character-theoretic content is therefore isolated into the two named
obligations `K_eq_V_index_pq` (the (14.11) cascade, whose structural input is
`main_size_bounds_structural` and whose character input is `betaM_expansion` /
`generic_character_bound`) and `V_cyclic` (13.2.a for `T`).  Feeds the (14.12) reduction; the
`L ≅ M` case transports it to `H = L_F` purely structurally (`H_cyclic_of_L_conj_M`). -/
theorem MHypothesis_kernel_cyclic [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) : IsCyclic ↥Mdata.K := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hnoV hncH0C hyp
  rw [(K_eq_V_index_pq _hG hnoV hncH0C hyp Ldata Mdata).1]
  exact V_cyclic _hG hnoV hncH0C hyp

/-- **Peterfalvi (14.12) structural input**: in the `L ≅ M` case, `H = L_F` is cyclic.  Since
`L ≅ M` (a conjugation `MulAut.conj g`), the maximal nilpotent normal Hall subgroup is
automorphism-equivariant (`maxNilpotentNormalHall_pointwise_smul`), so `H = L_F ≅ M_F = K`;
cyclicity of `K` is the §13/§14 obligation `MHypothesis_kernel_cyclic`.  This reduction is
purely structural — the character theory is confined to `MHypothesis_kernel_cyclic`. -/
theorem H_cyclic_of_L_conj_M [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (_hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M) :
    IsCyclic ↥Ldata.H := by
  obtain ⟨g, hg⟩ := _hconj
  have := MHypothesis_kernel_cyclic _hG hnoV hncH0C hyp Mdata
  rw [Ldata.H_eq_LF]
  -- `M_F` is the `conj g`-image of `L_F`: `conj g • L_F = (conj g • L)_F = M_F = K`.
  have hmap : (maxNilpotentNormalHall Ldata.L).map ((MulAut.conj g : MulAut G) : G →* G)
      = Mdata.K := by
    rw [← pointwise_mulAut_smul_eq_map, maxNilpotentNormalHall_pointwise_smul, hg, Mdata.K_eq_MF]
  set e : ↥(maxNilpotentNormalHall Ldata.L) ≃* ↥Mdata.K :=
    (MulEquiv.subgroupMap (MulAut.conj g) (maxNilpotentNormalHall Ldata.L)).trans
      (MulEquiv.subgroupCongr hmap) with he
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

/-- **Peterfalvi (14.12)**: if `L` is conjugate to `M`, then the field-normalizer configuration
(14.2) holds.  Textbook reduction: `L ≅ M ⟹ H ≅ K` cyclic (`H_cyclic_of_L_conj_M`), so every
subgroup of `H` — in particular `U` — is characteristic (`characteristic_of_isCyclic`), and (14.7)
`field_normalizer_of_U_characteristic` applies.  Carries **no `sorry`**; gated only through the
named §13/§14 obligation `H_cyclic_of_L_conj_M`. -/
theorem field_normalizer_of_L_conj_M [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M) :
    Nonempty (FieldNormalizerData hyp) := by
  have : IsCyclic ↥Ldata.H := H_cyclic_of_L_conj_M hG hnoV hncH0C hyp Ldata Mdata hconj
  exact field_normalizer_of_U_characteristic hG hnoV hncH0C hyp Ldata
    (characteristic_of_isCyclic (hyp.base.U.subgroupOf Ldata.H))

namespace OrthogonalitySwitchData

/-- In the exceptional branch of **Peterfalvi (14.14)**, the S-side congruence
branch `p ≡ 1 mod q` is impossible: the branch has `(q,p) = (3,5)`, and
`5` is not `1 mod 3`. -/
theorem not_p_modEq_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (hcaseB : data.caseB) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] := by
  intro hmod
  have hparams := data.caseB_params hcaseB
  have hmod' : 5 ≡ 1 [MOD 3] := by
    simpa [hparams.1, hparams.2] using hmod
  unfold Nat.ModEq at hmod'
  norm_num at hmod'

/-- In the exceptional branch of **Peterfalvi (14.14)**, the S-side case-(9.7.b)
order data is forced into its full cyclotomic branch.  This is the consumer form
needed for **Peterfalvi (14.15)**. -/
theorem u_eq_full_cyclotomic_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  Sdata.u_eq_of_not_modEq_one (data.not_p_modEq_one_of_caseB hcaseB)

/-- Numerically, the exceptional branch of **Peterfalvi (14.14)** gives
`u = (5^3 - 1)/(5 - 1) = 31`, once the S-side case-(9.7.b) order data has been
materialized. -/
theorem u_eq_thirty_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB) :
    hyp.base.u = 31 := by
  have hparams := data.caseB_params hcaseB
  have hu := data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB
  rw [hparams.1, hparams.2] at hu
  norm_num at hu
  exact hu

/-- Numerically, the exceptional branch of **Peterfalvi (14.14)** gives
`v = (3^5 - 1)/(3 - 1) = 121`, once the T-side case-(9.7.b) order data from
(14.4) has been materialized. -/
theorem v_eq_one_twenty_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Tdata : CaseBForTData hyp) (hcaseB : data.caseB) :
    hyp.base.v = 121 := by
  have hparams := data.caseB_params hcaseB
  rw [Tdata.v_eq, hparams.1, hparams.2]
  norm_num

/-- **Peterfalvi (14.16)**: the numerical gap in the exceptional branch.  If
case-(b) has `(q,p)=(3,5)` and `H > U`, then the lower bound `h > 2 p q u`
gives `(h - 1)/(p q) > (v - 1)/p`; the concrete values `u=31`, `v=121` also
give `(v - 1)/p > (u - 1)/q`. -/
theorem caseB_gap_inequalities_of_h_gt_two_mul_pq_mul_u
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Tdata : CaseBForTData hyp)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB)
    (hh_lower : 2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h) :
    (((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  have hparams := data.caseB_params hcaseB
  have hu31 := data.u_eq_thirty_one_of_caseB Sdata hcaseB
  have hv121 := data.v_eq_one_twenty_one_of_caseB Tdata hcaseB
  have hh930 : 930 < nc.h := by
    have h := hh_lower
    rw [hparams.1, hparams.2, hu31] at h
    norm_num at h
    exact h
  have hh_sub_ge : 930 ≤ nc.h - 1 := by omega
  constructor
  · have hgeQ : (930 : ℚ) ≤ ((nc.h - 1 : ℕ) : ℚ) := by
      exact_mod_cast hh_sub_ge
    have hgt : (24 : ℚ) < ((nc.h - 1 : ℕ) : ℚ) / 15 := by
      nlinarith
    rw [hparams.1, hparams.2, hv121]
    norm_num
    exact hgt
  · rw [hparams.1, hparams.2, hu31, hv121]
    norm_num

/-- Pointwise-in-the-left additivity of the canonical class-function inner product over a finite
sum: `(∑ i ∈ s, f i, ψ) = ∑ i ∈ s, (f i, ψ)`.  General-purpose `ClassFunction.inner` plumbing
(hoistable to `ClassFunction.lean`). -/
theorem inner_finset_sum_left {ι : Type*} [Fintype G]
    [Invertible (Nat.card G : ℂ)] (s : Finset ι)
    (f : ι → ClassFunction G ℂ) (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (∑ i ∈ s, f i) ψ = ∑ i ∈ s, ClassFunction.inner (f i) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ClassFunction.inner_add_left, ih, Finset.sum_insert ha]

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLMBasic.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`[L : H_L] = p q` in `Subgroup.index` form** — the (14.3) complement order
(`typeICoherent78_complementIndex_eq_pq`) transported to the canonical-kernel index
`((maxNilpotentNormalHall L).subgroupOf L).index` consumed by the (13.19.c) dichotomy bounds. -/
theorem typeICoherent78_index_eq_pq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (dataL : TypeICoherent78Data Ldata.L) :
    ((maxNilpotentNormalHall Ldata.L).subgroupOf Ldata.L).index
      = hyp.base.p * hyp.base.q := by
  have hker : dataL.kernelIn = (maxNilpotentNormalHall Ldata.L).subgroupOf Ldata.L := by
    change (dataL.typeIHyp.typeI.typeF.H).subgroupOf Ldata.L = _
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  rw [← hker]
  -- `kernelIn.index = complementIndex` (both are `|L| / |H_L|`), then the complement order.
  have hmul : dataL.kernelIn.index * Nat.card ↥dataL.kernelIn = Nat.card ↥Ldata.L :=
    Subgroup.index_mul_card dataL.kernelIn
  have hce : (dataL.h78 hG).complementIndex = dataL.kernelIn.index := by
    change Nat.card ↥Ldata.L / Nat.card dataL.kernel = dataL.kernelIn.index
    rw [show Nat.card dataL.kernel = Nat.card ↥dataL.kernelIn from
        (dataL.kernelOrder_eq hG) ▸ rfl,
      ← hmul, Nat.mul_div_cancel _ Nat.card_pos]
  rw [← hce]
  exact typeICoherent78_complementIndex_eq_pq hG Ldata dataL

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLM.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

/-- **`|H_L| = h`** — the (7.8) kernel of any coherence bundle on the (14.3) `L` is the
canonical `H = L_F`, so its order is the `NonConjugateHypothesis` parameter `h`. -/
theorem typeICoherent78_card_kernel_eq_h [Finite G]
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp)
    (dataL : TypeICoherent78Data nc.Ldata.L) :
    Nat.card ↥dataL.typeIHyp.H = nc.h := by
  have hHeq : dataL.typeIHyp.H = nc.Ldata.H := by
    change dataL.typeIHyp.typeI.typeF.H = nc.Ldata.H
    rw [dataL.typeIHyp.typeI.typeF.H_eq, nc.Ldata.H_eq_LF]
  rw [nc.h_eq_card_H, hHeq]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), the L-side signed `η`-grid expansion.**  Under case-(b)
(`(q,p) = (3,5)`) and the two gap inequalities, (13.19.c) applied on the S- and T-sides gives
the (14.11.2)-style signed expansion `β_L^τ = Σ_{ij} ε_ij η_ij − ε ζ_i^ν` of the L-side, with
the removed unit-norm member an `L`-family coherent image (`i ≠ ind1H`; the `−ψ̄^{τ₁}`
alternative is the conjugate member `conjIndex`).

Proven (lane c, issue 0115 Campaign A) from the honest (14.11.2) L-side conclusion
`lSide_expansion_classification`: the removed member is the distinguished coherent image
`ζ_0^ν` with `ε = 1` **or** the conjugate family member `ζ_{j₁}^ν = ν(ζ̄_0)`
(`exists_conjIndex`) with `ε = −1`, matching the Coq `FTtype2_support_coherence` alternatives
`chi = tau1L phi \/ chi = - tau1L phi^*`.  The strict gap inputs `ub_u`/`ub_v` of the
(c1)-branch refutations are derived here from the (14.14) gap chain `hhv`/`hvu` through the
`e_L = p q` and `|H_L| = h` bridges. -/
theorem lSide_signed_eta_expansion [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (dataL : TypeICoherent78Data nc.Ldata.L)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
      ∃ i : Fin (dataL.n + 1), i ≠ dataL.ind1H ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (dataL.h78 hG).beta
          = (∑ i' : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (signs i' j : ℂ) • hyp.base.eta i' j)
            - (ε : ℂ) • ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)) := by
  -- `e_L = |L : H_L| = p q` (`typeICoherent78_complementIndex_eq_pq`, the (14.3) Frobenius order).
  have hepq := typeICoherent78_complementIndex_eq_pq hG nc.Ldata dataL
  -- (14.11.2)-style strict gap inputs for the (13.19.c) dichotomy branches, in `dataL`
  -- coordinates: `(v−1)/p < (h−1)/e` is `hhv` (after `e = pq`, `|H_L| = h`), and
  -- `(u−1)/q < (h−1)/e` chains it with `hvu`.
  have hindex : ((maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L).index
      = hyp.base.p * hyp.base.q := typeICoherent78_index_eq_pq hG nc.Ldata dataL
  have hcardH : Nat.card ↥dataL.typeIHyp.H = nc.h :=
    typeICoherent78_card_kernel_eq_h nc dataL
  have hub_v : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) <
      ((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L).index : ℚ) := by
    rw [hcardH, hindex]
    exact hhv
  have hub_u : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) <
      ((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L).index : ℚ) :=
    lt_trans hvu hub_v
  obtain ⟨signs, chi, hsigns, hclass, hexp⟩ :=
    lSide_expansion_classification hG hnoV hncH0C nc.Ldata.L_maximal dataL hq3 hp5 hepq
      hub_u hub_v
  rcases hclass with hchi | hchi
  · -- `χ = ζ_0^ν`: the removed member is the distinguished image (`i = zetaDistinct`, `ε = 1`)
    refine ⟨signs, hsigns, (dataL.h78 hG).zetaDistinct, ?_, 1, Or.inl rfl, ?_⟩
    · have h := (dataL.h78 hG).zetaDistinct_ne_ind1H
      rwa [dataL.h78_ind1H_eq] at h
    · rw [hexp, hchi]
      norm_num
  · -- `χ = −(ζ̄_0)^ν`: the removed member is the conjugate family member (`ε = −1`)
    obtain ⟨j₁, hj₁ne, hj₁⟩ := dataL.exists_conjIndex hG
    refine ⟨signs, hsigns, j₁, ?_, -1, Or.inr rfl, ?_⟩
    · rwa [dataL.h78_ind1H_eq] at hj₁ne
    · rw [hexp, hchi, ← congrArg (dataL.h78 hG).nu hj₁]
      push_cast
      rw [neg_smul, one_smul]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (14.16) expansion input** — the §13-gated character content of the case-(b)
contradiction, split into its two genuine textbook gates and the sorry-free (13.19.b) engine.
Under case-(b) (`(q,p) = (3,5)`) and the two gap inequalities:

* the L-side signed `η`-grid expansion `β_L^τ = Σ ±η_ij − ε ζ_i^ν` is the named (13.19.c)
  producer `lSide_signed_eta_expansion`;
* the M-side orthogonality `(η_ij, ψ^{τ₁}) = 0` (`ψ^{τ₁} = ζ_M^ν`) is **proven** by the
  (3.6)–(3.8)/(13.19.b) engine `caseB_eta_orthogonal_psi`, whose one residual input is the
  named (13.19.a) Dade-support avoidance `mSide_dadeSupport_avoids_regular`. -/
theorem caseB_expansion_input [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
      ∃ i : Fin (dataL.n + 1), i ≠ dataL.ind1H ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (dataL.h78 _hG).beta
          = (∑ i' : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (signs i' j : ℂ) • hyp.base.eta i' j)
            - (ε : ℂ) • ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta i)) ∧
        ∀ (i' : Fin hyp.base.q) (j : Fin hyp.base.p),
          ClassFunction.inner (hyp.base.eta i' j)
            ((dataM.h78 _hG).nu
              ((dataM.h78 _hG).hyp76.zeta (dataM.h78 _hG).zetaDistinct)) = 0 := by
  obtain ⟨signs, hsigns, i, hi, ε, hε, hexp⟩ :=
    lSide_signed_eta_expansion _hG hnoV hncH0C dataL hq3 hp5 hhv hvu
  exact ⟨signs, hsigns, i, hi, ε, hε, hexp,
    caseB_eta_orthogonal_psi _hG hyp.base dataM
      (mSide_dadeSupport_avoids_regular _hG hnoV hncH0C nc.Mdata.M_maximal dataM)⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §16 producer for the (14.16) case-(b) contradiction inputs.**  The case-(b)
pairing comes from the enriched `OrthogonalitySwitchData.caseB_pairing` ((7.9) dichotomy);
the `χ_L ⊥ ψ^{τ₁}` orthogonality is the proven (4.1) cross-orthogonality
`pair_cross_orthogonal`; the remaining (13.19.c)/(14.11.2) grid content is the named
`caseB_expansion_input`. -/
theorem caseB_contradiction_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseB : data.caseB)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    Nonempty (CaseBContradictionData nc) := by
  obtain ⟨hq3, hp5⟩ := data.caseB_params hcaseB
  obtain ⟨dataL, dataM, hpair⟩ := data.caseB_pairing hcaseB _hG
  obtain ⟨signs, hsigns, i, hi, ε, hε, hexp, horth⟩ :=
    caseB_expansion_input _hG hnoV hncH0C dataL dataM hq3 hp5 hhv hvu
  have hjne : (dataM.h78 _hG).zetaDistinct ≠ dataM.ind1H := by
    have h := (dataM.h78 _hG).zetaDistinct_ne_ind1H
    rwa [dataM.h78_ind1H_eq] at h
  refine ⟨{
    betaL := (dataL.h78 _hG).beta
    chiL := (ε : ℂ) • ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta i))
    psiImg := (dataM.h78 _hG).nu ((dataM.h78 _hG).hyp76.zeta (dataM.h78 _hG).zetaDistinct)
    signs := signs
    signs_pm_one := hsigns
    betaL_expansion := hexp
    eta_orthogonal_psi := horth
    chiL_orthogonal_psi := ?_
    pairing_ne_zero := hpair }⟩
  rw [ClassFunction.inner_smul_left,
    pair_cross_orthogonal dataL dataM _hG nc.Ldata.L_maximal nc.Mdata.M_maximal
      nc.not_conj hi hjne, mul_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.16)**: character-theoretic endpoint of the exceptional
case.  The two strict gap inequalities let (13.19.c) be applied on both the
S- and T-sides, giving the same signed `eta_ij` expansion as in (14.11.2) for
`beta_L^tau`; this contradicts the nonzero pairing in case-(b) of (14.14).

De-opacified (W4 §16, lane-h): the genuine character theory (the `β_L^τ` expansion, the `η`-grid /
`χ_L` orthogonalities to `ψ^{τ₁}`, and the case-(b) pairing) is the faithful
`CaseBContradictionData`;
the contradiction itself is the pure inner-product computation
`(β_L^τ, ψ^{τ₁}) = (Σ ±η_ij − χ_L, ψ^{τ₁})
= Σ ±·0 − 0 = 0`, contradicting `(β_L^τ, ψ^{τ₁}) ≠ 0`. -/
theorem caseB_character_contradiction_of_gap_inequalities
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseB : data.caseB)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    False := by
  -- The (14.11.2)-style signed `eta_ij` expansion of `beta_L^tau` and its orthogonalities.
  obtain ⟨⟨betaL, chiL, psiImg, signs, _hsigns, hexp, heta_orth, hchiL_orth, hpair_ne⟩⟩ :=
    caseB_contradiction_data _hG hnoV hncH0C data hcaseB hhv hvu
  -- `(beta_L^tau, psi^tau_1) = 0` by linearity + orthogonality, contradicting case-(b).
  refine hpair_ne ?_
  rw [hexp, ClassFunction.inner_sub_left, hchiL_orth, sub_zero, inner_finset_sum_left]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_finset_sum_left]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [ClassFunction.inner_smul_left, heta_orth i j, mul_zero]

/-- **Peterfalvi (14.16)**: consumer form of the exceptional case-(b) branch
under `H > U`.  All numerical work in the paragraph is discharged here; only
the named character-theoretic endpoint remains as a producer. -/
theorem caseB_contradiction_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Tdata : CaseBForTData hyp)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    False := by
  have hu_full := data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB
  have hh_lower := h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
    _hG hu_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q hx_ne_one_of_quotient
  rcases data.caseB_gap_inequalities_of_h_gt_two_mul_pq_mul_u
      Tdata Sdata hcaseB hh_lower with ⟨hhv, hvu⟩
  exact data.caseB_character_contradiction_of_gap_inequalities _hG hnoV hncH0C hcaseB hhv hvu

end OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.14) character dichotomy** — the genuine §7/§8 content of the orthogonality
switch.  By (8.17.c) the Dade supports `Ã₁(L)` and `Ã₁(M)` are disjoint, so by (7.9) either the
`M`-side pairing `(β_M^τ, φ^τ₁) ≠ 0` or the `L`-side pairing `(β_L^τ, ψ^τ₁) ≠ 0`.  In the first
case the (7.8.b) coherence-norm bound on the `β_M`-expansion `β_M^τ = a Σ aᵢ φᵢ^{τ₁} + Δ` gives
`Σ aᵢ² ≤ pq − 1`, i.e. `(h−1)/pq ≤ pq−1`; in the second the same estimate on the `β_L`-expansion
gives `(v−1)/pq ≤ pq−1`.  This isolates the character-theoretic input to `orthogonality_switch`;
the case-(b) passage to `q = 3`, `p = 5` is the arithmetic
`Hypothesis.caseB_forces_q_three_and_p_five`. -/
theorem orthogonality_switch_pairing_bounds [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    (((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)) ∨
      ((∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
          ∃ (dataL : TypeICoherent78Data nc.Ldata.L)
            (dataM : TypeICoherent78Data nc.Mdata.M),
            ClassFunction.inner
              ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                  nc.Mdata.M_maximal nc.not_conj).first.beta)
              ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                  nc.Mdata.M_maximal nc.not_conj).secondZetaImage) ≠ 0) ∧
        (((hyp.base.v - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ≤
          ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ))) := by
  classical
  -- The two (14.14) coherence bundles, for `L ⊇ N_G(U)` and `M ⊇ N_G(V)`.
  obtain ⟨dataL⟩ := TypeICoherent78Data.nonempty _hG hnoV nc.Ldata.L_maximal nc.Ldata.isTypeI
  obtain ⟨dataM⟩ := TypeICoherent78Data.nonempty _hG hnoV nc.Mdata.M_maximal
    ⟨nc.Mdata.typeIHyp.typeI⟩
  have hnc' : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup nc.Mdata.M nc.Ldata.L :=
    fun h => nc.not_conj h.symm
  -- `L`-side sizes: `|H| = h` and `[L : H] = p q`.
  have hcardL : Nat.card ↥dataL.kernelIn = nc.h := by
    have h1 : Nat.card ↥dataL.kernelIn = Nat.card ↥dataL.kernel :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv
    have h2 : dataL.kernel = nc.Ldata.H := by
      rw [show dataL.kernel = maxNilpotentNormalHall nc.Ldata.L from
          dataL.typeIHyp.typeI.typeF.H_eq, ← nc.Ldata.H_eq_LF]
    rw [h1, h2, nc.h_eq_card_H]
  have hidxL : (dataL.kernelIn).index = hyp.base.p * hyp.base.q := by
    have h := OddOrder.Peterfalvi.S15.typeIFrobenius_kernel_index_eq_complement
      nc.Ldata.typeI_data.frobenius
    have h2 : dataL.kernelIn
        = (maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L := by
      rw [show dataL.kernelIn = (dataL.typeIHyp.typeI.typeF.H).subgroupOf nc.Ldata.L
          from rfl, dataL.typeIHyp.typeI.typeF.H_eq]
    rw [h2, ← nc.Ldata.typeI_data_L_eq]
    exact h.trans nc.Ldata.typeI_complement_card_eq_pq
  -- `M`-side sizes: `|K| = v` ((14.11) `K = V`, `|V| = v·d`, `d = 1`) and `[M : K] = p q`.
  obtain ⟨hKV, hepq⟩ := K_eq_V_index_pq _hG hnoV hncH0C hyp nc.Ldata nc.Mdata
  have hkerM : dataM.kernel = nc.Mdata.K := by
    rw [show dataM.kernel = maxNilpotentNormalHall nc.Mdata.M from
        dataM.typeIHyp.typeI.typeF.H_eq, ← nc.Mdata.K_eq_MF]
  have hd1 : hyp.base.d = 1 := by
    have hTII : IsTypeII hyp.base.T := T_typeII _hG hnoV hncH0C hyp
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact hyp.V_inf_centralizer_Q_eq_bot _hG
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  have hcardM : Nat.card ↥dataM.kernelIn = hyp.base.v := by
    have h1 : Nat.card ↥dataM.kernelIn = Nat.card ↥dataM.kernel :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataM.kernel_le).toEquiv
    rw [h1, hkerM, hKV, hyp.base.card_V_eq_vd, hd1, mul_one]
  have hidxM : (dataM.kernelIn).index = hyp.base.p * hyp.base.q := by
    have h1 : dataM.kernelIn = nc.Mdata.K.subgroupOf nc.Mdata.M := by
      rw [show dataM.kernelIn = (dataM.kernel).subgroupOf nc.Mdata.M from rfl, hkerM]
    rw [h1, ← nc.Mdata.e_eq_index]
    exact hepq
  -- Convert the `ℚ`-subtractions to the `ℕ`-subtraction casts of the statement.
  have hpq1 : 1 ≤ hyp.base.p * hyp.base.q :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hyp.base.p_prime.pos.ne' hyp.base.q_prime.pos.ne')
  have hv1 : 1 ≤ hyp.base.v := by
    have hVpos : 0 < Nat.card ↥hyp.base.V := Nat.card_pos
    rw [hyp.base.card_V_eq_vd, hd1, mul_one] at hVpos
    exact hVpos
  have hh1 : 1 ≤ nc.h := (nc.h_odd _hG).pos
  -- The (7.9) pairing dichotomy, with the pairing itself retained in the case-(b) branch.
  rcases pairing_dichotomy dataL dataM _hG nc.Ldata.L_maximal nc.Mdata.M_maximal
      nc.not_conj with hfirst | hsecond
  · -- `⟨β_L, ζ_M^ν⟩ ≠ 0`: the `M`-kernel Bessel bound `(v − 1)/pq ≤ pq − 1` + the pairing.
    right
    have hMK := bessel_bound_of_inner_beta_zeta_ne_zero dataM dataL _hG
      nc.Mdata.M_maximal nc.Ldata.L_maximal hnc' hfirst
    rw [dataL.complementIndex_eq _hG, hcardM, hidxM, hidxL] at hMK
    refine ⟨fun hG' => ⟨dataL, dataM, hfirst⟩, ?_⟩
    rw [Nat.cast_sub hv1, Nat.cast_sub hpq1]
    push_cast at hMK ⊢
    convert hMK using 2
  · -- `⟨β_M, ζ_L^ν⟩ ≠ 0`: the `L`-kernel Bessel bound `(h − 1)/pq ≤ pq − 1`.
    left
    have hLH := bessel_bound_of_inner_beta_zeta_ne_zero dataL dataM _hG
      nc.Ldata.L_maximal nc.Mdata.M_maximal nc.not_conj hsecond
    rw [dataM.complementIndex_eq _hG, hcardL, hidxL, hidxM] at hLH
    rw [Nat.cast_sub hh1, Nat.cast_sub hpq1]
    push_cast at hLH ⊢
    convert hLH using 2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.14)**: either the case-(a) bound `(h − 1)/pq ≤ pq − 1` holds (the
`β_M`--`φ` pairing is nonzero), or the case-(b) exceptional primes `q = 3`, `p = 5` hold (the
`β_L`--`ψ` pairing is nonzero).

Assembled from the (7.9)+(8.17.c) character dichotomy `orthogonality_switch_pairing_bounds`, whose
two branches supply the case-(a) norm bound and the case-(b) `(v−1)/pq ≤ pq−1` bound; in case (b)
the arithmetic `caseB_forces_q_three_and_p_five` ((14.15)/(14.8.a)) turns that bound, together with
the (14.4) cyclotomic value of `v`, into `q = 3`, `p = 5`.  The abstract `caseA`/`caseB` props of
`OrthogonalitySwitchData` are taken to be the case-(a) bound and the `(q,p)=(3,5)` conclusion
themselves, so the downstream (14.15)/(14.16) machinery reads them off directly. -/
theorem orthogonality_switch [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    ∃ data : OrthogonalitySwitchData nc, data.caseA ∨ data.caseB := by
  obtain ⟨_Tdata, _, hv⟩ := caseB_for_T _hG hyp
  refine ⟨{
    caseA := ((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
      ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)
    caseA_bound := fun h => h
    caseB := (hyp.base.q = 3 ∧ hyp.base.p = 5) ∧
      haveI := hyp.base.finiteG
      ∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
        ∃ (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M),
          ClassFunction.inner
            ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                nc.Mdata.M_maximal nc.not_conj).first.beta)
            ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                nc.Mdata.M_maximal nc.not_conj).secondZetaImage) ≠ 0
    caseB_params := fun h => h.1
    caseB_pairing := fun h => h.2 }, ?_⟩
  rcases orthogonality_switch_pairing_bounds _hG hnoV hncH0C hyp nc with hA | ⟨hpair, hB⟩
  · exact Or.inl hA
  · exact Or.inr ⟨hyp.caseB_forces_q_three_and_p_five hv hB, hpair⟩

/-- **Peterfalvi (14.14)--(14.15)**: the full `u` value once the
cardinality consequences of (14.5) have been materialized.  The case-(b)
alternative of (14.14) is already full by the S-side order data; in case (a),
assuming the non-full value contradicts the fixed-point-free cardinal
congruences for `H` and `U`. -/
theorem u_final_value_of_fpf_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q]) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases orthogonality_switch _hG hnoV hncH0C hyp nc with ⟨data, hcase⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  rcases hcase with hcaseA | hcaseB
  · by_contra hu_not_full
    exact data.caseA_contradiction_of_nonfull_fpf_card_congruences
      _hG Sdata hcaseA hu_not_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q
  · exact data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB

/-- **Peterfalvi (14.15)**: `u` has the full cyclotomic value
`(p^q - 1) / (p - 1)`.

The proof consumes the cardinal consequences of (14.5): `u ∣ h`, the two
Frobenius-kernel congruences for `h`, and the fixed-point-free cardinal
congruence for `U`.  The arithmetic contradiction is packaged in
`u_final_value_of_fpf_card_congruences`. -/
theorem u_final_value [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  exact u_final_value_of_fpf_card_congruences _hG hnoV hncH0C hyp nc (nc.u_dvd_h _hG)
    hh_mod_p hh_mod_q (hyp.u_modEq_one_mod_q _hG)

/-- **Peterfalvi (14.16)**: in the non-conjugate case, the kernel `H` is
exactly `U`. -/
theorem H_eq_U [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    nc.Ldata.H = hyp.base.U := by
  by_contra hHU
  rcases orthogonality_switch _hG hnoV hncH0C hyp nc with ⟨data, hcase⟩
  rcases caseB_for_T _hG hyp with ⟨Tdata, _hT_caseB, _hv_eq⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  have hu_full := u_final_value _hG hnoV hncH0C hyp nc
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc,
      hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply, mul_one]
  have hU_le_H : hyp.base.U ≤ nc.Ldata.H := by
    rw [← nc.Ldata.typeI_data_H_eq]
    exact nc.Ldata.typeI_data.U_le_H
  have hx_ne_one_of_quotient :
      ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1 := by
    intro x hh_eq hx1
    have hH_card_eq_U_card : Nat.card ↥nc.Ldata.H = Nat.card ↥hyp.base.U := by
      rw [← nc.h_eq_card_H, hh_eq, hx1, mul_one, hU_card]
    have hU_eq_H : hyp.base.U = nc.Ldata.H :=
      Subgroup.eq_of_le_of_card_ge hU_le_H (le_of_eq hH_card_eq_U_card)
    exact hHU hU_eq_H.symm
  rcases hcase with hcaseA | hcaseB
  · exact data.caseA_contradiction_of_full_u_card_congruences
      _hG Sdata hcaseA hu_full (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient
  · exact data.caseB_contradiction_of_full_u_card_congruences
      _hG hnoV hncH0C Tdata Sdata hcaseB (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient

/-- **Peterfalvi §8 / BG 15.7(a)**: the type-`P` Fitting core `P = S_F` is a TI-subgroup of `G`.
The symmetric `S_nonI` carrier gives the type-II/type-III TI conclusion, whence the Fitting core
`S_F#` is TI (`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`; `sharpSubgroup = ·∖{1}`
matches `Subgroup.IsTI`).  Supplies the `P_isTI` field of `MHypothesis`. -/
theorem base_P_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : Subgroup.IsTI hyp.base.P := by
  rw [hyp.base.P_eq_SF]
  exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
    hyp.base.S_maximal
    (OddOrder.Peterfalvi.S13.fittingIsTI_of_isTypeNonI
      hG hyp.base.S_maximal hyp.base.S_nonI)

/-- **Peterfalvi §8, `T`-side**: the type-`P` Fitting core `Q = T_F` is a TI-subgroup of `G`.
`T`-side dual of `base_P_isTI` via `fittingIsTI_T` (`T` type II ⟹ type-`P₂`).  Supplies the `Q_isTI`
field of `MHypothesis`. -/
theorem base_Q_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.base.T) : Subgroup.IsTI hyp.base.Q := by
  rw [hyp.base.Q_eq_TF]
  exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
    hyp.base.T_maximal (OddOrder.Peterfalvi.S15.fittingIsTI_T hG hyp.base hTII)

/-- **Peterfalvi §13 `normalizer_V` (the `W`-exceptional-set normalizer)**: every nonempty
`X ⊆ W − (W₁ ∪ W₂)` has `N_G(X) = W`.  Read off the S-side type-`P` data `Sdata.normalizer_V`
((8.8) `W = W₁ × W₂` cyclic-TI structure), reconciled to the base `W`/`W₁`/`W₂`
(`Sdata_W1_eq`/`Sdata_W2_eq`, `W_eq_join`).  Supplies `MHypothesis`'s `W_normalizer_V`. -/
theorem base_W_normalizer_V (hyp : Hypothesis (G := G)) :
    ∀ X : Set G, X.Nonempty →
      X ⊆ (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) →
      Subgroup.normalizer X = hyp.base.W := by
  have hWeq : hyp.base.Sdata.W = hyp.base.W := by
    rw [hyp.base.Sdata.W_eq, hyp.base.Sdata_W1_eq, hyp.base.Sdata_W2_eq]
    exact hyp.base.W_eq_join.symm
  intro X hX hXsub
  rw [← hWeq]
  refine hyp.base.Sdata.normalizer_V X hX ?_
  rw [hWeq, hyp.base.Sdata_W1_eq, hyp.base.Sdata_W2_eq]
  exact hXsub

/-- **Order factorization of the type-`P` maximal `S`**: `|P| · |U| · |W₁| = |S|`
(`S = (P ⋊ U) ⋊ W₁`, `P = S_F`, `S' = P ⋊ U`).  From the `Sdata` complement indices
`card_W1_eq_derived_index` (`|W₁| = [S:S']`) and `card_U_eq_index` (`|U| = [S':P]`) via
`Subgroup.card_mul_index`. -/
theorem base_card_S_eq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.base.P * Nat.card ↥hyp.base.U * Nat.card ↥hyp.base.W1
      = Nat.card ↥hyp.base.S := by
  have hW1 : Nat.card ↥hyp.base.W1 = Nat.card ↥hyp.base.Sdata.W1 := by rw [hyp.base.Sdata_W1_eq]
  have hU : Nat.card ↥hyp.base.U = Nat.card ↥hyp.base.Sdata.U := by rw [hyp.base.Sdata_U_eq]
  have hP : hyp.base.P = maxNilpotentNormalHall hyp.base.S := hyp.base.P_eq_SF
  have hDle : derivedInG hyp.base.S ≤ hyp.base.S := Subgroup.map_subtype_le _
  have hPle : maxNilpotentNormalHall hyp.base.S ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU, ← hP]; exact le_sup_left
  have c1 : Nat.card ↥(derivedInG hyp.base.S) * Nat.card ↥hyp.base.Sdata.W1
      = Nat.card ↥hyp.base.S := by
    rw [hyp.base.Sdata.card_W1_eq_derived_index,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv]
    exact Subgroup.card_mul_index _
  have c2 : Nat.card ↥(maxNilpotentNormalHall hyp.base.S) * Nat.card ↥hyp.base.Sdata.U
      = Nat.card ↥(derivedInG hyp.base.S) := by
    rw [hyp.base.Sdata.card_U_eq_index,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hW1, hU, hP, ← c1, ← c2]

/-- **Peterfalvi (14.11.4)**: `|N_G(P)| = |P| · u · q`.  The Fitting core `P = S_F` is normal in
the maximal `S` and nontrivial (`W₂ ≤ P`), so `N_G(P) = S`
(`normalizer_eq_self_of_subgroupOf_normal_of_ne_bot`); then `|S| = |P|·|U|·|W₁|` (`base_card_S_eq`)
with `|U| = u·c`, `c = 1` (`c_eq_one_of_lambda_dichotomy`), `|W₁| = q`.  Supplies `MHypothesis`'s
`card_normalizer_P_eq`. -/
theorem base_card_normalizer_P_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G))
      = Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q := by
  have hPne : maxNilpotentNormalHall hyp.base.S ≠ ⊥ := by
    intro hbot
    have hW2 := OddOrder.Peterfalvi.S15.W2_le_P hG hyp.base
    rw [hyp.base.P_eq_SF, hbot, le_bot_iff] at hW2
    have hp1 : hyp.base.p = 1 := by rw [hyp.base.p_eq_card_W2, hW2, Subgroup.card_bot]
    exact hyp.base.p_prime.one_lt.ne' hp1
  have hNP : Subgroup.normalizer (hyp.base.P : Set G) = hyp.base.S := by
    rw [hyp.base.P_eq_SF]
    exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
      hyp.base.S_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hPne
  rw [hNP, ← base_card_S_eq hyp, hyp.base.card_U_eq_uc,
    hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply, mul_one,
    hyp.base.q_eq_card_W1]

/-- **Order factorization of the type-`P` maximal `T`** (T-side dual of `base_card_S_eq`):
`|Q| · |V| · |W₂| = |T|`, from a reconciled `TypePData T` (`tpd.U = V`, `tpd.W1 = W₂`, `Q = T_F`)
via `card_W1_eq_derived_index` / `card_U_eq_index` and `Subgroup.card_mul_index`. -/
theorem base_card_T_eq [Finite G] (hyp : Hypothesis (G := G))
    (tpd : OddOrder.GroupTheory.TypePData hyp.base.T) (hU : tpd.U = hyp.base.V)
    (hW1 : tpd.W1 = hyp.base.W2) :
    Nat.card ↥hyp.base.Q * Nat.card ↥hyp.base.V * Nat.card ↥hyp.base.W2
      = Nat.card ↥hyp.base.T := by
  have hW2c : Nat.card ↥hyp.base.W2 = Nat.card ↥tpd.W1 := by rw [hW1]
  have hVc : Nat.card ↥hyp.base.V = Nat.card ↥tpd.U := by rw [hU]
  have hQ : hyp.base.Q = maxNilpotentNormalHall hyp.base.T := hyp.base.Q_eq_TF
  have hDle : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hQle : maxNilpotentNormalHall hyp.base.T ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV, ← hQ]; exact le_sup_left
  have c1 : Nat.card ↥(derivedInG hyp.base.T) * Nat.card ↥tpd.W1 = Nat.card ↥hyp.base.T := by
    rw [tpd.card_W1_eq_derived_index, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv]
    exact Subgroup.card_mul_index _
  have c2 : Nat.card ↥(maxNilpotentNormalHall hyp.base.T) * Nat.card ↥tpd.U
      = Nat.card ↥(derivedInG hyp.base.T) := by
    rw [tpd.card_U_eq_index, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hW2c, hVc, hQ, ← c1, ← c2]

/-- **Peterfalvi (14.11.4)**: `|N_G(Q)| = |Q| · v · p` (T-side dual of `base_card_normalizer_P_eq`).
`Q = T_F` is normal in the maximal `T` and nontrivial (`W₁ ≤ Q`), so `N_G(Q) = T`; then
`|T| = |Q|·|V|·|W₂|` (`base_card_T_eq`) with `|V| = v·d`, `d = 1` (`V_inf_centralizer_Q_eq_bot`,
`D = V ⊓ C_G(Q) = ⊥`), `|W₂| = p`.  Supplies `MHypothesis`'s `card_normalizer_Q_eq`. -/
theorem base_card_normalizer_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hTII : IsTypeII hyp.base.T) :
    Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G))
      = Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p := by
  obtain ⟨tpd, hU, hW1, hW2⟩ := OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base
  have hQne : maxNilpotentNormalHall hyp.base.T ≠ ⊥ := by
    intro hbot
    have hW1le : hyp.base.W1 ≤ maxNilpotentNormalHall hyp.base.T := by
      rw [← hW2]
      exact le_trans tpd.W2_le (le_trans inf_le_left (le_of_eq tpd.H_eq))
    rw [hbot, le_bot_iff] at hW1le
    have hq1 : hyp.base.q = 1 := by rw [hyp.base.q_eq_card_W1, hW1le, Subgroup.card_bot]
    exact hyp.base.q_prime.one_lt.ne' hq1
  have hNQ : Subgroup.normalizer (hyp.base.Q : Set G) = hyp.base.T := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
      hyp.base.T_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hQne
  have hd1 : hyp.base.d = 1 := by
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact hyp.V_inf_centralizer_Q_eq_bot hG
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  rw [hNQ, ← base_card_T_eq hyp tpd hU hW1, hyp.base.card_V_eq_vd, hd1, mul_one,
    hyp.base.p_eq_card_W2]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.10)**: a type-I maximal subgroup `M` over `N_G(V)` together
with its Dade data exists.  Symmetric to `exists_LHypothesis`, packaging (13.17)
for the `V`-side with the Dade data and the virtual character `β_M` of (14.10).

The structural subgroup and the faithful (13.17.c)-dual index dichotomy come from
`S15.exists_M_structural_dichotomy`.  The complete §5--§8 character data then comes from
`TypeICoherent78Data.nonempty`: one bundle supplies the Dade setup, coherent extension, placed
family, distinguished `ψ = ζ₀`, and its canonical `Hypothesis78`.  Thus `τ`, `τ₁`, `ψ`, and `β_M`
are computed accessors of the same bundle rather than independently chosen carrier fields.

The TI / normalizer facts are the `base_*` helpers.  The two `G0` covering facts are elementary
set algebra on the (14.11.3) complement
`G₀ = G − [Ã(M) ∪ (W−(W₁∪W₂))^G ∪ (P#)^G ∪ (Q#)^G]`.

No conclusion of (14.11) is packaged here: `e = p q`, the `±1` signs, and the η-grid expansion
are produced only in the `K ≠ V` branch by `betaM_expansion_data`. -/
theorem exists_MHypothesis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    Nonempty (MHypothesis hyp) := by
  have hTII : IsTypeII hyp.base.T := T_typeII _hG hnoV hncH0C hyp
  have hc1 : hyp.base.c = 1 :=
    hyp.base.c_eq_one_of_lambda_dichotomy _hG hyp.nuGridSupply
  obtain ⟨M, structuralHyp, hM_max, hnorm_V, hindexCases⟩ :=
    OddOrder.Peterfalvi.S15.exists_M_structural_dichotomy_of_c_eq_one
      _hG hnoV hyp.base hc1 hTII
  obtain ⟨dataM⟩ :=
    TypeICoherent78Data.nonempty _hG hnoV hM_max ⟨structuralHyp.typeI⟩
  refine ⟨{
    M := M
    K := maxNilpotentNormalHall M
    M_maximal := hM_max
    normalizer_V_le_M := hnorm_V
    K_eq_MF := rfl
    hG := _hG
    coherent78 := dataM
    e := ((maxNilpotentNormalHall M).subgroupOf M).index
    k := Nat.card ↥(maxNilpotentNormalHall M)
    e_eq_index := rfl
    complementIndex_cases := hindexCases
    k_eq_card_K := rfl
    G0 := Set.univ \ (dataM.typeIHyp.dadeData.dade.dadeSupport ∪
      (conjClassSet ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
        ∪ conjClassSet (sharpSubgroup hyp.base.P)
        ∪ conjClassSet (sharpSubgroup hyp.base.Q)))
    G0_off_dadeSupport := ?offDade
    G0_orbit_cover := ?orbCover
    G0_avoid := ?avoid
    W_normalizer_V := base_W_normalizer_V hyp
    P_isTI := base_P_isTI _hG hyp
    Q_isTI := base_Q_isTI _hG hyp hTII
    card_normalizer_P_eq := base_card_normalizer_P_eq _hG hyp
    card_normalizer_Q_eq := base_card_normalizer_Q_eq _hG hyp hTII
  }⟩
  case offDade =>
    intro g hg hin
    exact hg.2 (Set.mem_union_left _ hin)
  -- **Peterfalvi (14.11.3)**: the concrete `G₀` avoids the three singular orbits — direct
  -- set algebra on the defining complement.
  case avoid =>
    intro g hg
    exact ⟨fun h => hg.2 (Set.mem_union_right _
        (Set.mem_union_left _ (Set.mem_union_left _ h))),
      fun h => hg.2 (Set.mem_union_right _
        (Set.mem_union_left _ (Set.mem_union_right _ h))),
      fun h => hg.2 (Set.mem_union_right _ (Set.mem_union_right _ h))⟩
  case orbCover =>
    intro g hgd hg0
    have hmem : g ∈ dataM.typeIHyp.dadeData.dade.dadeSupport ∪
        (conjClassSet ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
          ∪ conjClassSet (sharpSubgroup hyp.base.P)
          ∪ conjClassSet (sharpSubgroup hyp.base.Q)) := by
      by_contra h
      exact hg0 ⟨Set.mem_univ g, h⟩
    rcases hmem with h | h
    · exact absurd h hgd
    · exact h

/-- **Peterfalvi (14.16)**→(14.7) bridge: if the Fitting kernel `H` of `L`
coincides with `U`, then `U` is characteristic in `H` — it is the whole of `H`,
and `⊤` is characteristic.  This is what lets the non-conjugate case `H = U` of
(14.16) feed back into (14.7). -/
theorem U_characteristic_of_H_eq_U {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (hHU : Ldata.H = hyp.base.U) :
    (hyp.base.U.subgroupOf Ldata.H).Characteristic := by
  have htop : hyp.base.U.subgroupOf Ldata.H = ⊤ :=
    Subgroup.subgroupOf_eq_top.mpr (le_of_eq hHU)
  rw [htop]
  exact Subgroup.topCharacteristic

/-- **Peterfalvi (14.2)**: the field-normalizer configuration follows from the
Section 16 hypotheses.

This assembles Peterfalvi's concluding paragraph "By (14.12), (14.16) and (14.7),
the proof of Theorem (14.2) is complete."  Take the type-I subgroup `L` over
`N_G(U)` ((14.3), `exists_LHypothesis`) and split on whether `U` is characteristic
in `H`:

* if it is, (14.7) `field_normalizer_of_U_characteristic` finishes;
* otherwise take the type-I subgroup `M` over `N_G(V)` ((14.10),
  `exists_MHypothesis`) and split on whether `L` is conjugate to `M`:
  * if it is, (14.12) `field_normalizer_of_L_conj_M` finishes;
  * otherwise (14.13)–(14.16) `H_eq_U` give `H = U`, so `U` is characteristic in
    `H` (`U_characteristic_of_H_eq_U`), contradicting the branch assumption. -/
theorem field_normalizer_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hnoV hncH0C hyp
  by_cases hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic
  · exact field_normalizer_of_U_characteristic _hG hnoV hncH0C hyp Ldata hchar
  · obtain ⟨Mdata⟩ := exists_MHypothesis _hG hnoV hncH0C hyp
    by_cases hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
    · exact field_normalizer_of_L_conj_M _hG hnoV hncH0C hyp Ldata Mdata hconj
    · exact absurd
        (U_characteristic_of_H_eq_U Ldata
          (H_eq_U _hG hnoV hncH0C hyp
            { Ldata := Ldata, Mdata := Mdata, not_conj := hconj,
              h := Nat.card ↥Ldata.H, h_eq_card_H := rfl }))
        hchar

/-- **Peterfalvi Section 16 + BG Appendix C**: BG Appendix C turns the
field-normalizer configuration into `p <= q`, contradicting (14.1). -/
theorem nonexistence_of_G [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (bgAppendixC : FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q) :
    False := by
  rcases field_normalizer_structure hG hnoV hncH0C hyp with ⟨data⟩
  exact (not_lt_of_ge (bgAppendixC data)) hyp.q_lt_p

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/BG/AppC_FinalContradiction.lean =====
namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open OddOrder.Peterfalvi

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Appendix C + Peterfalvi Section 16**: once Peterfalvi constructs the
field-normalizer data, BG Theorem C contradicts the standing hypothesis `q < p`. -/
theorem final_contradiction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : S16.Hypothesis (G := G)) :
    False :=
  S16.nonexistence_of_G hG hnoV hncH0C hyp (theoremC hyp)

end OddOrder.BG.AppC

-- ===== OddOrder/FeitThompsonSection16Core.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

/-- The axiom-clean final-contradiction bridge: from the BG minimal-counterexample and
Peterfalvi Section 16 hypotheses, BG Appendix C closes the contradiction. -/
theorem _root_.solution {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Peterfalvi.S16.Hypothesis (G := G)) :
    False :=
  BG.AppC.final_contradiction hG hnoV hncH0C hyp

end OddOrder
