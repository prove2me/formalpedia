-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.T_typeIII_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:20:01.559191+00:00
-- url     : https://prove2.me/submissions/74887f37-c74e-41d6-99b7-ec989b3c62c6

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_Coherence/NormInequalities.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean
--   OddOrder/GroupTheory/RepresentationTheory/InflationInduction.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacter.lean
--   OddOrder/Peterfalvi/S16_CoreLemmas.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapPrimeTI.lean
--   OddOrder/Peterfalvi/S15_CaseBReducibleCoherence.lean
--   OddOrder/Peterfalvi/S15_CaseACoherence.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayerCore.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/OrderRelayer.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapCross.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjection.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjectionRigidity.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjectionResidual.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapGalois.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapMemberResidual.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
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
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Theorems.Thm_OddOrder_RepresentationTheory_cfdot_real_vchar_even
import Theorems.Thm_OddOrder_Peterfalvi_S15_gammaGrid_real_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_gammaGrid_Y_norm_bound_aux
import Theorems.Thm_OddOrder_Peterfalvi_S15_betaGrid_support_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_indPW1_inner_self_aux
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_S
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_analytic_inequality_of_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_sSet_irr
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_forces_T_caseB_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseB_member
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambdaWitness_of_caseA
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S15_c_eq_one_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S16_tSideDadeMap_eq_full_typeP1DadeMap_of_support
import Theorems.Thm_OddOrder_Peterfalvi_S16_tSide_beta_inner_eta_of_zeroColumn_projection
import Theorems.Thm_OddOrder_Peterfalvi_S16_tSideCoherentExtension_inner_trivial
import Theorems.Thm_OddOrder_Peterfalvi_S16_tSideCoherentExtension_conj
import Theorems.Thm_OddOrder_Peterfalvi_S16_tSideDelta_isReal
import Theorems.Thm_OddOrder_Peterfalvi_S16_member_residual_not_orthogonal_eta_of_refuter
import Theorems.Thm_OddOrder_Peterfalvi_S16_exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
import Theorems.Thm_OddOrder_Peterfalvi_S16_tSideDadeMap_inner_trivial
import Theorems.Thm_OddOrder_Peterfalvi_S16_exists_etaGrid_intProjection_of_inner_self_eq
import Theorems.Thm_OddOrder_Peterfalvi_S16_etaGrid_projection_sum_sq_le_of_residual_ne_zero
import Theorems.Thm_OddOrder_Peterfalvi_S16_etaGrid_zeroColumn_projection_of_coefficients_eq_column
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_calT1_family_galois
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_side_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_calT1_isCoherent
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_calT1_difference_support
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_coherent_image_inner_eta_eq_zero

-- ===== OddOrder/Peterfalvi/S07_Coherence/NormInequalities.lean =====
namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

namespace Hypothesis

variable {S : Set (ClassFunction L ℂ)} {A : Set L}

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

theorem not_isReal {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    ¬ χ.IsReal :=
  hyp.no_real_characters hχ

theorem ne_conj {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    χ ≠ χ.conj := by
  intro hχ_eq
  exact hyp.not_isReal hχ hχ_eq.symm

end Hypothesis

end OddOrder.Peterfalvi.S07

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section OrthogonalIntegerDecomposition

variable {ι : Type*}

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- Integer-coefficient Pythagoras bridge used in Peterfalvi (7.10): if a class
function decomposes as an orthogonal integer combination plus an orthogonal
residual, then an upper bound on its norm bounds the sum of the diagonal weights
for every nonzero coefficient. -/
theorem sum_weights_le_of_orthogonal_integer_decomposition
    (B : Finset ι) (v : ι → ClassFunction G ℂ) (x : ι → ℤ) (m : ι → ℝ)
    (Γ Γ₁ : ClassFunction G ℂ) (M : ℝ)
    (hΓ : Γ = (∑ i ∈ B, (((x i : ℝ) : ℂ) • v i)) + Γ₁)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then (m i : ℂ) else 0)
    (hΓ₁ : ∀ i ∈ B, ClassFunction.inner Γ₁ (v i) = 0)
    (hm_nonneg : ∀ i ∈ B, 0 ≤ m i)
    (hx_nonzero : ∀ i ∈ B, x i ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ M) :
    (∑ i ∈ B, m i) ≤ M := by
  classical
  have hpyth := inner_self_orthogonalSum_add_re (G := G) B v
    (fun i => (x i : ℝ)) m Γ₁ horth hΓ₁
  have hΓ_norm : (ClassFunction.inner Γ Γ).re =
      (∑ i ∈ B, (x i : ℝ) ^ 2 * m i) +
        (ClassFunction.inner Γ₁ Γ₁).re := by
    rw [hΓ]
    exact hpyth
  have hsum_le_sq : (∑ i ∈ B, m i) ≤
      ∑ i ∈ B, (x i : ℝ) ^ 2 * m i := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hcases : x i ≤ -1 ∨ 1 ≤ x i := by
      have hxi := hx_nonzero i hi
      omega
    have hx_sq : (1 : ℝ) ≤ (x i : ℝ) ^ 2 := by
      rcases hcases with hle | hge
      · have hle' : (x i : ℝ) ≤ -1 := by exact_mod_cast hle
        nlinarith
      · have hge' : (1 : ℝ) ≤ x i := by exact_mod_cast hge
        nlinarith
    simpa [one_mul] using mul_le_mul_of_nonneg_right hx_sq (hm_nonneg i hi)
  have hΓ₁_nonneg : 0 ≤ (ClassFunction.inner Γ₁ Γ₁).re :=
    inner_self_re_nonneg Γ₁
  rw [hΓ_norm] at hΓ_bound
  linarith

open scoped Classical in
/-- Rational-valued version of the integer-coefficient Pythagoras bridge.  This
matches the `𝓑`-sum in Peterfalvi (7.10), whose weights are rational ratios such
as `(h_j - 1) / e_j`, while the norm inequality lives in `ℝ`. -/
theorem sum_rat_weights_le_of_orthogonal_integer_decomposition
    (B : Finset ι) (v : ι → ClassFunction G ℂ) (x : ι → ℤ) (m : ι → ℚ)
    (Γ Γ₁ : ClassFunction G ℂ) (M : ℚ)
    (hΓ : Γ = (∑ i ∈ B, (((x i : ℝ) : ℂ) • v i)) + Γ₁)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then (m i : ℂ) else 0)
    (hΓ₁ : ∀ i ∈ B, ClassFunction.inner Γ₁ (v i) = 0)
    (hm_nonneg : ∀ i ∈ B, 0 ≤ m i)
    (hx_nonzero : ∀ i ∈ B, x i ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (M : ℝ)) :
    (∑ i ∈ B, m i) ≤ M := by
  have horth_real : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) =
        if i = j then (((m i : ℝ) : ℂ)) else 0 := by
    intro i hi j hj
    simpa using horth i hi j hj
  have hm_nonneg_real : ∀ i ∈ B, 0 ≤ (m i : ℝ) := by
    intro i hi
    exact_mod_cast hm_nonneg i hi
  have hreal := sum_weights_le_of_orthogonal_integer_decomposition
    B v x (fun i => (m i : ℝ)) Γ Γ₁ (M : ℝ) hΓ horth_real hΓ₁ hm_nonneg_real
    hx_nonzero hΓ_bound
  have hcast : ((∑ i ∈ B, m i) : ℝ) ≤ (M : ℝ) := by
    simpa using hreal
  exact_mod_cast hcast

end OrthogonalIntegerDecomposition

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

/-- **Size condition for an odd-order Frobenius group**: if a finite Frobenius group has kernel `N`
and complement `A` both of **odd** order, with `N ≠ ⊥`, then `2|A| + 1 ≤ |N|` (equivalently
`e ≤ (h-1)/2`).  The complement acts freely on `N#`, so `|A| ∣ |N| - 1` (`card_kernel_modEq_one`,
Isaacs 6.1); as `|N|` is odd, `|N| - 1` is even, and an odd divisor of an even number is at most
half
of it, so `|N| - 1 ≥ 2|A|`.  This is the `2e + 1 ≤ h` (`smallIndex`) input to the Peterfalvi §7
`(7.8.b)` norm bound. -/
theorem IsFrobeniusGroup.two_mul_card_complement_add_one_le_card_kernel {G : Type*} [Group G]
    [Finite G] {N A : Subgroup G} (hFrob : IsFrobeniusGroup G N A)
    (hNodd : Odd (Nat.card ↥N)) (hAodd : Odd (Nat.card ↥A)) (hNnt : N ≠ ⊥) :
    2 * Nat.card ↥A + 1 ≤ Nat.card ↥N := by
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNnt
  have hN1 : 1 < Nat.card ↥N := Finite.one_lt_card
  -- `|A| ∣ |N| - 1` from `|N| ≡ 1 [MOD |A|]` (Isaacs 6.1).
  obtain ⟨m, hm⟩ : Nat.card ↥A ∣ Nat.card ↥N - 1 :=
    (Nat.modEq_iff_dvd' hN1.le).mp hFrob.card_kernel_modEq_one.symm
  -- `|N| - 1` is even (`|N|` odd), `|A|` is odd, so the cofactor `m` is even.
  have hNm1_even : Even (Nat.card ↥N - 1) := Nat.Odd.sub_odd hNodd odd_one
  have hm_even : Even m := by
    rcases (Nat.even_mul.mp (hm ▸ hNm1_even)) with hA | hm
    · exact absurd hA (Nat.not_even_iff_odd.mpr hAodd)
    · exact hm
  -- `m ≠ 0` (else `|N| = 1`), so `m ≥ 2`; hence `|N| - 1 = |A|·m ≥ 2|A|`.
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · rw [h0, Nat.mul_zero] at hm; omega
    · exact hp
  have hm2 : 2 ≤ m := Nat.le_of_dvd hm_pos hm_even.two_dvd
  have hge : Nat.card ↥A * 2 ≤ Nat.card ↥A * m := Nat.mul_le_mul_left _ hm2
  omega

end OddOrder.Isaacs.Ch06

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

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Cross-Dade inner-product vanishing on disjoint conjugate supports** ((13.4) core (d)):
the inductions of `α` (supported in `A_M ⊆ M`) and `β` (supported in `A_N ⊆ N`) to `G` have
disjoint supports when nothing is conjugate into both `A_M` and `A_N`, so their inner product
vanishes.  This is Peterfalvi's `(α^τ, β^τ) = 0` for `α ∈ ℤ[𝒮, H^#]`, `β ∈ ℤ[𝒯, K^#]` (both Dade
isometries being `Ind` by (13.2.e), the supports lie in `(H^#)^G` resp. `(K^#)^G`). -/
theorem inner_induce_induce_eq_zero_of_disjoint [Fintype G] [Invertible (Nat.card G : ℂ)]
    {M N : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card ↥N : ℂ)]
    {A_M : Set ↥M} {A_N : Set ↥N}
    {α : ClassFunction ↥M ℂ} {β : ClassFunction ↥N ℂ}
    (hα : α.support ⊆ A_M) (hβ : β.support ⊆ A_N)
    (hdisj : Disjoint (ClassFunction.conjugatesIntoSet M A_M)
      (ClassFunction.conjugatesIntoSet N A_N)) :
    ClassFunction.inner (ClassFunction.induce M α) (ClassFunction.induce N β) = 0 :=
  ClassFunction.inner_eq_zero_of_disjoint_support
    (hdisj.mono (ClassFunction.support_induce_subset_conjugatesIntoSet hα)
      (ClassFunction.support_induce_subset_conjugatesIntoSet hβ))

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

/-- The parity calculation behind **Peterfalvi (13.14)**: if `p` is odd, the
geometric sum of its first `q` powers has the same parity as `q`. -/
private theorem sum_range_pow_mod_two_eq {p q : ℕ} (hpodd : Odd p) :
    (∑ k ∈ Finset.range q, p ^ k) % 2 = q % 2 := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hpow : p ^ q % 2 = 1 := Nat.odd_iff.mp hpodd.pow
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hpow]
      omega

/-- The oddness part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_odd {p q : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.odd_iff, sum_range_pow_mod_two_eq hpodd, Nat.odd_iff.mp hqodd]

/-- If `p` is not `1 mod q`, then the prime `q` does not divide the
cyclotomic quotient in **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_not_dvd_self_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ¬ q ∣ (p ^ q - 1) / (p - 1) := by
  have : Fact q.Prime := ⟨hq⟩
  intro hdiv
  rw [← Nat.geomSum_eq hp.two_le q] at hdiv
  have hsum_zero_nat : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hsum_zero_zmod : (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) = 0 := by
    simpa [Nat.cast_sum, Nat.cast_pow] using hsum_zero_nat
  have hgeom :
      (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) =
        (p : ZMod q) ^ q - 1 :=
    geom_sum_mul (p : ZMod q) q
  have hp_eq_one : (p : ZMod q) = 1 := by
    have hzero :
        (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) = 0 := by
      rw [hsum_zero_zmod, zero_mul]
    rw [hgeom, ZMod.pow_card] at hzero
    exact sub_eq_zero.mp hzero
  exact hpq ((ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hp_eq_one))

/-- Prime divisors of the cyclotomic quotient in the non-`1 mod q` case are
`1 mod q`. -/
theorem cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q])
    (hr : r.Prime) (hrdvd : r ∣ (p ^ q - 1) / (p - 1)) :
    r ≡ 1 [MOD q] := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact q.Prime := ⟨hq⟩
  have hr_ne_q : r ≠ q := by
    intro h
    exact cyclotomic_quotient_not_dvd_self_of_not_modEq_one hp hq hpq
      (by simpa [h] using hrdvd)
  have hr_not_dvd_q : ¬ r ∣ q := by
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with hr_eq_one | hr_eq_q
    · exact hr.ne_one hr_eq_one
    · exact hr_ne_q hr_eq_q
  have : NeZero (q : ZMod r) :=
    NeZero.of_not_dvd (ZMod r) hr_not_dvd_q
  have hrdvd_sum : r ∣ ∑ k ∈ Finset.range q, p ^ k := by
    simpa [Nat.geomSum_eq hp.two_le q] using hrdvd
  have hroot :
      Polynomial.IsRoot (Polynomial.cyclotomic q (ZMod r))
        (Nat.castRingHom (ZMod r) p) := by
    rw [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime]
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    simpa [Nat.cast_sum, Nat.cast_pow] using
      (ZMod.natCast_eq_zero_iff (∑ k ∈ Finset.range q, p ^ k) r).mpr hrdvd_sum
  have hcop : p.Coprime r :=
    Polynomial.coprime_of_root_cyclotomic hq.pos hroot
  have hnot_r_dvd_p : ¬ r ∣ p :=
    hr.coprime_iff_not_dvd.mp hcop.symm
  have hp_ne_zero : (p : ZMod r) ≠ 0 := by
    intro hzero
    exact hnot_r_dvd_p ((ZMod.natCast_eq_zero_iff p r).mp hzero)
  have horder_dvd : orderOf (p : ZMod r) ∣ r - 1 :=
    ZMod.orderOf_dvd_card_sub_one hp_ne_zero
  have horder_eq : q = orderOf (p : ZMod r) :=
    (Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf
  rw [← horder_eq] at horder_dvd
  exact ((Nat.modEq_iff_dvd' hr.pos).mpr horder_dvd).symm

/-- If every prime factor of `x` is `1 mod q`, then `x` is `1 mod q`. -/
theorem modEq_one_of_forall_primeFactors_modEq_one {x q : ℕ} (hx : x ≠ 0)
    (h : ∀ r ∈ x.primeFactors, r ≡ 1 [MOD q]) :
    x ≡ 1 [MOD q] := by
  rw [Nat.prod_primeFactors_coe_pow_factorization hx]
  have hprod :
      (∏ r ∈ x.primeFactors, r ^ x.factorization r) ≡
        ∏ r ∈ x.primeFactors, 1 [MOD q] :=
    Nat.ModEq.prod fun r hr => by
      simpa using (h r hr).pow (x.factorization r)
  simpa using hprod

/-- The divisor-congruence part of **Peterfalvi (13.14)** when `p` is not
`1 mod q`. -/
theorem cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q] := by
  intro x hx hxdvd
  refine modEq_one_of_forall_primeFactors_modEq_one hx fun r hrx => ?_
  exact cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one hp hq hpq
    (Nat.prime_of_mem_primeFactors hrx)
    ((Nat.dvd_of_mem_primeFactors hrx).trans hxdvd)

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

-- ===== OddOrder/GroupTheory/RepresentationTheory/InflationInduction.lean =====
namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Fiber cardinality of the quotient map.**  The number of `g : G` mapping to a fixed coset
`q : G ⧸ N` under `QuotientGroup.mk` equals `|N|` (every fiber is a coset of `N`,
`QuotientGroup.card_preimage_mk` with a singleton). -/
theorem card_filter_mk_eq {N : Subgroup G} [Fintype G] (q : G ⧸ N) :
    (Finset.univ.filter (fun g : G => (QuotientGroup.mk g : G ⧸ N) = q)).card = Nat.card ↥N := by
  have hcard : (Finset.univ.filter (fun g : G => (QuotientGroup.mk g : G ⧸ N) = q)).card
      = Nat.card ↥((QuotientGroup.mk : G → G ⧸ N) ⁻¹' ({q} : Set (G ⧸ N))) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine congrArg Finset.card ?_
    ext g
    simp [Set.mem_preimage]
  rw [hcard, QuotientGroup.card_preimage_mk N ({q} : Set (G ⧸ N))]
  simp

open scoped Classical in
/-- **Peterfalvi (1.6)(b)** (book p. 7): *induction commutes with inflation along a normal subgroup
contained in the kernel.*

Let `N ⊴ G` with `N ≤ H`, let `θ₁` be a class function on `H/N = H.map (mk' N)`, and let `θ` be the
class function on `H` it inflates to -- i.e. `θ(x) = θ₁(xN)` for all `x ∈ H` (`hinfl`).  Then

`Ind_H^G θ = (Ind_{H/N}^{G/N} θ₁) ∘ mk'`.

This is the book's statement: there `θ ∈ Irr(H)` is given with `N ⊆ Ker θ`, `θ₁` is *defined* by
`θ₁(xN) = θ(x)`, and `χ` -- the character of `G/N` with `χ(xN) = (Ind_H^G θ)(x)`, which exists by
(1.6)(a) -- is shown to equal `Ind_{H/N}^{G/N} θ₁`.  Saying "`χ` inflates to `Ind_H^G θ`" is the
same as the displayed equation, and stating it that way avoids having to construct `χ` (the
equation determines it, `mk'` being surjective).  Neither irreducibility of `θ` nor `N ⊆ Ker θ` is
needed beyond what `hinfl` already says: `hinfl` *is* the assertion that `θ` factors through `H/N`,
which for a character is exactly `N ⊆ Ker θ`.

*Proof* (the book's).  Both sides vanish off `H` resp. `H/N`, and the conjugator condition
`x⁻¹gx ∈ H` transports along `mk` (`N ≤ H`), so the two induction sums have matching terms:
`induceTerm H θ x g = induceTerm (H/N) θ₁ (mk x) (mk g)`.  Summing over `G` rather than `G/N`
overcounts by the constant fiber size `|N|` (`card_filter_mk_eq`), which the normalization
`⅟|H| = ⅟(|N|·|H/N|)` absorbs. -/
theorem induce_eq_compHom_induce_of_inflation {N H : Subgroup G} [N.Normal] (hNH : N ≤ H)
    [Fintype G] [Fintype (G ⧸ N)] [Invertible (Nat.card ↥H : ℂ)]
    [Invertible (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ)]
    (θ : ClassFunction ↥H ℂ) (θ₁ : ClassFunction ↥(H.map (QuotientGroup.mk' N)) ℂ)
    (hinfl : ∀ (x : G) (hx : x ∈ H),
      θ ⟨x, hx⟩ = θ₁ ⟨QuotientGroup.mk x, Subgroup.mem_map_of_mem _ hx⟩) :
    ClassFunction.induce H θ
      = ClassFunction.compHom (QuotientGroup.mk' N)
          (ClassFunction.induce (H.map (QuotientGroup.mk' N)) θ₁) := by
  classical
  -- Membership bridge: `mk y ∈ H/N ↔ y ∈ H` (uses `N ≤ H`).
  have hmem : ∀ y : G, (QuotientGroup.mk y : G ⧸ N) ∈ H.map (QuotientGroup.mk' N) ↔ y ∈ H := by
    intro y
    rw [← QuotientGroup.mk'_apply, ← Subgroup.mem_comap, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk', sup_eq_left.mpr hNH]
  -- `|H| = |N| · |H/N|`: `H` is the `mk`-preimage of `H/N`, whose fibers all have size `|N|`.
  have hcardH : (Nat.card ↥H : ℂ)
      = (Nat.card ↥N : ℂ) * (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ) := by
    have hset : ((QuotientGroup.mk : G → G ⧸ N) ⁻¹'
        (H.map (QuotientGroup.mk' N) : Set (G ⧸ N))) = (H : Set G) := by
      ext y
      rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, hmem y]
    have h := QuotientGroup.card_preimage_mk N (H.map (QuotientGroup.mk' N) : Set (G ⧸ N))
    rw [hset, SetLike.coe_sort_coe, SetLike.coe_sort_coe] at h
    exact_mod_cast h
  have hneN : (Nat.card ↥N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  ext g
  -- Termwise match, the heart of the proof.
  have hterm : ∀ x : G, ClassFunction.induceTerm H θ x g
      = ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁
          (QuotientGroup.mk x) (QuotientGroup.mk g) := by
    intro x
    have hconj : ((QuotientGroup.mk x : G ⧸ N)⁻¹ * QuotientGroup.mk g * QuotientGroup.mk x)
        = (QuotientGroup.mk (x⁻¹ * g * x) : G ⧸ N) := by
      simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    by_cases hx : x⁻¹ * g * x ∈ H
    · rw [ClassFunction.induceTerm_of_mem θ hx,
        ClassFunction.induceTerm_of_mem θ₁ (by rw [hconj]; exact (hmem _).mpr hx)]
      rw [hinfl (x⁻¹ * g * x) hx]
      congr 1
    · rw [ClassFunction.induceTerm_of_not_mem θ hx,
        ClassFunction.induceTerm_of_not_mem θ₁ (by rw [hconj]; exact fun h => hx ((hmem _).mp h))]
  -- Sum over `G` = `|N|` × sum over `G ⧸ N` (constant fiber size).
  have hsum : (∑ x : G, ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁
        (QuotientGroup.mk x) (QuotientGroup.mk g))
      = (Nat.card ↥N : ℂ) * ∑ q : G ⧸ N,
          ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁ q (QuotientGroup.mk g) := by
    rw [← Finset.sum_fiberwise' (Finset.univ) (fun x : G => (QuotientGroup.mk x : G ⧸ N))
      (fun q => ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁ q
        (QuotientGroup.mk g)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_filter_mk_eq q]
  rw [ClassFunction.compHom_apply, QuotientGroup.mk'_apply, ClassFunction.induce_apply,
    ClassFunction.induce_apply, Finset.sum_congr rfl (fun x _ => hterm x), hsum, ← mul_assoc]
  -- `⅟|H| · |N| = ⅟|H/N|`.
  congr 1
  rw [invOf_eq_inv, invOf_eq_inv, hcardH, mul_inv, mul_comm ((Nat.card ↥N : ℂ))⁻¹,
    mul_assoc, inv_mul_cancel₀ hneN, mul_one]

open scoped Classical in
/-- **P2 — trivial-character induction–inflation commute**: the `θ = 1` case of Peterfalvi (1.6)(b)
(`induce_eq_compHom_induce_of_inflation`).  For a normal
subgroup `N ⊴ G` contained in `A ≤ G`, the induced trivial character of `A` is the inflation of the
induced trivial character of the quotient subgroup `A/N = A.map (mk' N) ≤ G ⧸ N`:
`Ind_A^G 1_A = (Ind_{A/N}^{G/N} 1) ∘ mk'`.

Both are permutation characters.  Pointwise at `g` (`induceTriv_apply`): the conjugator sets
`{x : x⁻¹gx ∈ A}` and `{xq : xq⁻¹ḡxq ∈ A/N}` correspond under `mk` (`x⁻¹gx ∈ A ↔ mk(x⁻¹gx) ∈ A/N`,
using `N ≤ A`), with every fiber of `mk` of size `|N|`; the `⅟|A| = ⅟(|N|·|A/N|)` normalization
absorbs the `|N|` fiber factor. -/
theorem induce_one_eq_compHom_induce_one_of_le {N A : Subgroup G} [N.Normal] (hNA : N ≤ A)
    [Fintype G] [Fintype (G ⧸ N)] [Invertible (Nat.card ↥A : ℂ)]
    [Invertible (Nat.card ↥(A.map (QuotientGroup.mk' N)) : ℂ)] :
    ClassFunction.induce A (trivialClassFunction ↥A)
      = ClassFunction.compHom (QuotientGroup.mk' N)
          (ClassFunction.induce (A.map (QuotientGroup.mk' N))
            (trivialClassFunction ↥(A.map (QuotientGroup.mk' N)))) :=
  induce_eq_compHom_induce_of_inflation hNA (trivialClassFunction ↥A)
    (trivialClassFunction ↥(A.map (QuotientGroup.mk' N))) (fun _ _ => rfl)

open scoped Classical in
/-- **P3 — inflated class functions are orthogonal to irreducibles not killing `N`.**  For `N ⊴ G`,
any class function `φ` of `G ⧸ N` inflates to something orthogonal to every irreducible character
`ψ` of `G` whose kernel does **not** contain `N`: `⟨φ ∘ mk', ψ⟩_G = 0`.

Peterfalvi's "(13.18.b) `Ind_{PW₁}^S 1 ⊥ μ_{0j}` because `P ⊄ ker μ_{0j}`": expand `φ` in the
`Irr(G ⧸ N)` basis (`sum_inner_irreducibleCharacter_smul`); each `compHom (mk' N) χ̄` is the
irreducible `inflate N χ̄` with `N ⊆ ker` (`subset_characterKernel_inflate`), so it differs from `ψ`
(which has `N ⊄ ker`) and is orthogonal to it (`irreducibleCharacter_inner_eq_ite`). -/
theorem inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker {N : Subgroup G} [N.Normal]
    [Fintype G] [Finite (G ⧸ N)] [Finite (IrreducibleCharacter (G ⧸ N))]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card (G ⧸ N) : ℂ)]
    (φ : ClassFunction (G ⧸ N) ℂ) (ψ : IrreducibleCharacter G)
    (hψ : ¬ ((N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction G ℂ))) :
    ClassFunction.inner (ClassFunction.compHom (QuotientGroup.mk' N) φ)
        (ψ : ClassFunction G ℂ) = 0 := by
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have : Fintype (IrreducibleCharacter (G ⧸ N)) := Fintype.ofFinite _
  have compHom_sum : ∀ (s : Finset (IrreducibleCharacter (G ⧸ N)))
      (a : IrreducibleCharacter (G ⧸ N) → ℂ),
      ClassFunction.compHom (QuotientGroup.mk' N)
          (∑ χ ∈ s, a χ • (χ : ClassFunction (G ⧸ N) ℂ))
        = ∑ χ ∈ s, a χ •
            ClassFunction.compHom (QuotientGroup.mk' N) (χ : ClassFunction (G ⧸ N) ℂ) := by
    intro s a
    induction s using Finset.induction with
    | empty => simp [ClassFunction.compHom_zero]
    | @insert χ s hχ ih =>
        rw [Finset.sum_insert hχ, ClassFunction.compHom_add, ClassFunction.compHom_smul, ih,
          Finset.sum_insert hχ]
  conv_lhs => rw [← sum_inner_irreducibleCharacter_smul φ, compHom_sum]
  rw [inner_sum_left]
  refine Finset.sum_eq_zero (fun χ _ => ?_)
  have hne : inflate N χ ≠ ψ := fun heq =>
    hψ (heq ▸ subset_characterKernel_inflate N χ)
  rw [ClassFunction.inner_smul_left, ← inflate_coe N χ, irreducibleCharacter_inner_eq_ite,
    if_neg hne, mul_zero]

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Carrier for the virtual character `beta_j` and `Gamma_j` in Peterfalvi (13.18).

**De-opacified (W3 §15); faithful to Peterfalvi (13.18) after the issue-3003 correction.**  This
carrier previously held six free `_formula : Prop` placeholders (the
[[scaffold-sorry-free-not-done]] convention).  Since `BetaData` has no external consumers (only
`beta_support_norm_and_remainder` produces it), the fields are now the **genuine Peterfalvi (13.18)
statements** about `β_j`/`Γ`, tied to `hyp`, the grid `hyp.eta`, and `S`:

* `support_formula` — **(13.18.a)** the support of `β_j` is contained in `S`'s η-carrier support;
* `norm_formula` — **(13.18.b)** `‖β_j‖²_S = (u−1)/q + 2` (its Frobenius `Ind` half is the
sorry-free
  `norm_induce_one_frobenius`);
* `Gamma_orthogonal_one` — **(13.18.c)** `(Γ, 1_G) = 0`, the residual is orthogonal to the
principal;
* `Gamma_real` — **(13.18.c)** `Γ` is real (`Γ.conj = Γ`);
* `Y_norm_bound` — **(13.18.d)** for any split `Γ = X + Y` (`X ⊥ Y`, `Y ⊥` grid), `‖Y‖² ≤ (u−1)/q`.

The remaining half of **(13.18.c)** — `Γ`'s `j`-independence (`defGamma`) — is the standalone proven
`gammaGrid_defGamma` (not a field here, to keep the `FiniteInduce` `τ_S` instances out of this
structure's explicit inner-product binders).  ⚠ The **removed** fields `Gamma_independent`
(`⟨Γ,η_ik⟩ = 0`) and the old `Y_norm_bound` (`‖Γ‖² ≤ (u−1)/q + 1`) were **overstatements** —
(13.18.c)
says `Γ` is independent of `j`, not grid-orthogonal, and (13.18.d) bounds the grid-orthogonal part
`Y`, not `‖Γ‖²` (issue 3003).

The genuine grid/Dade content bottoms out at the (3.2) τ-isometry (`tau3`, σ-pinned 2026-06-15) and
the (13.18.b) Frobenius norm; it is isolated into the single faithful producer
`betaData_of_grid`. -/
structure BetaData (hyp : Hypothesis (G := G)) where
  j : Fin hyp.p
  j_ne_zero : (j : ℕ) ≠ 0
  beta : ClassFunction ↥hyp.S ℂ
  Gamma : ClassFunction G ℂ
  /-- **(13.18.a)** support control: `β_j ∈ CF(S, P^# ∪ V_S)` — the Coq-faithful exact carrier
  (`PVSbeta`).  (The previous grid form `supp(β_j) ⊆ ⋃ᵢ supp(μ_{ij})` was an unfaithful
  restate; issue-3003 pattern.) -/
  support_formula : beta.support ⊆
    {z : ↥hyp.S |
      (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.P ∪
        OddOrder.GroupTheory.conjClassSetIn hyp.S
          (OddOrder.GroupTheory.typePV hyp.S hyp.Sdata)}
  /-- **(13.18.b)** norm: `‖β_j‖²_S = (u−1)/q + 2`, whose `Ind_{PW₁}^S 1` half is
  `norm_induce_one_frobenius`. -/
  norm_formula :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner beta beta
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)
  /-- **(13.18)** `Γ_j` is orthogonal to the principal character `1_G` (part of (13.18.c)). -/
  Gamma_orthogonal_one :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner Gamma (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0
  /-- **(13.18.c)** `Γ_j` is a real virtual character. -/
  Gamma_real : Gamma.conj = Gamma
  /-- **(13.18.d)** residual-norm bound: for any split `Γ = X + Y` with `X ⊥ Y` and `Y` orthogonal
  to the whole `η`-grid, `‖Y‖² ≤ (u−1)/q`.  This is the genuine (13.18.d) feeding the (14.14)
  case-`(c1)`/`(c2)` orthogonality switch.  (The previous field `‖Γ‖² ≤ (u−1)/q + 1` was **not**
  this statement — an overstatement, since `‖Γ‖² = ‖X‖² + ‖Y‖²` with `X` the nonzero grid-component;
  see issue 3003.  The (13.18.c) `j`-independence half is the standalone `gammaGrid_defGamma`.) -/
  Y_norm_bound :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (X Y : ClassFunction G ℂ), Gamma = X + Y → ClassFunction.inner X Y = 0 →
        (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
        (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ)

/-- **(13.18.b), Frobenius half**: `‖Ind_{PW₁}^S 1‖²_S = (u−1)/q + 1`.

By the inflation `Ind_{PW₁}^S 1 = Ind_{W̄₁}^{S̄} 1` inflated through `P` (P2
`induce_one_eq_compHom_induce_one_of_le` + P1 `inner_compHom_mk'_eq`), its `S`-norm equals
`‖Ind_{W̄₁}^{S̄} 1‖²` in the Frobenius quotient `S̄ = S/P ≅ U⋊W₁` (`uW1_isComplement_P` transported
by `isFrobeniusGroup_map_equiv`), which `norm_induce_one_frobenius` evaluates to
`(|U|−1)/|W₁| + 1 = (u−1)/q + 1` (using `c = 1`, Pf (13.12), so `|U| = u`).  The
`FiniteInduce`-instance content is `indPW1_inner_self_aux`; here we bridge to the caller's
`Fintype`/`Invertible` instances (both `Subsingleton`). -/
theorem indPW1_inner_self_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by
  intro _ _
  convert indPW1_inner_self_aux _hG hyp hc1 using 2
  exact Subsingleton.elim _ _

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacter.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`P ⊄ ker μ_{0j}`** (Pf (13.18.b) kernel step, `S`-side).  For `j ≠ 0`, the base-row grid
irreducible `μ_{0j}` does not have the Fitting kernel `P` in its character kernel.

Contrapositive of Peterfalvi's argument (mirroring `PrimeTIResidue.constituent_P_not_subset_ker`):
if `P ⊆ ker μ_{0j}` then `W₂ ⊆ P ⊆ ker μ_{0j}`, so `Res_{S'} μ_{0j}` is trivial on the `W₂`-part
(`characterKernel_restrict_subgroupOf`); its constituent `ψ` — the (4.5.a) source of
`μ_j = ∑_i μ_{ij} = Ind_{S'} ψ`, with `⟨Res_{S'} μ_{0j}, ψ⟩ = 1` by Frobenius reciprocity — inherits
that kernel containment (`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), contradicting
the
`mu_colSum_eq_induce` clause `W₂ ⊄ ker ψ`. -/
theorem P_not_subset_characterKernel_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)) := by
  classical
  set μ0 := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμ0
  have hW2_le_P : hyp.W2 ≤ hyp.P := by
    have h := hyp.Sdata.W2_le
    rw [hyp.Sdata_W2_eq, hyp.Sdata.H_eq, ← hyp.P_eq_SF] at h
    exact h.trans inf_le_left
  intro hPker
  obtain ⟨psiS, hpsiIrr, hpsiInd, hpsiW2⟩ := hyp.mu_colSum_eq_induce j
  have hj' : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by rw [h])
  have hW2notpsi := hpsiW2 hj'
  have hW2Sker : (hyp.W2.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel μ0 :=
    fun x hx => hPker (Subgroup.comap_mono hW2_le_P hx)
  have hRker := OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf
    ((derivedInG hyp.S).subgroupOf hyp.S) hW2Sker
  have hResChar := OddOrder.Peterfalvi.S08.isCharacter_restrict
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j).isCharacter
    ((derivedInG hyp.S).subgroupOf hyp.S)
  -- `⟨∑_i μ_{ij}, μ_{0j}⟩ = 1` (orthonormality: only the `i = 0` term survives).
  have hmul : ClassFunction.inner (∑ i, hyp.mu i j) μ0 = 1 := by
    rw [inner_sum_left]
    refine (Finset.sum_eq_single ⟨0, hyp.q_prime.pos⟩ (fun i _ hi => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨hyp.mu i j, hyp.mu_irreducible i j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      rw [if_neg (fun heq => hi (hyp.mu_col_injective j
        (congrArg (fun χ : IrreducibleCharacter ↥hyp.S => (χ : ClassFunction ↥hyp.S ℂ)) heq)))] at h
      exact h
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      simpa using h
  have hfrob := ClassFunction.inner_induce_eq_inner_restrict
    ((derivedInG hyp.S).subgroupOf hyp.S) psiS μ0
  rw [← hpsiInd, hmul] at hfrob
  have hinner : ClassFunction.inner
      (ClassFunction.restrict ((derivedInG hyp.S).subgroupOf hyp.S) μ0) psiS ≠ 0 := by
    rw [RepresentationTheory.inner_conj_symm, ← hfrob]; simp
  exact hW2notpsi (fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hpsiIrr hinner (hRker hx))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b) orthogonality half** (`FiniteInduce`-instance form). -/
private theorem indPW1_inner_mu_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  classical
  have hP_le_S : hyp.P ≤ hyp.S :=
    (by rw [hyp.S_deriv_eq_PU]; exact le_sup_left : hyp.P ≤ derivedInG hyp.S).trans
      (Subgroup.map_subtype_le _)
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono le_sup_left
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA]
  exact OddOrder.RepresentationTheory.inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker _
    ⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ j, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
    (P_not_subset_characterKernel_mu _hG hyp j hj)

/-- **(13.18.b), orthogonality half**: `⟨Ind_{PW₁}^S 1, μ_{0j}⟩ = 0` for `j ≠ 0`.

`Ind_{PW₁}^S 1 = (Ind_{Ā}^{S̄} 1) ∘ mk'` (P2) is inflated from `S̄ = S/P`, so all its irreducible
constituents kill `P`; `μ_{0j}` does not (`P_not_subset_characterKernel_mu`), so they are orthogonal
(`inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker`).  `_aux` carries the `FiniteInduce`
instances; the wrapper bridges to the caller's (`Subsingleton`). -/
theorem indPW1_inner_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  intro _ _
  convert indPW1_inner_mu_aux _hG hyp j _hj using 2
  exact Subsingleton.elim _ _

/-- **(13.18.b) norm**: `‖β_j‖²_S = (u−1)/q + 2`.

Genuine reduction: `β_j = Ind_{PW₁}^S 1 − μ_{0j}`, so by bilinearity
`‖β_j‖² = ‖Ind‖² − ⟨Ind,μ_{0j}⟩ − ⟨μ_{0j},Ind⟩ + ‖μ_{0j}‖²`.  Here `‖μ_{0j}‖² = 1` is **proven**
from `hyp.mu_irreducible` (via `irreducibleCharacter_inner_eq_ite`), `⟨μ_{0j},Ind⟩ = 0` follows
from `⟨Ind,μ_{0j}⟩ = 0` by conjugate symmetry, and the remaining `‖Ind‖² = (u−1)/q + 1`
(`indPW1_inner_self`) and `⟨Ind,μ_{0j}⟩ = 0` (`indPW1_inner_mu`) are the isolated §13 obligations.
`(u−1)/q + 1 + 1 = (u−1)/q + 2`. -/
theorem betaGrid_norm_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (betaGrid hyp j) (betaGrid hyp j)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ) := by
  intro _ _
  set μ := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμdef
  have hμμ : ClassFunction.inner μ μ = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩)
    simpa using hite
  have hIμ : ClassFunction.inner (indPW1 hyp) μ = 0 := indPW1_inner_mu hG hyp j hj
  have hμI : ClassFunction.inner μ (indPW1 hyp) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hIμ, star_zero]
  have hII : ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) :=
    indPW1_inner_self_of_c_eq_one hG hyp hc1
  have hbeta : betaGrid hyp j = indPW1 hyp - μ := rfl
  rw [hbeta, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hII, hIμ, hμI, hμμ]
  push_cast
  ring

/-- **The Coq `A0beta` inclusion `P^# ∪ V_S ⊆ 'A0(S)`** (the final step of (13.18.a)): the sharp
Fitting kernel `P^#` and the `S`-class-closure of the cyclic-TI set `V = W − (W₁ ∪ W₂)` both land
in the honest `A₀(S) = A(S) ∪ V^S`.  The `V^S` part is the definitional right component (after the
`Sdata.W1/W2` synchronization); `P^#` lands in `A(S) = centralizerSupport (S_σ^#) S'` because
`P = S_F ≤ S_σ` (`maxNilpotentNormalHall_le_Msigma`, every maximal — general type `P`),
`P ≤ S' = P ⊔ U`, and every element self-centralizes. -/
theorem sharpP_union_V_subset_A0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    sharpSubgroup hyp.P ∪
        conjClassSetIn hyp.S (typePV hyp.S hyp.Sdata)
      ⊆ S10.typePACore0 hyp.S hyp.Sdata := by
  have hPle_Ms : hyp.P ≤ OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.S_maximal
  intro z hz
  rcases hz with hzP | hzV
  · -- `P^# ⊆ A(S) ⊆ A₀(S)`.
    refine S10.typePACore_subset_A0Set hyp.Sdata ?_
    obtain ⟨hzP_mem, hz1⟩ := hzP
    rw [Set.mem_singleton_iff] at hz1
    refine S10.mem_typePACore.mpr ⟨?_, hz1, z, ⟨hPle_Ms hzP_mem, ?_⟩, ?_⟩
    · have hPle : hyp.P ≤ derivedInG hyp.S := by
        rw [hyp.S_deriv_eq_PU]; exact le_sup_left
      exact hPle hzP_mem
    · rwa [Set.mem_singleton_iff]
    · exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff] at hw; subst hw; rfl
  · exact Set.mem_union_right _ hzV

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.a), `'A0(S)`-support form**: `supp(β_j) ⊆ 'A0(S)` for `j ≠ 0`.

The Coq `A0beta` (`PFsection13.v:1870`), obtained from `PVSbeta` (`β_j ∈ 'CF(S, P^# ∪ V_S)`,
`PFsection13.v:1833`) via `P^# ∪ V_S ⊆ 'A0(S)`.  `PVSbeta` cancels the induced permutation character
`Ind_{PW₁}^S 1` against `μ_{0j}` off `P^# ∪ V_S`, using the `W₁`-class `normedTI` structure in
`S̄ = S/P = Ū ⋊ W̄₁` (Coq `gammaW1`) together with the prime-`TI` residue value `prTIirr_id`; both
bottom out at the shared prime-`TI` residue content (issue 9014) that connects the free `μ`-grid to
the σ-residue theory.  **This single `'A0`-support obligation is what both
`gammaGrid_orthogonal_one`
and `gammaGrid_Y_norm_bound` reduce to** (the honest `'A0`-Dade=Ind bridge
`sInstance_dade0_eq_induce`, issue 9076, then discharges the remaining Dade content). -/
theorem betaGrid_A0_support_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S := by
  intro z hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact sharpP_union_V_subset_A0 hG hyp (betaGrid_support_of_c_eq_one hG hyp hc1 j hj hz)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0`.

**De-scaffolded** (issue 9076): the `'A0(S)` `normedTI` content the old docstring flagged as
"missing" is now supplied by the honest `'A0`-Dade=Ind bridge `sInstance_dade0_eq_induce`.
Reduction
(Coq `oGamma1`): `⟨Γ,1⟩ = ⟨τ_S β_{#1},1⟩ − ⟨1,1⟩ + ⟨η_{01},1⟩`, and
* `⟨1,1⟩ = 1` (`constOne_inner_self_eq_one`);
* `⟨η_{01},1⟩ = 0` — grid orthogonality: `1_G = η_{00}` (`eta_principal_eq_trivial`) and `η_{01} ⊥
  η_{00}` (`eta_orthonormal`);
* `⟨τ_S β_{#1},1_G⟩ = 1` — the bridge gives `τ_S β_{#1} = Ind_S^G β_{#1}` (needs `β_{#1}` supported
in
  `'A0(S)`, `betaGrid_A0_support`), so by Frobenius reciprocity (`inner_induce_eq_inner_restrict`)
  `⟨Ind_S^G β_{#1}, 1_G⟩ = ⟨β_{#1}, 1_S⟩ = ⟨Ind_{PW₁}^S 1, 1_S⟩ − ⟨μ_{01}, 1_S⟩ = 1 − 0`, where
  `⟨Ind 1, 1_S⟩ = 1` (`inner_induce_trivialChar_constOne_eq_one`) and `⟨μ_{01}, 1_S⟩ = 0` (`μ_{01}`
  irreducible and `≠ 1_S`, since `⟨Ind 1, μ_{01}⟩ = 0 ≠ 1`, `indPW1_inner_mu`).

The **single** remaining gate is `betaGrid_A0_support` (the (13.18.a) `'A0`-support). -/
private theorem gammaGrid_orthogonal_one_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  classical
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Fintype ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `⟨Ind_{PW₁}^S 1, 1_S⟩ = 1`.
  have hind : ClassFunction.inner (indPW1 hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 1 := by
    rw [indPW1, ←
        OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
    exact OddOrder.Peterfalvi.S09.Cert.inner_induce_trivialChar_constOne_eq_one
      ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
  -- `⟨μ_{01}, 1_S⟩ = 0`: `μ_{01}` is irreducible and `≠ 1_S` (else `⟨Ind 1, μ_{01}⟩ = 1 ≠ 0`).
  have hmu : ClassFunction.inner
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 0 := by
    have hIμ : ClassFunction.inner (indPW1 hyp)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 :=
      indPW1_inner_mu hG hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)
    have hne : (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
          hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
        ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S := by
      intro heq
      apply one_ne_zero (α := ℂ)
      have hcf : hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) :=
        congrArg (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
          (χ : ClassFunction ↥hyp.S ℂ)) heq
      rw [hcf, hind] at hIμ
      exact hIμ
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
        hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S)
    rw [if_neg hne] at hite
    exact hite
  -- `⟨τ_S(β_{#1}), 1_G⟩ = 1` via the `'A0`-Dade=Ind bridge + Frobenius reciprocity.
  have htau : ClassFunction.inner (tauSbetaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 1 := by
    have hbridge : tauSbetaGrid hG hyp
        = ClassFunction.induce hyp.S (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩) := by
      rw [tauSbetaGrid]
      exact hyp.sInstance_dade0_eq_induce hG hnoV
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1
          ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num))
    rw [hbridge, ClassFunction.inner_induce_eq_inner_restrict]
    have hres : ClassFunction.restrict hyp.S
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) := by
      ext x; rw [ClassFunction.restrict_apply]; rfl
    rw [hres]
    simp only [betaGrid]
    rw [ClassFunction.inner_sub_left, hind, hmu, sub_zero]
  -- `⟨η_{01}, 1_G⟩ = 0`.
  have heta : ClassFunction.inner
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    have h00 : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ := by
      rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl
    rw [h00]
    have horth := OddOrder.Peterfalvi.S16.eta_orthonormal hyp
      ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.q_prime.pos⟩
      ⟨1, by have := hyp.three_le_p; omega⟩ ⟨0, hyp.p_prime.pos⟩
    rw [if_neg (by rintro ⟨-, h2⟩; exact absurd (congrArg Fin.val h2) (by norm_num))] at horth
    exact horth
  rw [GammaGrid, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one, htau, heta]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0` (public form).  Thin wrapper over `gammaGrid_orthogonal_one_aux`
that reconciles the caller's `Fintype G`/`Invertible (Nat.card G : ℂ)` instances with the
`FiniteInduce`-scoped ones the core proof uses (both are `Subsingleton`). -/
theorem gammaGrid_orthogonal_one_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner (GammaGrid hG hyp)
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  intro _ _
  convert gammaGrid_orthogonal_one_aux hG hnoV hyp hc1 using 2; exact Subsingleton.elim _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.d) residual-norm bound**: for any split `Γ = X + Y` with `X ⊥ Y` and `Y` orthogonal
to the whole `η`-grid `{η_{ik}}`, `‖Y‖² ≤ (u−1)/q` — fully proven (Coq `PFsection13.v:1915-1934`;
the earlier `Re⟨Γ,Γ⟩ ≤ (u−1)/q + 1` overstatement was corrected in issue 3003: `‖Γ‖²` itself is
**not** bounded, only the grid-orthogonal residual `Y`).  Public form of
`gammaGrid_Y_norm_bound_aux`, reconciling the caller's `Fintype G`/`Invertible` instances with
the `FiniteInduce`-scoped ones (both are `Subsingleton`). -/
theorem gammaGrid_Y_norm_bound_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (X Y : ClassFunction G ℂ), GammaGrid hG hyp = X + Y →
        ClassFunction.inner X Y = 0 →
        (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
        (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) := by
  intro _ _ X Y defXY oXY oYeta
  have h := gammaGrid_Y_norm_bound_aux hG hnoV hyp hc1 X Y defXY
    (by convert oXY using 2; exact Subsingleton.elim _ _)
    (fun i k => by convert oYeta i k using 2; exact Subsingleton.elim _ _)
  convert h using 3
  exact Subsingleton.elim _ _

/-- **Faithful §13 producer for Peterfalvi (13.18).**  The (13.18) virtual characters `β_j`/`Γ`
and their genuine properties (support (13.18.a), the (13.18.b) norm `‖β_j‖² = (u−1)/q + 2`,
orthogonality of `Γ` to `1_G`, reality, and the (13.18.d) `‖Y‖²` residual bound) are supplied here.
The concrete `β_j = betaGrid hyp j` and `Γ = GammaGrid hG hyp` are built from the honest `S`-side
Dade isometry `τ_S` (`hyp.dadeHypS0`, **not** the `= 0` placeholder `hyp.tauS`) and the induced
trivial character `Ind_{PW₁}^S 1`.  The bundled properties are the precisely-isolated §13
obligations `betaGrid_support` / `betaGrid_norm` / `gammaGrid_orthogonal_one` /
`gammaGrid_real` / `gammaGrid_Y_norm_bound`; the (13.18.c) `j`-independence is the standalone
`gammaGrid_defGamma` (proven, modulo the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`).
Their deep content bottoms out at the (13.2.e) `A₀(S)` normedTI Dade=Ind bridge, the (5.3)
`S`↔`W` Dade cross-relation, and the Frobenius norm `norm_induce_one_frobenius`. -/
noncomputable def betaData_of_grid_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    BetaData hyp where
  j := j
  j_ne_zero := hj
  beta := betaGrid hyp j
  Gamma := GammaGrid hG hyp
  support_formula := betaGrid_support_of_c_eq_one hG hyp hc1 j hj
  norm_formula := betaGrid_norm_of_c_eq_one hG hyp hc1 j hj
  Gamma_orthogonal_one := gammaGrid_orthogonal_one_of_c_eq_one hG hnoV hyp hc1
  Gamma_real := gammaGrid_real_of_c_eq_one hG hnoV hyp hc1
  Y_norm_bound := gammaGrid_Y_norm_bound_of_c_eq_one hG hnoV hyp hc1

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_CoreLemmas.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace Hypothesis

/-- The congruence used in **Peterfalvi (14.4)**: from `q < p` and `q` prime,
`q` cannot be `1 mod p`. -/
theorem q_not_modEq_one_mod_p (hyp : Hypothesis (G := G)) :
    ¬ hyp.base.q ≡ 1 [MOD hyp.base.p] := by
  intro hmod
  have hp_gt_one : 1 < hyp.base.p := hyp.base.q_prime.one_lt.trans hyp.q_lt_p
  have hq_eq_one : hyp.base.q = 1 :=
    Nat.ModEq.eq_of_lt_of_lt hmod hyp.q_lt_p hp_gt_one
  exact hyp.base.q_prime.ne_one hq_eq_one

/-- The T-side cyclotomic quotient from **Peterfalvi (14.4)** is odd. -/
theorem tSide_cyclotomic_quotient_odd (hyp : Hypothesis (G := G)) :
    Odd ((hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)) :=
  OddOrder.Peterfalvi.S15.cyclotomic_quotient_odd
    hyp.base.q_prime hyp.base.q_odd hyp.base.p_odd

/-- Every positive divisor of the T-side cyclotomic quotient from
**Peterfalvi (14.4)** is `1 mod p`. -/
theorem tSide_cyclotomic_quotient_divisor_modEq_one (hyp : Hypothesis (G := G)) :
    ∀ x : ℕ, x ≠ 0 →
      x ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) →
        x ≡ 1 [MOD hyp.base.p] :=
  OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one
    hyp.base.q_prime hyp.base.p_prime hyp.q_not_modEq_one_mod_p

end Hypothesis

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **The `T`-side derived complement `T = T' ⋊ W₂`, index `[T : T'] = p`** (Coq
`index_sdprod defT`, `p = |W2|`).  From the base `W2_isComplement_T_deriv` (`T' ⋊ W₂ = T`, available
ungated at the §16 construction) and `p = |W2|` (`p_eq_card_W2`).  The degree factor of Coq
`calT1_1p` (`Ind_{QV}^T θ (1) = [T:QV]·θ(1) = p` for linear `θ`). -/
theorem T_derived_index_eq_p (hyp : Hypothesis (G := G)) :
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T).index = hyp.base.p := by
  have hW2_le_T : hyp.base.W2 ≤ hyp.base.T := by
    have h1 : hyp.base.W2 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_right
    have h2 : hyp.base.W ≤ hyp.base.T := by rw [hyp.base.W_eq_inter]; exact inf_le_right
    exact h1.trans h2
  rw [hyp.base.W2_isComplement_T_deriv.symm.index_eq_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2_le_T).toEquiv, hyp.base.p_eq_card_W2]

/-- **`Q.subgroupOf QV` is normal in `QV = T' = derivedInG T`** (`Q = T_F` normalized by `T ⊇ T'`).
The normality feeding the `QV/Q` quotient (Coq `nsQQV`). -/
theorem T_Q_subgroupOf_derived_normal (hyp : Hypothesis (G := G)) :
    (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).Normal := by
  have hQ_le : hyp.base.Q ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_left
  have hM'_le_T : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hT_le_NQ : hyp.base.T ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)

/-- **The `T`-side complement `Q ⋊ V = QV = T'`** (Coq `defQV`): `Q` (normal in `T'`, being `T_F`
restricted) and `V` complement inside `derivedInG T`, from `Q ⊔ V = T'` (`T_deriv_eq_QV`) and
`Q ⊓ V = ⊥` (`Q_inf_V_eq_bot`).  The `sdprod` giving `QV/Q ≅ V`.  Mirrors the complement built
inside
`S15.coprime_card_V_card_Q_of_disjoint`. -/
theorem T_Q_isComplement_V_derived [Finite G] (hyp : Hypothesis (G := G)) :
    Subgroup.IsComplement' (hyp.base.Q.subgroupOf (derivedInG hyp.base.T))
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) := by
  have hQ_le : hyp.base.Q ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have := T_Q_subgroupOf_derived_normal hyp
  have hQnVn_inf : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ⊓
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
      OneMemClass.coe_one]
    refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
    have hxQV : x ∈ (hyp.base.Q ⊓ hyp.base.V : Subgroup G) := ⟨hxQ, hxV⟩
    rwa [hyp.base.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
  have hQnVn_sup : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ⊔
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.base.T_deriv_eq_QV.symm,
      Subgroup.subgroupOf_self]
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hQnVn_inf)
  have hmul := Subgroup.normal_mul (hyp.base.Q.subgroupOf (derivedInG hyp.base.T))
    (hyp.base.V.subgroupOf (derivedInG hyp.base.T))
  rw [hQnVn_sup, Subgroup.coe_top] at hmul
  exact hmul.symm

/-- **`|QV/Q| = |V|`** (Coq `card_isog (sdprod_isog defQV)`): the quotient of `QV = T'` by `Q` has
the order of the complement `V`.  The source of the abelian-quotient irreducible count `v − 1`
(nonprincipal `QV/Q`-irreducibles) in Coq `size calT1 = (v.-1) %/ p`. -/
theorem T_card_quot_Q_derived_eq_card_V [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card (↥(derivedInG hyp.base.T) ⧸ (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)))
      = Nat.card ↥hyp.base.V := by
  have hV_le : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have := T_Q_subgroupOf_derived_normal hyp
  -- `QV/Q ≅ V.subgroupOf QV` via the complement (`Q` normal in the `K`-slot).
  rw [Nat.card_congr (T_Q_isComplement_V_derived hyp).symm.QuotientMulEquiv.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv]

/-- **The intrinsic type-III `U ⋊ W₁` Frobenius** (ungated).  From `hIII : IsTypeIII T` take the
*intrinsic* datum `td = hIII.some : TypeIIIData T`; its `td.typeP.U ⋊ td.typeP.W₁` is a Frobenius
group (Peterfalvi Def (8.4), `S11.typeP_uW1_frobenius` fed the non-triviality `td.common.1`).

Crucially this **avoids** the T-side reconciliation `S15.reconciled_typePData_T` (then sorried,
which is
what gated the abstract-`V`/`W₂` route): the datum `td` comes straight from `IsTypeIII T` with no
reconciliation to the abstract Hypothesis fields `V`/`W₂`.  It is the ungated source of the quotient
Frobenius `T/Q` needed for `inertia_inflate_eq_of_frobeniusQuotient`.  (Coq `frobVW2`.) -/
theorem T_typeIII_UW1_frobenius {M : Subgroup G} (td : OddOrder.GroupTheory.TypeIIIData M) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(td.typeP.U ⊔ td.typeP.W1)
      (td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1))
      (td.typeP.W1.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) :=
  OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP td.common.1

/-- **The intrinsic type-III cyclic factor has order `p`** (ungated): `|td.typeP.W₁| = [T:T'] = p`.
`td.typeP.W₁` complements `T' = derivedInG T` in `T` (`M_complement`), so `|W₁| = [T:T']`
(`card_W1_eq_derived_index`), and `[T:T'] = p` (`T_derived_index_eq_p`).  This is the orbit-size /
degree factor of `calT1` (Coq `index_sdprod defT`, `p = |W₂|`; note the intrinsic `.W₁` is the
`T'`-complement, matching Coq's `W₂` — the abstract-Hypothesis `W₂` — **not** the abstract `W₁`). -/
theorem T_typeIII_card_W1 [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    Nat.card ↥td.typeP.W1 = hyp.base.p := by
  rw [td.typeP.card_W1_eq_derived_index, T_derived_index_eq_p hyp]

/-- **The intrinsic type-III complement has order `|V|`** (ungated, canonical):
`|td.typeP.U| = |V|`.
`|td.typeP.U| = [T' : M_F]` (`card_U_eq_index`, `M_F = Q`), and `[T' : M_F] = |QV/Q| = |V|`
(`Subgroup.index_eq_card` + `T_card_quot_Q_derived_eq_card_V`).  The equality is **canonical** —
both
sides are the intrinsic index `[T':M_F]` — so it needs *no* reconciliation of `td.typeP.U` with the
abstract `V` (the source of `calT1`'s abelian-quotient count `size = (v−1)/p`). -/
theorem T_typeIII_card_U [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    Nat.card ↥td.typeP.U = Nat.card ↥hyp.base.V := by
  rw [td.typeP.card_U_eq_index, ← hyp.base.Q_eq_TF, Subgroup.index_eq_card]
  exact T_card_quot_Q_derived_eq_card_V hyp

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open scoped Classical in
/-- Galois closure passes from a source family to its induced family. -/
theorem inducedFamily_mapRingEquiv_mem
    {L : Type*} [Group L] [Fintype L]
    (K : Subgroup L) [Finite K] [Invertible (Nat.card K : ℂ)]
    (𝒯 : Finset (IrreducibleCharacter K))
    (hgalois : ∀ (σc : ℂ ≃+* ℂ) θ, θ ∈ 𝒯 →
      IrreducibleCharacter.galoisMap σc θ ∈ 𝒯)
    (σc : ℂ ≃+* ℂ) {ζ : ClassFunction L ℂ}
    (hζ : ζ ∈ (↑(𝒯.image (fun θ =>
      ClassFunction.induce K θ.toClassFunction)) :
        Set (ClassFunction L ℂ))) :
    ClassFunction.mapRingEquiv σc ζ ∈
      (↑(𝒯.image (fun θ => ClassFunction.induce K θ.toClassFunction)) :
        Set (ClassFunction L ℂ)) := by
  rw [Finset.mem_coe, Finset.mem_image] at hζ ⊢
  obtain ⟨θ, hθ, rfl⟩ := hζ
  refine ⟨IrreducibleCharacter.galoisMap σc θ, hgalois σc θ hθ, ?_⟩
  exact (ClassFunction.mapRingEquiv_induce σc θ.toClassFunction).symm

/-- **The intrinsic type-III kernel size bound `2p + 1 ≤ |V|`** (ungated, the crude `hcard2` input).
The intrinsic `U ⋊ W₁` Frobenius (`T_typeIII_UW1_frobenius`) has odd kernel `U` (`|U| = |V|`,
`T_typeIII_card_U`) and odd complement `W₁` (`|W₁| = p`, `T_typeIII_card_W1`); the odd-order
Frobenius
size condition `IsFrobeniusGroup.two_mul_card_complement_add_one_le_card_kernel` (`|A| ∣ |N|−1`, and
`|N|−1` even with `|A|` odd forces `|N|−1 ≥ 2|A|`) then gives `2p + 1 ≤ |V|`.

This is the **ungated** source of the `calT1` crude size bound `2 ≤ (|V|−1)/p` (`hcard2` in
`T_typeIII_ratio_le`): it needs only oddness (subgroups of the odd `G`) plus the intrinsic Frobenius
index `[T:T'] = p` — **not** the lane-b-gated `|V|`-lower-bound `v = (q^p−1)/(q−1)` (13.15).  (The
`v`-value is still needed for the *exact* count `(v−1)/p`, but the coherence input `hcard2` only
needs
`≥ 2`.) -/
theorem T_typeIII_two_p_add_one_le_card_V [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    2 * hyp.base.p + 1 ≤ Nat.card ↥hyp.base.V := by
  have := hyp.base.finiteG
  have hfrob := T_typeIII_UW1_frobenius td
  have hVodd : Odd (Nat.card ↥hyp.base.V) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.V)
  -- Kernel `|U.subgroupOf| = |U| = |V|`, complement `|W₁.subgroupOf| = |W₁| = p`.
  have hcardN : Nat.card ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1))
      = Nat.card ↥hyp.base.V := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
      T_typeIII_card_U hyp td]
  have hcardA : Nat.card ↥(td.typeP.W1.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) = hyp.base.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
      T_typeIII_card_W1 hyp td]
  have hNodd : Odd (Nat.card ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1))) := by
    rw [hcardN]; exact hVodd
  have hAodd : Odd (Nat.card ↥(td.typeP.W1.subgroupOf (td.typeP.U ⊔ td.typeP.W1))) := by
    rw [hcardA]; exact hyp.base.p_odd
  have h := hfrob.two_mul_card_complement_add_one_le_card_kernel hNodd hAodd hfrob.ne_bot_kernel
  rwa [hcardN, hcardA] at h

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapPrimeTI.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped Classical in
/-- A linear `calT1` source induces to degree `[T:T'] = p`. -/
theorem typeIII_induced_source_degree [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T]
    [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible
      (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (θ : IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (hθ1 : (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1) :
    ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        θ.toClassFunction 1 = (hyp.base.p : ℂ) := by
  have : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  rw [ClassFunction.induce_apply_one, T_derived_index_eq_p hyp,
    hθ1, mul_one]

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

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapCross.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped BigOperators

open scoped Classical in
/-- **Peterfalvi (13.2.e), type-`P₁` `A₀(M)` has no escaping point.**

This is the Type-`P₁` instance of Coq `FTtypeP_facts(e)` (`PFsection13.v:224–242`).
An escaping `A₀(M)` point is `M_σ#` by (8.13.b).  BG Theorem D(4) attaches a unique
maximal neighbour `N`, of type `F` or `P₂`.  In the type-`F` branch, Peterfalvi (12.7)
Frobenius-kernel regularity forces the point into `N_σ`, contradicting D(4).  In the
type-`P₂` branch, D(4) makes `M` type `F`, contradicting that `M` is type `P₁`.

This is the genuine group-theoretic producer behind the T-side full-`A₀` normed-TI
input; it does not use the downstream conclusion that `T` is type II. -/
theorem escaping_typePA0_eq_empty_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {M : Subgroup G} (hM : M ∈ OddOrder.GroupTheory.maximalSubgroups G)
    (data : OddOrder.GroupTheory.TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    OddOrder.GroupTheory.escapingCentralizerSet M
      (OddOrder.GroupTheory.typePA0 M data) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro a haesc
  have haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.Peterfalvi.S10.escaping_typePA0_mem_sigmaSharp_of_isTypeP1
      hG hM data hP1 haesc
  obtain ⟨R, -, N, ⟨hNmem, -, hMFN, hxAN, hNtype, -, hP2imp⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.exists_RData_escape_structure hG hM haσ haesc.2
  rcases hNtype with hNF | hNP2
  · have hNmax : N ∈ OddOrder.GroupTheory.maximalSubgroups G := hNmem.1
    have hNI : OddOrder.GroupTheory.IsTypeI N :=
      (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hNmax).mpr hNF
    obtain ⟨fdata, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV hNmax hNI
    have hker : fdata.typeI.typeF.H = OddOrder.BG.Ch3.S10.Msigma N := by
      rw [fdata.typeI.typeF.H_eq]
      exact hMFN
    obtain ⟨haN, hne⟩ : a ∈ OddOrder.BG.Ch4.S16.hatMsigma N := hxAN.1.1
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨hzMσ, hzC⟩ := Subgroup.mem_inf.mp z.2
    have hzN : (z : G) ∈ N := OddOrder.BG.Ch3.S10.Msigma_le N hzMσ
    have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have haker : (⟨a, haN⟩ : ↥N) ∈ fdata.typeI.typeF.H.subgroupOf N := by
      refine fdata.frobenius.centralizer_kernel_le ⟨(z : G), hzN⟩
        (Subgroup.mem_subgroupOf.mpr (by rw [hker]; exact hzMσ))
        (fun h => hzG1 (congrArg Subtype.val h)) ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hzC).symm
    exact hxAN.2 (SetLike.mem_coe.mpr
      (by rw [← hker]; exact Subgroup.mem_subgroupOf.mp haker))
  · obtain ⟨hFM, -⟩ := hP2imp hNP2
    exact OddOrder.BG.Ch4.S14.not_isTypeP_and_isTypeF ⟨hP1.1, hFM⟩

open scoped Classical in
/-- **Peterfalvi (13.2.e), full type-`P₁` `A₀(M)` is a TI-subset.**

The escape exclusion above makes every faithful Dade stabilizer trivial; Peterfalvi
(2.3), already encoded by `Hypothesis.isTISubset_of_forall_H_eq_bot`, then supplies the
full TI statement.  This is Coq's `normedTI 'A0(M) G M` conclusion with no downstream
type-II assumption. -/
theorem typePA0_isTISubset_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {M : Subgroup G} (hM : M ∈ OddOrder.GroupTheory.maximalSubgroups G)
    (data : OddOrder.GroupTheory.TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    OddOrder.GroupTheory.IsTISubset (OddOrder.GroupTheory.typePA0 M data) M := by
  let := Fintype.ofFinite G
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hM data hP1).some
  apply full.dade.isTISubset_of_forall_H_eq_bot
  intro a
  rw [full.H_eq_ftSupportKernel]
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping (by
    intro haesc
    have hempty := escaping_typePA0_eq_empty_of_isTypeP1 hG hnoV hM data hP1
    rw [hempty] at haesc
    exact Set.notMem_empty a.1 haesc)

open scoped Classical in
/-- **Peterfalvi (13.2.e), reduction of full `A₀(T)` normed-TI to `A(T)`.**

The exceptional `V^T` part is already non-escaping, so centralizer containment on
`A(T)=typePA(T)` implies every full `A₀(T)` point is non-escaping. Hence the faithful
Dade stabilizer `H(a)=ftSupportKernel ... a` is bottom. -/
theorem fullTypeP1Dade_H_eq_bot_of_typePA_centralizer_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hA : ∀ x ∈ OddOrder.GroupTheory.typePA hyp.base.T dataT,
      Subgroup.centralizer ({x} : Set G) ≤ hyp.base.T) :
    ∀ a,
      ((OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
        hG hyp.base.T_maximal dataT hP1).some.dade.H a) = ⊥ := by
  classical
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hyp.base.T_maximal dataT hP1).some
  have hA0 : ∀ x ∈ OddOrder.GroupTheory.typePA0 hyp.base.T dataT,
      Subgroup.centralizer ({x} : Set G) ≤ hyp.base.T := by
    intro x hx
    change x ∈ OddOrder.GroupTheory.typePA hyp.base.T dataT ∪
      OddOrder.GroupTheory.conjClassSetIn hyp.base.T
        (OddOrder.GroupTheory.typePV hyp.base.T dataT) at hx
    rcases hx with hxA | hxV
    · exact hA x hxA
    · exact OddOrder.Peterfalvi.S10.conjClassSetIn_typePV_centralizer_le_M dataT hxV
  intro a
  change full.dade.H a = ⊥
  rw [full.H_eq_ftSupportKernel]
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping
    (fun hesc => hesc.2 (hA0 a.1 a.2))

open scoped Classical in
/-- **Peterfalvi (13.2.e), full `A₀(T)` normed-TI gives trivial Dade stabilizers.**

This is the direct bridge from the Coq conclusion `normedTI 'A0(T) G T` to the selected
full type-`P₁` Dade datum.  TI controls each point centralizer, while the exceptional
`V^T` reduction is handled by `fullTypeP1Dade_H_eq_bot_of_typePA_centralizer_le`. -/
theorem fullTypeP1Dade_H_eq_bot_of_isTISubset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T) :
    ∀ a,
      ((OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
        hG hyp.base.T_maximal dataT hP1).some.dade.H a) = ⊥ :=
  fullTypeP1Dade_H_eq_bot_of_typePA_centralizer_le hG hyp dataT hP1 fun _ hx =>
    hTI.centralizer_le (Set.mem_union_left _ hx)

open scoped Classical in
/-- **Peterfalvi (13.2.e), exact T-side Dade=induction bridge.**

Once the full type-`P₁` `A₀(T)` Dade datum has trivial point stabilizers—the
Lean form of Coq's `normedTI 'A0(T) G T` conclusion—the (2.5) uniqueness theorem
identifies its Dade map with `Ind_T^G`.  Composing with
`tSideDadeMap_eq_full_typeP1DadeMap_of_support` gives the (14.9) map
`τ_T φ = Ind_T^G φ` for every `A₁(T)`-supported `φ`.

The only non-formal input is `hH`; no normed-TI content is hidden in this theorem. -/
theorem tSideDadeMap_eq_induce_of_full_typeP1_H_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hH : ∀ a,
      ((OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
        hG hyp.base.T_maximal dataT hP1).some.dade.H a) = ⊥)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    tSideDadeMap hyp hG φ = ClassFunction.induce hyp.base.T φ := by
  classical
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hyp.base.T_maximal dataT hP1).some
  have hPA : OddOrder.GroupTheory.typePA hyp.base.T dataT =
      OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    OddOrder.Peterfalvi.S10.typePA_eq_sigmaSharp_of_isTypeP1
      hG hyp.base.T_maximal dataT hP1
  have hA1A0 : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T ⊆
      OddOrder.GroupTheory.typePA0 hyp.base.T dataT := by
    rw [← hPA]
    exact Set.subset_union_left
  have hfullSupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T :=
    hφsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA1A0)
  rw [tSideDadeMap_eq_full_typeP1DadeMap_of_support hG hyp dataT hP1 hφsupp,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support full.dade
      (full.dade.fullDadeIsometryData) hfullSupp]
  have hind := OddOrder.Peterfalvi.S14.isDadeMap_induce_of_forall_H_eq_bot full.dade
    (by simpa only [full] using hH)
  have heq := OddOrder.Peterfalvi.S04.IsDadeMap.unique
    (full.dade.isDadeMap_dadeMap (k := ℂ)) hind
  exact congrFun heq ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hfullSupp⟩

open scoped Classical in
/-- **Peterfalvi (13.2.e), T-side Dade=induction from full `A₀(T)` normed-TI.**

This is the form consumed by (14.9): once the genuine `A₀(T)` TI theorem is available,
the reconciled T-side Dade map is induction on every `A₁(T)`-supported class function. -/
theorem tSideDadeMap_eq_induce_of_isTISubset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    tSideDadeMap hyp hG φ = ClassFunction.induce hyp.base.T φ :=
  tSideDadeMap_eq_induce_of_full_typeP1_H_eq_bot hG hyp dataT hP1
    (fullTypeP1Dade_H_eq_bot_of_isTISubset hG hyp dataT hP1 hTI) hφsupp

/-- Conjugate closures are disjoint when a prime divides every order on the left
and no order on the right.

This is the abstract order-separation core used in Peterfalvi (14.9). -/
theorem disjoint_conjugatesIntoSet_of_prime_order_separator
    {M N : Subgroup G} {A : Set ↥M} {B : Set ↥N} {p : ℕ}
    (hA : ∀ y ∈ A, p ∣ orderOf (y : G))
    (hB : ∀ z ∈ B, ¬ p ∣ orderOf (z : G)) :
    Disjoint (ClassFunction.conjugatesIntoSet M A)
      (ClassFunction.conjugatesIntoSet N B) := by
  rw [Set.disjoint_left]
  rintro g ⟨a, ha, hya⟩ ⟨b, hb, hzb⟩
  have horda : orderOf (a⁻¹ * g * a) = orderOf g := by
    simpa [MulAut.conj_apply] using
      (orderOf_injective (MulAut.conj a⁻¹).toMonoidHom
        (MulAut.conj a⁻¹).injective g)
  have hordb : orderOf (b⁻¹ * g * b) = orderOf g := by
    simpa [MulAut.conj_apply] using
      (orderOf_injective (MulAut.conj b⁻¹).toMonoidHom
        (MulAut.conj b⁻¹).injective g)
  have hp : p ∣ orderOf g := by
    rw [← horda]
    exact hA ⟨a⁻¹ * g * a, ha⟩ hya
  exact hB ⟨b⁻¹ * g * b, hb⟩ hzb (by rwa [hordb])

/-- **Peterfalvi (14.9), the S/T order separator.**

For a type-`P` maximal `T`, `[T:T']=p` and `|T'|` are coprime.  Consequently every
element conjugate into `(T')#` has order prime to `p`, so its conjugate closure is
disjoint from the closure of any S-side set whose elements all have order divisible by `p`.

This is the group-theoretic core of Coq's `QV'betaS` support separation.  The remaining
character input is precisely the (13.18.a) assertion that every point in the support of
`β_S` has order divisible by `p`. -/
theorem disjoint_conjugatesIntoSet_S_Tderived_of_p_dvd [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    {A : Set ↥hyp.base.S}
    (hpA : ∀ y ∈ A, hyp.base.p ∣ orderOf (y : G)) :
    Disjoint (ClassFunction.conjugatesIntoSet hyp.base.S A)
      (ClassFunction.conjugatesIntoSet hyp.base.T
        {z : ↥hyp.base.T |
          (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup
            (OddOrder.GroupTheory.derivedInG hyp.base.T)}) := by
  apply disjoint_conjugatesIntoSet_of_prime_order_separator hpA
  intro z hz
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI
      hG hyp.base.T_maximal hyp.base.T_nonI
  have hcop : Nat.Coprime
      (Nat.card ↥(OddOrder.GroupTheory.derivedInG hyp.base.T)) hyp.base.p := by
    have h := OddOrder.Peterfalvi.S15.coprime_card_derivedInG_index_of_isTypeP
      hG hyp.base.T_maximal hP
    rwa [T_derived_index_eq_p hyp] at h
  have hord : orderOf (z : G) ∣
      Nat.card ↥(OddOrder.GroupTheory.derivedInG hyp.base.T) := by
    have hz' : (z : G) ∈ OddOrder.GroupTheory.derivedInG hyp.base.T := hz.1
    have h1 := orderOf_dvd_natCard
      (⟨(z : G), hz'⟩ : ↥(OddOrder.GroupTheory.derivedInG hyp.base.T))
    rwa [← Subgroup.orderOf_coe] at h1
  exact hyp.base.p_prime.coprime_iff_not_dvd.mp
    ((hcop.coprime_dvd_left hord).symm)

open scoped Classical in
/-- **Peterfalvi (13.18.a), every point of `P# ∪ V_S` has p-divisible order.**

On `P#` this is the p-group order criterion using `|P|=p^q`.  A regular
`V_S = (W ∖ (W₁ ∪ W₂))^S` point has a σ-prime divisor; since
`S_σ=P` and `|P|=p^q`, that prime is exactly `p`. -/
theorem p_dvd_orderOf_of_mem_sharpP_union_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    {y : G}
    (hy : y ∈ OddOrder.GroupTheory.sharpSubgroup hyp.base.P ∪
      OddOrder.GroupTheory.conjClassSetIn hyp.base.S
        (OddOrder.GroupTheory.typePV hyp.base.S hyp.base.Sdata)) :
    hyp.base.p ∣ orderOf y := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rcases hy with hyP | hyV
  · have hPgroup : IsPGroup hyp.base.p ↥hyp.base.P :=
      IsPGroup.of_card (hyp.base.card_P_eq hG hyp.base.Sdata_W2_eq)
    have hdiv := hPgroup.dvd_orderOf (g := ⟨y, hyP.1⟩) (by
      intro h
      exact hyP.2 (congrArg Subtype.val h))
    rwa [← Subgroup.orderOf_coe] at hdiv
  · obtain ⟨v, hv, m, hmS, hmv⟩ := hyV
    obtain ⟨r, hrord, _hrσ, hrW2⟩ :=
      OddOrder.Peterfalvi.S10.exists_sigma_prime_dvd_orderOf_typePV
        hG hyp.base.S_maximal hyp.base.Sdata hv
    rw [hyp.base.Sdata_W2_eq, ← hyp.base.p_eq_card_W2] at hrW2
    have hrp : r = hyp.base.p :=
      (Nat.prime_dvd_prime_iff_eq (Nat.mem_primeFactors.mp hrord).1
        hyp.base.p_prime).mp hrW2
    have hpv : hyp.base.p ∣ orderOf v :=
      hrp ▸ Nat.dvd_of_mem_primeFactors hrord
    have hord : orderOf y = orderOf v := by
      rw [← hmv]
      simpa [MulAut.conj_apply] using
        (orderOf_injective (MulAut.conj m).toMonoidHom
          (MulAut.conj m).injective v)
    rwa [hord]

/-- **Peterfalvi (13.18.a)/(14.9), exact S/T source-support separation.**

The conjugate closure of the genuine S-side support carrier `P# ∪ V_S` is disjoint
from the conjugate closure of `(T')#`.  This closes the group/order part of the
`QV'betaS` argument; only the character statement
`supp(β_S) ⊆ P# ∪ V_S` remains to feed it. -/
theorem disjoint_conjugatesIntoSet_sharpP_union_typePV_Tderived [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Disjoint
      (ClassFunction.conjugatesIntoSet hyp.base.S
        {y : ↥hyp.base.S |
          (y : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.base.P ∪
            OddOrder.GroupTheory.conjClassSetIn hyp.base.S
              (OddOrder.GroupTheory.typePV hyp.base.S hyp.base.Sdata)})
      (ClassFunction.conjugatesIntoSet hyp.base.T
        {z : ↥hyp.base.T |
          (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup
            (OddOrder.GroupTheory.derivedInG hyp.base.T)}) :=
  disjoint_conjugatesIntoSet_S_Tderived_of_p_dvd hG hyp fun _ hy =>
    p_dvd_orderOf_of_mem_sharpP_union_typePV hG hyp hy

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.9), cross-Dade orthogonality from the exact support inputs.**

This is the final consumer of the two genuine character-theoretic residuals in the
`τ_T`/`τ_S` cross term.  Full `A₀(T)` normed-TI identifies the T-side Dade map with
induction, while `supp(β_S) ⊆ P# ∪ V_S` places the S-side Dade map in its already-proved
`A₀(S)` induction range.  The exact order separator above then makes the induced
characters orthogonal.

No support or TI content is hidden here: `hTI` and `hbeta` are the two exact inputs of
this reusable boundary theorem.  The Type-`P₁` TI producer is now proved above; the
specialized theorem below discharges `hTI` and retains only the (13.18.a) β support. -/
theorem tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_exact_supports [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T)
    (hbeta : (OddOrder.Peterfalvi.S15.betaGrid hyp.base
      ⟨1, by have := hyp.base.three_le_p; omega⟩).support ⊆
        {y : ↥hyp.base.S |
          (y : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.base.P ∪
            OddOrder.GroupTheory.conjClassSetIn hyp.base.S
              (OddOrder.GroupTheory.typePV hyp.base.S hyp.base.Sdata)})
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ)
      (OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base) = 0 := by
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hsig : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T =
      OddOrder.GroupTheory.sharpSubgroup
        (OddOrder.GroupTheory.derivedInG hyp.base.T) := by
    rw [← OddOrder.Peterfalvi.S10.typePA_eq_sigmaSharp_of_isTypeP1
      hG hyp.base.T_maximal dataT hP1,
      OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG]
  have hφderiv : φ.support ⊆
      {z : ↥hyp.base.T |
        (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup
          (OddOrder.GroupTheory.derivedInG hyp.base.T)} := by
    intro z hz
    have hz' := hφsupp hz
    change (z : G) ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T at hz'
    rwa [hsig] at hz'
  have hbetaA0 : (OddOrder.Peterfalvi.S15.betaGrid hyp.base
      ⟨1, by have := hyp.base.three_le_p; omega⟩).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S10.typePACore0 hyp.base.S hyp.base.Sdata)
        hyp.base.S := by
    intro y hy
    exact OddOrder.Peterfalvi.S15.sharpP_union_V_subset_A0 hG hyp.base (hbeta hy)
  have hTmap : tSideDadeMap hyp hG φ = ClassFunction.induce hyp.base.T φ :=
    tSideDadeMap_eq_induce_of_isTISubset hG hyp dataT hP1 hTI hφsupp
  have hSmap : OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base =
      ClassFunction.induce hyp.base.S
        (OddOrder.Peterfalvi.S15.betaGrid hyp.base
          ⟨1, by have := hyp.base.three_le_p; omega⟩) := by
    rw [OddOrder.Peterfalvi.S15.tauSbetaGrid]
    exact hyp.base.sInstance_dade0_eq_induce hG hnoV hbetaA0
  rw [hTmap, hSmap]
  exact OddOrder.Peterfalvi.S15.inner_induce_induce_eq_zero_of_disjoint
    hφderiv hbeta
      (disjoint_conjugatesIntoSet_sharpP_union_typePV_Tderived hG hyp).symm

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.9), cross-Dade orthogonality from the exact β support.**

The Type-`P₁` full-`A₀(T)` TI theorem is now proved internally, so the only remaining
character-theoretic input for the S/T Dade cross term is Peterfalvi (13.18.a)'s exact
`β_S` support statement. -/
theorem tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_beta_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    (hbeta : (OddOrder.Peterfalvi.S15.betaGrid hyp.base
      ⟨1, by have := hyp.base.three_le_p; omega⟩).support ⊆
        {y : ↥hyp.base.S |
          (y : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.base.P ∪
            OddOrder.GroupTheory.conjClassSetIn hyp.base.S
              (OddOrder.GroupTheory.typePV hyp.base.S hyp.base.Sdata)})
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ)
      (OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base) = 0 :=
  tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_exact_supports hG hnoV hyp dataT hP1
    (typePA0_isTISubset_of_isTypeP1 hG hnoV hyp.base.T_maximal dataT hP1)
    hbeta hφsupp

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.9), unconditional cross-Dade orthogonality.**

The S-side exact support is supplied by the fully proved `(13.18.a)` theorem
`S15.betaGrid_support_of_c_eq_one`, with (13.12) supplied by the upstream Core endpoint
`Hypothesis.c_eq_one_of_lambda_dichotomy`; all group structure, normed-TI, Dade=Ind, and
support-separation steps are therefore discharged. -/
theorem tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G,
      M ∈ OddOrder.GroupTheory.maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hc1 : hyp.base.c = 1)
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ)
      (OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base) = 0 :=
  tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_beta_support hG hnoV hyp dataT hP1
    (OddOrder.Peterfalvi.S15.betaGrid_support_of_c_eq_one hG hyp.base
      hc1
      ⟨1, by have := hyp.base.three_le_p; omega⟩ (by norm_num))
    hφsupp

/-- The inner product of two virtual characters is symmetric: its value is
an integer, hence fixed by complex conjugation. -/
theorem inner_eq_swap_of_mem_ZIrr [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {φ ψ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (hψ : ψ ∈ ZIrr G) :
    ClassFunction.inner φ ψ = ClassFunction.inner ψ φ := by
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hφ hψ
  calc
    ClassFunction.inner φ ψ = (m : ℂ) := hm
    _ = star (m : ℂ) := by rw [star_intCast]
    _ = star (ClassFunction.inner φ ψ) := by rw [hm]
    _ = ClassFunction.inner ψ φ :=
      (OddOrder.RepresentationTheory.inner_conj_symm φ ψ).symm

/-- **Peterfalvi (14.9), S/T gap assembly.**

Expand `Γ = σβ - 1 + η` and `Δ = τβ - 1 + a`.  Cross-Dade
orthogonality and the T-side β–η row give `⟨τβ, Γ⟩ = -1`;
principal orthogonality of `Γ` kills the trivial term.  Integrality of
the remaining virtual-character pairings removes the Hermitian
conjugations and yields `⟨Γ,a⟩ = 1 + ⟨Δ,Γ⟩`. -/
theorem gap_cross_inner_identity [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {Γ Δ τβ σβ η a one : ClassFunction G ℂ}
    (hΓZ : Γ ∈ ZIrr G) (haZ : a ∈ ZIrr G) (honeZ : one ∈ ZIrr G)
    (hΓ : Γ = σβ - one + η)
    (hΔ : Δ = τβ - one + a)
    (hτβ_one : ClassFunction.inner τβ one = 1)
    (hτβ_σβ : ClassFunction.inner τβ σβ = 0)
    (hτβ_eta : ClassFunction.inner τβ η = 0)
    (hΓ_one : ClassFunction.inner Γ one = 0) :
    ClassFunction.inner Γ a = 1 + ClassFunction.inner Δ Γ := by
  have hτβΓ : ClassFunction.inner τβ Γ = -1 := by
    rw [hΓ, ClassFunction.inner_add_right, ClassFunction.inner_sub_right,
      hτβ_σβ, hτβ_one, hτβ_eta]
    norm_num
  have honeΓ : ClassFunction.inner one Γ = 0 := by
    rw [inner_eq_swap_of_mem_ZIrr honeZ hΓZ, hΓ_one]
  have haΓ : ClassFunction.inner a Γ = ClassFunction.inner Γ a :=
    inner_eq_swap_of_mem_ZIrr haZ hΓZ
  rw [hΔ, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    hτβΓ, honeΓ, haΓ]
  ring

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjection.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- A test character orthogonal to the eta-grid but not to `b` witnesses that the perpendicular
eta-grid residual of `b` is nonzero. -/
theorem etaGrid_projection_residual_ne_zero_of_inner [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    (b psi : ClassFunction G ℂ) (m : Fin base.q → Fin base.p → ℤ)
    (hbpsi : ClassFunction.inner b psi ≠ 0)
    (hetapsi : ∀ i j, ClassFunction.inner (base.eta i j) psi = 0) :
    b - etaGridProjection base m ≠ 0 := by
  intro hzero
  have hbproj : b = etaGridProjection base m := sub_eq_zero.mp hzero
  apply hbpsi
  rw [hbproj, etaGridProjection, inner_sum_left]
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_sum_left]
  apply Finset.sum_eq_zero
  intro j _
  rw [ClassFunction.inner_smul_left, hetapsi i j, mul_zero]

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjectionRigidity.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), regular-set vanishing of the T-side bridge.**
If `φ` is supported on `A(T) = T_σ#`, the restricted T-side Dade map agrees with the
full type-`P₁` map.  On the regular type-`P` set `V(T)`, the full map evaluates to `φ`,
which is zero because `V(T)` is disjoint from `T'`.  Class invariance extends the
vanishing to the conjugacy saturation used by the shared eta-grid. -/
theorem tSideDadeMap_vanish_on_etaRegular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ∀ x ∈ conjClassSet
      ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      tSideDadeMap hyp hG φ x = 0 := by
  classical
  let dataT := (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose
  have hdata := (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose_spec
  have hW1 : dataT.W1 = hyp.base.W2 := hdata.2.1
  have hW2 : dataT.W2 = hyp.base.W1 := hdata.2.2
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := by
    have hcls := OddOrder.BG.Ch4.S16.proposition_type_classification
      hG hyp.base.T_maximal
    exact (hcls.2.2.1.mp (Or.inl hIII)).1
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hyp.base.T_maximal dataT hP1).some
  have hPA : OddOrder.GroupTheory.typePA hyp.base.T dataT =
      OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    OddOrder.Peterfalvi.S10.typePA_eq_sigmaSharp_of_isTypeP1
      hG hyp.base.T_maximal dataT hP1
  have hA1A0 : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T ⊆
      OddOrder.GroupTheory.typePA0 hyp.base.T dataT := by
    rw [← hPA]
    exact Set.subset_union_left
  have hfullSupp : φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T :=
    hφsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA1A0)
  have hmaps : tSideDadeMap hyp hG φ =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
        (full.dade.fullDadeIsometryData) φ := by
    simpa only [full] using
      tSideDadeMap_eq_full_typeP1DadeMap_of_support hG hyp dataT hP1 hφsupp
  have hW : dataT.W = hyp.base.W := by
    rw [dataT.W_eq, hW1, hW2, hyp.base.W_eq_join, sup_comm]
  have hV : OddOrder.GroupTheory.typePV hyp.base.T dataT =
      (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) := by
    simp only [OddOrder.GroupTheory.typePV, hW, hW1, hW2, Set.union_comm]
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := hx
  rw [hmaps]
  rw [← (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
    (full.dade.fullDadeIsometryData) φ).of_isConj
      (isConj_iff.mpr ⟨g, hg⟩)]
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.base.T dataT := hV.symm ▸ hw
  have hwA0 : w ∈ OddOrder.GroupTheory.typePA0 hyp.base.T dataT :=
    Set.mem_union_right _ (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support full.dade
    (full.dade.fullDadeIsometryData) hfullSupp]
  let a : {a : G // a ∈ OddOrder.GroupTheory.typePA0 hyp.base.T dataT} := ⟨w, hwA0⟩
  have hwh : w ∈ full.dade.hCoset a := ⟨1, full.dade.H a |>.one_mem, by simp [a]⟩
  rw [full.dade.isDadeMap_dadeMap.map_eq_of_mem_hCoset _ a hwh]
  by_contra hne
  have hwSupp : (⟨w, full.dade.mem_L hwA0⟩ : ↥hyp.base.T) ∈ φ.support :=
    ClassFunction.mem_support.mpr hne
  have hwSigma : w ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T := hφsupp hwSupp
  have hwDeriv : w ∈ derivedInG hyp.base.T := by
    rw [OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma
      hG hyp.base.T_maximal hP1]
    exact hwSigma.1
  exact (OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived dataT hwV) hwDeriv

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The T-side bridge coefficients satisfy Peterfalvi's (3.7) four-corner relation. -/
theorem tSideDadeMap_etaGrid_relation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (i : Fin hyp.base.q) (j : Fin hyp.base.p) :
    ClassFunction.inner (tSideDadeMap hyp hG φ) (hyp.base.eta i j) +
        ClassFunction.inner (tSideDadeMap hyp hG φ)
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) =
      ClassFunction.inner (tSideDadeMap hyp hG φ)
          (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩) +
        ClassFunction.inner (tSideDadeMap hyp hG φ)
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  exact inner_eta_grid_relation hyp.base
    (tSideDadeMap_vanish_on_etaRegular hG hyp hIII hφsupp) i j

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), the principal T-side eta coefficient.**
Dade reciprocity preserves the trivial multiplicity, and `η₀₀ = 1_G`. -/
theorem tSideDadeMap_inner_eta_principal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ)
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) =
      ClassFunction.inner φ (trivialClassFunction ↥hyp.base.T) := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  rw [eta_principal_eq_trivial hyp.base,
    tSideDadeMap_inner_trivial hyp hG hφsupp]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), integral T-side projection with principal and four-corner data.** -/
theorem exists_tSide_etaGrid_intProjection_with_relation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hφone : ClassFunction.inner φ
      (trivialClassFunction ↥hyp.base.T) = 1)
    (hτZ : tSideDadeMap hyp hG φ ∈ ZIrr G)
    (hτnorm : ClassFunction.inner (tSideDadeMap hyp hG φ) (tSideDadeMap hyp hG φ) =
      (((hyp.base.p : ℤ) + 1) : ℂ)) :
    ∃ m : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, ClassFunction.inner (tSideDadeMap hyp hG φ) (hyp.base.eta i j) =
        (m i j : ℂ)) ∧
      ClassFunction.inner (tSideDadeMap hyp hG φ) (tSideDadeMap hyp hG φ) =
        ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ) +
          ClassFunction.inner
            (tSideDadeMap hyp hG φ - etaGridProjection hyp.base m)
            (tSideDadeMap hyp hG φ - etaGridProjection hyp.base m) ∧
      (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) ≤
        (hyp.base.p : ℤ) + 1 ∧
      m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 ∧
      (∀ i j, m i j + m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ =
        m i ⟨0, hyp.base.p_prime.pos⟩ + m ⟨0, hyp.base.q_prime.pos⟩ j) := by
  obtain ⟨m, hcoeff, hpyth, hbound⟩ :=
    exists_etaGrid_intProjection_of_inner_self_eq hyp.base hτZ hτnorm
  have hprincipalC := tSideDadeMap_inner_eta_principal hG hyp hφsupp
  rw [hφone,
    hcoeff ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩] at hprincipalC
  have hprincipal :
      m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 := by
    exact_mod_cast hprincipalC
  have hrelation : ∀ i j,
      m i j + m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ =
        m i ⟨0, hyp.base.p_prime.pos⟩ + m ⟨0, hyp.base.q_prime.pos⟩ j := by
    intro i j
    have h := tSideDadeMap_etaGrid_relation hG hyp hIII hφsupp i j
    rw [hcoeff i j,
      hcoeff ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩,
      hcoeff i ⟨0, hyp.base.p_prime.pos⟩,
      hcoeff ⟨0, hyp.base.q_prime.pos⟩ j] at h
    exact_mod_cast h
  exact ⟨m, hcoeff, hpyth, hbound, hprincipal, hrelation⟩

/-- **Peterfalvi (11.9)(a), the axis-coefficient arithmetic.**
Suppose the nonprincipal row and column coefficients are constant, the four-corner
coefficient is their sum minus the principal coefficient `1`, and the projection norm
is at most `p`, where `3 ≤ q < p`.  Then exactly the two axis projections remain:
the zero-column coefficients `(1,0,0)` or the zero-row coefficients `(0,1,0)`.

This is the integer inequality core of Coq `FTtype34_structure`.  The character-theoretic
(11.8) non-orthogonality subsequently excludes the zero-row alternative. -/
theorem axis_coefficients_eq_column_or_row
    {q p a10 a01 a11 : ℤ}
    (hq : 3 ≤ q) (hp : 3 ≤ p) (hqp : q < p)
    (hrelation : a11 = a10 + a01 - 1)
    (hbound :
      1 + (q - 1) * a10 ^ 2 + (p - 1) * a01 ^ 2 +
        (q - 1) * (p - 1) * a11 ^ 2 ≤ p) :
    (a10 = 1 ∧ a01 = 0 ∧ a11 = 0) ∨
      (a10 = 0 ∧ a01 = 1 ∧ a11 = 0) := by
  have hq0 : 0 ≤ q - 1 := by omega
  have hp0 : 0 ≤ p - 1 := by omega
  have h10nonneg : 0 ≤ (q - 1) * a10 ^ 2 :=
    mul_nonneg hq0 (sq_nonneg a10)
  have h01nonneg : 0 ≤ (p - 1) * a01 ^ 2 :=
    mul_nonneg hp0 (sq_nonneg a01)
  have hprod0 : 0 ≤ (q - 1) * (p - 1) := mul_nonneg hq0 hp0
  have h11nonneg : 0 ≤ (q - 1) * (p - 1) * a11 ^ 2 :=
    mul_nonneg hprod0 (sq_nonneg a11)
  have ha11 : a11 = 0 := by
    by_contra hne
    have hsquare : 1 ≤ a11 ^ 2 := by
      nlinarith [Int.one_le_abs hne, sq_abs a11]
    have hlower := mul_le_mul_of_nonneg_left hsquare hprod0
    have hgap : 0 ≤ (q - 3) * (p - 1) :=
      mul_nonneg (by omega) hp0
    nlinarith
  have hsum : a10 + a01 = 1 := by omega
  by_cases h01 : a01 = 0
  · left
    refine ⟨by omega, h01, ha11⟩
  · have h01square : 1 ≤ a01 ^ 2 := by
      nlinarith [Int.one_le_abs h01, sq_abs a01]
    have h01lower := mul_le_mul_of_nonneg_left h01square hp0
    have ha10 : a10 = 0 := by
      by_contra h10
      have h10square : 1 ≤ a10 ^ 2 := by
        nlinarith [Int.one_le_abs h10, sq_abs a10]
      have h10lower := mul_le_mul_of_nonneg_left h10square hq0
      nlinarith
    right
    refine ⟨ha10, by omega, ha11⟩

/-- **Peterfalvi (11.9)(a), full-grid norm compression.**  If the eta-projection coefficients
are constant on each nonprincipal axis and satisfy the four-corner relation, their full squared
norm is exactly the three-coefficient expression used by `axis_coefficients_eq_column_or_row`.

This is the finite-grid bookkeeping between the already-proven sharp projection bound
`sum m_ij^2 <= p` and the arithmetic dichotomy.  It partitions each axis into its principal point
and complement; the four-corner relation makes every interior coefficient equal to `m_11`. -/
theorem etaGrid_axis_sum_eq_sum_sq
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin base.q → Fin base.p → ℤ)
    (hprincipal :
      m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ = 1)
    (hrow : ∀ i, i ≠ ⟨0, base.q_prime.pos⟩ →
      m i ⟨0, base.p_prime.pos⟩ =
        m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩)
    (hcol : ∀ j, j ≠ ⟨0, base.p_prime.pos⟩ →
      m ⟨0, base.q_prime.pos⟩ j =
        m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩)
    (hrelation : ∀ i j,
      m i j + m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ =
        m i ⟨0, base.p_prime.pos⟩ + m ⟨0, base.q_prime.pos⟩ j) :
    1 + ((base.q : ℤ) - 1) *
          m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩ ^ 2 +
        ((base.p : ℤ) - 1) *
          m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 +
        ((base.q : ℤ) - 1) * ((base.p : ℤ) - 1) *
          m ⟨1, base.q_prime.one_lt⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 =
      ∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 := by
  classical
  let i0 : Fin base.q := ⟨0, base.q_prime.pos⟩
  let j0 : Fin base.p := ⟨0, base.p_prime.pos⟩
  let i1 : Fin base.q := ⟨1, base.q_prime.one_lt⟩
  let j1 : Fin base.p := ⟨1, base.p_prime.one_lt⟩
  have hinter : ∀ i, i ≠ i0 → ∀ j, j ≠ j0 → m i j = m i1 j1 := by
    intro i hi j hj
    have hij := hrelation i j
    have h11 := hrelation i1 j1
    have h00 : m i0 j0 = 1 := by simpa [i0, j0] using hprincipal
    have hi0 : m i j0 = m i1 j0 := by
      simpa [i0, i1, j0] using hrow i (by simpa [i0] using hi)
    have h0j : m i0 j = m i0 j1 := by
      simpa [i0, j0, j1] using hcol j (by simpa [j0] using hj)
    change m i j + m i0 j0 = m i j0 + m i0 j at hij
    change m i1 j1 + m i0 j0 = m i1 j0 + m i0 j1 at h11
    rw [h00, hi0, h0j] at hij
    rw [h00] at h11
    omega
  have sum_eq_base_add_const : ∀ {n : ℕ} (x0 : Fin n) (f : Fin n → ℤ) (a b : ℤ),
      f x0 = a → (∀ x, x ≠ x0 → f x = b) →
        (∑ x : Fin n, f x) = a + ((n : ℤ) - 1) * b := by
    intro n x0 f a b hx0 hrest
    have hn : 1 ≤ n := by
      have hx0lt := x0.isLt
      omega
    calc
      (∑ x : Fin n, f x) =
          (∑ x ∈ Finset.univ.erase x0, f x) + f x0 :=
        (Finset.sum_erase_add Finset.univ f (Finset.mem_univ x0)).symm
      _ = (∑ x ∈ Finset.univ.erase x0, b) + a := by
        rw [hx0]
        congr 1
        exact Finset.sum_congr rfl fun x hx => hrest x (Finset.ne_of_mem_erase hx)
      _ = a + ((n : ℤ) - 1) * b := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ x0),
          Finset.card_univ, Fintype.card_fin]
        push_cast [Nat.cast_sub hn]
        ring
  have hrow0 : (∑ j : Fin base.p, (m i0 j) ^ 2) =
      1 + ((base.p : ℤ) - 1) * (m i0 j1) ^ 2 := by
    apply sum_eq_base_add_const j0 _ 1 ((m i0 j1) ^ 2)
    · simp only [i0, j0, hprincipal, one_pow]
    · intro j hj
      rw [hcol j (by simpa [j0] using hj)]
  have hrowOther : ∀ i, i ≠ i0 →
      (∑ j : Fin base.p, (m i j) ^ 2) =
        (m i1 j0) ^ 2 + ((base.p : ℤ) - 1) * (m i1 j1) ^ 2 := by
    intro i hi
    apply sum_eq_base_add_const j0 _ ((m i1 j0) ^ 2) ((m i1 j1) ^ 2)
    · rw [hrow i (by simpa [i0] using hi)]
    · intro j hj
      rw [hinter i hi j hj]
  have hgrid := sum_eq_base_add_const i0
    (fun i => ∑ j : Fin base.p, (m i j) ^ 2)
    (1 + ((base.p : ℤ) - 1) * (m i0 j1) ^ 2)
    ((m i1 j0) ^ 2 + ((base.p : ℤ) - 1) * (m i1 j1) ^ 2)
    hrow0 hrowOther
  change
    1 + ((base.q : ℤ) - 1) * (m i1 j0) ^ 2 +
          ((base.p : ℤ) - 1) * (m i0 j1) ^ 2 +
          ((base.q : ℤ) - 1) * ((base.p : ℤ) - 1) * (m i1 j1) ^ 2 =
        ∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2
  calc
    _ = 1 + ((base.p : ℤ) - 1) * (m i0 j1) ^ 2 +
          ((base.q : ℤ) - 1) *
            ((m i1 j0) ^ 2 + ((base.p : ℤ) - 1) * (m i1 j1) ^ 2) := by ring
    _ = _ := hgrid.symm

/-- The sharp full-grid coefficient bound supplies the axis bound expected by the arithmetic
dichotomy. -/
theorem etaGrid_axis_bound_of_sum_sq_le
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin base.q → Fin base.p → ℤ)
    (hprincipal :
      m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ = 1)
    (hrow : ∀ i, i ≠ ⟨0, base.q_prime.pos⟩ →
      m i ⟨0, base.p_prime.pos⟩ =
        m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩)
    (hcol : ∀ j, j ≠ ⟨0, base.p_prime.pos⟩ →
      m ⟨0, base.q_prime.pos⟩ j =
        m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩)
    (hrelation : ∀ i j,
      m i j + m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ =
        m i ⟨0, base.p_prime.pos⟩ + m ⟨0, base.q_prime.pos⟩ j)
    (hfull : (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤ base.p) :
    1 + ((base.q : ℤ) - 1) *
          m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩ ^ 2 +
        ((base.p : ℤ) - 1) *
          m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 +
        ((base.q : ℤ) - 1) * ((base.p : ℤ) - 1) *
          m ⟨1, base.q_prime.one_lt⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 ≤ base.p := by
  rw [etaGrid_axis_sum_eq_sum_sq base m hprincipal hrow hcol hrelation]
  exact hfull

/-- Lift the three-coefficient arithmetic classification to the full eta-grid.
The axis-constancy hypotheses are the exact output expected from Peterfalvi (3.9)(b)
and Dade--Galois commutation. -/
theorem etaGrid_coefficients_eq_column_or_row
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (hqp : base.q < base.p)
    (m : Fin base.q → Fin base.p → ℤ)
    (hprincipal :
      m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ = 1)
    (hrow : ∀ i, i ≠ ⟨0, base.q_prime.pos⟩ →
      m i ⟨0, base.p_prime.pos⟩ =
        m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩)
    (hcol : ∀ j, j ≠ ⟨0, base.p_prime.pos⟩ →
      m ⟨0, base.q_prime.pos⟩ j =
        m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩)
    (hrelation : ∀ i j,
      m i j + m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ =
        m i ⟨0, base.p_prime.pos⟩ + m ⟨0, base.q_prime.pos⟩ j)
    (haxisBound :
      1 + ((base.q : ℤ) - 1) *
            m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩ ^ 2 +
          ((base.p : ℤ) - 1) *
            m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 +
          ((base.q : ℤ) - 1) * ((base.p : ℤ) - 1) *
            m ⟨1, base.q_prime.one_lt⟩ ⟨1, base.p_prime.one_lt⟩ ^ 2 ≤
        (base.p : ℤ)) :
    (∀ i j, m i j = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0) ∨
      (∀ i j, m i j = if i = ⟨0, base.q_prime.pos⟩ then 1 else 0) := by
  let i0 : Fin base.q := ⟨0, base.q_prime.pos⟩
  let j0 : Fin base.p := ⟨0, base.p_prime.pos⟩
  let i1 : Fin base.q := ⟨1, base.q_prime.one_lt⟩
  let j1 : Fin base.p := ⟨1, base.p_prime.one_lt⟩
  have hqZ : (3 : ℤ) ≤ base.q := by exact_mod_cast base.three_le_q
  have hpZ : (3 : ℤ) ≤ base.p := by exact_mod_cast base.three_le_p
  have hqpZ : (base.q : ℤ) < base.p := by exact_mod_cast hqp
  have haxis := axis_coefficients_eq_column_or_row hqZ hpZ hqpZ
    (show m i1 j1 = m i1 j0 + m i0 j1 - 1 by
      have h := hrelation i1 j1
      have hp0 : m i0 j0 = 1 := by simpa [i0, j0] using hprincipal
      change m i1 j1 + m i0 j0 = m i1 j0 + m i0 j1 at h
      rw [hp0] at h
      omega)
    (by simpa [i0, j0, i1, j1] using haxisBound)
  rcases haxis with hcolumn | hrowAxis
  · left
    intro i j
    by_cases hj : j = j0
    · rw [if_pos (by simpa [j0] using hj)]
      by_cases hi : i = i0
      · rw [hi, hj]
        simpa [i0, j0] using hprincipal
      · rw [hj]
        simpa [i0, j0, i1] using
          (hrow i (by simpa [i0] using hi)).trans hcolumn.1
    · rw [if_neg (by simpa [j0] using hj)]
      by_cases hi : i = i0
      · rw [hi]
        simpa [i0, j0, j1] using (hcol j (by simpa [j0] using hj)).trans hcolumn.2.1
      · have h := hrelation i j
        rw [hprincipal, hrow i (by simpa [i0] using hi),
          hcol j (by simpa [j0] using hj), hcolumn.1, hcolumn.2.1] at h
        omega
  · right
    intro i j
    by_cases hi : i = i0
    · rw [if_pos (by simpa [i0] using hi)]
      by_cases hj : j = j0
      · rw [hi, hj]
        simpa [i0, j0] using hprincipal
      · rw [hi]
        simpa [i0, j0, j1] using
          (hcol j (by simpa [j0] using hj)).trans hrowAxis.2.1
    · rw [if_neg (by simpa [i0] using hi)]
      by_cases hj : j = j0
      · rw [hj]
        simpa [i0, j0, i1] using (hrow i (by simpa [i0] using hi)).trans hrowAxis.1
      · have h := hrelation i j
        rw [hprincipal, hrow i (by simpa [i0] using hi),
          hcol j (by simpa [j0] using hj), hrowAxis.1, hrowAxis.2.1] at h
        omega

/-- **Peterfalvi (11.9)(a), eta-grid projection rigidity.**  The sharp bound on the full
integer projection grid, together with the Galois-axis constancy and the four-corner relation,
forces the grid to be a coordinate row or column.  Unlike
`etaGrid_coefficients_eq_column_or_row`, this is stated with the full squared norm produced by
the projection argument. -/
theorem etaGrid_coefficients_eq_column_or_row_of_sum_sq_le
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (hqp : base.q < base.p)
    (m : Fin base.q → Fin base.p → ℤ)
    (hprincipal :
      m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ = 1)
    (hrow : ∀ i, i ≠ ⟨0, base.q_prime.pos⟩ →
      m i ⟨0, base.p_prime.pos⟩ =
        m ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩)
    (hcol : ∀ j, j ≠ ⟨0, base.p_prime.pos⟩ →
      m ⟨0, base.q_prime.pos⟩ j =
        m ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩)
    (hrelation : ∀ i j,
      m i j + m ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ =
        m i ⟨0, base.p_prime.pos⟩ + m ⟨0, base.q_prime.pos⟩ j)
    (hfull : (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤ base.p) :
    (∀ i j, m i j = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0) ∨
      (∀ i j, m i j = if i = ⟨0, base.q_prime.pos⟩ then 1 else 0) := by
  apply etaGrid_coefficients_eq_column_or_row base hqp m hprincipal hrow hcol hrelation
  exact etaGrid_axis_bound_of_sum_sq_le base m hprincipal hrow hcol hrelation hfull

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The eta-grid projection has precisely its defining coefficient against
each eta character. -/
theorem etaGridProjection_inner_eta [Finite G]
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin base.q → Fin base.p → ℤ) (k : Fin base.q) (l : Fin base.p) :
    ClassFunction.inner (etaGridProjection base m) (base.eta k l) = (m k l : ℂ) := by
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  rw [etaGridProjection, OddOrder.RepresentationTheory.inner_sum_left]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    apply Finset.sum_eq_zero
    intro j _
    rw [ClassFunction.inner_smul_left, eta_orthonormal, if_neg, mul_zero]
    exact fun h => hik h.1)]
  rw [OddOrder.RepresentationTheory.inner_sum_left]
  rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ _) (fun j _ hjl => by
    rw [ClassFunction.inner_smul_left, eta_orthonormal, if_neg, mul_zero]
    exact fun h => hjl h.2)]
  rw [ClassFunction.inner_smul_left, eta_orthonormal, if_pos ⟨rfl, rfl⟩, mul_one]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Subtracting the eta-grid projection kills every eta coefficient. -/
theorem etaGrid_projection_residual_inner_eta_eq_zero [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (b : ClassFunction G ℂ) (m : Fin base.q → Fin base.p → ℤ)
    (hm : ∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ)) :
    ∀ i j,
      ClassFunction.inner (b - etaGridProjection base m) (base.eta i j) = 0 := by
  intro i j
  rw [ClassFunction.inner_sub_left, hm,
    etaGridProjection_inner_eta base m i j, sub_self]

/-- The second projection alternative is literally the zero-row eta sum. -/
theorem etaGridProjection_eq_zeroRow_of_coefficients_eq_row
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin base.q → Fin base.p → ℤ)
    (hrow : ∀ i j,
      m i j = if i = ⟨0, base.q_prime.pos⟩ then 1 else 0) :
    etaGridProjection base m =
      ∑ j : Fin base.p, base.eta ⟨0, base.q_prime.pos⟩ j := by
  classical
  rw [etaGridProjection]
  rw [Finset.sum_eq_single_of_mem (⟨0, base.q_prime.pos⟩ : Fin base.q)
    (Finset.mem_univ _) (fun i _ hi => by
      apply Finset.sum_eq_zero
      intro j _
      rw [hrow, if_neg hi, Int.cast_zero, zero_smul])]
  apply Finset.sum_congr rfl
  intro j _
  rw [hrow, if_pos rfl, Int.cast_one, one_smul]

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjectionResidual.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), the perpendicular T-side residual is nonzero.**
Let `ζ` belong to the coherent T-side family and let `φ` be supported on `A₁(T)`.
If `φ` is not orthogonal to `ζ - ζ̄`, then the Dade image of this difference is a test
virtual character which:

* is not orthogonal to the Dade image of `φ`, by the supported Dade isometry;
* is orthogonal to every eta-grid character, because coherence identifies it with
  `τ₁ζ - τ₁ζ̄` and both coherent images are eta-orthogonal.

Hence no eta-grid projection of the Dade image of `φ` can equal the whole image. -/
theorem tSide_etaGridProjection_residual_ne_zero_of_coherent_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis
      (L := ↥hyp.base.T) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hsupp : ∀ ξ ∈ S, (ξ - ξ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    {ζ φ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S) (hζirr : IsIrreducibleCharacter ζ)
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hφpair : ClassFunction.inner φ (ζ - ζ.conj) ≠ 0)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ) :
    tSideDadeMap hyp hG φ - etaGridProjection hyp.base m ≠ 0 := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  let theta : ClassFunction ↥hyp.base.T ℂ := ζ - ζ.conj
  have hζc : ζ.conj ∈ S := hyp07.conjugate_closed hζ
  have hthetaSupp : theta.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    simpa [theta] using hsupp ζ hζ
  have hthetaSupported : theta ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.base.T) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) := by
    refine ⟨?_, hthetaSupp⟩
    exact Submodule.sub_mem _ (Submodule.subset_span hζ) (Submodule.subset_span hζc)
  have hcorr : tSideDadeMap hyp hG theta =
      coh.extension ζ - coh.extension ζ.conj := by
    rw [← coh.extends_on_supported theta hthetaSupported, map_sub]
  have hpair :
      ClassFunction.inner (tSideDadeMap hyp hG φ) (tSideDadeMap hyp hG theta) ≠ 0 := by
    simp only [tSideDadeMap]
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (tSideDadeSupport_nonempty hG hyp).some.dade hφsupp hthetaSupp]
    simpa [theta] using hφpair
  have hζeta := T_typeIII_coherent_image_inner_eta_eq_zero hG hyp hIII
    hyp07.conjugate_closed hyp07.no_real_characters hsupp coh hζ hζirr
  have hζceta := T_typeIII_coherent_image_inner_eta_eq_zero hG hyp hIII
    hyp07.conjugate_closed hyp07.no_real_characters hsupp coh hζc hζirr.conj
  apply etaGrid_projection_residual_ne_zero_of_inner hyp.base
    (tSideDadeMap hyp hG φ) (tSideDadeMap hyp hG theta) m hpair
  intro i j
  rw [OddOrder.RepresentationTheory.inner_conj_symm, hcorr,
    ClassFunction.inner_sub_left, hζeta i j, hζceta i j, sub_zero, star_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Specialise the coherent-pair residual witness to the bridge source `ν₀ - ζ`.
It is enough that the prime-TI anchor `ν₀` be orthogonal to both `ζ` and `ζ̄`;
the coherent family supplies `ζ ⟂ ζ̄` and irreducibility supplies `‖ζ‖² = 1`,
so `⟨ν₀-ζ, ζ-ζ̄⟩ = -1`. -/
theorem tSide_etaGridProjection_residual_ne_zero_of_anchor_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis
      (L := ↥hyp.base.T) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hsupp : ∀ ξ ∈ S, (ξ - ξ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S) (hζirr : IsIrreducibleCharacter ζ)
    (hbridgeSupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hνζ : ClassFunction.inner ν0 ζ = 0)
    (hνζc : ClassFunction.inner ν0 ζ.conj = 0)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ) :
    tSideDadeMap hyp hG (ν0 - ζ) - etaGridProjection hyp.base m ≠ 0 := by
  apply tSide_etaGridProjection_residual_ne_zero_of_coherent_pair
    hG hyp hIII hyp07 coh hsupp hζ hζirr hbridgeSupp ?_ m
  have hζc : ζ.conj ∈ S := hyp07.conjugate_closed hζ
  have hζne : ζ ≠ ζ.conj := hyp07.ne_conj hζ
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 :=
    hyp07.pairwise_orthogonal hζ hζc hζne
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hνζ, hνζc, hζirr.inner_self_eq_one, hζζc]
  norm_num

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapGalois.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), Galois bridge decomposition** (Coq `aut_phi`).
If the prime-TI anchor `ν₀` is fixed by a coefficient automorphism `σ`, then

`σ(τ_T(ν₀ - ζ)) = τ_T(ν₀ - ζ) + τ_T(ζ - σζ)`.

The only character-theoretic input is the supportedness of `ν₀ - ζ`: it lets
the explicit Dade map commute with `σ`.  The remaining identity is linearity. -/
theorem tSideDadeMap_mapRingEquiv_bridge [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (σc : ℂ ≃+* ℂ)
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    (hν0 : ClassFunction.mapRingEquiv σc ν0 = ν0)
    (hbridgeSupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.mapRingEquiv σc (tSideDadeMap hyp hG (ν0 - ζ)) =
      tSideDadeMap hyp hG (ν0 - ζ) +
        tSideDadeMap hyp hG (ζ - ClassFunction.mapRingEquiv σc ζ) := by
  let side := (tSideDadeSupport_nonempty hG hyp).some
  change ClassFunction.mapRingEquiv σc
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
        (side.dade.fullDadeIsometryData) (ν0 - ζ)) = _
  rw [← OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
    side.dade (side.dade.fullDadeIsometryData) σc hbridgeSupp]
  change tSideDadeMap hyp hG (ClassFunction.mapRingEquiv σc (ν0 - ζ)) = _
  rw [← map_add]
  congr 1
  rw [ClassFunction.mapRingEquiv_sub, hν0]
  abel

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- A supported difference of two coherent-family members has Dade image
orthogonal to every test function orthogonal to the two coherent images. -/
theorem tSideDadeMap_inner_eq_zero_of_coherent_difference [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ζ ζ' : ClassFunction ↥hyp.base.T ℂ} (hζ : ζ ∈ S) (hζ' : ζ' ∈ S)
    (hdiffSupp : (ζ - ζ').support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    {η : ClassFunction G ℂ}
    (horth : ∀ ξ ∈ S, ClassFunction.inner (coh.extension ξ) η = 0) :
    ClassFunction.inner (tSideDadeMap hyp hG (ζ - ζ')) η = 0 := by
  have hdiffSupported : ζ - ζ' ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.base.T) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hζ)
      (Submodule.subset_span hζ'), hdiffSupp⟩
  rw [← coh.extends_on_supported (ζ - ζ') hdiffSupported, map_sub,
    ClassFunction.inner_sub_left, horth ζ hζ, horth ζ' hζ', sub_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), integral coefficient transport** (Coq `a_aut`).
The Galois bridge identity and coherent-difference orthogonality force an
integral eta coefficient to be constant along the chosen Galois transport. -/
theorem tSideDadeMap_inner_galois_eq_intCast [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (σc : ℂ ≃+* ℂ)
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    {η η' : ClassFunction G ℂ} (m : ℤ)
    (hν0 : ClassFunction.mapRingEquiv σc ν0 = ν0)
    (hbridgeZ : ν0 - ζ ∈ ZIrr ↥hyp.base.T)
    (hbridgeSupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hη : ClassFunction.mapRingEquiv σc η = η')
    (hηZ : η ∈ ZIrr G)
    (hm : ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ)) η = (m : ℂ))
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hζ : ζ ∈ S) (hσζ : ClassFunction.mapRingEquiv σc ζ ∈ S)
    (hcorrSupp : (ζ - ClassFunction.mapRingEquiv σc ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (horth : ∀ ξ ∈ S, ClassFunction.inner (coh.extension ξ) η' = 0) :
    ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ)) η' = (m : ℂ) := by
  apply ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add σc m
  · simpa [tSideDadeMap] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (tSideDadeSupport_nonempty hG hyp).some.dade hbridgeSupp hbridgeZ)
  · exact hηZ
  · exact tSideDadeMap_mapRingEquiv_bridge hG hyp σc hν0 hbridgeSupp
  · exact hη
  · exact hm
  · exact tSideDadeMap_inner_eq_zero_of_coherent_difference hG hyp coh
      hζ hσζ hcorrSupp horth

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), Galois constancy on the two eta axes.**
Assume the nonprincipal row and column eta characters are coefficient-Galois conjugate to
`eta_10` and `eta_01`.  Galois closure of the coherent source family, supportedness of all
family differences, and coherent-image orthogonality then turn `a_aut` into equality of the
integer projection coefficients along each axis.  This is the character-theoretic input of
`etaGrid_coefficients_eq_column_or_row`. -/
theorem tSideDadeMap_eta_axis_coefficients_constant [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {nu0 zeta : ClassFunction ↥hyp.base.T ℂ}
    (hbridgeZ : nu0 - zeta ∈ ZIrr ↥hyp.base.T)
    (hbridgeSupp : (nu0 - zeta).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hzeta : zeta ∈ S)
    (hgalois : ∀ (sigma : ℂ ≃+* ℂ) xi, xi ∈ S →
      ClassFunction.mapRingEquiv sigma xi ∈ S)
    (hdiffSupp : ∀ xi ∈ S, ∀ xi' ∈ S, (xi - xi').support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (horth : ∀ xi ∈ S, ∀ i : Fin hyp.base.q, ∀ j : Fin hyp.base.p,
      ClassFunction.inner (coh.extension xi) (hyp.base.eta i j) = 0)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ)
    (hm : ∀ i j, ClassFunction.inner (tSideDadeMap hyp hG (nu0 - zeta))
      (hyp.base.eta i j) = (m i j : ℂ))
    (hnu0 : ∀ sigma : ℂ ≃+* ℂ, ClassFunction.mapRingEquiv sigma nu0 = nu0)
    (hrowOrbit : ∀ i : Fin hyp.base.q, i ≠ ⟨0, hyp.base.q_prime.pos⟩ →
      ∃ sigma : ℂ ≃+* ℂ,
        ClassFunction.mapRingEquiv sigma
            (hyp.base.eta ⟨1, hyp.base.q_prime.one_lt⟩
              ⟨0, hyp.base.p_prime.pos⟩) =
          hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)
    (hcolumnOrbit : ∀ j : Fin hyp.base.p, j ≠ ⟨0, hyp.base.p_prime.pos⟩ →
      ∃ sigma : ℂ ≃+* ℂ,
        ClassFunction.mapRingEquiv sigma
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩
              ⟨1, hyp.base.p_prime.one_lt⟩) =
          hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) :
    (∀ i : Fin hyp.base.q, i ≠ ⟨0, hyp.base.q_prime.pos⟩ →
      m i ⟨0, hyp.base.p_prime.pos⟩ =
        m ⟨1, hyp.base.q_prime.one_lt⟩ ⟨0, hyp.base.p_prime.pos⟩) ∧
    (∀ j : Fin hyp.base.p, j ≠ ⟨0, hyp.base.p_prime.pos⟩ →
      m ⟨0, hyp.base.q_prime.pos⟩ j =
        m ⟨0, hyp.base.q_prime.pos⟩ ⟨1, hyp.base.p_prime.one_lt⟩) := by
  constructor
  · intro i hi
    obtain ⟨sigma, hsigma⟩ := hrowOrbit i hi
    have hsigmaZ := hgalois sigma zeta hzeta
    have htransport := tSideDadeMap_inner_galois_eq_intCast hG hyp sigma
      (m ⟨1, hyp.base.q_prime.one_lt⟩ ⟨0, hyp.base.p_prime.pos⟩)
      (hnu0 sigma) hbridgeZ hbridgeSupp hsigma
      (eta_mem_ZIrr hyp.base _ _) (hm _ _) coh hzeta hsigmaZ
      (hdiffSupp zeta hzeta _ hsigmaZ)
      (fun xi hxi => horth xi hxi i ⟨0, hyp.base.p_prime.pos⟩)
    exact Int.cast_injective ((hm i ⟨0, hyp.base.p_prime.pos⟩).symm.trans htransport)
  · intro j hj
    obtain ⟨sigma, hsigma⟩ := hcolumnOrbit j hj
    have hsigmaZ := hgalois sigma zeta hzeta
    have htransport := tSideDadeMap_inner_galois_eq_intCast hG hyp sigma
      (m ⟨0, hyp.base.q_prime.pos⟩ ⟨1, hyp.base.p_prime.one_lt⟩)
      (hnu0 sigma) hbridgeZ hbridgeSupp hsigma
      (eta_mem_ZIrr hyp.base _ _) (hm _ _) coh hzeta hsigmaZ
      (hdiffSupp zeta hzeta _ hsigmaZ)
      (fun xi hxi => horth xi hxi ⟨0, hyp.base.q_prime.pos⟩ j)
    exact Int.cast_injective ((hm ⟨0, hyp.base.q_prime.pos⟩ j).symm.trans htransport)

/-- **Peterfalvi (3.9.b), the threaded full Galois orbits in eta-grid notation.**
The Section 16 carrier stores the producer equalities in their canonical form
`mapRingEquiv u (tau3 (omega ...)) = tau3 (omega ...)`; the defining identity
`eta = tau3 ∘ omega` turns them into the exact row/column orbit pair consumed by
`tSideDadeMap_eta_axis_coefficients_constant`. -/
theorem eta_axis_galois_orbits_of_hypothesis
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    (∀ i : Fin base.q, i ≠ ⟨0, base.q_prime.pos⟩ →
      ∃ sigma : ℂ ≃+* ℂ,
        ClassFunction.mapRingEquiv sigma
            (base.eta ⟨1, base.q_prime.one_lt⟩ ⟨0, base.p_prime.pos⟩) =
          base.eta i ⟨0, base.p_prime.pos⟩) ∧
    (∀ j : Fin base.p, j ≠ ⟨0, base.p_prime.pos⟩ →
      ∃ sigma : ℂ ≃+* ℂ,
        ClassFunction.mapRingEquiv sigma
            (base.eta ⟨0, base.q_prime.pos⟩ ⟨1, base.p_prime.one_lt⟩) =
          base.eta ⟨0, base.q_prime.pos⟩ j) := by
  constructor
  · intro i hi
    obtain ⟨sigma, hsigma⟩ := base.eta_row_galois_orbit i hi
    refine ⟨sigma, ?_⟩
    rw [base.eta_eq_tau_omega, base.eta_eq_tau_omega]
    exact hsigma
  · intro j hj
    obtain ⟨sigma, hsigma⟩ := base.eta_column_galois_orbit j hj
    refine ⟨sigma, ?_⟩
    rw [base.eta_eq_tau_omega, base.eta_eq_tau_omega]
    exact hsigma

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapMemberResidual.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Peterfalvi (4.4)--(4.5), the Section 12 zero column is the prime-TI
anchor.**  The column-`0` dual is trivial, so its distinguished constituent
restricts to `1_{M'}`.  Summing the whole column and applying (4.5.a) therefore
gives exactly `Ind_{M'}^M 1`, independently of every enumeration choice.

This is the source-side identification needed to compare the Section 11
residual with `primeTIred 0` in the T-side (11.9.a) projection. -/
theorem s12_muGrid_zeroColumn_sum_eq_induce_trivial [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) =
      ClassFunction.induce ((derivedInG M).subgroupOf M)
        (trivialClassFunction ↥((derivedInG M).subgroupOf M)) := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    OddOrder.Peterfalvi.S12.typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let chi2 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  have hchi2 : chi2 = 1 := by
    dsimp only [chi2]
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by
      apply Fin.ext
      simp, OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup_zero]
  have hsum : ClassFunction.induce h.K
        (ClassFunction.restrict h.K
          ((h.columnFamily chi2).mu 0 : ClassFunction ↥M ℂ)) =
      ∑ i : Fin (Nat.card h.W1),
        ((h.columnFamily chi2).mu i : ClassFunction ↥M ℂ) :=
    h.induce_restrict_certainType_eq chi2
  have hsource : ClassFunction.restrict h.K
        ((h.columnFamily chi2).mu 0 : ClassFunction ↥M ℂ) =
      trivialClassFunction ↥h.K := by
    rw [hchi2, h.certainType_zero_column_anchor.2]
    ext x
    simp
  rw [hsource] at hsum
  calc
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) =
        ∑ i : Fin (Nat.card h.W1),
          ((h.columnFamily chi2).mu i : ClassFunction ↥M ℂ) := by
      rw [← Equiv.sum_comp (finCongr hcardW1.symm)
        (fun i : Fin (Nat.card h.W1) =>
          ((h.columnFamily chi2).mu i : ClassFunction ↥M ℂ))]
      exact Finset.sum_congr rfl (fun i _ => by
        unfold OddOrder.Peterfalvi.S12.Hypothesis.muGrid
        rfl)
    _ = ClassFunction.induce h.K (trivialClassFunction ↥h.K) := hsum.symm
    _ = ClassFunction.induce ((derivedInG M).subgroupOf M)
          (trivialClassFunction ↥((derivedInG M).subgroupOf M)) := rfl

open scoped Classical in
/-- **Peterfalvi (2.11)/(11.8), the Section 12 residual uses the T-side
Dade map.**  For the specified type-`P₁` datum, the Section 12 full `A₀(T)`
map restricts to the canonical `A₁(T)` map.  Together with the zero-column
anchor above, this identifies the complete source term used by (11.8) with
the `τ_T(ν₀-ζ)` term of (11.9.a). -/
theorem s12Tau_zeroColumn_sub_eq_tSideDadeMap [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (side : Hypothesis (G := G))
    (dataT : TypePData side.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 side.base.T)
    (hIII : IsTypeIII side.base.T)
    (zeta nu0 : ClassFunction ↥side.base.T ℂ)
    (hnu0 : nu0 = ClassFunction.induce
      ((derivedInG side.base.T).subgroupOf side.base.T)
      (trivialClassFunction
        ↥((derivedInG side.base.T).subgroupOf side.base.T)))
    (hsupp : (nu0 - zeta).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp side.base.T) side.base.T) :
    (s12HypothesisOfTypePData hG side.base.T_maximal dataT (Or.inl hIII) hP1).tau
        ((∑ i : Fin (s12HypothesisOfTypePData hG side.base.T_maximal dataT
              (Or.inl hIII) hP1).w1,
            (s12HypothesisOfTypePData hG side.base.T_maximal dataT
              (Or.inl hIII) hP1).muGrid hG hG.odd i 0) - zeta) =
      tSideDadeMap side hG (nu0 - zeta) := by
  let hyp12 := s12HypothesisOfTypePData hG side.base.T_maximal dataT
    (Or.inl hIII) hP1
  have hanchor := s12_muGrid_zeroColumn_sum_eq_induce_trivial hG hyp12
  have hmap := tSideDadeMap_eq_full_typeP1DadeMap_of_support
    hG side dataT hP1 hsupp
  change hyp12.tau
      ((∑ i : Fin hyp12.w1, hyp12.muGrid hG hG.odd i 0) - zeta) =
    tSideDadeMap side hG (nu0 - zeta)
  rw [hanchor, ← hnu0]
  simpa only [hyp12, s12HypothesisOfTypePData,
    OddOrder.Peterfalvi.S12.Hypothesis.tau] using hmap.symm

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Peterfalvi (14.9), the Γ-Bessel assembly skeleton** — the *proven* structural core of the
character body, isolating the char-cascade carriers as precisely-named hypotheses.  Coq
`FTtypeP_min_typeII` (PFsection14.v:764--853): given the coherent `τ₁`-image family `calT1`
(orthonormal degree-`p` induced characters, whose `|calT1| = (v−1)/p` count is the proven
`T_typeIII_calT1_card` after the (13.12) `d = 1` substitution `v = |V|`) and the `S`-side `βₛ`
bridge gap `Γ`, the parity fact `⟨Γ, τ₁ζ⟩ ≡ 1 (mod 2)` per `ζ` (`S09.cfdot_real_vchar_even`) makes
each integer pairing coefficient `x ζ = ⟨Γ, τ₁ζ⟩` **nonzero**; then the orthogonal-integer Bessel
bridge `S09.sum_rat_weights_le_of_orthogonal_integer_decomposition` (Coq's `orthogonal_split` +
Bessel over `‖Γ‖² ≤ (u−1)/q`) gives `∑_{ζ ∈ calT1} 1 ≤ ⟨Γ,Γ⟩ ≤ (u−1)/q`, i.e.
`|calT1| = (v−1)/p ≤ (u−1)/q`.

This is the **genuinely-available** arithmetic of (14.9): everything downstream of the carriers is
proven here (the orthonormal-family Bessel step with unit weights `m ζ = 1`, the `∑ 1 = |calT1|`
count-collapse, and the `⟨Γ,Γ⟩ ≤ (u−1)/q` chaining).  The four hypotheses package exactly the deep
carriers that the honest §16 build still owes, each cited from its own construction at the
`T_typeIII_ratio_le` call site:

* `hcount : (calT1.card : ℚ) = (v−1)/p` — the coherent count (proven `T_typeIII_calT1_card` in `|V|`
  form) **after** the (13.12) `d = 1` substitution `v = |V|`
  (`Hypothesis.V_inf_centralizer_Q_eq_bot`);
* `horth` — orthonormality of the `τ₁`-images (the `calT1` **coherence** carrier, proven skeleton
  `T_typeIII_calT1_coherent` fed a T-side `S07.Hypothesis` Dade package);
* `hdecomp`/`hΓ₁`/`hx` — the `S`-side `βₛ` bridge gap `Γ = ∑ x_ζ·τ₁ζ + Γ₁` (`Γ₁ ⊥ τ₁ζ`), with the
  parity nonzeroness `x_ζ ≠ 0` (Coq `nzT1_Ga` via `cfdot_real_vchar_even`);
* `hnorm : ⟨Γ,Γ⟩.re ≤ (u−1)/q` — the `S`-side norm bound on the bridge gap.

Its output `(v−1)/p ≤ (u−1)/q` is exactly the (14.9) `≤` whose `>` counterpart (14.8)
`key_inequality` contradicts. -/
theorem T_typeIII_ratio_le_of_gamma_bridge [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis (G := G))
    (calT1 : Finset (ClassFunction G ℂ)) (Γ Γ₁ : ClassFunction G ℂ)
    (x : ClassFunction G ℂ → ℤ)
    (hcount : (calT1.card : ℚ) = ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (hdecomp : Γ = (∑ a ∈ calT1, (((x a : ℝ) : ℂ) • a)) + Γ₁)
    (hΓ₁ : ∀ a ∈ calT1, ClassFunction.inner Γ₁ a = 0)
    (hx : ∀ a ∈ calT1, x a ≠ 0)
    (hnorm : (ClassFunction.inner Γ Γ).re ≤
      ((((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) : ℚ) : ℝ)) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  classical
  -- Bessel over the orthonormal `calT1` (unit weights `m a = 1`, integer coeffs `x a ≠ 0`),
  -- against the norm bound `⟨Γ,Γ⟩ ≤ (u−1)/q`: yields `∑_{a ∈ calT1} 1 ≤ (u−1)/q`.
  have hbessel := OddOrder.Peterfalvi.S09.sum_rat_weights_le_of_orthogonal_integer_decomposition
    (ι := ClassFunction G ℂ) calT1 (fun a => a) x (fun _ => (1 : ℚ)) Γ Γ₁
    (((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ))
    hdecomp
    (fun a ha b hb => by rw [horth a ha b hb]; split <;> simp)
    hΓ₁
    (fun _ _ => zero_le_one)
    hx
    hnorm
  -- `∑_{a ∈ calT1} 1 = |calT1|`, and `|calT1| = (v−1)/p` by the coherent count.
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcount] at hbessel
  exact hbessel

open scoped Classical in
/-- **(14.9) Γ-bridge extraction engine.**  Given the `S`-side gap `Γ`, its integral nonzero
coefficients on the orthonormal coherent family `calT1`, and the orthogonality of that family to the
η-grid, define the complementary term `Γ₁ := Γ - ∑_ζ x_ζ·ζ`.  Orthonormality makes `Γ₁`
orthogonal to every family member, hence to the projection sum.  The projection sum is η-grid
orthogonal by hypothesis, so the genuine **Peterfalvi (13.18.d)** field `BetaData.Y_norm_bound`
applies to the split `Γ = Γ₁ + ∑_ζ x_ζ·ζ`.

The resulting bound is on the projection sum—not on `Γ` itself—and feeds the proven Bessel skeleton
`T_typeIII_ratio_le_of_gamma_bridge`.  Thus this theorem exactly matches the corrected (13.18.d)
statement and assumes no overstrong full-gap norm bound. -/
theorem T_typeIII_ratio_le_of_sSide_gap [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis (G := G)) (calT1 : Finset (ClassFunction G ℂ))
    (horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (hcount : (calT1.card : ℚ) = ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (Γ : ClassFunction G ℂ) (x : ClassFunction G ℂ → ℤ)
    (hxcoe : ∀ a ∈ calT1, ClassFunction.inner Γ a = ((x a : ℝ) : ℂ))
    (hx : ∀ a ∈ calT1, x a ≠ 0)
    (heta : ∀ a ∈ calT1, ∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
      ClassFunction.inner a (hyp.base.eta i k) = 0)
    (hYnorm : ∀ (X Y : ClassFunction G ℂ), Γ = X + Y →
      ClassFunction.inner X Y = 0 →
      (∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
        ClassFunction.inner Y (hyp.base.eta i k) = 0) →
      (ClassFunction.inner Y Y).re ≤
        ((hyp.base.u : ℚ) - 1) / (hyp.base.q : ℚ)) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  classical
  set Γ₁ : ClassFunction G ℂ := Γ - ∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a with hΓ₁def
  have hdecomp : Γ = (∑ a ∈ calT1, (((x a : ℝ) : ℂ) • a)) + Γ₁ := by rw [hΓ₁def]; abel
  -- `Γ₁` is orthogonal to every member: `⟨Γ₁, b⟩ = ⟨Γ, b⟩ − ∑_a x_a·⟨a,b⟩ = x_b − x_b = 0`
  -- (inner is linear in the first argument, `inner_smul_left : ⟨c•φ,ψ⟩ = c·⟨φ,ψ⟩`).
  have hΓ₁ : ∀ a ∈ calT1, ClassFunction.inner Γ₁ a = 0 := by
    intro b hb
    have hsum_left : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner (∑ a ∈ s, ((x a : ℝ) : ℂ) • a) b
          = ∑ a ∈ s, ClassFunction.inner (((x a : ℝ) : ℂ) • a) b := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_left, ih, Finset.sum_insert hc]
    rw [hΓ₁def, ClassFunction.inner_sub_left, hsum_left calT1, hxcoe b hb,
      Finset.sum_eq_single b
        (fun a ha hab => by
          rw [ClassFunction.inner_smul_left, horth a ha b hb, if_neg hab, mul_zero])
        (fun hbni => absurd hb hbni),
      ClassFunction.inner_smul_left, horth b hb b hb, if_pos rfl, mul_one, sub_self]
  -- The projection sum is the `Y` in (13.18.d).  Its complement `Γ₁` is orthogonal to it
  -- because `Γ₁` is orthogonal to every member of `calT1`.
  have hΓ₁sum : ClassFunction.inner Γ₁
      (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a) = 0 := by
    have hsum_right : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner Γ₁ (∑ a ∈ s, ((x a : ℝ) : ℂ) • a)
          = ∑ a ∈ s, ClassFunction.inner Γ₁ (((x a : ℝ) : ℂ) • a) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_right, ih, Finset.sum_insert hc]
    rw [hsum_right calT1]
    apply Finset.sum_eq_zero
    intro a ha
    rw [ClassFunction.inner_smul_right, hΓ₁ a ha, mul_zero]
  have hsum_eta : ∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
      ClassFunction.inner (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a)
        (hyp.base.eta i k) = 0 := by
    intro i k
    have hsum_left : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner (∑ a ∈ s, ((x a : ℝ) : ℂ) • a) (hyp.base.eta i k)
          = ∑ a ∈ s,
            ClassFunction.inner (((x a : ℝ) : ℂ) • a) (hyp.base.eta i k) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_left, ih, Finset.sum_insert hc]
    rw [hsum_left calT1]
    apply Finset.sum_eq_zero
    intro a ha
    rw [ClassFunction.inner_smul_left, heta a ha i k, mul_zero]
  have hdecomp' : Γ = Γ₁ + ∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a := by
    rw [hdecomp]
    abel
  have hnormRaw := hYnorm Γ₁
    (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a) hdecomp' hΓ₁sum hsum_eta
  have hu1 : 1 ≤ hyp.base.u := by
    have huc : 0 < hyp.base.u * hyp.base.c := by
      rw [← hyp.base.card_U_eq_uc]
      exact Nat.card_pos
    exact (CanonicallyOrderedAdd.mul_pos.mp huc).1
  have hsubcast : ((hyp.base.u - 1 : ℕ) : ℚ) = (hyp.base.u : ℚ) - 1 := by
    rw [Nat.cast_sub hu1]
    norm_num
  have hnorm : (ClassFunction.inner
      (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a)
      (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a)).re ≤
        ((((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) : ℚ) : ℝ) := by
    rw [hsubcast]
    simpa using hnormRaw
  exact T_typeIII_ratio_le_of_gamma_bridge hyp calT1
    (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a) 0 x hcount horth (by simp) (by simp) hx hnorm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The (13.18) gap `Γ` is a virtual character.  Its Dade term is virtual because
`β_{#1} = Ind_{PW₁}^S 1 - μ_{0,#1}` is virtual and has the (13.18.a) `A₀(S)` support;
subtracting `1_G` and adding `η_{0,#1}` preserves `ZIrr` membership.

This proof deliberately exposes its existing upstream gate: the only non-formal input is
`S15.betaGrid_A0_support_of_c_eq_one`, with (13.12) threaded explicitly from the Core
endpoint. -/
private theorem sSideGamma_mem_ZIrr_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.base.c = 1) :
    OddOrder.Peterfalvi.S15.GammaGrid hG hyp.base ∈ ZIrr G := by
  classical
  let PW1 := (hyp.base.P ⊔ hyp.base.W1).subgroupOf hyp.base.S
  have htrivZ : trivialClassFunction ↥PW1 ∈ ZIrr ↥PW1 := by
    simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using
      (trivialIrreducibleCharacter ↥PW1).mem_ZIrr
  have hindZ : ClassFunction.induce PW1 (trivialClassFunction ↥PW1) ∈
      ZIrr ↥hyp.base.S :=
    ClassFunction.induce_mem_ZIrr PW1 htrivZ
  let j : Fin hyp.base.p := ⟨1, by have := hyp.base.three_le_p; omega⟩
  have hbetaZ : OddOrder.Peterfalvi.S15.betaGrid hyp.base j ∈ ZIrr ↥hyp.base.S := by
    rw [OddOrder.Peterfalvi.S15.betaGrid, OddOrder.Peterfalvi.S15.indPW1]
    exact (ZIrr ↥hyp.base.S).sub_mem hindZ
      (hyp.base.mu_irreducible ⟨0, hyp.base.q_prime.pos⟩ j).mem_ZIrr
  have htauZ : OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base ∈ ZIrr G := by
    simpa [OddOrder.Peterfalvi.S15.tauSbetaGrid, j] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.base.dadeHypS0 hG)
        (OddOrder.Peterfalvi.S15.betaGrid_A0_support_of_c_eq_one
          hG hyp.base hc1 j (by simp [j])) hbetaZ)
  have honeZ : (trivialIrreducibleCharacter G : ClassFunction G ℂ) ∈ ZIrr G :=
    (trivialIrreducibleCharacter G).mem_ZIrr
  have hetaZ : hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j ∈ ZIrr G :=
    eta_mem_ZIrr hyp.base _ _
  change OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base -
      (trivialIrreducibleCharacter G : ClassFunction G ℂ) + hyp.base.eta _ j ∈ ZIrr G
  exact (ZIrr G).add_mem ((ZIrr G).sub_mem htauZ honeZ) hetaZ

open scoped Classical in
/-- **Peterfalvi (14.9), `nzT1_Ga` parity extraction.**  Let `Γ` and every member of the coherent
`calT1` image be virtual characters.  If each member `a` admits the real virtual residual `Δ_a`
from the (14.9) expansion, with both `Δ_a` and `Γ` orthogonal to `1_G` and
`⟨Γ,a⟩ = 1 + ⟨Δ_a,Γ⟩`, then `⟨Γ,a⟩` is an odd integer and hence nonzero.

The parity statement is exactly `RepresentationTheory.cfdot_real_vchar_even`: `⟨Δ_a,Γ⟩` is even
because
trivial coefficients vanish.  This theorem performs all integrality/parity bookkeeping after the
genuine `Δ_a` construction; no prime-TI or Dade hypothesis is hidden in its conclusion. -/
theorem gap_coefficients_nonzero_of_delta_parity [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hodd : Odd (Nat.card G))
    (calT1 : Finset (ClassFunction G ℂ)) (Γ : ClassFunction G ℂ)
    (hΓZ : Γ ∈ ZIrr G) (hΓR : ClassFunction.IsReal Γ)
    (hΓ1 : ClassFunction.inner Γ
      (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0)
    (hmemZ : ∀ a ∈ calT1, a ∈ ZIrr G)
    (hDelta : ∀ a ∈ calT1, ∃ Δ : ClassFunction G ℂ,
      Δ ∈ ZIrr G ∧ ClassFunction.IsReal Δ ∧
        ClassFunction.inner Δ
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 ∧
        ClassFunction.inner Γ a = 1 + ClassFunction.inner Δ Γ) :
    ∃ x : ClassFunction G ℂ → ℤ,
      (∀ a ∈ calT1, ClassFunction.inner Γ a = ((x a : ℝ) : ℂ)) ∧
        ∀ a ∈ calT1, x a ≠ 0 := by
  let x : ClassFunction G ℂ → ℤ := fun a =>
    if ha : a ∈ calT1 then
      (ClassFunction.inner_mem_ZIrr_int hΓZ (hmemZ a ha)).choose
    else 0
  have hxcoe : ∀ a ∈ calT1, ClassFunction.inner Γ a = ((x a : ℝ) : ℂ) := by
    intro a ha
    rw [show x a = (ClassFunction.inner_mem_ZIrr_int hΓZ (hmemZ a ha)).choose by
      simp only [x, dif_pos ha]]
    exact_mod_cast (ClassFunction.inner_mem_ZIrr_int hΓZ (hmemZ a ha)).choose_spec
  refine ⟨x, hxcoe, ?_⟩
  intro a ha hxa0
  obtain ⟨Δ, hΔZ, hΔR, hΔ1, hrelation⟩ := hDelta a ha
  obtain ⟨m, c, d, hm, hc, hd, heven⟩ :=
    OddOrder.RepresentationTheory.cfdot_real_vchar_even hodd hΔZ hΔR hΓZ hΓR
  have hc0 : c = 0 := by
    rw [hΔ1] at hc
    exact_mod_cast hc
  have hd0 : d = 0 := by
    rw [hΓ1] at hd
    exact_mod_cast hd
  have hm_even : Even m := by
    simpa [hc0, hd0] using heven
  have hcast : ((x a : ℤ) : ℂ) = ((1 + m : ℤ) : ℂ) := by
    calc
      ((x a : ℤ) : ℂ) = ClassFunction.inner Γ a := by
        exact_mod_cast (hxcoe a ha).symm
      _ = 1 + ClassFunction.inner Δ Γ := hrelation
      _ = ((1 + m : ℤ) : ℂ) := by rw [← hm]; push_cast; ring
  have hxint : x a = 1 + m := by
    exact_mod_cast hcast
  rcases hm_even with ⟨k, hk⟩
  omega

/-- **Peterfalvi (14.9), the character body** — the structural `≤` half of the ratio comparison, the
sole deep obligation of (14.9).  Coq `PFsection14` `FTtypeP_min_typeII`, lines 737--853: assuming
`T`
is type III, build `calT1 = seqIndD QV T QV Q` (the degree-`p` induced characters of `T`, from
`T' = Q ⊔ V` via `T_deriv_eq_QV`), coherent by uniform-degree coherence
(`S07.coherent_of_constant_degree` / Coq `uniform_degree_coherence`).

The T-side family data are constructed: `T_typeIII_calT1_family_galois` and its orbit count give
`|calT1| = (|V|−1)/p`; `T_typeIII_calT1_isCoherent` supplies the coherent extension; the direct
(13.4) producer `T_side_caseB_facts` gives `D = ⊥`, hence `|V| = v`; and
`T_typeIII_coherent_image_inner_eta_eq_zero` proves every coherent image orthogonal to the shared
`eta`-grid by restricting the full type-P1 Dade map and applying the norm-two rigidity engine.

The prime-TI anchor is fixed by coefficient Galois automorphisms, so the full eta-axis orbits now
give axis constancy and the sharp norm gives the column-or-row projection dichotomy.  The sole
remaining local residual in this ratio theorem is Coq (11.8)
`FTtype34_not_ortho_cycTIiso`, which excludes the wrong zero-row alternative.  After it, the proven
Γ-Bessel skeleton `T_typeIII_ratio_le_of_sSide_gap` combines orthogonality, the exact count, and
the concrete (13.18.d) bound `betaData.Y_norm_bound` to obtain
`(v − 1)/p ≤ (u − 1)/q`, contradicting the strict (14.8) inequality. -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  -- Coq `FTtypeP_min_typeII` body (PFsection14.v:737--853): `calT1`/coherence + Γ-Bessel.
  -- Reduced to the proven Γ-Bessel skeleton `T_typeIII_ratio_le_of_gamma_bridge`; every
  -- char-cascade
  -- carrier is now supplied, so this theorem carries **no local `sorry`**.  The last residual —
  -- the Coq (11.8) `FTtype34_not_ortho_cycTIiso` non-orthogonality `hnotZeroRowProjection` — is now
  -- discharged by transporting the canonical narrow-`𝒮(H₀C)` refuter through the global σ/η grid
  -- identification ((3.9)(a) rigidity).  The upstream inputs it cites (Type-P₁ `A₀`-normed-TI,
  -- (13.18.a) β-support, §11 zero-column projection) are all proved.
  classical
  have hc1 : hyp.base.c = 1 :=
    hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have := hyp.base.finiteG
  have : Fintype ↥hyp.base.T := Fintype.ofFinite _
  have : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥hyp.base.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- **Carrier 1 (the coherent `τ₁`-image family, now DISCHARGED from the (14.9) coherence).**
  -- The intrinsic type-III datum builds the degree-`p` `Ind_{QV}^T`-family `calT1_set` with all
  -- coherence inputs (`T_typeIII_calT1_family`); the T-side Dade package + coherence engine
  -- (`T_typeIII_calT1_isCoherent`, i.e. `T_typeIII_hyp07` ∘ `T_typeIII_calT1_coherent`) then
  -- produce
  -- the coherent map `τ₁ = hτ.extension`.  Its image `calT1 := τ₁(calT1_set)` is an **orthonormal**
  -- set of `G`-class functions (`horth`), because `τ₁` is an isometry on `ℤ[calT1_set]`
  -- (`IsCoherent.extension_inner_eq`) and the source members are orthonormal irreducibles.
  obtain ⟨𝒯, hinertia, hne, hlinear, hconj𝒯, hgalois𝒯, hcount_V⟩ :=
    T_typeIII_calT1_family_galois hyp hIII.some
  set calT1_set : Set (ClassFunction ↥hyp.base.T ℂ) :=
    ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) with hcalT1
  -- Members of `calT1_set` are orthonormal irreducibles of `T` (irreducible + pairwise orthogonal
  -- via `T_typeIII_hyp07`'s family predicates), reused below for `horth`.
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at hχ
    obtain ⟨θ, hθ, rfl⟩ := hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- `hcard2 : 2 ≤ |calT1_set|` — the crude size bound `(|V|−1)/p ≥ 2`, **ungated**: from the
  -- intrinsic `2p + 1 ≤ |V|` (`T_typeIII_two_p_add_one_le_card_V`, odd-order Frobenius `U ⋊ W₁`)
  -- and the count `|calT1_set| = (|V|−1)/p` (`hcount_V`), via `2 ≤ (|V|−1)/p ⟺ 2p ≤ |V|−1`.  The
  -- lane-b `|V|`-lower-bound (`v = (q^p−1)/(q−1)`, 13.15) is only needed for the *exact* count, not
  -- this `≥ 2`.
  have hcard2 : 2 ≤ calT1_set.ncard := by
    have hV := T_typeIII_two_p_add_one_le_card_V hG hyp hIII.some
    have hncard : calT1_set.ncard = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
      rw [hcalT1, Set.ncard_coe_finset]; exact hcount_V
    rw [hncard, Nat.le_div_iff_mul_le hyp.base.p_prime.pos]
    omega
  -- The T-side coherence: `τ₁ = hτ.extension`, `IsCoherent (tSideDadeMap) calT1_set A₁(T)`.
  obtain ⟨hyp07, htau, ⟨hτ⟩⟩ :=
    T_typeIII_calT1_isCoherent hyp hG hIII 𝒯 hinertia hlinear hne hconj𝒯 calT1_set hcalT1 hcard2
  rw [htau] at hτ
  -- `calT1 := τ₁(calT1_set)`, the coherent-image `Finset` in `CF(G)`.
  set calT1 : Finset (ClassFunction G ℂ) :=
    calT1_set.toFinset.image (⇑hτ.extension) with hcalT1img
  -- **`horth`: the coherent images are orthonormal** — the discharged coherence carrier.
  have horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0 := by
    intro a ha b hb
    rw [hcalT1img, Finset.mem_image] at ha hb
    obtain ⟨ζ, hζT, rfl⟩ := ha
    obtain ⟨ζ', hζ'T, rfl⟩ := hb
    rw [Set.mem_toFinset] at hζT hζ'T
    -- `⟨τ₁ζ, τ₁ζ'⟩ = ⟨ζ, ζ'⟩` (coherent isometry on `ℤ[calT1_set]`).
    have hiso : ClassFunction.inner (hτ.extension ζ) (hτ.extension ζ')
        = ClassFunction.inner ζ ζ' :=
      hτ.extension_inner_eq ζ ζ' (Submodule.subset_span hζT) (Submodule.subset_span hζ'T)
    -- `⟨ζ, ζ'⟩ = if ζ = ζ' then 1 else 0` (orthonormal irreducibles).
    have hsrc : ClassFunction.inner ζ ζ' = if ζ = ζ' then (1 : ℂ) else 0 := by
      by_cases hζζ' : ζ = ζ'
      · subst hζζ'; rw [if_pos rfl]; exact (hirr ζ hζT).inner_self_eq_one
      · rw [if_neg hζζ']; exact hyp07.pairwise_orthogonal hζT hζ'T hζζ'
    rw [hiso, hsrc]
    -- The image equality `τ₁ζ = τ₁ζ'` iff `ζ = ζ'` (injectivity from the isometry).
    by_cases hζζ' : ζ = ζ'
    · rw [if_pos hζζ', if_pos (by rw [hζζ'])]
    · rw [if_neg hζζ', if_neg ?_]
      -- if `τ₁ζ = τ₁ζ'` then `⟨ζ,ζ'⟩ = ⟨τ₁ζ,τ₁ζ⟩ = ⟨ζ,ζ⟩ = 1 ≠ 0 = ⟨ζ,ζ'⟩`, contradiction.
      intro hab
      have h1 : ClassFunction.inner ζ ζ' = ClassFunction.inner ζ ζ := by
        rw [← hiso, ← hab,
          hτ.extension_inner_eq ζ ζ (Submodule.subset_span hζT) (Submodule.subset_span hζT)]
      rw [hsrc, if_neg hζζ', (hirr ζ hζT).inner_self_eq_one] at h1
      exact one_ne_zero h1.symm
  -- The coherent extension is injective on `calT1_set`: equality of two images would turn the
  -- source cross-inner-product `0` into the source self-inner-product `1`.
  have hinj : Set.InjOn (⇑hτ.extension) (↑calT1_set.toFinset : Set _) := by
    intro ζ hζ ζ' hζ' heq
    have hζS : ζ ∈ calT1_set := by simpa using hζ
    have hζ'S : ζ' ∈ calT1_set := by simpa using hζ'
    by_contra hne
    have hEq : ClassFunction.inner ζ ζ' = ClassFunction.inner ζ ζ := by
      rw [← hτ.extension_inner_eq ζ ζ' (Submodule.subset_span hζS)
          (Submodule.subset_span hζ'S), ← heq,
        hτ.extension_inner_eq ζ ζ (Submodule.subset_span hζS) (Submodule.subset_span hζS)]
    rw [hyp07.pairwise_orthogonal hζS hζ'S hne, (hirr ζ hζS).inner_self_eq_one] at hEq
    exact zero_ne_one hEq
  have hcalcard : calT1.card = calT1_set.toFinset.card := by
    rw [hcalT1img, Finset.card_image_of_injOn hinj]
  have hsourcecard :
      calT1_set.toFinset.card = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
    rw [← Set.ncard_eq_toFinset_card' calT1_set, hcalT1, Set.ncard_coe_finset]
    exact hcount_V
  -- (13.4) gives `D = ⊥`; hence `d = |D| = 1` and `|V| = v d = v`.
  have hDbot : hyp.base.D = ⊥ := (T_side_caseB_facts hG hyp).1
  have hd1 : hyp.base.d = 1 := by
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  have hVcard : Nat.card ↥hyp.base.V = hyp.base.v := by
    rw [hyp.base.card_V_eq_vd, hd1, mul_one]
  -- The same (13.4) value makes `v ≡ 1 (mod p)`, so the exact Nat quotient casts to the
  -- rational ratio used by the Bessel engine.
  have hvfull := (T_side_caseB_facts hG hyp).2
  have hvodd : Odd hyp.base.v := by
    rw [hvfull]
    exact hyp.tSide_cyclotomic_quotient_odd
  have hvdvd :
      hyp.base.v ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
    rw [hvfull]
  have hvmod : hyp.base.v ≡ 1 [MOD hyp.base.p] :=
    hyp.tSide_cyclotomic_quotient_divisor_modEq_one
      hyp.base.v hvodd.pos.ne' hvdvd
  have hpdiv : hyp.base.p ∣ hyp.base.v - 1 :=
    (Nat.modEq_iff_dvd' hvodd.pos).mp hvmod.symm
  have hcount : (calT1.card : ℚ) =
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) := by
    rw [hcalcard, hsourcecard, hVcard]
    exact Nat.cast_div hpdiv (Nat.cast_ne_zero.mpr hyp.base.p_prime.ne_zero)
  -- The genuine (13.18) gap is the concrete `GammaGrid`.  Its virtuality follows from the
  -- supported S-side Dade image; reality and principal orthogonality are the faithful BetaData
  -- fields.  The coherent images are virtual characters by the coherent-extension contract.
  let betaData := OddOrder.Peterfalvi.S15.betaData_of_grid_of_c_eq_one
    hG hnoV hyp.base hc1 ⟨1, hyp.base.p_prime.one_lt⟩ (by simp)
  have hGammaZ : betaData.Gamma ∈ ZIrr G := by
    simpa [betaData, OddOrder.Peterfalvi.S15.betaData_of_grid_of_c_eq_one] using
      (sSideGamma_mem_ZIrr_of_c_eq_one hG hyp hc1)
  have hGammaR : ClassFunction.IsReal betaData.Gamma :=
    betaData.Gamma_real
  have hGamma1 : ClassFunction.inner betaData.Gamma
      (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 := by
    exact betaData.Gamma_orthogonal_one
  have hmemZ : ∀ a ∈ calT1, a ∈ ZIrr G := by
    intro a ha
    rw [hcalT1img, Finset.mem_image] at ha
    obtain ⟨ζ, hζT, rfl⟩ := ha
    rw [Set.mem_toFinset] at hζT
    exact hτ.extension_mem_ZIrr ζ (Submodule.subset_span hζT)
  have hdiff_supp := T_typeIII_calT1_difference_support
    hyp hG hIII 𝒯 hlinear calT1_set hcalT1
  have hgaloisT : ∀ (sigma : ℂ ≃+* ℂ) ξ, ξ ∈ calT1_set →
      ClassFunction.mapRingEquiv sigma ξ ∈ calT1_set := by
    intro sigma ξ hξ
    rw [hcalT1] at hξ ⊢
    exact inducedFamily_mapRingEquiv_mem
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) 𝒯 hgalois𝒯 sigma hξ
  -- This is now the exact remaining (14.9) character construction: for each coherent image
  -- `a = τ₁ζ`, build `Δ_a = τ_T(ν₀ - ζ) - 1_G + a`, prove it real/virtual and orthogonal
  -- to `1_G`, and establish the expansion `⟨Γ,a⟩ = 1 + ⟨Δ_a,Γ⟩`.  All integrality and
  -- parity bookkeeping after this witness is discharged by the theorem below.
  have hDelta : ∀ a ∈ calT1, ∃ Δ : ClassFunction G ℂ,
      Δ ∈ ZIrr G ∧ ClassFunction.IsReal Δ ∧
        ClassFunction.inner Δ
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 ∧
        ClassFunction.inner betaData.Gamma a =
          1 + ClassFunction.inner Δ betaData.Gamma := by
    intro a ha
    rw [hcalT1img, Finset.mem_image] at ha
    obtain ⟨ζ, hζT, rfl⟩ := ha
    rw [Set.mem_toFinset] at hζT
    have hζform := hζT
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at hζform
    obtain ⟨θ, hθ, hζeq⟩ := hζform
    have hζ1_ind :=
      typeIII_induced_source_degree hyp θ (hlinear θ hθ)
    have hζ1 : ζ 1 = (hyp.base.p : ℂ) :=
      hζeq ▸ hζ1_ind
    have hζirr_ind : IsIrreducibleCharacter (ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) := by
      simpa only [hζeq] using hirr ζ hζT
    obtain ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτβZ, hτβ1, hβconj,
        hνinner, hνζ, hνζc, hβnorm, hτβnorm, hνfixed, hν0eq⟩ :=
      exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
        hG hyp hIII θ (hne θ hθ) hζirr_ind hζ1_ind
    rw [hζeq] at hβZ hβsupp hτβZ hτβ1 hβconj hνζ hνζc hβnorm hτβnorm
    have hζone : ClassFunction.inner ζ
        (trivialClassFunction ↥hyp.base.T) = 0 := by
      rw [← hζeq]
      exact OddOrder.Peterfalvi.S09.Cert.inner_induce_constOne_eq_zero
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hne θ hθ)
    have hβinner : ClassFunction.inner (ν0 - ζ)
        (trivialClassFunction ↥hyp.base.T) = 1 := by
      rw [ClassFunction.inner_sub_left, hνinner, hζone, sub_zero]
    obtain ⟨mT, hmT, hpythT, hboundT, hprincipalT, hrelationT⟩ :=
      exists_tSide_etaGrid_intProjection_with_relation hG hyp hIII hβsupp hβinner hτβZ hτβnorm
    have hperpT := tSide_etaGridProjection_residual_ne_zero_of_anchor_orthogonal
      hG hyp hIII hyp07 hτ
      (fun ξ hξ => hdiff_supp ξ hξ ξ.conj (hyp07.conjugate_closed hξ))
      hζT (hirr ζ hζT) hβsupp hνζ hνζc mT
    have hsumSqT :
        (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (mT i j) ^ 2 : ℤ) ≤
          (hyp.base.p : ℤ) :=
      etaGrid_projection_sum_sq_le_of_residual_ne_zero
        hyp.base hτβZ hτβnorm mT hmT hperpT
    have horbits := eta_axis_galois_orbits_of_hypothesis hyp.base
    have haxis := tSideDadeMap_eta_axis_coefficients_constant
      hG hyp hβZ hβsupp hτ hζT hgaloisT hdiff_supp
      (fun ξ hξ i j =>
        T_typeIII_coherent_image_inner_eta_eq_zero hG hyp hIII
          hyp07.conjugate_closed hyp07.no_real_characters
          (fun χ hχ => hdiff_supp χ hχ χ.conj (hyp07.conjugate_closed hχ))
          hτ hξ (hirr ξ hξ) i j)
      mT hmT hνfixed horbits.1 horbits.2
    have hshape := etaGrid_coefficients_eq_column_or_row_of_sum_sq_le
      hyp.base hyp.q_lt_p mT hprincipalT haxis.1 haxis.2 hrelationT hsumSqT
    have hτβinner : ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 1 := by
      change ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
        (trivialClassFunction G) = 1
      rw [tSideDadeMap_inner_trivial hyp hG hβsupp, hβinner]
    have htrivSelf : ClassFunction.inner
        (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 1 :=
      (trivialIrreducibleCharacter G).isIrreducible.inner_self_eq_one
    have hζcT : ζ.conj ∈ calT1_set := hyp07.conjugate_closed hζT
    have hExtOne : ClassFunction.inner (hτ.extension ζ)
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 := by
      change ClassFunction.inner (hτ.extension ζ)
        (trivialClassFunction G) = 0
      exact tSideCoherentExtension_inner_trivial hyp hG hyp07 hτ hζT
        (hirr ζ hζT) hζone
        (hdiff_supp ζ.conj hζcT ζ hζT)
    have hExtConj : (hτ.extension ζ).conj = hτ.extension ζ.conj :=
      tSideCoherentExtension_conj hyp hG hIII 𝒯 hne calT1_set hcalT1
        hyp07 hτ hirr hζT
    have hζdiffSupp : (ζ - ζ.conj).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T :=
      hdiff_supp ζ hζT ζ.conj hζcT
    let Δ : ClassFunction G ℂ :=
      tSideDadeMap hyp hG (ν0 - ζ) -
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
        hτ.extension ζ
    have hOneZ :
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) ∈ ZIrr G :=
      (trivialIrreducibleCharacter G).mem_ZIrr
    have hExtZ : hτ.extension ζ ∈ ZIrr G :=
      hτ.extension_mem_ZIrr ζ (Submodule.subset_span hζT)
    have hΔZ : Δ ∈ ZIrr G := by
      change tSideDadeMap hyp hG (ν0 - ζ) -
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
        hτ.extension ζ ∈ ZIrr G
      exact (ZIrr G).add_mem ((ZIrr G).sub_mem hτβZ hOneZ) hExtZ
    have hΔreal : ClassFunction.IsReal Δ := by
      change ClassFunction.IsReal
        (tSideDadeMap hyp hG (ν0 - ζ) -
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
          hτ.extension ζ)
      exact tSideDelta_isReal hyp hG hτ hζT hζcT hβsupp hζdiffSupp
        hβconj hExtConj
    have hΔone : ClassFunction.inner Δ
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 := by
      change ClassFunction.inner
          (tSideDadeMap hyp hG (ν0 - ζ) -
              (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
            hτ.extension ζ)
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0
      rw [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
        hτβinner, htrivSelf]
      rw [hExtOne]
      norm_num
    have hrelation : ClassFunction.inner betaData.Gamma (hτ.extension ζ) =
        1 + ClassFunction.inner Δ betaData.Gamma := by
      -- The remaining deep input is now exact: Coq (11.8) rules out the
      -- zero-row branch of the proven (11.9) column-or-row dichotomy.
      -- The S/T cross orthogonality is no longer assumed: the landed exact-support
      -- consumer proves it from prime-TI support, Type-P₁ normed-TI, and order separation.
      have hnotZeroRowProjection :
          ¬ ∀ i : Fin hyp.base.q, ∀ j : Fin hyp.base.p,
            ClassFunction.inner
                (tSideDadeMap hyp hG (ν0 - ζ) -
                  ∑ j' : Fin hyp.base.p,
                    hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j')
                (hyp.base.eta i j) = 0 := by
        -- Coq (11.8) `FTtype34_not_ortho_cycTIiso`: the canonical narrow-`𝒮(H₀C)`
        -- refuter, transported through the global sigma/eta grid identification
        -- ((3.9)(a) rigidity) and the Dade-image anchor `ν₀ = Ind_{T'}^T 1`.
        have hP1' : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := by
          obtain ⟨_, _, hcIII_IV, _, _, _⟩ :=
            OddOrder.BG.Ch4.S16.proposition_type_classification
              hG hyp.base.T_maximal
          exact (hcIII_IV.mp (Or.inl hIII)).1
        obtain ⟨-, hW1spec, hW2spec⟩ :=
          (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose_spec
        set dataT' :=
          (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose
          with hdataT'
        have hW : dataT'.W = hyp.base.W := by
          rw [dataT'.W_eq, hW1spec, hW2spec, sup_comm, ← hyp.base.W_eq_join]
        have hV : typePV hyp.base.T dataT' =
            (hyp.base.W : Set G) \
              ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) := by
          unfold typePV
          rw [hW, hW1spec, hW2spec, Set.union_comm]
        -- `ζ`/`ν₀` were built under the local `haveI : Fintype ↥T := Fintype.ofFinite _`
        -- instances (`this✝`), which are *definitionally* the scoped
        -- `S12.FiniteInduce.finiteSubFintype`/`natCardInvC` but appear as opaque fvars, so the
        -- scoped-instance `inducedFamily` / `s12Tau…` consumers need a `Subsingleton.elim` bridge.
        have hzetaS : ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily hyp.base.T :=
          ⟨θ, hne θ hθ, by convert hζeq.symm using 2; exact Subsingleton.elim _ _⟩
        -- `hν0eq` carries the local `haveI` `Fintype`/`Invertible` diamond (opaque fvars,
        -- definitionally the scoped `S12.FiniteInduce.*`), bridged by `Subsingleton.elim`.
        have himage := s12Tau_zeroColumn_sub_eq_tSideDadeMap hG hyp dataT' hP1'
          hIII ζ ν0
          (by convert hν0eq using 2; exact Subsingleton.elim _ _) hβsupp
        have hzeta1 : ζ 1 =
            ((s12HypothesisOfTypePData hG hyp.base.T_maximal dataT'
              (Or.inl hIII) hP1').w1 : ℂ) := by
          rw [show (s12HypothesisOfTypePData hG hyp.base.T_maximal dataT'
              (Or.inl hIII) hP1').w1 = Nat.card ↥dataT'.W1 from rfl,
            hW1spec, ← hyp.base.p_eq_card_W2]
          exact hζ1
        -- `member_residual…eta`'s `¬∀ … inner[scoped] … = 0` conclusion; the local goal states the
        -- same `inner` under the `haveI` diamond, so bridge the reindexed `∀` per-entry.
        have hkey := member_residual_not_orthogonal_eta_of_refuter hG hyp.base
          (s12HypothesisOfTypePData hG hyp.base.T_maximal dataT'
            (Or.inl hIII) hP1')
          hW hW2spec hW1spec hV (Or.inl hIII)
          (OddOrder.Peterfalvi.S13.secondDerived_eq_fitting_of_base hG
            (s12HypothesisOfTypePData hG hyp.base.T_maximal dataT'
              (Or.inl hIII) hP1') (Or.inl hIII)
            (fun s13 => hncH0C s13))
          (OddOrder.Peterfalvi.S13.card_H_eq_of_base hG
            (s12HypothesisOfTypePData hG hyp.base.T_maximal dataT'
              (Or.inl hIII) hP1') (Or.inl hIII)
            (fun s13 => hncH0C s13))
          -- `(11.3)` narrow-`𝒮(H₀C)` noncoherence.  The unconditional heir
          -- `S_H0C_not_coherent_unconditional` lives behind the `S12_Noncoherence` pair
          -- machinery, which transitively imports this S16 cluster; from here (upstream of that
          -- back-edge) the in-DAG refuter is the legacy `S_H0C_not_coherent`, exactly as its
          -- docstring reserves for consumers above the pair machinery.
          (fun s13hyp => hncH0C s13hyp)
          ζ hzetaS (hirr ζ hζT) hzeta1
          -- `source` is inferred from `himage` (scoped `tSideDadeMap`); the local goal states the
          -- same `inner (tSideDadeMap …) …` under the `haveI` diamond, bridged per-entry below.
          _ himage
        intro hgoal
        exact hkey (fun i j => by
          convert hgoal i j <;> exact Subsingleton.elim _ _)
      have hresidual :
          (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (mT i j) ^ 2 : ℤ) ≤
              (hyp.base.p : ℤ) ∧
          (∀ j : Fin hyp.base.p,
            ClassFunction.inner
                (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)
                (tSideDadeMap hyp hG (ν0 - ζ)) =
              ClassFunction.inner
                (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)
                (∑ i : Fin hyp.base.q,
                  hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
        refine ⟨hsumSqT, ?_⟩
        rcases hshape with hcolumn | hrow
        · exact etaGrid_zeroColumn_projection_of_coefficients_eq_column
            hyp.base (tSideDadeMap hyp hG (ν0 - ζ)) mT hmT hcolumn
        · -- Coq (11.8): exclude the zero-row projection.
          exfalso
          apply hnotZeroRowProjection
          intro i j
          rw [← etaGridProjection_eq_zeroRow_of_coefficients_eq_row hyp.base mT hrow]
          exact etaGrid_projection_residual_inner_eta_eq_zero
            hyp.base (tSideDadeMap hyp hG (ν0 - ζ)) mT hmT i j
      have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := by
        obtain ⟨_, _, hcIII_IV, _, _, _⟩ :=
          OddOrder.BG.Ch4.S16.proposition_type_classification
            hG hyp.base.T_maximal
        exact (hcIII_IV.mp (Or.inl hIII)).1
      let dataT :=
        (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose
      have hcross :
          ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
            (OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base) = 0 :=
        tSideDadeMap_inner_tauSbetaGrid_eq_zero_of_c_eq_one
          hG hnoV hyp hc1 dataT hP1 hβsupp
      have hτβeta : ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩
            ⟨1, by have := hyp.base.three_le_p; omega⟩) = 0 := by
        have hne0 :
            (⟨1, by have := hyp.base.three_le_p; omega⟩ : Fin hyp.base.p) ≠
              ⟨0, hyp.base.p_prime.pos⟩ := by
          intro h
          have hv := congrArg Fin.val h
          norm_num at hv
        have hrow := tSide_beta_inner_eta_of_zeroColumn_projection
          hyp.base (tSideDadeMap hyp hG (ν0 - ζ)) hresidual.2
          ⟨1, by have := hyp.base.three_le_p; omega⟩
        simpa only [if_neg hne0] using hrow
      have hΓdef : betaData.Gamma =
          OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base -
              (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
            hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩
              ⟨1, by have := hyp.base.three_le_p; omega⟩ := by
        rfl
      have hΔdef : Δ =
          tSideDadeMap hyp hG (ν0 - ζ) -
              (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
            hτ.extension ζ := by
        rfl
      exact gap_cross_inner_identity hGammaZ hExtZ hOneZ hΓdef hΔdef
        hτβinner hcross hτβeta hGamma1
    exact ⟨Δ, hΔZ, hΔreal, hΔone, hrelation⟩
  obtain ⟨x, hxcoe, hx⟩ :
      ∃ (x : ClassFunction G ℂ → ℤ),
        (∀ a ∈ calT1, ClassFunction.inner betaData.Gamma a = ((x a : ℝ) : ℂ)) ∧
        (∀ a ∈ calT1, x a ≠ 0) := by
    exact gap_coefficients_nonzero_of_delta_parity hG.odd calT1 betaData.Gamma
      hGammaZ hGammaR hGamma1 hmemZ hDelta
  have heta : ∀ a ∈ calT1, ∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
      ClassFunction.inner a (hyp.base.eta i k) = 0 := by
    intro a ha i k
    rw [hcalT1img, Finset.mem_image] at ha
    obtain ⟨ζ, hζT, rfl⟩ := ha
    rw [Set.mem_toFinset] at hζT
    exact T_typeIII_coherent_image_inner_eta_eq_zero hG hyp hIII
      hyp07.conjugate_closed hyp07.no_real_characters
      (fun χ hχ => hdiff_supp χ hχ χ.conj (hyp07.conjugate_closed hχ))
      hτ hζT (hirr ζ hζT) i k
  exact T_typeIII_ratio_le_of_sSide_gap hyp calT1 horth hcount
    betaData.Gamma x hxcoe hx heta betaData.Y_norm_bound

end OddOrder.Peterfalvi.S16
