-- Prove2me | solution 1 for OddOrder.exists_section16MaximalPair_data
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:43:57.575729+00:00
-- url     : https://prove2.me/submissions/e9930306-a23d-409a-a9a5-2165dcf66273

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CharacterEstimate.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/FrobeniusFamily.lean
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
--   OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean
--   OddOrder/Peterfalvi/S09_FrobeniusFamilyOrthogonality.lean
--   OddOrder/Peterfalvi/S09_TwoFamiliesParity.lean
--   OddOrder/Peterfalvi/S09_FrobeniusParity.lean
--   OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean
--   OddOrder/Peterfalvi/S09_FrobeniusGammaNormEstimate.lean
--   OddOrder/Peterfalvi/S09_FrobeniusBsumEstimate.lean
--   OddOrder/Peterfalvi/S09_FrobeniusGoodIndexEstimate.lean
--   OddOrder/Isaacs/Ch06_FrobeniusActions/KernelNilpotent.lean
--   OddOrder/Peterfalvi/S09_FrobeniusCardG0LowerBound.lean
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/SigmaCovers.lean
--   OddOrder/Peterfalvi/S14_MaximalI/TypeICovering.lean
--   OddOrder/FeitThompsonSection16Core.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_FeitThompsonSection16Core
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.Nilpotent
import Theorems.Thm_OddOrder_Isaacs_Ch06_isNilpotent_of_isFrobeniusAction_of_prime_card_aux
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_delta_isReal
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_exists_conjIndex_hypothesis78
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_zeta_ne_conj
import Theorems.Thm_OddOrder_Peterfalvi_S09_Hypothesis79_zetaImage_cross_eq_zero_of_conjIndex
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_weightedNuSum_inner_self_eq
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_exists_weightedGammaDecomposition
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_distinguishedNuAt_chiRhoNormSq_ge_of_reverseCoefficient_ne
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_distinguishedNuAt_chiRhoNormSq_ge
import Theorems.Thm_OddOrder_Peterfalvi_S09_reduced_inequality_of_estimates
import Theorems.Thm_OddOrder_RepresentationTheory_cfdot_real_vchar_even
import Theorems.Thm_OddOrder_Peterfalvi_S14_exists_typeICovering
import Theorems.Thm_OddOrder_Peterfalvi_S14_theorem88_dichotomy

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

/-- Combined beta-norm form using one orthogonality direction and irreducibility of `ζ`. -/
theorem betaNormSq_eq_complementIndex_add_one_of_zeta_ind_orthogonal_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  exact H78.betaNormSq_eq_complementIndex_add_one
    (H78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
      hind_norm hzeta_ind hzeta_irr)

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

/-- Any indexed coherent image `νζᵢ` has norm one once the source `ζᵢ` is irreducible. -/
theorem nu_zeta_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
        (H78.nu (H78.hyp76.zeta i)) = 1 :=
  H78.nu_zeta_inner_self_eq_one hi
    (H78.zeta_inner_self_eq_one_of_irreducible hzeta_irr)

/-- Coherence makes an indexed image `νζᵢ` a signed irreducible character once
the source `ζᵢ` is irreducible.  This records exactly the sign ambiguity left by
the virtual-character norm-one criterion. -/
theorem exists_zsmul_irreducibleCharacter_nu_zeta_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ∃ (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
        H78.nu (H78.hyp76.zeta i) = ε • (ξ : ClassFunction G ℂ) :=
  OddOrder.RepresentationTheory.exists_zsmul_irreducibleCharacter_of_inner_self_one
    (H78.nu_zeta_mem_ZIrr_of_isCoherent hcoh hnu hi)
    (H78.nu_zeta_inner_self_eq_one_of_irreducible hi hzeta_irr)

/-- Distinguished-`ζ` specialization of the signed image criterion. -/
theorem exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ∃ (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
        H78.nu (H78.hyp76.zeta H78.zetaDistinct) = ε • (ξ : ClassFunction G ℂ) :=
  H78.exists_zsmul_irreducibleCharacter_nu_zeta_of_isCoherent hcoh hnu
    H78.zetaDistinct_ne_ind1H hzeta_irr

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

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/CharacterEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

namespace FrobeniusFamily

variable {k : ℕ}

theorem mem_G0_iff (F : FrobeniusFamily G k) {x : G} :
    x ∈ F.G0 ↔ ∀ i, x ∉ F.kernelSpread i := Iff.rfl

lemma one_mem_G0 (F : FrobeniusFamily G k) : (1 : G) ∈ F.G0 := by
  intro i
  exact F.one_not_mem_kernelSpread i

open scoped Classical in
/-- The identity contribution in Peterfalvi (7.10): since `1 ∈ G₀`, any class
function with `1 ≤ |χ(1)|²` contributes at least `1` to the `G₀` norm sum. -/
lemma one_le_G0_norm_sum_of_one_le_norm_one [Fintype G]
    (F : FrobeniusFamily G k) (χ : ClassFunction G ℂ)
    (hone : (1 : ℝ) ≤ ‖(χ : G → ℂ) 1‖ ^ 2) :
    (1 : ℝ) ≤
      ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
        ‖(χ : G → ℂ) g‖ ^ 2 := by
  classical
  have hmem : (1 : G) ∈ Finset.univ.filter (fun g : G => g ∈ F.G0) := by
    simp [F.one_mem_G0]
  exact hone.trans
    (Finset.single_le_sum (f := fun g : G => ‖(χ : G → ℂ) g‖ ^ 2)
      (fun g _ => sq_nonneg _) hmem)

/-- A signed irreducible character has `|χ(1)|² ≥ 1`.  This is the numerical
content behind the `χ₁(1)^2` term in Peterfalvi (7.10). -/
lemma one_le_norm_sq_apply_one_of_signed_irreducible
    (χ : ClassFunction G ℂ) (ε : ℤ)
    (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_one :
      (χ : G → ℂ) 1 =
        (ε : ℂ) * ((ξ : ClassFunction G ℂ) : G → ℂ) 1) :
    (1 : ℝ) ≤ ‖(χ : G → ℂ) 1‖ ^ 2 := by
  obtain ⟨d, hdpos, hd⟩ :=
    OddOrder.RepresentationTheory.irreducibleCharacter_apply_one_eq_pos_natCast ξ
  rw [hχ_one, hd]
  rcases hε with rfl | rfl
  · rw [Int.cast_one, one_mul, Complex.norm_natCast]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    nlinarith
  · rw [Int.cast_neg, Int.cast_one, neg_one_mul, norm_neg, Complex.norm_natCast]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    nlinarith

open scoped Classical in
/-- Signed-irreducible form of the `G₀` identity contribution used in (7.10). -/
lemma one_le_G0_norm_sum_of_signed_irreducible [Fintype G]
    (F : FrobeniusFamily G k) (χ : ClassFunction G ℂ) (ε : ℤ)
    (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ : χ = ε • (ξ : ClassFunction G ℂ)) :
    (1 : ℝ) ≤
      ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
        ‖(χ : G → ℂ) g‖ ^ 2 := by
  have hχ_one :
      (χ : G → ℂ) 1 =
        (ε : ℂ) * ((ξ : ClassFunction G ℂ) : G → ℂ) 1 := by
    rw [hχ, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ),
      ClassFunction.smul_apply]
  exact F.one_le_G0_norm_sum_of_one_le_norm_one χ
    (one_le_norm_sq_apply_one_of_signed_irreducible χ ε ξ hε hχ_one)

/-- The sharp kernel H_i^# has cardinality |H_i| - 1. -/
lemma ncard_kernel_sharp [Finite G] (F : FrobeniusFamily G k) (i : Fin k) :
    ((F.H i : Set G) \ ({1} : Set G)).ncard = Nat.card (F.H i) - 1 := by
  have hHcard : (F.H i : Set G).ncard = Nat.card (F.H i) := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have h1_mem : (1 : G) ∈ (F.H i : Set G) := (F.H i).one_mem
  rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr h1_mem) (Set.finite_singleton _),
    Set.ncard_singleton, hHcard]

/-- `e_i = |L_i : H_i|` equals the order of the Frobenius complement `C`. -/
lemma e_eq_card_complement [Finite G] (F : FrobeniusFamily G k) (i : Fin k)
    {C : Subgroup ↥(F.L i)} (hC : IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    F.e i = Nat.card C := by
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]; exact hC.isComplement.card_mul_card
  have h := Nat.mul_div_cancel_left (Nat.card C) (Nat.card_pos (α := F.H i))
  rw [hprod] at h
  exact h

/-- The Frobenius product formula `|H_i| * e_i = |L_i|`. -/
lemma h_mul_e_eq_card_L [Finite G] (F : FrobeniusFamily G k) (i : Fin k) :
    F.h i * F.e i = Nat.card (F.L i) := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]
    exact hC.isComplement.card_mul_card
  rw [F.e_eq_card_complement i hC]
  exact hprod

/-- The Frobenius congruence gives `e_i ∣ h_i - 1`. -/
lemma e_dvd_h_sub_one [Finite G] (F : FrobeniusFamily G k) (i : Fin k) :
    F.e i ∣ F.h i - 1 := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hmod : Nat.card (F.H i) ≡ 1 [MOD Nat.card C] := by
    have := hC.card_kernel_modEq_one
    rwa [hN_card] at this
  have hdvd : Nat.card C ∣ Nat.card (F.H i) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.card_pos (α := F.H i))).mp hmod.symm
  rw [F.e_eq_card_complement i hC]
  exact hdvd

/-- A Frobenius kernel in the family is nontrivial, so `2 ≤ h_i`. -/
lemma two_le_h [Finite G] (F : FrobeniusFamily G k) (i : Fin k) : 2 ≤ F.h i := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hh_eq : F.h i = Nat.card (F.H i) := rfl
  rw [hh_eq, ← hN_card]
  have hnt : Nontrivial ((F.H i).subgroupOf (F.L i)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hC.ne_bot_kernel
  have h1 : 1 < Nat.card ((F.H i).subgroupOf (F.L i)) :=
    Finite.one_lt_card_iff_nontrivial.mpr hnt
  omega

/-- In an odd-order ambient group, each Frobenius kernel order `h_i` is odd. -/
lemma odd_h [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) : Odd (F.h i) := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]
    exact hC.isComplement.card_mul_card
  have hLodd : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  exact (Nat.odd_mul.mp (hprod ▸ hLodd)).1

/-- In an odd-order ambient group, each complement index `e_i` is odd. -/
lemma odd_e [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) : Odd (F.e i) := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]
    exact hC.isComplement.card_mul_card
  have hLodd : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  have hCodd : Odd (Nat.card C) := (Nat.odd_mul.mp (hprod ▸ hLodd)).2
  rw [F.e_eq_card_complement i hC]
  exact hCodd

/-- The Frobenius complement of `L_i` is nontrivial, so `e_i = |L_i : H_i| ≥ 2`. -/
lemma two_le_e [Finite G] (F : FrobeniusFamily G k) (i : Fin k) : 2 ≤ F.e i := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  rw [F.e_eq_card_complement i hC]
  have hnt : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.ne_bot_complement
  have h1 : 1 < Nat.card C := Finite.one_lt_card_iff_nontrivial.mpr hnt
  omega

/-- `H_i^#` has cardinality `h_i - 1` as a `Nat.card` statement. -/
lemma card_kernel_sharp_eq_h_sub_one [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) = F.h i - 1 := by
  rw [Nat.card_coe_set_eq]
  exact F.ncard_kernel_sharp i

/-- The local sharp-kernel ratio `|H_i^#| / |L_i|` as a real number, in the
denominator order used by the real reduced-family estimate. -/
lemma card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h_real [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) : ℝ) /
        (Nat.card (F.L i) : ℝ) =
      ((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ)) := by
  have hh1 : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  rw [F.card_kernel_sharp_eq_h_sub_one i, ← F.h_mul_e_eq_card_L i]
  rw [Nat.cast_sub hh1, Nat.cast_mul]
  rw [mul_comm (F.h i : ℝ) (F.e i : ℝ)]
  norm_num

/-- The unweighted `𝓑`-sum term from Peterfalvi (7.10) is nonnegative. -/
lemma h_sub_one_div_e_nonneg [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    0 ≤ ((F.h i : ℚ) - 1) / (F.e i : ℚ) := by
  have hh1_nat : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  have he1_nat : 1 ≤ F.e i := by
    have h2 := F.two_le_e i
    omega
  have hh1 : (1 : ℚ) ≤ F.h i := by exact_mod_cast hh1_nat
  have hepos : (0 : ℚ) < F.e i := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one he1_nat)
  exact div_nonneg (sub_nonneg.mpr hh1) (le_of_lt hepos)

/-- `2 e_i + 1 ≤ h_i`.  From `e_i ∣ h_i - 1` (Frobenius: `|H_i| ≡ 1 mod e_i`)
together with `|L_i|` odd (whence `e_i` is odd and `h_i - 1` is even), the
quotient `(h_i - 1)/e_i` is even and positive, so `h_i - 1 ≥ 2 e_i`. -/
lemma two_mul_e_add_one_le_h [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) : 2 * F.e i + 1 ≤ F.h i := by
  obtain ⟨m, hm⟩ := F.e_dvd_h_sub_one i
  have hh_odd : Odd (F.h i) := F.odd_h hodd i
  have he_odd : Odd (F.e i) := F.odd_e hodd i
  have hh_ge2 : 2 ≤ F.h i := F.two_le_h i
  have hh_sub_even : Even (F.h i - 1) := by
    obtain ⟨j, hj⟩ := hh_odd
    exact ⟨j, by omega⟩
  have hm_even : Even m := by
    rw [hm] at hh_sub_even
    rcases Nat.even_mul.mp hh_sub_even with he_even | hm_even
    · exact absurd he_even (Nat.not_even_iff_odd.mpr he_odd)
    · exact hm_even
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.mul_zero] at hm
      omega
    · exact h0
  have hm_ge2 : 2 ≤ m := by
    rcases hm_even with ⟨t, ht⟩
    omega
  have hmul : F.e i * 2 ≤ F.e i * m := Nat.mul_le_mul_left _ hm_ge2
  omega

/-- There is an index whose kernel order is minimal among the family. -/
lemma exists_min_h_index [Finite G] (F : FrobeniusFamily G k) :
    ∃ i : Fin k, ∀ j : Fin k, F.h i ≤ F.h j := by
  classical
  have hkpos : 0 < k := by
    have htwo : 2 ≤ k := F.two_le
    omega
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hkpos⟩, by simp⟩
  rcases Finset.exists_min_image (Finset.univ : Finset (Fin k)) (fun i => F.h i) hne with
    ⟨i, _hi, hmin⟩
  exact ⟨i, fun j => hmin j (by simp)⟩

/-- If `h_i` is chosen minimal, then every other odd coprime kernel order is at
least `h_i + 2`. -/
lemma h_add_two_le_h_of_min [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) {i j : Fin k} (hij : i ≠ j)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) : F.h i + 2 ≤ F.h j := by
  have hcop : Nat.Coprime (F.h i) (F.h j) := by
    simpa [h] using F.coprime_kernel hij
  have hne : F.h i ≠ F.h j := by
    intro heq
    have hone : F.h i = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (by
      rw [← heq])
    have h2 := F.two_le_h i
    omega
  have hi_odd : Odd (F.h i) := F.odd_h hodd i
  have hj_odd : Odd (F.h j) := F.odd_h hodd j
  have hlt : F.h i < F.h j := by
    have hle := hmin j
    omega
  obtain ⟨a, ha⟩ := hi_odd
  obtain ⟨b, hb⟩ := hj_odd
  omega

/-- A minimal kernel order gives the denominator comparison used in the
`𝓑`-sum estimate in Peterfalvi (7.10). -/
lemma h_sub_one_div_h_mul_e_le_h_sub_one_div_e_div_min_add_two [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i j : Fin k}
    (hij : i ≠ j) (hmin : ∀ l : Fin k, F.h i ≤ F.h l) :
    ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)) ≤
      (((F.h j : ℚ) - 1) / (F.e j : ℚ)) / ((F.h i : ℚ) + 2) := by
  have hden_le_nat : F.h i + 2 ≤ F.h j := F.h_add_two_le_h_of_min hodd hij hmin
  have hhj_ge2 : 2 ≤ F.h j := F.two_le_h j
  have hej_ge2 : 2 ≤ F.e j := F.two_le_e j
  have hhj_ne : (F.h j : ℚ) ≠ 0 := by positivity
  have hei_ne : (F.e j : ℚ) ≠ 0 := by positivity
  have hden_ne : (F.h i : ℚ) + 2 ≠ 0 := by positivity
  have hden_le : (F.h i : ℚ) + 2 ≤ (F.h j : ℚ) := by
    exact_mod_cast hden_le_nat
  field_simp [hhj_ne, hei_ne, hden_ne]
  have hsub_nonneg : 0 ≤ (F.h j : ℚ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ F.h j))
  nlinarith

/-- Summed denominator comparison for any set of indices avoiding the chosen
minimal index. -/
lemma sum_h_sub_one_div_h_mul_e_le_sum_h_sub_one_div_e_div_min_add_two [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (s : Finset (Fin k))
    (hs : ∀ j ∈ s, i ≠ j) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ))) ≤
      (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) / ((F.h i : ℚ) + 2) := by
  calc
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)))
        ≤ ∑ j ∈ s, (((F.h j : ℚ) - 1) / (F.e j : ℚ)) /
            ((F.h i : ℚ) + 2) := by
            refine Finset.sum_le_sum fun j hj => ?_
            exact F.h_sub_one_div_h_mul_e_le_h_sub_one_div_e_div_min_add_two
              hodd (hs j hj) hmin
    _ = (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) /
          ((F.h i : ℚ) + 2) := by
        rw [Finset.sum_div]

/-- If the unweighted `𝓑`-sum is bounded by `e_i - 1`, then the weighted sum is
bounded by `(e_i - 1)/(h_i + 2)`, as in Peterfalvi (7.10). -/
lemma sum_h_sub_one_div_h_mul_e_le_e_sub_one_div_min_add_two [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (s : Finset (Fin k))
    (hs : ∀ j ∈ s, i ≠ j)
    (hsum : (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ))) ≤
      ((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2) := by
  have hden_pos : 0 < (F.h i : ℚ) + 2 := by positivity
  have hweighted := F.sum_h_sub_one_div_h_mul_e_le_sum_h_sub_one_div_e_div_min_add_two
    hodd hmin s hs
  have hscaled :
      (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) / ((F.h i : ℚ) + 2) ≤
        ((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2) := by
    exact div_le_div_of_nonneg_right hsum (le_of_lt hden_pos)
  linarith

/-- The explicit right-hand side in Peterfalvi (7.10) is positive for every member
of an odd-order Frobenius family.  This is the arithmetic input used in the final
(7.11) contradiction once `(7.10)` gives the lower bound. -/
lemma lowerBoundTerm_pos [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) :
    0 < ((F.e i : ℚ) - 1) *
      (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
          ((F.e i : ℚ) * (F.h i : ℚ)) +
        2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  have he2 : (2 : ℚ) ≤ (F.e i : ℚ) := by
    exact_mod_cast F.two_le_e i
  have hh2 : 2 * (F.e i : ℚ) + 1 ≤ (F.h i : ℚ) := by
    exact_mod_cast F.two_mul_e_add_one_le_h hodd i
  have hepos : (0 : ℚ) < (F.e i : ℚ) := by linarith
  have hhpos : (0 : ℚ) < (F.h i : ℚ) := by linarith
  have heh : (0 : ℚ) < (F.e i : ℚ) * (F.h i : ℚ) := mul_pos hepos hhpos
  have hh2pos : (0 : ℚ) < (F.h i : ℚ) * ((F.h i : ℚ) + 2) :=
    mul_pos hhpos (by linarith)
  refine mul_pos (by linarith) ?_
  have h1 : 0 ≤
      ((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
        ((F.e i : ℚ) * (F.h i : ℚ)) :=
    div_nonneg (by linarith) (le_of_lt heh)
  have h2 : 0 < (2 : ℚ) / ((F.h i : ℚ) * ((F.h i : ℚ) + 2)) :=
    div_pos (by norm_num) hh2pos
  linarith

/-- The final arithmetic rearrangement in Peterfalvi (7.10). -/
lemma lowerBoundTerm_final_rearrange [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2)) =
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  have he_ne : (F.e i : ℚ) ≠ 0 := by
    have h2 := F.two_le_e i
    positivity
  have hh_ne : (F.h i : ℚ) ≠ 0 := by
    have h2 := F.two_le_h i
    positivity
  have hh2_ne : (F.h i : ℚ) + 2 ≠ 0 := by
    have h2 := F.two_le_h i
    positivity
  field_simp [he_ne, hh_ne, hh2_ne]
  ring

/-- The penultimate estimate in Peterfalvi (7.10) implies the displayed lower
bound for the same index. -/
lemma lowerBoundTerm_of_penultimate [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k)
    (hpen : ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2))) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rw [← F.lowerBoundTerm_final_rearrange i]
  exact hpen

/-- The `𝓑`-sum estimate in Peterfalvi (7.10) gives the penultimate displayed
inequality once the main character-theoretic estimate has isolated the same
`𝓑`-sum. -/
lemma penultimate_of_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hbase :
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)))) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2)) := by
  have hBweighted := F.sum_h_sub_one_div_h_mul_e_le_e_sub_one_div_min_add_two
    hodd hmin B hB_ne hBsum
  linarith

/-- The `𝓑`-sum estimate plus the main character-theoretic estimate gives the
final displayed lower bound for the same minimal index. -/
lemma lowerBoundTerm_of_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hbase :
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)))) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  exact F.lowerBoundTerm_of_penultimate i
    (F.penultimate_of_Bsum_bound hodd hmin B hB_ne hBsum hbase)

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/FrobeniusFamily.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

namespace FrobeniusFamily

variable {k : ℕ}

/-- Direct `𝓑`-sum bridge for Peterfalvi (7.10): an orthogonal integer
combination with diagonal weights `(h_j - 1) / e_j` and norm at most `e_i - 1`
gives exactly the `Bsum_le` field required by `CharacterEstimateData`. -/
lemma Bsum_le_of_orthogonal_integer_decomposition [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k} (B : Finset (Fin k))
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1) :
    (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1 := by
  classical
  have horth' : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        @ite ℂ (j = l) (Classical.propDecidable (j = l))
          (F.BsumWeight j : ℂ) 0 := by
    intro j hj l hl
    by_cases h : j = l
    · simpa [h] using horth j hj l hl
    · simpa [h] using horth j hj l hl
  have hm_nonneg : ∀ j ∈ B, 0 ≤ F.BsumWeight j := by
    intro j _hj
    simpa [BsumWeight] using F.h_sub_one_div_e_nonneg j
  let M : ℚ := (F.e i : ℚ) - 1
  have hM_eq : (M : ℝ) = (F.e i : ℝ) - 1 := by
    dsimp [M]
    norm_num
  have hbound : (ClassFunction.inner Γ Γ).re ≤ (M : ℝ) := by
    rw [hM_eq]
    exact hΓ_bound
  have hrat := sum_rat_weights_le_of_orthogonal_integer_decomposition
    B v x F.BsumWeight Γ Γ₁ M hΓ horth' hΓ₁ hm_nonneg hx_nonzero hbound
  simpa [BsumWeight, M] using hrat

/-- Real-valued input form of `base_estimate_of_reduced_family_inequality`.
This matches the actual codomain of (7.5), (7.8.b), and the norm estimates before
the final rational display of Peterfalvi (7.10). -/
lemma base_estimate_of_real_reduced_family_inequality [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) (B : Finset (Fin k))
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) := by
  have hG_ne : (Nat.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hneg :
      (1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ) =
        -(((Nat.card F.G0 : ℝ) - 1) / (Nat.card G : ℝ)) := by
    field_simp [hG_ne]
    ring
  rw [hneg] at hred
  have hreal :
      1 - (F.e i : ℝ) / (F.h i : ℝ) -
        (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
        (∑ j ∈ B, ((F.h j : ℝ) - 1) /
          ((F.e j : ℝ) * (F.h j : ℝ))) ≤
        ((Nat.card F.G0 : ℝ) - 1) / (Nat.card G : ℝ) := by
    linarith
  rw [ge_iff_le]
  rw [← Rat.cast_le (K := ℝ)]
  norm_num
  have hG0_ncard : (F.G0.ncard : ℝ) = Nat.card F.G0 := by
    exact_mod_cast (Nat.card_coe_set_eq F.G0)
  rw [hG0_ncard]
  linarith

open scoped Classical in
/-- Base-estimate form of Peterfalvi (7.10) obtained directly from the (7.5)
family inequality package and the per-index lower bounds.

This removes the former standalone `hred` input for the base estimate: the caller
only supplies the actual (7.5) family package, the identity contribution on
`G₀`, the selected (7.8.b) lower bound, and the nonnegative outside-`𝓑`
contributions.  The cardinality hypotheses identify the (7.5) local data with
the Frobenius-family notation used in (7.10). -/
lemma base_estimate_of_family71_reduced_estimates
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (B : Finset (Fin k))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hG0sum :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
          ‖(χ : G → ℂ) g‖ ^ 2)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) := by
  classical
  have hratio : ∀ j : Fin k,
      (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ) =
        ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) := by
    intro j
    rw [hA j, hL j]
    exact F.card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h_real j
  have hgood' : ∀ j : Fin k, i ≠ j → j ∉ B →
      (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ) ≤
        P.chiRhoNormSq χ j := by
    intro j hij hjB
    rw [hratio j]
    exact hgood j hij hjB
  have hG0sumP :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ P.G0),
          ‖(χ : G → ℂ) g‖ ^ 2 := by
    rw [hG0]
    exact hG0sum
  have hredP :=
    reduced_inequality_of_estimates P χ hχ i B
      (1 - (F.e i : ℝ) / (F.h i : ℝ))
      hB_ne hG0sumP hi hgood'
  have hredF :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0 := by
    have hredP' :
        ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ) -
            (Nat.card (P.A i) : ℝ) / (Nat.card (P.L i) : ℝ) -
            (∑ j ∈ B,
              (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ))) ≤ 0 := by
      rw [← hG0]
      exact hredP
    have hsum_ratio :
        (∑ j ∈ B, (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ)) =
          ∑ j ∈ B, ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) :=
      Finset.sum_congr rfl (fun j _ => hratio j)
    rwa [hratio i, hsum_ratio] at hredP'
  exact F.base_estimate_of_real_reduced_family_inequality i B hredF

open scoped Classical in
/-- Signed-irreducible variant of
`base_estimate_of_family71_reduced_estimates`.

This packages the exact first inequality in Peterfalvi (7.10):
`(|G₀|-1)/|G| ≥ (|G₀|-χ₁(1)^2)/|G|`, using that the selected `χ₁` is a signed
irreducible character and `1 ∈ G₀`. -/
lemma base_estimate_of_family71_reduced_estimates_of_signed_irreducible
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (B : Finset (Fin k))
    (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_signed : χ = ε • (ξ : ClassFunction G ℂ))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) :=
  F.base_estimate_of_family71_reduced_estimates P χ hχ B hL hA hG0 hB_ne
    (F.one_le_G0_norm_sum_of_signed_irreducible χ ε ξ hε hχ_signed)
    hi hgood

open scoped Classical in
/-- Constructor form of the signed-irreducible `(7.5)` base assembly, retaining
only the `𝓑`-sum bound as a separate final-assembly input. -/
noncomputable def characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_signed : χ = ε • (ξ : ClassFunction G ℂ))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum :
      (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    F.CharacterEstimateData where
  i := i
  hmin := hmin
  B := B
  B_avoids_min := hB_ne
  Bsum_le := hBsum
  base_estimate :=
    F.base_estimate_of_family71_reduced_estimates_of_signed_irreducible
      P χ hχ B ε ξ hε hχ_signed hL hA hG0 hB_ne hi hgood

/-- The named character-estimate data implies the displayed lower bound of
Peterfalvi (7.10). -/
lemma lowerBoundTerm_of_characterEstimateData [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : F.CharacterEstimateData) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rcases hdata with ⟨i, hmin, B, hB_ne, hBsum, hbase⟩
  exact ⟨i, F.lowerBoundTerm_of_Bsum_bound hodd hmin B hB_ne hBsum hbase⟩

end FrobeniusFamily

/-- **Peterfalvi (7.11), displayed-bound form.**  The final contradiction from the
existential lower bound displayed in (7.10).

This isolates the terminal arithmetic of (7.11): any proof of the displayed (7.10) bound,
including the downstream theorem `card_G0_lower_bound` or the conditional §9 assembly lemmas,
can be consumed without duplicating the `G₀ = {1}` contradiction proof. -/
theorem not_trivial_G0_of_lowerBoundTerm [Finite G] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G))
    (hbound :
      ∃ i : Fin k,
        ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
          ((F.e i : ℚ) - 1) *
            (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
                ((F.e i : ℚ) * (F.h i : ℚ)) +
              2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))))
    (hG0 : F.G0 = {(1 : G)}) : False := by
  obtain ⟨i, hi⟩ := hbound
  -- `G₀ = {1}` forces `|G₀| = 1`, so the left-hand side of (7.10) is `0`.
  have hcard : Nat.card F.G0 = 1 := by rw [hG0]; simp
  -- The right-hand side of (7.10) is strictly positive.
  have hRHS := F.lowerBoundTerm_pos hodd i
  -- But the conditional (7.10) lower bound says it is `≤ 0` — contradiction.
  rw [hcard] at hi
  have hlhs : ((1 : ℕ) : ℚ) - 1 = 0 := by norm_num
  rw [hlhs, zero_div] at hi
  linarith [hi, hRHS]

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

-- ===== OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **`ζ − ζ̄` is supported on `A = H^#`** (equal degree).  Both `ζ = ζ_0` and `ζ̄ = ζ_{j₁}` are
induced from `K`, so vanish off `H`, and their common degree `ζ(1) = [L:K]` (real) makes the
difference vanish at `1`.  The `A`-support input to `coherence_hagree_dadeMap` for `hab_supp`. -/
theorem hypothesis78_zeta_sub_conj_support [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    {j₁ : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hj₁ : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁
      = ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj) :
    ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
        - (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) := by
  classical
  -- `ζ(1) = [L:K]` (as in `hypothesis78_zeta_ne_conj`).
  have hdeg : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct (1 : ↥(F.L i))
      = (((F.H i).subgroupOf (F.L i)).index : ℂ) := by
    have hzd : (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 := rfl
    have hz0χ : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta 0
        = Classical.choose (F.exists_sibley_distinguished_char i hodd hnilp C hFrob) := by
      rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0]
      exact (F.sibleyPlacedFamily i hodd hnilp C hFrob).induce_zero_eq
    rw [hzd, hz0χ]
    exact (Classical.choose_spec (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).2
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hj₁, ClassFunction.conj_apply] at hx
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, F.sharpImage_subgroupOf_eq i,
    OddOrder.Peterfalvi.S04.mem_sharp]
  refine ⟨?_, ?_⟩
  · -- `(x:G) ∈ H_i`: else `ζ x = 0`, so the difference vanishes.
    by_contra hxH
    apply hx
    rw [(F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH,
      star_zero, sub_zero]
  · -- `(x:G) ≠ 1`: at `1`, `ζ(1) = [L:K]` is real, so `ζ(1) − star ζ(1) = 0`.
    intro hx1
    apply hx
    rw [OneMemClass.coe_eq_one.mp hx1, hdeg]
    simp

open OddOrder.Peterfalvi.S09.Cert in
/-- **`hab_supp`: `(ζ^ν − ζ̄^ν)` is supported in the Dade support.**  The coherent extension agrees
with the Dade isometry on the equal-degree difference (`coherence_hagree_dadeMap`, `di = 1`), so
`ν(ζ) − ν(ζ̄) = τ(ζ − ζ̄)` is a Dade image, which vanishes off `dadeSupport`
(`map_eq_zero_of_not_mem_dadeSupport`).  The last input to
`zetaImage_cross_eq_zero_of_conjIndex`. -/
theorem hypothesis78_nu_zeta_sub_conj_support [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    {j₁ : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hj₁ne_ind : j₁ ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H)
    (hj₁ : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁
      = ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj) :
    ((F.hypothesis78 i hodd hnilp C hFrob).nu
          ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct)
        - (F.hypothesis78 i hodd hnilp C hFrob).nu
            ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁)).support
      ⊆ (F.hypothesis78 i hodd hnilp C hFrob).hyp76.hyp71.hyp.dadeSupport := by
  classical
  -- `θ_j ≠ 1_K` for `j ≠ ind1H` (via `inj`), giving `S`-membership `ζ_j = Ind θ_j ∈ S`.
  have hθ_ne : ∀ j, j ≠ (F.sibleyPlacedFamily i hodd hnilp C hFrob).ind1H →
      (F.sibleyPlacedFamily i hodd hnilp C hFrob).θ j ≠ trivialIrreducibleCharacter _ := by
    intro j hj h
    refine hj ((F.sibleyPlacedFamily i hodd hnilp C hFrob).inj ?_)
    simp only [h, (F.sibleyPlacedFamily i hodd hnilp C hFrob).triv]
  have hzd_mem : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
      ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
    rw [show (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 from rfl,
      congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0]
    exact ⟨(F.sibleyPlacedFamily i hodd hnilp C hFrob).θ 0,
      hθ_ne 0 (Ne.symm (F.sibleyPlacedFamily i hodd hnilp C hFrob).ind1H_ne_zero), rfl⟩
  have hj₁_mem : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁
      ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
    rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) j₁]
    exact ⟨(F.sibleyPlacedFamily i hodd hnilp C hFrob).θ j₁, hθ_ne j₁ hj₁ne_ind, rfl⟩
  have hsupp' : ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
        - (1 : ℂ) • (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) := by
    rw [one_smul]; exact F.hypothesis78_zeta_sub_conj_support i hodd hnilp C hFrob hj₁
  have hagree := coherence_hagree_dadeMap
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
    (F.coherence i hodd hnilp C hFrob) hzd_mem hj₁_mem
    (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  have heq : (F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct)
      - (F.hypothesis78 i hodd hnilp C hFrob).nu
          ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁)
      = ((F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
            |>.fullDadeIsometryData.toDadeMap)
          ⟨_, (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [F.hypothesis78_nu_eq i hodd hnilp C hFrob,
      ← one_smul ℂ ((F.coherence i hodd hnilp C hFrob).extension
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁))]
    exact hagree.symm
  rw [heq]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  have hdade :=
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
      |>.fullDadeIsometryData.toDadeIsometryData.isDadeMap
  exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)

/-- **The Frobenius-family `hzeta_cross`** (Peterfalvi (7.9), coq `disjoint_coherent_ortho`).  For
two distinct Frobenius members `i ≠ j`, the two distinguished coherent images are orthogonal:
`⟨ζ_i^{ν_i}, ζ_j^{ν_j}⟩ = 0`.  Assembles `zetaImage_cross_eq_zero_of_conjIndex` from all the
Frobenius-level inputs: the coherence over `sourceSet` (`hypothesis78_isCoherent_sourceSet`) with
`ν = coherence.extension` (`hypothesis78_nu_eq`), irreducibility (`hypothesis78_zeta_irreducible`),
the conjugate index (`exists_conjIndex_hypothesis78`), non-realness
(`hypothesis78_zeta_ne_conj`), and the Dade-agreement support
(`hypothesis78_nu_zeta_sub_conj_support`).  The `hzeta_cross` hypothesis of the (7.9)
`conclusion` producers, en route to `card_G0_lower_bound` (7.10). -/
theorem hypothesis79_zetaImage_cross_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i j : Fin k) (hij : i ≠ j) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C_i : Subgroup ↥(F.L i))
    (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)
    [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]
    [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]
    [((F.H j).subgroupOf (F.L j)).Normal]
    (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
    (C_j : Subgroup ↥(F.L j))
    (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j) :
    ClassFunction.inner
        (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).firstZetaImage
        (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).secondZetaImage
      = 0 := by
  obtain ⟨j₁, hj₁ne_ind, hj₁⟩ := F.exists_conjIndex_hypothesis78 i hodd hnilp_i C_i hFrob_i
  obtain ⟨j₂, hj₂ne_ind, hj₂⟩ := F.exists_conjIndex_hypothesis78 j hodd hnilp_j C_j hFrob_j
  exact (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j
      hFrob_j).zetaImage_cross_eq_zero_of_conjIndex
    (F.hypothesis78_isCoherent_sourceSet i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_nu_eq i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_isCoherent_sourceSet j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_nu_eq j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_zeta_irreducible i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_zeta_irreducible j hodd hnilp_j C_j hFrob_j)
    hj₁ne_ind hj₁ (F.hypothesis78_zeta_ne_conj i hodd hnilp_i C_i hFrob_i)
    hj₂ne_ind hj₂ (F.hypothesis78_zeta_ne_conj j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_nu_zeta_sub_conj_support i hodd hnilp_i C_i hFrob_i hj₁ne_ind hj₁)
    (F.hypothesis78_nu_zeta_sub_conj_support j hodd hnilp_j C_j hFrob_j hj₂ne_ind hj₂)

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusFamilyOrthogonality.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section GeneralIndex

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

/-- Every non-principal member of the Sibley induced family is irreducible. -/
theorem hypothesis78_zeta_irreducible_at
    {r : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H) :
    IsIrreducibleCharacter
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r) := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) r]
  have hr_pf : r ≠ pf.ind1H := by
    intro h
    apply hr
    exact h.trans (show pf.ind1H =
      (F.hypothesis78 i hodd hnilp C hFrob).ind1H from rfl)
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hFrob (pf.θ r) (by
    intro htriv
    exact hr_pf (pf.inj (by simp only [htriv, pf.triv])))

/-- Every non-principal coherent image has norm one. -/
theorem hypothesis78_nu_zeta_norm_one_at
    {r : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H) :
    ClassFunction.inner
      ((F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r))
      ((F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r)) = 1 := by
  rw [(F.hypothesis78 i hodd hnilp C hFrob).nu_isometry r r hr hr]
  exact IsIrreducibleCharacter.inner_self_eq_one
    (F.hypothesis78_zeta_irreducible_at i hodd hnilp C hFrob hr)

end GeneralIndex

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_TwoFamiliesParity.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace Hypothesis79

variable {G : Type*} [Group G] [Fintype G]

variable {A₁ : Set G} {L₁ : Subgroup G} [Fintype L₁]

variable [Invertible (Nat.card L₁ : ℂ)]

variable {A₂ : Set G} {L₂ : Subgroup G} [Fintype L₂]

variable [Invertible (Nat.card L₂ : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Peterfalvi (7.9), parity step** at Hypothesis (7.9) generality: `⟨Δ₁, Δ₂⟩` is an even
integer.

`H79.odd_card` makes the ambient group odd, so the parity primitive `cfdot_real_vchar_even`
applies to the two real virtual characters `Δ₁, Δ₂` and gives
`⟨Δ₁, Δ₂⟩ ≡ ⟨Δ₁, 1_G⟩ · ⟨Δ₂, 1_G⟩ (mod 2)`.  The (7.8.a) beta decomposition of the first
member forces `⟨Δ₁, 1_G⟩ = 0` (`delta_orth_one`), so the product vanishes and `⟨Δ₁, Δ₂⟩` is
even.

The coherence data `hcoh₁`/`hnu₁`/`hcoh₂`/`hnu₂` together with `hind₁Z`/`hzeta₁_irr`/
`hind₂Z`/`hzeta₂_irr` are exactly the premises that place `Δ₁, Δ₂` in `ℤ[Irr G]`; they are the
book's "both families are coherent" hypothesis, not a specialization. -/
theorem delta_even
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
    (hzeta₂_irr : IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    (hreal₁ : ClassFunction.IsReal H79.first.delta)
    (hreal₂ : ClassFunction.IsReal H79.second.delta)
    (hBD₁ : H79.first.BetaDecomp) :
    ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z := by
  classical
  -- `Δ ∈ ℤ[Irr G]` for both members, off the two coherences.
  obtain ⟨hδ₁Z, hδ₂Z, -, -⟩ :=
    H79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁Z hzeta₁_irr hind₂Z hzeta₂_irr
  -- Parity primitive on the two real virtual characters.
  obtain ⟨m, a, b, hm, ha, hb, heven⟩ :=
    cfdot_real_vchar_even H79.odd_card hδ₁Z hreal₁ hδ₂Z hreal₂
  -- `a = ⟨Δ₁, 1_G⟩ = 0` (`constOne` and the trivial character coincide definitionally).
  have horth : ClassFunction.inner H79.first.delta
      ((trivialIrreducibleCharacter G : IrreducibleCharacter G) : ClassFunction G ℂ) = 0 :=
    H79.first.delta_orth_one hBD₁
  have ha0 : a = 0 := by exact_mod_cast ha.trans horth
  exact ⟨m, hm.symm, by simpa [ha0] using heven⟩

end Hypothesis79

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusParity.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **`Ind 1_H` is a virtual character** (the `hindZ` input of the (7.9) parity route): the
`ind1H`-indexed member of the `i`-th Sibley family is `Ind_{H_i}^{L_i} 1`, induced from an
irreducible, hence in `ℤ[Irr L_i]`. -/
theorem hypothesis78_ind1H_mem_ZIrr [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
      (F.hypothesis78 i hodd hnilp C hFrob).ind1H ∈ ZIrr ↥(F.L i) := by
  classical
  rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) _]
  exact ClassFunction.induce_mem_ZIrr _
    ((F.sibleyPlacedFamily i hodd hnilp C hFrob).θ _).property.mem_ZIrr

/-- **The (7.9) `hdelta_even` for a Frobenius family**: `⟨Δ_i, Δ_j⟩` is an even integer.

Both residuals are real (`hypothesis78_delta_isReal`) virtual characters
(`delta_mem_ZIrr_…_of_isCoherent`), so the odd-order parity primitive gives
`⟨Δ_i, Δ_j⟩ ≡ ⟨Δ_i, 1_G⟩ · ⟨Δ_j, 1_G⟩ (mod 2)`, and `⟨Δ_i, 1_G⟩ = 0` (`delta_orth_one`). -/
theorem hypothesis79_delta_even [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i j : Fin k) (hij : i ≠ j) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C_i : Subgroup ↥(F.L i))
    (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)
    [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]
    [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]
    [((F.H j).subgroupOf (F.L j)).Normal]
    (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
    (C_j : Subgroup ↥(F.L j))
    (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j) :
    ∃ z : ℤ,
      ClassFunction.inner
          (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).first.delta
          (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).second.delta
        = (z : ℂ) ∧ Even z := by
  classical
  -- The whole parity argument is the generic `Hypothesis79.delta_even`
  -- (`S09_TwoFamiliesParity`); this layer only supplies the Frobenius-side producers.
  exact (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).delta_even
    (F.hypothesis78_isCoherent_sourceSet i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_nu_eq i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_isCoherent_sourceSet j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_nu_eq j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_ind1H_mem_ZIrr i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_zeta_irreducible i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_ind1H_mem_ZIrr j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_zeta_irreducible j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_delta_isReal i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_delta_isReal j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_betaDecomp i hodd hnilp_i C_i hFrob_i)

/-- **Peterfalvi (7.9) for a Frobenius family**: for distinct members `i ≠ j`,
`⟨β_i, ζ_j^{ν_j}⟩ ≠ 0` or `⟨β_j, ζ_i^{ν_i}⟩ ≠ 0`.

Assembles the parity route `conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity`
from the Frobenius-level suppliers: the Sibley coherence over the source set with `ν` its
extension, `Ind 1_H ∈ ℤ[Irr L]`, irreducibility of the distinguished `ζ`, the (7.8.a) beta
decompositions, the cross orthogonality `⟨ζ_i^ν, ζ_j^ν⟩ = 0`, and the even parity of
`⟨Δ_i, Δ_j⟩` (`hypothesis79_delta_even`).  This is the `hbeta_ne` source for the good-index
norm estimates in the (7.10) assembly. -/
theorem hypothesis79_conclusion [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i j : Fin k) (hij : i ≠ j) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C_i : Subgroup ↥(F.L i))
    (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)
    [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]
    [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]
    [((F.H j).subgroupOf (F.L j)).Normal]
    (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
    (C_j : Subgroup ↥(F.L j))
    (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j) :
    (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).conclusion := by
  classical
  exact (F.hypothesis79 i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j
      hFrob_j).conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    (F.hypothesis78_isCoherent_sourceSet i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_nu_eq i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_isCoherent_sourceSet j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_nu_eq j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_ind1H_mem_ZIrr i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_zeta_irreducible i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_ind1H_mem_ZIrr j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_zeta_irreducible j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis78_betaDecomp i hodd hnilp_i C_i hFrob_i)
    (F.hypothesis78_betaDecomp j hodd hnilp_j C_j hFrob_j)
    (F.hypothesis79_zetaImage_cross_eq_zero i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j)
    (F.hypothesis79_delta_even i j hij hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j)

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalCoefficient

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Fintype ↥((F.H i).subgroupOf (F.L i))]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
/-- The zeroth degree ratio in the concrete Frobenius family is one. -/
theorem hypothesis78_d_zero_eq_one :
    (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d 0 = 1 := by
  have : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  let H78 := localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hz0 : H78.hyp76.zeta 0 (1 : ↥(F.L i)) ≠ 0 := by
    rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0]
    exact Cert.induce_apply_one_ne_zero ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  exact (mul_right_cancel₀ hz0 (by
    rw [one_mul]
    exact H78.hyp76.zeta_one_eq_d_mul 0)).symm

end LocalCoefficient

end FrobeniusFamily

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section FamilyRealization

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- The (7.9) parity alternative makes every selected projection coefficient
nonzero whenever the reverse cross coefficient vanishes. -/
theorem exists_weightedGammaDecomposition_of_reverse_eq_zero
    (i : Fin k) (B : Finset (Fin k))
    (hB : ∀ j ∈ B, i ≠ j)
    (hreverse : ∀ j ∈ B,
      ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob j)
        (F.distinguishedNuAt hodd hnilp C hFrob i) = 0) :
    ∃ x : Fin k → ℤ, ∃ Γ₁ : ClassFunction G ℂ,
      (∀ j, ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob i)
        (F.distinguishedNuAt hodd hnilp C hFrob j) = (x j : ℂ)) ∧
      (∀ j ∈ B, ∀ l ∈ B,
        ClassFunction.inner
          (F.weightedNuSumAt hodd hnilp C hFrob j)
          (F.weightedNuSumAt hodd hnilp C hFrob l) =
            if j = l then (F.BsumWeight j : ℂ) else 0) ∧
      F.gammaAt hodd hnilp C hFrob i =
        (∑ j ∈ B,
          (((x j : ℝ) : ℂ) • F.weightedNuSumAt hodd hnilp C hFrob j)) + Γ₁ ∧
      (∀ j ∈ B, ClassFunction.inner Γ₁
        (F.weightedNuSumAt hodd hnilp C hFrob j) = 0) ∧
      ∀ j ∈ B, x j ≠ 0 := by
  classical
  obtain ⟨x, Γ₁, hx, horth, hdecomp, hΓ₁⟩ :=
    F.exists_weightedGammaDecomposition hodd hnilp C hFrob i B hB
  refine ⟨x, Γ₁, hx, horth, hdecomp, hΓ₁, ?_⟩
  intro j hj
  let : Fintype ↥(F.L i) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(F.L i) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L i)).ne')
  let : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  let : Invertible
      (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : ((F.H i).subgroupOf (F.L i)).Normal := (hFrob i).isNormal
  let : Fintype ↥(F.L j) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  let : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  let : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
  have hc :=
    F.hypothesis79_conclusion i j (hB j hj) hodd
      (hnilp i) (C i) (hFrob i) (hnilp j) (C j) (hFrob j)
  change
    ClassFunction.inner
        (F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).beta
        ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).nu
          ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).hyp76.zeta 0)) ≠ 0 ∨
      ClassFunction.inner
        (F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).beta
        ((F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).nu
          ((F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).hyp76.zeta 0)) ≠ 0
    at hc
  have hreverse' :
      ClassFunction.inner
        (F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).beta
        ((F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).nu
          ((F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).hyp76.zeta 0)) = 0 := by
    simpa [betaAt, distinguishedNuAt] using hreverse j hj
  have hforward :
      ClassFunction.inner
        (F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).beta
        ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).nu
          ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).hyp76.zeta 0)) ≠ 0 := by
    rcases hc with h | h
    · exact h
    · exact False.elim (h hreverse')
  have hforwardAt :
      ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob i)
        (F.distinguishedNuAt hodd hnilp C hFrob j) ≠ 0 := by
    simpa [betaAt, distinguishedNuAt] using hforward
  intro hx0
  apply hforwardAt
  simpa [hx0] using hx j

theorem mem_reverseCoefficientZeroIndices_iff (i j : Fin k) :
    j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i ↔
      i ≠ j ∧ ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob j)
        (F.distinguishedNuAt hodd hnilp C hFrob i) = 0 := by
  classical
  simp [reverseCoefficientZeroIndices]

/-- Consumer-ready form of the (7.10) Gamma decomposition on Peterfalvi's
concrete set B.  It exposes exactly the orthogonality, decomposition, residual
orthogonality, and nonzero coefficients required by the B-sum norm bridge. -/
theorem exists_weightedGammaDecomposition_on_reverseCoefficientZeroIndices
    (i : Fin k) :
    ∃ x : Fin k → ℤ, ∃ Γ₁ : ClassFunction G ℂ,
      (∀ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
        ∀ l ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
          ClassFunction.inner
            (F.weightedNuSumAt hodd hnilp C hFrob j)
            (F.weightedNuSumAt hodd hnilp C hFrob l) =
              if j = l then (F.BsumWeight j : ℂ) else 0) ∧
      F.gammaAt hodd hnilp C hFrob i =
        (∑ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
          (((x j : ℝ) : ℂ) • F.weightedNuSumAt hodd hnilp C hFrob j)) + Γ₁ ∧
      (∀ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
        ClassFunction.inner Γ₁
          (F.weightedNuSumAt hodd hnilp C hFrob j) = 0) ∧
      ∀ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
        x j ≠ 0 := by
  classical
  let B := F.reverseCoefficientZeroIndices hodd hnilp C hFrob i
  have hB : ∀ j ∈ B, i ≠ j := by
    intro j hj
    exact (F.mem_reverseCoefficientZeroIndices_iff
      hodd hnilp C hFrob i j).mp hj |>.1
  have hreverse : ∀ j ∈ B,
      ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob j)
        (F.distinguishedNuAt hodd hnilp C hFrob i) = 0 := by
    intro j hj
    exact (F.mem_reverseCoefficientZeroIndices_iff
      hodd hnilp C hFrob i j).mp hj |>.2
  obtain ⟨x, Γ₁, _hx, horth, hdecomp, hΓ₁, hx_nonzero⟩ :=
    F.exists_weightedGammaDecomposition_of_reverse_eq_zero
      hodd hnilp C hFrob i B hB hreverse
  exact ⟨x, Γ₁, horth, hdecomp, hΓ₁, hx_nonzero⟩

end FamilyRealization

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusGammaNormEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalGammaNorm

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

/-- The induced principal member has norm square equal to the Frobenius
complement index.  This is the first source inner product in (7.8.b). -/
theorem hypothesis78_ind1H_inner_self_eq_complementIndex :
    ClassFunction.inner
      ((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).hyp76.zeta
        (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).ind1H)
      ((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).hyp76.zeta
        (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).ind1H) =
      ((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).complementIndex : ℂ) := by
  classical
  let H78 := localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hz_ind : H78.hyp76.zeta H78.ind1H =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (trivialIrreducibleCharacter
          ↥((F.H i).subgroupOf (F.L i)) : ClassFunction _ ℂ) := by
    rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) H78.ind1H,
      show H78.ind1H = pf.ind1H from rfl, pf.triv]
  rw [Cert.complementIndex_eq_subgroupOf_index H78]
  change ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
      (H78.hyp76.zeta H78.ind1H) =
    (((F.H i).subgroupOf (F.L i)).index : ℂ)
  rw [hz_ind]
  exact Cert.induce_trivialChar_normSq_eq_index
    ((F.H i).subgroupOf (F.L i))

/-- The distinguished non-principal induced character is orthogonal to the
induced principal member.  This is the cross term in the source norm of
`Ind 1_H - zeta`. -/
theorem hypothesis78_zetaDistinct_inner_ind1H_eq_zero :
    ClassFunction.inner
      ((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).hyp76.zeta
        (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).zetaDistinct)
      ((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).hyp76.zeta
        (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).ind1H) = 0 := by
  classical
  let H78 := localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  rw [show H78.zetaDistinct = 0 from rfl,
    congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0,
    congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) H78.ind1H,
    show H78.ind1H = pf.ind1H from rfl]
  exact Cert.induce_family_orthogonal_of_injective
    ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj 0 pf.ind1H
      (Ne.symm pf.ind1H_ne_zero)

/-- The source norm computation in (7.8.b), transported through the Dade
isometry: the concrete `beta` has norm square `e + 1`. -/
theorem hypothesis78_betaNormSq_eq_complementIndex_add_one :
    (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).betaNormSq =
      ((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).complementIndex : ℝ) + 1 := by
  let H78 := localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  exact H78.betaNormSq_eq_complementIndex_add_one_of_zeta_ind_orthogonal_of_zeta_irreducible
    (F.hypothesis78_ind1H_inner_self_eq_complementIndex i hodd hnilp C hFrob)
    (F.hypothesis78_zetaDistinct_inner_ind1H_eq_zero i hodd hnilp C hFrob)
    (F.hypothesis78_zeta_irreducible i hodd hnilp C hFrob)

/-- The concrete beta decomposition has Peterfalvi's orthogonal norm
expansion.  The weighted-sum norm was evaluated by the induced-family degree
sum in `hypothesis78_weightedNuSum_inner_self_eq`. -/
theorem hypothesis78_betaNormSq_eq_orthogonal_expand :
    (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).betaNormSq =
      2 +
        ((((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).kernelOrder : ℝ) - 1) /
          ((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).complementIndex : ℝ)) *
          ((localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).a : ℝ) ^ 2 -
        2 * ((localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).a : ℝ) +
          (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).gammaNormSq
            (localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob) := by
  let H78 := localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  let hBD := localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  let : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  have hzeta_norm :
      ClassFunction.inner
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
    F.hypothesis78_nu_zeta_norm_one_at i hodd hnilp C hFrob
      H78.zetaDistinct_ne_ind1H
  have hweighted_zeta :
      ClassFunction.inner H78.weightedNuSum
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 := by
    have h := F.hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
      i hodd hnilp C hFrob (r := H78.zetaDistinct)
        H78.zetaDistinct_ne_ind1H
    rw [show H78.zetaDistinct = 0 from rfl,
      F.hypothesis78_d_zero_eq_one i hodd hnilp C hFrob] at h
    exact h
  have hweighted_norm :
      ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
        ((((H78.kernelOrder : ℝ) - 1) /
          (H78.complementIndex : ℝ)) : ℂ) := by
    have h := F.hypothesis78_weightedNuSum_inner_self_eq
      i hodd hnilp C hFrob
    have hh : H78.kernelOrder = F.h i := rfl
    have he : H78.complementIndex = F.e i := rfl
    rw [hh, he]
    convert h using 1
    all_goals norm_num
  exact H78.betaNormSq_eq_of_weightedNuSum_norm hBD
    hzeta_norm hweighted_zeta hweighted_norm

/-- Exact residual norm formula underlying the upper bound in (7.8.b). -/
theorem hypothesis78_gammaNormSq_eq :
    (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).gammaNormSq
        (localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob) =
      ((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).complementIndex : ℝ) - 1 -
        ((localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).kernelOrder : ℝ) *
          (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).normQuadraticCorrection
            (localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob) := by
  let H78 := localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  let hBD := localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  exact H78.gammaNormSq_eq_of_betaNormSq_expand hBD
    (F.hypothesis78_betaNormSq_eq_complementIndex_add_one
      i hodd hnilp C hFrob)
    (F.hypothesis78_betaNormSq_eq_orthogonal_expand
      i hodd hnilp C hFrob)

omit [((F.H i).subgroupOf (F.L i)).Normal] in
/-- Odd-order Frobenius cardinalities give the small-index inequality
`2e + 1 ≤ h` used in (7.8.b). -/
theorem hypothesis78_smallIndex_at :
    (localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).smallIndex := by
  let H78 := localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  have hoddL : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  have hKodd : Odd (Nat.card ↥((F.H i).subgroupOf (F.L i))) :=
    hoddL.of_dvd_nat
      (Subgroup.card_subgroup_dvd_card ((F.H i).subgroupOf (F.L i)))
  have hCodd : Odd (Nat.card ↥C) :=
    hoddL.of_dvd_nat (Subgroup.card_subgroup_dvd_card C)
  have hcompl :
      Nat.card ↥((F.H i).subgroupOf (F.L i)) * Nat.card ↥C =
        Nat.card ↥(F.L i) :=
    hFrob.isComplement.card_mul_card
  have hKcard : Nat.card ↥((F.H i).subgroupOf (F.L i)) =
      Nat.card ↥(F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hfrob := hFrob.two_mul_card_complement_add_one_le_card_kernel
    hKodd hCodd hFrob.ne_bot_kernel
  change 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
  have hke : H78.kernelOrder =
      Nat.card ↥((F.H i).subgroupOf (F.L i)) := by
    change Nat.card ↥(F.H i) =
      Nat.card ↥((F.H i).subgroupOf (F.L i))
    exact hKcard.symm
  have hce : H78.complementIndex = Nat.card ↥C := by
    change Nat.card ↥(F.L i) / Nat.card ↥(F.H i) = Nat.card ↥C
    rw [← hKcard, ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
  rw [hke, hce]
  exact hfrob

/-- **Peterfalvi (7.8.b), concrete residual bound.**  The Gamma term in the
canonical beta decomposition of the `i`-th Frobenius member satisfies
`‖Gamma_i‖² ≤ e_i - 1`. -/
theorem hypothesis78_gamma_inner_self_re_le :
    (ClassFunction.inner
      (localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).Gamma
      (localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob).Gamma).re ≤
        (F.e i : ℝ) - 1 := by
  let H78 := localH78_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  let hBD := localBD_S09_FrobeniusGammaNormEstimate F i hodd hnilp C hFrob
  have hlocal := H78.gammaNormSq_le_of_normQuadraticCorrection_eq hBD
    (F.hypothesis78_gammaNormSq_eq i hodd hnilp C hFrob)
    (F.hypothesis78_smallIndex_at i hodd hnilp C hFrob)
  have he : H78.complementIndex = F.e i := rfl
  change H78.gammaNormSq hBD ≤ (F.e i : ℝ) - 1
  simpa [he] using hlocal

end LocalGammaNorm

section FamilyGammaNorm

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- Family-wide form of the concrete (7.8.b) residual bound. -/
theorem gammaAt_inner_self_re_le (i : Fin k) :
    (ClassFunction.inner
      (F.gammaAt hodd hnilp C hFrob i)
      (F.gammaAt hodd hnilp C hFrob i)).re ≤
        (F.e i : ℝ) - 1 := by
  classical
  let : Fintype ↥(F.L i) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(F.L i) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L i)).ne')
  let : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  let : Invertible
      (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : ((F.H i).subgroupOf (F.L i)).Normal := (hFrob i).isNormal
  simpa only [gammaAt] using
    (F.hypothesis78_gamma_inner_self_re_le
      i hodd (hnilp i) (C i) (hFrob i))

end FamilyGammaNorm

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusBsumEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section FamilyBsum

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- Peterfalvi's concrete set `B` contains only indices different from the
selected member. -/
theorem reverseCoefficientZeroIndices_avoids (i : Fin k) :
    ∀ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i, i ≠ j := by
  intro j hj
  exact (F.mem_reverseCoefficientZeroIndices_iff
    hodd hnilp C hFrob i j).mp hj |>.1

/-- **Peterfalvi (7.10), concrete B-sum bound.**  On the set of other family
members whose reverse coefficient vanishes, the weighted Gamma projection and
`‖Gamma_i‖² ≤ e_i - 1` give
`sum_{j in B} (h_j - 1) / e_j ≤ e_i - 1`. -/
theorem reverseCoefficientZeroIndices_Bsum_le (i : Fin k) :
    (∑ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
      ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1 := by
  classical
  let B := F.reverseCoefficientZeroIndices hodd hnilp C hFrob i
  obtain ⟨x, Γ₁, horth, hΓ, hΓ₁, hx_nonzero⟩ :=
    F.exists_weightedGammaDecomposition_on_reverseCoefficientZeroIndices
      hodd hnilp C hFrob i
  exact F.Bsum_le_of_orthogonal_integer_decomposition B
    (F.weightedNuSumAt hodd hnilp C hFrob) x
    (F.gammaAt hodd hnilp C hFrob i) Γ₁
    hΓ horth hΓ₁ hx_nonzero
    (F.gammaAt_inner_self_re_le hodd hnilp C hFrob i)

end FamilyBsum

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusGoodIndexEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section GoodIndex

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- Consumer form for Peterfalvi's complement of `B`: an index distinct from
the selected member and not in the vanishing-coefficient set satisfies the
(7.8.c) good-index lower bound. -/
theorem reverseCoefficientZeroIndices_good_bound (i j : Fin k)
    (hij : i ≠ j)
    (hjB : j ∉ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i) :
    ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) j := by
  apply F.distinguishedNuAt_chiRhoNormSq_ge_of_reverseCoefficient_ne
    hodd hnilp C hFrob i j hij
  intro hzero
  apply hjB
  exact (F.mem_reverseCoefficientZeroIndices_iff
    hodd hnilp C hFrob i j).2 ⟨hij, hzero⟩

end GoodIndex

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/KernelNilpotent.lean =====
namespace OddOrder.Isaacs.Ch06

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open scoped Pointwise

section

/-- **Isaacs Thm 6.24** (p. 196, action form): the target of a Frobenius action of a
nontrivial finite group is nilpotent (Thompson).

The actor is first replaced by a prime-order subgroup
(`IsFrobeniusAction.actorSubgroup`), then
`isNilpotent_of_isFrobeniusAction_of_prime_card_aux` runs the book's induction. -/
theorem isNilpotent_of_isFrobeniusAction
    {A N : Type*} [Group A] [Finite A] [Nontrivial A] [Group N] [Finite N]
    [MulDistribMulAction A N] (hFrob : IsFrobeniusAction A N) :
    Group.IsNilpotent N := by
  classical
  have h1 : Nat.card A ≠ 1 := (Finite.one_lt_card_iff_nontrivial.mpr ‹_›).ne'
  have hp : (Nat.card A).minFac.Prime := Nat.minFac_prime h1
  have : Fact (Nat.card A).minFac.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := A) (Nat.card A).minFac (Nat.minFac_dvd _)
  have hcard : Nat.card ↥(Subgroup.zpowers x) = (Nat.card A).minFac := by
    rw [Nat.card_zpowers, hx]
  exact isNilpotent_of_isFrobeniusAction_of_prime_card_aux hp hcard (Nat.card N) N le_rfl
    (hFrob.actorSubgroup _)

/-- **Isaacs Thm 6.24** (p. 196, subgroup-pair form): the kernel of a finite Frobenius
group is nilpotent (Thompson). -/
theorem IsFrobeniusGroup.isNilpotent_kernel
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G}
    (h : IsFrobeniusGroup G N A) : Group.IsNilpotent ↥N := by
  let : N.Normal := h.isNormal
  let : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr h.ne_bot_kernel
  have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr h.ne_bot_complement
  exact isNilpotent_of_isFrobeniusAction h.toFrobeniusAction

end

end OddOrder.Isaacs.Ch06

-- ===== OddOrder/Peterfalvi/S09_FrobeniusCardG0LowerBound.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

open scoped Classical in
/-- The character-estimate package in Peterfalvi (7.10), assembled from the
canonical coherent image at a member of minimal kernel order. -/
noncomputable def characterEstimateData_of_isNilpotent
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hnilp : ∀ j : Fin k,
      Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j))) :
    F.CharacterEstimateData := by
  let C : ∀ j : Fin k, Subgroup ↥(F.L j) :=
    fun j => Classical.choose (F.isFrobenius j)
  have hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j) :=
    fun j => Classical.choose_spec (F.isFrobenius j)
  let hminExists := F.exists_min_h_index
  let i : Fin k := Classical.choose hminExists
  have hmin : ∀ j : Fin k, F.h i ≤ F.h j :=
    Classical.choose_spec hminExists
  letI : Fintype ↥(F.L i) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L i) : ℂ) :=
    (F.familyHypothesis71).invertibleL i
  letI : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : ((F.H i).subgroupOf (F.L i)).Normal := (hFrob i).isNormal
  let H78 := F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)
  let chi := F.distinguishedNuAt hodd hnilp C hFrob i
  let B := F.reverseCoefficientZeroIndices hodd hnilp C hFrob i
  let hsig :=
    H78.exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet i hodd (hnilp i) (C i) (hFrob i))
      (F.hypothesis78_nu_eq i hodd (hnilp i) (C i) (hFrob i))
      (F.hypothesis78_zeta_irreducible i hodd (hnilp i) (C i) (hFrob i))
  let eps : ℤ := Classical.choose hsig
  let hsigXi := Classical.choose_spec hsig
  let xi : IrreducibleCharacter G := Classical.choose hsigXi
  have hsigned := Classical.choose_spec hsigXi
  have heps : eps = 1 ∨ eps = -1 := hsigned.1
  have hsigned := hsigned.2
  have hzetaDistinct : H78.zetaDistinct = 0 := rfl
  have hsignedZero :
      H78.nu (H78.hyp76.zeta 0) = eps • (xi : ClassFunction G ℂ) := by
    simpa only [hzetaDistinct, eps, xi] using hsigned
  have hchi_signed : chi = eps • (xi : ClassFunction G ℂ) := by
    change H78.nu (H78.hyp76.zeta 0) = eps • (xi : ClassFunction G ℂ)
    exact hsignedZero
  have hzero_ne : (0 : Fin (H78.hyp76.n + 1)) ≠ H78.ind1H := by
    rw [← hzetaDistinct]
    exact H78.zetaDistinct_ne_ind1H
  have hchi_norm : ClassFunction.inner chi chi = 1 := by
    change ClassFunction.inner (H78.nu (H78.hyp76.zeta 0))
      (H78.nu (H78.hyp76.zeta 0)) = 1
    exact F.hypothesis78_nu_zeta_norm_one_at
      i hodd (hnilp i) (C i) (hFrob i) hzero_ne
  have hL : ∀ j : Fin k, (F.familyHypothesis71).L j = F.L j :=
    fun _ => rfl
  have hA : ∀ j : Fin k,
      (F.familyHypothesis71).A j = ((F.H j : Set G) \ ({1} : Set G)) :=
    fun _ => rfl
  have hG0 : (F.familyHypothesis71).G0 = F.G0 := by
    ext g
    change (∀ j, g ∉ (F.hypothesis71 j).hyp.dadeSupport) ↔
      ∀ j, g ∉ F.kernelSpread j
    constructor
    · intro hg j hj
      exact hg j ((F.dadeSupport_hypothesis71_eq_kernelSpread j).symm ▸ hj)
    · intro hg j hj
      exact hg j (F.dadeSupport_hypothesis71_eq_kernelSpread j ▸ hj)
  exact F.characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible
    F.familyHypothesis71 chi hchi_norm hmin B eps xi heps hchi_signed hL hA hG0
    (F.reverseCoefficientZeroIndices_avoids hodd hnilp C hFrob i)
    (F.reverseCoefficientZeroIndices_Bsum_le hodd hnilp C hFrob i)
    (F.distinguishedNuAt_chiRhoNormSq_ge hodd hnilp C hFrob i)
    (F.reverseCoefficientZeroIndices_good_bound hodd hnilp C hFrob i)

end FrobeniusFamily

variable {G : Type*} [Group G]

/-- Thompson's theorem (Isaacs Thm 6.24) applied to a `FrobeniusFamily`: every
member's kernel is nilpotent.

Peterfalvi derives this inside the proof of (7.10) ("By a theorem of Thompson"),
so it is *not* a hypothesis of the book statement; condition (7.10)(a) — each
`L i` is a Frobenius group with kernel `H i` — already forces it. -/
theorem FrobeniusFamily.isNilpotent_kernel [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (j : Fin k) :
    Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)) := by
  obtain ⟨C, hC⟩ := F.isFrobenius j
  exact hC.isNilpotent_kernel

/-- **Peterfalvi (7.10).** Under `FrobeniusFamily` with `G` of odd order there is
an index `i` for which, writing `e = e_i` and `h = h_i`,

`(|G₀| - 1)/|G| ≥ (e - 1) · ((h - 2e - 1)/(e·h) + 2/(h·(h+2)))`.

The nilpotence of the Frobenius kernels — the Sibley-coherence prerequisite — is
**not** a hypothesis: it is derived from condition (7.10)(a) via Thompson's
theorem (`FrobeniusFamily.isNilpotent_kernel`), exactly as the book does. -/
theorem card_G0_lower_bound [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact F.lowerBoundTerm_of_characterEstimateData hodd
    (F.characterEstimateData_of_isNilpotent hodd F.isNilpotent_kernel)

/-- **Peterfalvi (7.11).** No odd-order Frobenius family can have its conjugate
kernel spreads cover every nonidentity element.

As in (7.10), kernel nilpotence is derived from (7.10)(a) by Thompson's theorem
rather than assumed. -/
theorem not_trivial_G0 [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hG0 : F.G0 = {(1 : G)}) : False := by
  exact not_trivial_G0_of_lowerBoundTerm F hodd
    (card_G0_lower_bound F hodd) hG0

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/SigmaCovers.lean =====
namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG 14.7, `|K| ≠ |K*|`**: the two κ-Hall factors of a type-`P` dual pair have distinct orders.
They are coprime (`coprime_card_kappaHall_Kstar`) and `|K| > 1` (`card_kappaHall_ne_one`), so
equality
would force `|K| = 1`. -/
theorem card_kappaHall_ne_card_Kstar [Finite G] {M K Kstar : Subgroup G} (hP : IsTypeP M)
    (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Nat.card ↥K ≠ Nat.card ↥Kstar := by
  intro heq
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Kstar) :=
    coprime_card_kappaHall_Kstar hKM hK hKstar
  rw [← heq, Nat.Coprime, Nat.gcd_self] at hcop
  exact card_kappaHall_ne_one hP hKM hK hcop

end OddOrder.BG.Ch4.S14

-- ===== OddOrder/Peterfalvi/S14_MaximalI/TypeICovering.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section Theorem1217

variable [Finite G]

/-- **Peterfalvi (12.17), non-existence half**: in a minimal simple group of odd order, not every
maximal subgroup is of type I.

*Proof.*  Assume otherwise.  The §8 covering theory (`exists_typeICovering`) provides the family of
conjugacy-class representatives `reps i` of the maximal subgroups, whose kernels `(reps i)_F` are
pairwise-coprime TI-subsets covering `G#`.  Each `reps i` is a Frobenius group with kernel
`(reps i)_F` by (12.7) (`typeI_frobenius`) and equals its own `N_G((reps i)_F)`
(`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`), so these data assemble into a Frobenius
family in the sense of (7.10) (`S09.FrobeniusFamily`).  The covering makes `G₀ = {1}`, contradicting
(7.11) (`S09.not_trivial_G0`). -/
theorem not_all_maximal_typeI (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M) :
    ¬ (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) := by
  intro hall
  obtain ⟨cov⟩ := exists_typeICovering hG hnoV hall
  let F : OddOrder.Peterfalvi.S09.FrobeniusFamily G cov.k :=
    { L := cov.reps
      H := fun i => maxNilpotentNormalHall (cov.reps i)
      two_le := cov.two_le
      kernel_le := fun i => OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (cov.reps i)
      isFrobenius := fun i => by
        obtain ⟨fd, -⟩ := typeI_frobenius hG hnoV (cov.reps_maximal i) (hall _ (cov.reps_maximal i))
        refine ⟨fd.complement, ?_⟩
        rw [← fd.typeI.typeF.H_eq]
        exact fd.frobenius
      normalizer_eq := fun i =>
        maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG (cov.reps_maximal i) (by
          obtain ⟨td⟩ := hall _ (cov.reps_maximal i)
          rw [← td.typeF.H_eq]
          exact td.typeF.H_nontrivial)
      isTI := cov.isTI
      coprime_kernel := cov.coprime }
  have hG0 : F.G0 = {(1 : G)} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨F.one_mem_G0, fun x hx => ?_⟩
    by_contra hx1
    obtain ⟨i, g, hg⟩ := cov.covers x hx1
    exact (F.mem_G0_iff.mp hx) i ⟨g, hg⟩
  -- Kernel nilpotence is no longer supplied here: (7.11) derives it from condition (7.10)(a)
  -- via Thompson's theorem (`FrobeniusFamily.isNilpotent_kernel`), as the book does.
  exact OddOrder.Peterfalvi.S09.not_trivial_G0 F hG.odd hG0

end Theorem1217

/-- **Peterfalvi (12.17)**: the all-type-I case of Theorem (8.8) is impossible, so the case-(b)
data of (8.8) exists.  Immediate from the (8.8) dichotomy (`theorem88_dichotomy`) and the
non-existence half `not_all_maximal_typeI`. -/
theorem theorem88_caseB_holds [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M) :
    Nonempty (OddOrder.Peterfalvi.S10.Theorem88CaseBData G) :=
  (theorem88_dichotomy hG).resolve_left (not_all_maximal_typeI hG hnoV)

end OddOrder.Peterfalvi.S14

-- ===== OddOrder/FeitThompsonSection16Core.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

/-- **Canonical type-`P` maximal pair data** (issue 7005): for a minimal simple group of odd order,
there is a type-`P` dual pair `S, T` together with the full κ-Hall witness data of BG Theorem 14.7
(`typeP_duality`).  This is the data an *enriched* `Section16MaximalPair` carries so the type-`P`
structure producer can discharge the pairing `S ∩ T = K × K*`: the intrinsic covering axiom
(`theorem88_caseB`) fixes the partner only up to conjugacy, so an arbitrary maximal pair need not
have `S ∩ T` a cyclic product (the type-emptiness obstruction of the bare producer).

Mirrors the dichotomy branch of `theoremI_nilpotentHall_conjugacy_and_type_dichotomy`, additionally
exposing the canonical partner `T = Mstar` and its κ-Hall factors `K, K*` (dropped by the
dichotomy).  Case (a) of (8.8) (every maximal Type I) is excluded by Peterfalvi (12.17). -/
theorem _root_.solution {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M) :
    ∃ S T K Kstar : Subgroup G,
      S ∈ maximalSubgroups G ∧ T ∈ maximalSubgroups G ∧ S ≠ T ∧
      IsTypeNonI S ∧ IsTypeNonI T ∧ (IsTypeII S ∨ IsTypeII T) ∧
      (∀ M : Subgroup G, M ∈ maximalSubgroups G →
        IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨ (∃ g : G, MulAut.conj g • M = T)) ∧
      K ≤ S ∧ Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S) ∧
      Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) ∧
      BG.Ch4.S14.IsTypeP S ∧ BG.Ch4.S14.IsTypeP T ∧ ¬ BG.Ch4.S14.IsConjugateSubgroup S T ∧
      Kstar ≤ T ∧ Ch03.IsHallSubgroup (BG.Ch4.S14.kappa T) (Kstar.subgroupOf T) ∧
      K = BG.Ch3.S10.Msigma T ⊓ Subgroup.centralizer (Kstar : Set G) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ Nat.card ↥K < Nat.card ↥Kstar := by
  classical
  have notTypeI_imp_typeP : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
      ¬ IsTypeI N → BG.Ch4.S14.IsTypeP N := by
    intro N hN hnotI
    have hiff := (BG.Ch4.S16.proposition_type_classification hG hN).1
    have hnotF : ¬ BG.Ch4.S14.IsTypeF N := fun hF => hnotI (hiff.mpr hF)
    rw [BG.Ch4.S14.IsTypeP, Set.nonempty_iff_ne_empty]
    exact fun he => hnotF he
  have typeP_imp_nonI : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
      BG.Ch4.S14.IsTypeP N → IsTypeNonI N := by
    intro N hN hP
    obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ := BG.Ch4.S16.proposition_type_classification hG hN
    by_cases hk : BG.Ch4.S14.kappa N = BG.Ch4.S14.sigmaComplementPrimes N
    · have hP1 : BG.Ch4.S14.IsTypeP1 N := ⟨hP, hk⟩
      by_cases hMF : BG.Ch4.S15.MF N = BG.Ch3.S10.Msigma N
      · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
      · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
        · exact Or.inr (Or.inl hIII)
        · exact Or.inr (Or.inr (Or.inl hIV))
    · exact Or.inl (hbII.mpr ⟨hP, hk⟩)
  by_cases hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M
  · obtain ⟨cb⟩ := Peterfalvi.S14.theorem88_caseB_holds hG hnoV
    exact absurd (hall cb.S cb.S_maximal)
      (BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG cb.S_maximal cb.S_nonI)
  · push Not at hall
    obtain ⟨S, hS, hSnotI⟩ := hall
    have hSP : BG.Ch4.S14.IsTypeP S := notTypeI_imp_typeP S hS hSnotI
    have : Group.IsSolvable ↥S := hG.isSolvable_of_mem_maximalSubgroups hS
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥S) (BG.Ch4.S14.kappa S)
    set K : Subgroup G := K'.map S.subtype with hKdef
    have hKeq : K.subgroupOf S = K' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S) := by
      rw [hKeq]; exact hK'
    set Kstar : Subgroup G :=
      BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    have hKM : K ≤ S := Subgroup.map_subtype_le K'
    obtain ⟨_, _, Mstar, ⟨hMstarMem, hMstarP, hSnconjMstar,
        ⟨hKstarMstar, hKstar_hall, hK_eq⟩, hcyc, _, hP2disj, hcover⟩, _⟩ :=
      BG.Ch4.S14.typeP_duality hG hS hSP hKM hK hKstardef
    -- The structural data is symmetric in `(S, K) ↔ (Mstar, K*)`; collect the shared facts once.
    have hSne : S ≠ Mstar := by
      rintro rfl; exact hSnconjMstar (BG.Ch4.S14.IsConjugateSubgroup.refl S)
    have hnonIS : IsTypeNonI S := typeP_imp_nonI S hS hSP
    have hnonIM : IsTypeNonI Mstar := typeP_imp_nonI Mstar hMstarMem hMstarP
    have hone : IsTypeII S ∨ IsTypeII Mstar := by
      rcases hP2disj with hP2S | hP2M
      · exact Or.inl ((BG.Ch4.S16.proposition_type_classification hG hS).2.1.mpr hP2S)
      · exact Or.inr ((BG.Ch4.S16.proposition_type_classification hG hMstarMem).2.1.mpr hP2M)
    have hcov : ∀ M : Subgroup G, M ∈ maximalSubgroups G →
        IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨ (∃ g : G, MulAut.conj g • M = Mstar) := by
      intro M hM
      by_cases hMI : IsTypeI M
      · exact Or.inl hMI
      · exact Or.inr (hcover M hM (notTypeI_imp_typeP M hM hMI))
    -- The two κ-Hall factors have distinct orders, so one of the two labellings has `|K| < |K*|`.
    rcases lt_or_gt_of_ne (BG.Ch4.S14.card_kappaHall_ne_card_Kstar hSP hKM hK hKstardef) with
      hlt | hgt
    · exact ⟨S, Mstar, K, Kstar, hS, hMstarMem, hSne, hnonIS, hnonIM, hone, hcov, hKM, hK,
        hKstardef, hSP, hMstarP, hSnconjMstar, hKstarMstar, hKstar_hall, hK_eq, hcyc, hlt⟩
    · refine ⟨Mstar, S, Kstar, K, hMstarMem, hS, hSne.symm, hnonIM, hnonIS, hone.symm, ?_,
        hKstarMstar, hKstar_hall, hK_eq, hMstarP, hSP, fun h => hSnconjMstar h.symm, hKM, hK,
        hKstardef, ?_, hgt⟩
      · intro M hM
        rcases hcov M hM with hI | hSc | hMc
        · exact Or.inl hI
        · exact Or.inr (Or.inr hSc)
        · exact Or.inr (Or.inl hMc)
      · rw [sup_comm]; exact hcyc

end

end OddOrder
