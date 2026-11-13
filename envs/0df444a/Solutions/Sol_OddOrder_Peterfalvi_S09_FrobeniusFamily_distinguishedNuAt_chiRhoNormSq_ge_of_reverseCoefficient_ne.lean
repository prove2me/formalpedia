-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.distinguishedNuAt_chiRhoNormSq_ge_of_reverseCoefficient_ne
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:26:24.12418+00:00
-- url     : https://prove2.me/submissions/9cc0dd49-e697-4ba9-8cdc-c0beeadeed19

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CharacterEstimate.lean
--   OddOrder/Peterfalvi/S09_FrobeniusEstimate.lean
--   OddOrder/Peterfalvi/S09_FrobeniusParity.lean
--   OddOrder/Peterfalvi/S09_FrobeniusGoodIndexEstimate.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_NormalCase
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_QuadraticTerm
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_TwoFamilies
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis78
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaNormEstimate
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CoherenceFormula
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CharacterEstimate
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusEstimate
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis79_zeta_cross_eq_zero_at
import Theorems.Thm_OddOrder_Peterfalvi_S09_Hypothesis78_chiRho_norm_sq_eq_card_ratio_mul

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

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/CharacterEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

namespace FrobeniusFamily

variable {k : ℕ}

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

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09.Cert

/-- **The `ρ`-map is restriction, for a TI Dade datum** (trivial local subgroups `H(a) = ⊥`, the
`of_isTISubset` case).  For `a ∈ A`, the `(7.2)` coset average
`χ^ρ(a) = (1/|H(a)|) ∑_{x ∈ H(a)} χ(a·x)` collapses (each `x = 1`, so every summand is `χ(a)`) to
`χ(a)`.  This is what makes two `Hypothesis71`'s built from the *same* TI subset — even via
different
`of_isTISubset` expressions — agree on `chiRho` (hence `chiRhoCF`/`chiRhoNormSq`). -/
theorem chiRho_apply_of_trivial_local {G : Type*} [Group G] {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card G : ℂ)] (H71 : Hypothesis71 G A L)
    (hbot : ∀ (a : G) (ha : a ∈ A), H71.hyp.H ⟨a, ha⟩ = ⊥)
    (χ : ClassFunction G ℂ) {a : L} (ha : (a : G) ∈ A) :
    H71.chiRho χ a = χ (a : G) := by
  classical
  rw [H71.chiRho_of_mem χ ha]
  have hval : ∀ x : ↥(H71.hyp.H ⟨(a : G), ha⟩), χ ((a : G) * (x : G)) = χ (a : G) := by
    intro x
    have hx2 : (x : G) ∈ (⊥ : Subgroup G) := by rw [← hbot (a : G) ha]; exact x.2
    rw [Subgroup.mem_bot.mp hx2, mul_one]
  have hne : (Nat.card (H71.hyp.H ⟨(a : G), ha⟩) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos).ne'
  rw [Finset.sum_congr rfl (fun x _ => hval x), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- **The good-index norm lower bound** (Peterfalvi (7.10), the `hgood` core).  For `χ ∈ Irr G`
orthogonal to `S^ν` with `(β, χ) ≠ 0` (`χ` is a constituent of the (7.8.a) `β`), the (7.8.c.ii)
formula `‖χ^ρ‖² = (|A|/|L|)·(β,χ)·(β,χ)‾` together with integrality `(β,χ) ∈ ℤ` (`β ∈ ℤ[Irr]`,
`χ ∈ Irr`) gives `|(β,χ)|² ≥ 1`, hence `|A|/|L| ≤ ‖χ^ρ‖²`.  This is the per-good-member estimate
`hgood` of the (7.10) `characterEstimateData` assembly. -/
theorem chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero {G : Type*} [Group G] [Fintype G]
    {A : Set G} {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    [Invertible (Nat.card G : ℂ)] (H78 : Hypothesis78 G A L)
    (χ : ClassFunction G ℂ) (hχ_irr : IsIrreducibleCharacter χ)
    (hχ_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner χ (H78.nu (H78.hyp76.zeta i)) = 0)
    (hdiffZ : H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L)
    (hbeta_ne : ClassFunction.inner H78.beta χ ≠ 0) :
    (Nat.card A : ℝ) / (Nat.card ↥L : ℝ)
      ≤ (ClassFunction.inner (H78.hyp76.hyp71.chiRhoCF χ) (H78.hyp76.hyp71.chiRhoCF χ)).re := by
  have heq := H78.chiRho_norm_sq_eq_card_ratio_mul χ hχ_irr hχ_orth
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int
    (H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr hdiffZ) hχ_irr.mem_ZIrr
  have hβχ : ClassFunction.inner H78.beta χ = (m : ℂ) := hm
  have hm_ne : m ≠ 0 := by
    intro h0
    apply hbeta_ne
    rw [hβχ, h0, Int.cast_zero]
  -- `‖χ^ρ‖² = (|A|/|L|)·m²`, a real number.
  have hstar : star ((m : ℤ) : ℂ) = ((m : ℤ) : ℂ) := by simp
  have hRHS : ((Nat.card A : ℂ) / (Nat.card ↥L : ℂ)) *
        (ClassFunction.inner H78.beta χ * star (ClassFunction.inner H78.beta χ))
      = (((Nat.card A : ℝ) / (Nat.card ↥L : ℝ) * (m : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [hβχ, hstar]
    push_cast
    ring
  rw [heq, hRHS, Complex.ofReal_re]
  -- `|A|/|L| ≤ |A|/|L| · m²`, since `|A|/|L| ≥ 0` and `m² ≥ 1`.
  have hratio_nonneg : (0 : ℝ) ≤ (Nat.card A : ℝ) / (Nat.card ↥L : ℝ) := by positivity
  have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm_ne
    have h2 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast h1
    nlinarith [sq_abs (m : ℝ), abs_nonneg (m : ℝ)]
  nlinarith [hratio_nonneg, hm2]

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The Sibley (7.1) `ρ`-map equals the family (7.1) `ρ`-map** (the (7.8.b)→(7.5) bridge).  Both
`sibleyToHypothesis71 i` (the Dade datum coherence is coherent for) and `hypothesis71 i` (the family
`FamilyHypothesis71` uses) are `of_isTISubset` on the *same* TI subset `H_i^#` (their supports agree
by `sharpImage_subgroupOf_eq`), with trivial local subgroups, so `chiRho` (hence `chiRhoCF`) is
restriction to `H_i^#` for both — they coincide (`chiRho_apply_of_trivial_local`).  This identifies
`H78.zetaNuRhoNormSq` (built on `sibleyToHypothesis71`) with `P.chiRhoNormSq` (built on
`hypothesis71`), the last link from the (7.8.b) bound to the (7.5) family estimate. -/
theorem sibleyToHypothesis71_chiRhoCF_eq [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    (χ : ClassFunction G ℂ) :
    (F.sibleyToHypothesis71 i hodd hnilp C hFrob).chiRhoCF χ = (F.hypothesis71 i).chiRhoCF χ := by
  ext a
  rw [Hypothesis71.chiRhoCF_apply, Hypothesis71.chiRhoCF_apply]
  by_cases ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)
  · have haS : (a : G) ∈ OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i)) := by
      rw [F.sharpImage_subgroupOf_eq i]; exact ha
    rw [chiRho_apply_of_trivial_local _ (fun _ _ => rfl) χ haS,
      chiRho_apply_of_trivial_local _ (fun _ _ => rfl) χ ha]
  · have haS : (a : G) ∉ OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i)) := by
      rw [F.sharpImage_subgroupOf_eq i]; exact ha
    rw [(F.sibleyToHypothesis71 i hodd hnilp C hFrob).chiRho_of_not_mem χ haS,
      (F.hypothesis71 i).chiRho_of_not_mem χ ha]

end FrobeniusFamily

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

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusGoodIndexEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

private theorem chiRhoCF_neg [Fintype G] {A : Set G} {L : Subgroup G}
    (H71 : Hypothesis71 G A L) (chi : ClassFunction G ℂ) :
    H71.chiRhoCF (-chi) = -H71.chiRhoCF chi := by
  classical
  ext a
  change H71.chiRho (-chi) a = -H71.chiRho chi a
  by_cases ha : (a : G) ∈ A
  · rw [H71.chiRho_of_mem _ ha, H71.chiRho_of_mem _ ha]
    simp only [ClassFunction.neg_apply, Finset.sum_neg_distrib]
    ring
  · rw [H71.chiRho_of_not_mem _ ha, H71.chiRho_of_not_mem _ ha, neg_zero]

section GoodIndex

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- **Peterfalvi (7.8.c), concrete good-index bound.**  If the reverse
coefficient of the `j`-th beta against the selected coherent image at `i` is
nonzero, then the `j`-th rho norm of that selected image is at least the local
sharp-kernel ratio. -/
theorem _root_.solution
    (i j : Fin k) (hij : i ≠ j)
    (hcoeff : ClassFunction.inner
      (F.betaAt hodd hnilp C hFrob j)
      (F.distinguishedNuAt hodd hnilp C hFrob i) ≠ 0) :
    ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) j := by
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
  let : Fintype ↥(F.L j) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  let : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  let : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
  let H78i := F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)
  let H78j := F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)
  obtain ⟨eps, xi, heps, hsigned⟩ :=
    H78i.exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet i hodd (hnilp i) (C i) (hFrob i))
      (F.hypothesis78_nu_eq i hodd (hnilp i) (C i) (hFrob i))
      (F.hypothesis78_zeta_irreducible i hodd (hnilp i) (C i) (hFrob i))
  have hzetaDistinct_i : H78i.zetaDistinct = 0 := rfl
  rw [hzetaDistinct_i] at hsigned
  have hsignedAt : F.distinguishedNuAt hodd hnilp C hFrob i =
      eps • (xi : ClassFunction G ℂ) := by
    simpa [distinguishedNuAt, H78i] using hsigned
  have hzero_ne_i : (0 : Fin (H78i.hyp76.n + 1)) ≠ H78i.ind1H := by
    rw [← hzetaDistinct_i]
    exact H78i.zetaDistinct_ne_ind1H
  have hcross : ∀ r : Fin (H78j.hyp76.n + 1), r ≠ H78j.ind1H →
      ClassFunction.inner
        (F.distinguishedNuAt hodd hnilp C hFrob i)
        (H78j.nu (H78j.hyp76.zeta r)) = 0 := by
    intro r hr
    simpa [distinguishedNuAt, H78i, H78j] using
      (F.hypothesis79_zeta_cross_eq_zero_at
        hodd (hnilp i) (C i) (hFrob i) (hnilp j) (C j) (hFrob j)
        hij hzero_ne_i hr)
  have hdiffZ :
      H78j.hyp76.zeta H78j.ind1H - H78j.hyp76.zeta H78j.zetaDistinct ∈
        ZIrr ↥(F.L j) :=
    H78j.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (F.hypothesis78_ind1H_mem_ZIrr j hodd (hnilp j) (C j) (hFrob j))
      (F.hypothesis78_zeta_irreducible j hodd (hnilp j) (C j) (hFrob j))
  have hcoeff' : ClassFunction.inner H78j.beta
      (F.distinguishedNuAt hodd hnilp C hFrob i) ≠ 0 := by
    simpa [betaAt, H78j] using hcoeff
  have hratio :
      (Nat.card (OddOrder.Peterfalvi.S08.sharpImage
          ((F.H j).subgroupOf (F.L j))) : ℝ) /
          (Nat.card ↥(F.L j) : ℝ) =
        ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) := by
    rw [F.sharpImage_subgroupOf_eq j]
    exact F.card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h_real j
  rcases heps with rfl | rfl
  · have hsignedOne : F.distinguishedNuAt hodd hnilp C hFrob i =
        (xi : ClassFunction G ℂ) := by simpa using hsignedAt
    have horthXi : ∀ r : Fin (H78j.hyp76.n + 1), r ≠ H78j.ind1H →
        ClassFunction.inner (xi : ClassFunction G ℂ)
          (H78j.nu (H78j.hyp76.zeta r)) = 0 := by
      intro r hr
      simpa [hsignedOne] using hcross r hr
    have hcoeffXi : ClassFunction.inner H78j.beta
        (xi : ClassFunction G ℂ) ≠ 0 := by
      simpa [hsignedOne] using hcoeff'
    have hbound := chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero
      H78j (xi : ClassFunction G ℂ) xi.property horthXi hdiffZ hcoeffXi
    change (Nat.card (OddOrder.Peterfalvi.S08.sharpImage
        ((F.H j).subgroupOf (F.L j))) : ℝ) / (Nat.card ↥(F.L j) : ℝ) ≤
      (ClassFunction.inner
        ((F.sibleyToHypothesis71 j hodd (hnilp j) (C j) (hFrob j)).chiRhoCF
          (xi : ClassFunction G ℂ))
        ((F.sibleyToHypothesis71 j hodd (hnilp j) (C j) (hFrob j)).chiRhoCF
          (xi : ClassFunction G ℂ))).re at hbound
    rw [F.sibleyToHypothesis71_chiRhoCF_eq] at hbound
    change ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
      (ClassFunction.inner
        ((F.hypothesis71 j).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i))
        ((F.hypothesis71 j).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i))).re
    rw [hsignedOne]
    rw [← hratio]
    exact hbound
  · have hsignedNeg : F.distinguishedNuAt hodd hnilp C hFrob i =
        -(xi : ClassFunction G ℂ) := by simpa using hsignedAt
    have horthXi : ∀ r : Fin (H78j.hyp76.n + 1), r ≠ H78j.ind1H →
        ClassFunction.inner (xi : ClassFunction G ℂ)
          (H78j.nu (H78j.hyp76.zeta r)) = 0 := by
      intro r hr
      have hz := hcross r hr
      rw [hsignedNeg, ClassFunction.inner_neg_left, neg_eq_zero] at hz
      exact hz
    have hcoeffXi : ClassFunction.inner H78j.beta
        (xi : ClassFunction G ℂ) ≠ 0 := by
      intro hz
      apply hcoeff'
      rw [hsignedNeg, ClassFunction.inner_neg_right, hz, neg_zero]
    have hbound := chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero
      H78j (xi : ClassFunction G ℂ) xi.property horthXi hdiffZ hcoeffXi
    change (Nat.card (OddOrder.Peterfalvi.S08.sharpImage
        ((F.H j).subgroupOf (F.L j))) : ℝ) / (Nat.card ↥(F.L j) : ℝ) ≤
      (ClassFunction.inner
        ((F.sibleyToHypothesis71 j hodd (hnilp j) (C j) (hFrob j)).chiRhoCF
          (xi : ClassFunction G ℂ))
        ((F.sibleyToHypothesis71 j hodd (hnilp j) (C j) (hFrob j)).chiRhoCF
          (xi : ClassFunction G ℂ))).re at hbound
    rw [F.sibleyToHypothesis71_chiRhoCF_eq] at hbound
    change ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
      (ClassFunction.inner
        ((F.hypothesis71 j).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i))
        ((F.hypothesis71 j).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i))).re
    rw [hsignedNeg, chiRhoCF_neg, ClassFunction.inner_neg_left,
      ClassFunction.inner_neg_right, neg_neg]
    rw [← hratio]
    exact hbound

end GoodIndex

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
