-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_zetaNuRhoNormSq_ge_at
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:31:12.488595+00:00
-- url     : https://prove2.me/submissions/5b3fc74e-3bc8-41d4-a671-b5524bd703ee

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
--   OddOrder/Peterfalvi/S09_FrobeniusFamilyOrthogonality.lean
--   OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean
--   OddOrder/Peterfalvi/S09_FrobeniusGammaNormEstimate.lean
--   OddOrder/Peterfalvi/S09_FrobeniusSelectedEstimate.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_QuadraticTerm
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaNormEstimate
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CoherenceFormula
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusSelectedEstimate
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_coherence_agreement_at

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

/-- With the weighted-sum coefficient normalized, `BetaDecomp` gives
`(β, ζ^ν) = a - 1`. -/
theorem beta_inner_zetaImage_eq_int_sub_one_of_weighted
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzetaImage_norm :
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1)
    (hweighted :
      ClassFunction.inner H78.weightedNuSum
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1) :
    ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
      (hBD.a : ℂ) - 1 := by
  rw [hBD.beta_eq, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    H78.constOne_orth_zetaImage hBD, hzetaImage_norm, hweighted,
    H78.gamma_orth_zetaImage hBD]
  ring

end Hypothesis78

end Section_7_8

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

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
/-- Every concrete Frobenius-family degree ratio is fixed by complex conjugation. -/
theorem hypothesis78_star_d_at
    (r : Fin ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.n + 1)) :
    star ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d r) =
      (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d r := by
  have : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  let H78 := localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hzeta : ∀ s, H78.hyp76.zeta s =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ s : ClassFunction _ ℂ) :=
    fun s => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) s
  have hz0 : H78.hyp76.zeta 0 (1 : ↥(F.L i)) ≠ 0 := by
    rw [hzeta 0]
    exact Cert.induce_apply_one_ne_zero ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  have hreal : ∀ s, star (H78.hyp76.zeta s (1 : ↥(F.L i))) =
      H78.hyp76.zeta s (1 : ↥(F.L i)) := by
    intro s
    rw [hzeta s]
    exact Cert.induce_apply_one_star ((F.H i).subgroupOf (F.L i)) (pf.θ s)
  have hd : H78.hyp76.d r =
      H78.hyp76.zeta r (1 : ↥(F.L i)) /
        H78.hyp76.zeta 0 (1 : ↥(F.L i)) := by
    rw [eq_div_iff hz0]
    exact (H78.hyp76.zeta_one_eq_d_mul r).symm
  rw [hd, star_div₀, hreal r, hreal 0]

end LocalCoefficient

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

end LocalGammaNorm

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusSelectedEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalSelectedEstimate

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

private noncomputable abbrev localBD :=
  F.hypothesis78_betaDecomp i hodd hnilp C hFrob

/-- **Peterfalvi (7.8.b), canonical local form.**  The distinguished coherent
image in the canonical `Hypothesis78` attached to a Frobenius-family member
satisfies `1 - e/h <= normSq (zeta_0^(nu rho))`. -/
theorem _root_.solution :
    1 - ((localH78_S09_FrobeniusSelectedEstimate F i hodd hnilp C hFrob).complementIndex : ℝ) /
        ((localH78_S09_FrobeniusSelectedEstimate F i hodd hnilp C hFrob).kernelOrder : ℝ) ≤
      (localH78_S09_FrobeniusSelectedEstimate F i hodd hnilp C hFrob).zetaNuRhoNormSq := by
  classical
  let H78 := localH78_S09_FrobeniusSelectedEstimate F i hodd hnilp C hFrob
  let hBD := localBD F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hzeta : ∀ r, H78.hyp76.zeta r =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ r : ClassFunction _ ℂ) :=
    fun r => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) r
  have hz0 : H78.hyp76.zeta 0 (1 : ↥(F.L i)) ≠ 0 := by
    rw [hzeta 0]
    exact Cert.induce_apply_one_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  have hz0_induced : ClassFunction.induce ((F.H i).subgroupOf (F.L i))
      (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) ≠ 0 :=
    Cert.induce_apply_one_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  have horth : ∀ r s, r ≠ s →
      ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta s) = 0 := by
    intro r s hrs
    rw [hzeta r, hzeta s]
    exact Cert.induce_family_orthogonal_of_injective
      ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj r s hrs
  have hzero_ne : (0 : Fin (H78.hyp76.n + 1)) ≠ H78.ind1H := by
    exact Ne.symm pf.ind1H_ne_zero
  have hζ0norm : ClassFunction.inner (H78.hyp76.zeta 0)
      (H78.hyp76.zeta 0) = 1 := by
    exact IsIrreducibleCharacter.inner_self_eq_one
      (F.hypothesis78_zeta_irreducible i hodd hnilp C hFrob)
  have hzetaImageNorm : ClassFunction.inner
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
    F.hypothesis78_nu_zeta_norm_one_at i hodd hnilp C hFrob
      H78.zetaDistinct_ne_ind1H
  have hweighted : ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 := by
    have h := F.hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
      i hodd hnilp C hFrob (r := H78.zetaDistinct)
        H78.zetaDistinct_ne_ind1H
    rw [show H78.zetaDistinct = 0 from rfl,
      F.hypothesis78_d_zero_eq_one i hodd hnilp C hFrob] at h
    exact h
  have hbeta : ClassFunction.inner H78.beta
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = (hBD.a : ℂ) - 1 :=
    H78.beta_inner_zetaImage_eq_int_sub_one_of_weighted hBD
      hzetaImageNorm hweighted
  have hz_ind : H78.hyp76.zeta H78.ind1H =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (trivialIrreducibleCharacter
          ↥((F.H i).subgroupOf (F.L i)) : ClassFunction _ ℂ) := by
    rw [hzeta, show H78.ind1H = pf.ind1H from rfl, pf.triv]
  have hd1 : H78.hyp76.d H78.ind1H = 1 := by
    change ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (pf.θ pf.ind1H : ClassFunction _ ℂ) (1 : ↥(F.L i)) /
        ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) = 1
    have hdeg_match := H78.zeta_one_eq_ind1H_one
    change ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ pf.ind1H : ClassFunction _ ℂ) (1 : ↥(F.L i)) at hdeg_match
    rw [← hdeg_match, div_self hz0_induced]
  have hP_ind1H : H78.hyp76.zeta H78.ind1H (1 : ↥(F.L i)) =
      (H78.complementIndex : ℂ) := by
    rw [Cert.complementIndex_eq_subgroupOf_index H78, hz_ind]
    exact Cert.induce_trivialChar_apply_eq_index
      ((F.H i).subgroupOf (F.L i)) (Subgroup.one_mem _)
  have hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H =
      (H78.complementIndex : ℂ) := by
    exact F.hypothesis78_ind1H_inner_self_eq_complementIndex
      i hodd hnilp C hFrob
  have hz0_compl : H78.hyp76.zeta 0 (1 : ↥(F.L i)) =
      (H78.complementIndex : ℂ) := by
    change H78.hyp76.zeta H78.zetaDistinct (1 : ↥(F.L i)) =
      (H78.complementIndex : ℂ)
    rw [H78.zeta_one_eq_ind1H_one, hP_ind1H]
  have hz0_deg : ClassFunction.induce ((F.H i).subgroupOf (F.L i))
      (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) =
        (((F.H i).subgroupOf (F.L i)).index : ℂ) := by
    calc
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) =
          Classical.choose
            (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)
              (1 : ↥(F.L i)) := congrArg
                (fun χ : ClassFunction ↥(F.L i) ℂ => χ 1) pf.induce_zero_eq
      _ = (((F.H i).subgroupOf (F.L i)).index : ℂ) :=
        (Classical.choose_spec
          (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).2
  have hGsum : ∑ r ∈ (Finset.Ioi (0 : Fin (H78.hyp76.n + 1))).erase H78.ind1H,
        H78.hyp76.zeta r 1 ^ 2 / H78.hyp76.zetaNormSq r =
      (H78.complementIndex : ℂ) * ((H78.kernelOrder : ℂ) - 1) -
        (H78.complementIndex : ℂ) ^ 2 := by
    rw [Cert.complementIndex_eq_subgroupOf_index H78,
      show (H78.kernelOrder : ℂ) =
          (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) from by
        rw [show H78.kernelOrder =
            Nat.card ↥((F.H i).subgroupOf (F.L i)) from
          (Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv).symm]]
    exact Cert.family_degree_sum_Ioi
      ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj pf.cover pf.ind1H
        pf.ind1H_ne_zero pf.triv hz0_deg hζ0norm
  exact Cert.zetaNuRhoNormSq_ge_of_facts H78 hBD rfl horth
    (by
      rw [Cert.cCoeff_nu_zeta_zero_ind1H_eq H78 H78.nu rfl hd1]
      simpa only [show H78.zetaDistinct = 0 from rfl] using hbeta)
    (fun r hr0 hrind =>
      Cert.cCoeff_nu_zeta_zero_eq_neg_d H78.hyp76 H78.nu
        (fun s _ hsind =>
          F.hypothesis78_coherence_agreement_at
            i hodd hnilp C hFrob hsind)
        H78.nu_isometry hzero_ne (fun s hs => horth s 0 hs)
        hζ0norm r hr0 hrind)
    (F.hypothesis78_star_d_at i hodd hnilp C hFrob)
    (fun r => by
      rw [hzeta r]
      exact Cert.induce_apply_one_star
        ((F.H i).subgroupOf (F.L i)) (pf.θ r))
    (fun r => by
      change H78.hyp76.zeta r (1 : ↥(F.L i)) /
          H78.hyp76.zeta 0 (1 : ↥(F.L i)) =
        H78.hyp76.zeta r (1 : ↥(F.L i)) /
          (H78.complementIndex : ℂ)
      rw [hz0_compl])
    hN_ind1H hP_ind1H hGsum
    (F.hypothesis78_smallIndex_at i hodd hnilp C hFrob)

end LocalSelectedEstimate

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
