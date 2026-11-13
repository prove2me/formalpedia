-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.exists_weightedGammaDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:31:11.535188+00:00
-- url     : https://prove2.me/submissions/d4434b23-c4d8-45d0-9592-7d7ae01bb85a

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_FrobeniusFamilyOrthogonality.lean
--   OddOrder/Peterfalvi/S09_FrobeniusParity.lean
--   OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_NormalCase
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_QuadraticTerm
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaDecomposition
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis79_zeta_cross_eq_zero_at
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_weightedNuSum_inner_self_eq
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_coherence_agreement_at

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

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusFamilyOrthogonality.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section CrossFamily

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) {i j : Fin k}

variable (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C_i : Subgroup ↥(F.L i))

variable (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)

variable [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]

variable [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]

variable [((F.H j).subgroupOf (F.L j)).Normal]

variable (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C_j : Subgroup ↥(F.L j))

variable (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j)

/-- Weighted coherent sums from distinct Frobenius-family members are
orthogonal. -/
theorem hypothesis79_weightedNuSum_cross_eq_zero (hij : i ≠ j) :
    ClassFunction.inner
      (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).weightedNuSum
      (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum = 0 := by
  classical
  rw [Hypothesis78.weightedNuSum, Hypothesis78.weightedNuSum,
    OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun r hr_mem => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero fun s hs_mem => ?_
  have hr :
      r ≠ (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).ind1H :=
    (Finset.mem_erase.mp hr_mem).1
  have hs :
      s ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H :=
    (Finset.mem_erase.mp hs_mem).1
  rw [ClassFunction.inner_smul_left,
    OddOrder.RepresentationTheory.inner_smul_right,
    F.hypothesis79_zeta_cross_eq_zero_at
      hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j hij hr hs,
    mul_zero, mul_zero]

end CrossFamily

section WeightedNorm

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

/-- Rational-cast form of the weighted norm used by the (7.10)
orthogonal-decomposition estimate. -/
theorem hypothesis78_weightedNuSum_inner_self_eq_BsumWeight :
    ClassFunction.inner
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum =
        (F.BsumWeight i : ℂ) := by
  rw [F.hypothesis78_weightedNuSum_inner_self_eq i hodd hnilp C hFrob]
  simp only [BsumWeight]
  norm_num

end WeightedNorm

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

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
/-- The coherent degree-zero difference is supported on the local Dade support. -/
theorem hypothesis78_nu_zeta_sub_d_smul_support_at
    {r : Fin ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).ind1H) :
    ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).nu
          ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta r) -
        (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d r •
          (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).nu
            ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta 0)).support
      ⊆ (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.hyp71.hyp.dadeSupport := by
  have : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  let H78 := localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob
  rw [← F.hypothesis78_coherence_agreement_at i hodd hnilp C hFrob hr]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  exact hg (H78.hyp76.hyp71.isDadeMap.map_eq_zero_of_not_mem_dadeSupport
    (H78.hyp76.psiSupp r) g hgnot)

end LocalCoefficient

section CrossProjection

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) {i j : Fin k}

variable (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Fintype ↥((F.H i).subgroupOf (F.L i))]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C_i : Subgroup ↥(F.L i))

variable (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)

variable [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]

variable [Fintype ↥((F.H j).subgroupOf (F.L j))]

variable [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]

variable [((F.H j).subgroupOf (F.L j)).Normal]

variable (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C_j : Subgroup ↥(F.L j))

variable (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j)

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
omit [Fintype ↥((F.H j).subgroupOf (F.L j))] in
/-- The weighted coherent sum of one family is orthogonal to every
non-principal coherent source image of a distinct family. -/
theorem hypothesis79_weightedNuSum_cross_zeta_eq_zero_at
    (hij : i ≠ j)
    {r : Fin ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H) :
    ClassFunction.inner
      (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).weightedNuSum
      ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta r)) = 0 := by
  classical
  rw [Hypothesis78.weightedNuSum,
    OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [ClassFunction.inner_smul_left,
    F.hypothesis79_zeta_cross_eq_zero_at
      hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j hij
      (Finset.ne_of_mem_erase hs) hr,
    mul_zero]

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
omit [Fintype ↥((F.H j).subgroupOf (F.L j))] in
/-- Expanding the selected beta decomposition against a coherent source image
of a distinct family leaves only the Gamma term. -/
theorem hypothesis79_beta_inner_nu_zeta_eq_gamma
    (hBD_i : (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).BetaDecomp)
    (hBD_j : (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).BetaDecomp)
    (hij : i ≠ j)
    {r : Fin ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H) :
    ClassFunction.inner
        (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta r)) =
      ClassFunction.inner hBD_i.Gamma
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta r)) := by
  let H78i := F.hypothesis78 i hodd hnilp_i C_i hFrob_i
  let H78j := F.hypothesis78 j hodd hnilp_j C_j hFrob_j
  have hone : ClassFunction.inner (Hypothesis71.constOne G)
      (H78j.nu (H78j.hyp76.zeta r)) = 0 := by
    rw [Hypothesis71.ClassFunction.inner_symm, hBD_j.orth_one r hr, star_zero]
  have hzeta : ClassFunction.inner
      (H78i.nu (H78i.hyp76.zeta H78i.zetaDistinct))
      (H78j.nu (H78j.hyp76.zeta r)) = 0 :=
    F.hypothesis79_zeta_cross_eq_zero_at
      hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j hij
      H78i.zetaDistinct_ne_ind1H hr
  have hweighted : ClassFunction.inner H78i.weightedNuSum
      (H78j.nu (H78j.hyp76.zeta r)) = 0 :=
    F.hypothesis79_weightedNuSum_cross_zeta_eq_zero_at
      hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j hij hr
  rw [hBD_i.beta_eq, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    hone, hzeta, hweighted, mul_zero]
  ring

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
omit [Fintype ↥((F.H j).subgroupOf (F.L j))] in
/-- The coefficient of Gamma on any source image in a distinct Frobenius
family is its local degree ratio times the distinguished beta coefficient. -/
theorem hypothesis79_gamma_inner_nu_zeta_eq_d_mul
    (hBD_i : (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).BetaDecomp)
    (hBD_j : (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).BetaDecomp)
    (hij : i ≠ j)
    {r : Fin ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H) :
    ClassFunction.inner hBD_i.Gamma
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta r)) =
      (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.d r *
        ClassFunction.inner
          (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
            ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta 0)) := by
  have : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  have : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  let H78i := F.hypothesis78 i hodd hnilp_i C_i hFrob_i
  let H78j := F.hypothesis78 j hodd hnilp_j C_j hFrob_j
  let H79 :=
    F.hypothesis79 i j hij hodd
      hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j
  have hsupp :
      (H78j.nu (H78j.hyp76.zeta r) -
        H78j.hyp76.d r • H78j.nu (H78j.hyp76.zeta 0)).support
        ⊆ H78j.hyp76.hyp71.hyp.dadeSupport :=
    F.hypothesis78_nu_zeta_sub_d_smul_support_at
      j hodd hnilp_j C_j hFrob_j hr
  have hzero : ClassFunction.inner H78i.beta
      (H78j.nu (H78j.hyp76.zeta r) -
        H78j.hyp76.d r • H78j.nu (H78j.hyp76.zeta 0)) = 0 := by
    apply ClassFunction.inner_eq_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro g hg_beta hg_diff
    exact Set.disjoint_left.mp H79.dadeSupport_disjoint
      (H78i.beta_support_subset_dadeSupport hg_beta)
      (hsupp hg_diff)
  have hbeta_gamma := F.hypothesis79_beta_inner_nu_zeta_eq_gamma
    hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j
    hBD_i hBD_j hij hr
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_smul_right,
    F.hypothesis78_star_d_at j hodd hnilp_j C_j hFrob_j r,
    hbeta_gamma] at hzero
  linear_combination hzero

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
omit [Fintype ↥((F.H j).subgroupOf (F.L j))] in
/-- The distinguished beta coefficient against another family is an integer,
because both class functions are virtual characters. -/
theorem hypothesis79_exists_integral_beta_zeta_coefficient :
    ∃ x : ℤ,
      ClassFunction.inner
          (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
            ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta 0)) =
        (x : ℂ) := by
  classical
  let H78i := F.hypothesis78 i hodd hnilp_i C_i hFrob_i
  let H78j := F.hypothesis78 j hodd hnilp_j C_j hFrob_j
  have h0 : (0 : Fin (H78j.hyp76.n + 1)) ≠ H78j.ind1H := by
    intro h
    apply H78j.zetaDistinct_ne_ind1H
    exact (show H78j.zetaDistinct = 0 from rfl).trans h
  have hbetaZ : H78i.beta ∈ ZIrr G :=
    H78i.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (F.hypothesis78_ind1H_mem_ZIrr i hodd hnilp_i C_i hFrob_i)
      (F.hypothesis78_zeta_irreducible i hodd hnilp_i C_i hFrob_i)
  have hnuZ : H78j.nu (H78j.hyp76.zeta 0) ∈ ZIrr G :=
    H78j.nu_zeta_mem_ZIrr_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet j hodd hnilp_j C_j hFrob_j)
      (F.hypothesis78_nu_eq j hodd hnilp_j C_j hFrob_j) h0
  exact ClassFunction.inner_mem_ZIrr_int hbetaZ hnuZ

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
omit [Fintype ↥((F.H j).subgroupOf (F.L j))] in
/-- The cross-family integer coefficient is exactly the orthogonal projection
coefficient of Gamma onto the other family's weighted coherent sum. -/
theorem hypothesis79_gamma_inner_weightedNuSum_eq_mul_self
    (hBD_i : (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).BetaDecomp)
    (hBD_j : (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).BetaDecomp)
    (hij : i ≠ j) (x : ℤ)
    (hx : ClassFunction.inner
        (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta 0)) =
      (x : ℂ)) :
    ClassFunction.inner hBD_i.Gamma
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum =
      (x : ℂ) * ClassFunction.inner
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum := by
  have : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  have : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  classical
  let H78j := F.hypothesis78 j hodd hnilp_j C_j hFrob_j
  let coeff : Fin (H78j.hyp76.n + 1) → ℂ := fun r =>
    H78j.hyp76.zeta r (1 : ↥(F.L j)) /
      (H78j.hyp76.zeta H78j.zetaDistinct (1 : ↥(F.L j)) *
        ClassFunction.inner (H78j.hyp76.zeta r) (H78j.hyp76.zeta r))
  have hpoint : ∀ r ∈ Finset.univ.erase H78j.ind1H,
      ClassFunction.inner hBD_i.Gamma
          (H78j.nu (H78j.hyp76.zeta r)) =
        (x : ℂ) * ClassFunction.inner H78j.weightedNuSum
          (H78j.nu (H78j.hyp76.zeta r)) := by
    intro r hr
    have hr' : r ≠ H78j.ind1H := Finset.ne_of_mem_erase hr
    calc
      ClassFunction.inner hBD_i.Gamma
          (H78j.nu (H78j.hyp76.zeta r)) =
        H78j.hyp76.d r *
          ClassFunction.inner
            (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
            (H78j.nu (H78j.hyp76.zeta 0)) :=
        F.hypothesis79_gamma_inner_nu_zeta_eq_d_mul
          hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j
          hBD_i hBD_j hij hr'
      _ = H78j.hyp76.d r * (x : ℂ) := by rw [hx]
      _ = (x : ℂ) * ClassFunction.inner H78j.weightedNuSum
          (H78j.nu (H78j.hyp76.zeta r)) := by
        rw [F.hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
          j hodd hnilp_j C_j hFrob_j hr']
        ring
  have hW : H78j.weightedNuSum =
      ∑ r ∈ Finset.univ.erase H78j.ind1H,
        coeff r • H78j.nu (H78j.hyp76.zeta r) := by
    rfl
  have hGammaExpand :
      ClassFunction.inner hBD_i.Gamma H78j.weightedNuSum =
        ∑ r ∈ Finset.univ.erase H78j.ind1H,
          star (coeff r) *
            ClassFunction.inner hBD_i.Gamma
              (H78j.nu (H78j.hyp76.zeta r)) := by
    calc
      ClassFunction.inner hBD_i.Gamma H78j.weightedNuSum =
          ClassFunction.inner hBD_i.Gamma
            (∑ r ∈ Finset.univ.erase H78j.ind1H,
              coeff r • H78j.nu (H78j.hyp76.zeta r)) :=
        congrArg (ClassFunction.inner hBD_i.Gamma) hW
      _ = ∑ r ∈ Finset.univ.erase H78j.ind1H,
          star (coeff r) *
            ClassFunction.inner hBD_i.Gamma
              (H78j.nu (H78j.hyp76.zeta r)) := by
        rw [OddOrder.RepresentationTheory.inner_sum_right]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [ClassFunction.inner_smul_right]
  have hWExpand :
      ClassFunction.inner H78j.weightedNuSum H78j.weightedNuSum =
        ∑ r ∈ Finset.univ.erase H78j.ind1H,
          star (coeff r) *
            ClassFunction.inner H78j.weightedNuSum
              (H78j.nu (H78j.hyp76.zeta r)) := by
    calc
      ClassFunction.inner H78j.weightedNuSum H78j.weightedNuSum =
          ClassFunction.inner H78j.weightedNuSum
            (∑ r ∈ Finset.univ.erase H78j.ind1H,
              coeff r • H78j.nu (H78j.hyp76.zeta r)) :=
        congrArg (ClassFunction.inner H78j.weightedNuSum) hW
      _ = ∑ r ∈ Finset.univ.erase H78j.ind1H,
          star (coeff r) *
            ClassFunction.inner H78j.weightedNuSum
              (H78j.nu (H78j.hyp76.zeta r)) := by
        rw [OddOrder.RepresentationTheory.inner_sum_right]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [ClassFunction.inner_smul_right]
  rw [hGammaExpand, hWExpand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hpoint r hr]
  ring

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
omit [Fintype ↥((F.H j).subgroupOf (F.L j))] in
/-- Rational-weight form of the Gamma projection identity used in Peterfalvi
(7.10). -/
theorem hypothesis79_gamma_inner_weightedNuSum_eq_mul_BsumWeight
    (hBD_i : (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).BetaDecomp)
    (hBD_j : (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).BetaDecomp)
    (hij : i ≠ j) (x : ℤ)
    (hx : ClassFunction.inner
        (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta 0)) =
      (x : ℂ)) :
    ClassFunction.inner hBD_i.Gamma
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum =
      (x : ℂ) * (F.BsumWeight j : ℂ) := by
  have : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  have : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  calc
    ClassFunction.inner hBD_i.Gamma
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum =
      (x : ℂ) * ClassFunction.inner
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum :=
      F.hypothesis79_gamma_inner_weightedNuSum_eq_mul_self
        hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j
        hBD_i hBD_j hij x hx
    _ = (x : ℂ) * (F.BsumWeight j : ℂ) := by
      rw [F.hypothesis78_weightedNuSum_inner_self_eq_BsumWeight
        j hodd hnilp_j C_j hFrob_j]

end CrossProjection

end FrobeniusFamily

namespace Cert

section ProjectionResidual

variable {G ι : Type*} [Group G]

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- **Peterfalvi (7.10), orthogonal projection residual.**  If a finite family
is orthogonal with diagonal weights m_j and Gamma has integer projection
coefficient x_j on every selected member, then subtracting those projections
constructs a residual orthogonal to the entire selected family. -/
theorem exists_orthogonal_projection_residual
    (B : Finset ι) (v : ι → ClassFunction G ℂ)
    (x : ι → ℤ) (m : ι → ℂ) (Γ : ClassFunction G ℂ)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then m i else 0)
    (hproj : ∀ j ∈ B,
      ClassFunction.inner Γ (v j) = (((x j : ℝ) : ℂ)) * m j) :
    ∃ Γ₁ : ClassFunction G ℂ,
      Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁ ∧
      ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0 := by
  classical
  let projection : ClassFunction G ℂ :=
    ∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)
  refine ⟨Γ - projection, ?_, ?_⟩
  · dsimp [projection]
    abel
  · intro j hj
    have hsum :
        ClassFunction.inner projection (v j) =
          (((x j : ℝ) : ℂ)) * m j := by
      change ClassFunction.inner
        (∑ l ∈ B, (((x l : ℝ) : ℂ) • v l)) (v j) =
          (((x j : ℝ) : ℂ)) * m j
      rw [OddOrder.RepresentationTheory.inner_sum_left,
        Finset.sum_eq_single_of_mem j hj (fun l hl hlj => by
          rw [ClassFunction.inner_smul_left, horth l hl j hj,
            if_neg hlj, mul_zero]),
        ClassFunction.inner_smul_left, horth j hj j hj, if_pos rfl]
    rw [ClassFunction.inner_sub_left, hsum, hproj j hj, sub_self]

end ProjectionResidual

end Cert

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

/-- **Peterfalvi (7.10), family-wide weighted Gamma decomposition.**  For a
selected member i and a finite set B of distinct other members, choose the
integral cross-family coefficients x_j.  The Gamma residual at i is the sum of
the corresponding orthogonal weighted coherent projections plus a residual
Gamma₁ orthogonal to every selected weighted sum. -/
theorem _root_.solution
    (i : Fin k) (B : Finset (Fin k))
    (hB : ∀ j ∈ B, i ≠ j) :
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
      ∀ j ∈ B, ClassFunction.inner Γ₁
        (F.weightedNuSumAt hodd hnilp C hFrob j) = 0 := by
  classical
  have hex : ∀ j : Fin k, ∃ x : ℤ,
      ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob i)
        (F.distinguishedNuAt hodd hnilp C hFrob j) = (x : ℂ) := by
    intro j
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
    simpa [betaAt, distinguishedNuAt] using
      (F.hypothesis79_exists_integral_beta_zeta_coefficient
        (i := i) (j := j) hodd
        (hnilp i) (C i) (hFrob i) (hnilp j) (C j) (hFrob j))
  choose x hx using hex
  have horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner
        (F.weightedNuSumAt hodd hnilp C hFrob j)
        (F.weightedNuSumAt hodd hnilp C hFrob l) =
          if j = l then (F.BsumWeight j : ℂ) else 0 := by
    intro j _hj l _hl
    by_cases hjl : j = l
    · subst l
      rw [if_pos rfl]
      let : Fintype ↥(F.L j) := Fintype.ofFinite _
      let : Invertible (Nat.card ↥(F.L j) : ℂ) :=
        invertibleOfNonzero
          (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
      let : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
      let : Invertible
          (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      let : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
      simpa [weightedNuSumAt] using
        (F.hypothesis78_weightedNuSum_inner_self_eq_BsumWeight
          j hodd (hnilp j) (C j) (hFrob j))
    · rw [if_neg hjl]
      let : Fintype ↥(F.L j) := Fintype.ofFinite _
      let : Invertible (Nat.card ↥(F.L j) : ℂ) :=
        invertibleOfNonzero
          (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
      let : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
      let : Invertible
          (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      let : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
      let : Fintype ↥(F.L l) := Fintype.ofFinite _
      let : Invertible (Nat.card ↥(F.L l) : ℂ) :=
        invertibleOfNonzero
          (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L l)).ne')
      let : Fintype ↥((F.H l).subgroupOf (F.L l)) := Fintype.ofFinite _
      let : Invertible
          (Nat.card ↥((F.H l).subgroupOf (F.L l)) : ℂ) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      let : ((F.H l).subgroupOf (F.L l)).Normal := (hFrob l).isNormal
      simpa [weightedNuSumAt] using
        (F.hypothesis79_weightedNuSum_cross_eq_zero
          (i := j) (j := l) hodd
          (hnilp j) (C j) (hFrob j) (hnilp l) (C l) (hFrob l) hjl)
  have hproj : ∀ j ∈ B,
      ClassFunction.inner
        (F.gammaAt hodd hnilp C hFrob i)
        (F.weightedNuSumAt hodd hnilp C hFrob j) =
          (((x j : ℝ) : ℂ)) * (F.BsumWeight j : ℂ) := by
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
    have hxj :
        ClassFunction.inner
          (F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).beta
          ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).nu
            ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).hyp76.zeta 0)) =
            (x j : ℂ) := by
      simpa [betaAt, distinguishedNuAt] using hx j
    have hp :=
      F.hypothesis79_gamma_inner_weightedNuSum_eq_mul_BsumWeight
        (i := i) (j := j) hodd
        (hnilp i) (C i) (hFrob i) (hnilp j) (C j) (hFrob j)
        (F.hypothesis78_betaDecomp i hodd (hnilp i) (C i) (hFrob i))
        (F.hypothesis78_betaDecomp j hodd (hnilp j) (C j) (hFrob j))
        (hB j hj) (x j) hxj
    have hcast : (((x j : ℝ) : ℂ)) = (x j : ℂ) := by
      norm_num
    rw [hcast]
    simpa [gammaAt, weightedNuSumAt] using hp
  obtain ⟨Γ₁, hdecomp, hΓ₁⟩ :=
    Cert.exists_orthogonal_projection_residual B
      (F.weightedNuSumAt hodd hnilp C hFrob) x
      (fun j => (F.BsumWeight j : ℂ))
      (F.gammaAt hodd hnilp C hFrob i)
      (fun j hj l hl => by
        rw [horth j hj l hl]
        by_cases hjl : j = l <;> simp [hjl])
      hproj
  exact ⟨x, Γ₁, hx, horth, hdecomp, hΓ₁⟩

end FamilyRealization

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
