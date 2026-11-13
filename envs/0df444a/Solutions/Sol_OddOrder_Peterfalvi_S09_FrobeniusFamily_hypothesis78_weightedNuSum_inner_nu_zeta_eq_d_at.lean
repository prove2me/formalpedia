-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:26:11.410395+00:00
-- url     : https://prove2.me/submissions/032659d6-ef5c-4e03-9035-1ce3c41ca091

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaDecomposition

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
/-- The weighted coherent sum projects onto each non-principal source image
with coefficient equal to the corresponding local degree ratio. -/
theorem _root_.solution
    {r : Fin ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).ind1H) :
    ClassFunction.inner
        (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).weightedNuSum
        ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).nu
          ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta r)) =
      (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d r := by
  have : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  let H78 := localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hzeta : ∀ s, H78.hyp76.zeta s =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ s : ClassFunction _ ℂ) :=
    fun s => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) s
  have horth : ∀ s t, s ≠ t →
      ClassFunction.inner (H78.hyp76.zeta s) (H78.hyp76.zeta t) = 0 := by
    intro s t hst
    rw [hzeta s, hzeta t]
    exact Cert.induce_family_orthogonal_of_injective
      ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj s t hst
  have hnorm : ∀ s,
      ClassFunction.inner (H78.hyp76.zeta s) (H78.hyp76.zeta s) ≠ 0 := by
    intro s
    rw [hzeta s]
    exact Cert.induce_norm_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ s)
  have hz0 : H78.hyp76.zeta 0 (1 : ↥(F.L i)) ≠ 0 := by
    rw [hzeta 0]
    exact Cert.induce_apply_one_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  have hprojection := Cert.inner_weightedNuSum_nu_gen
    H78.hyp76.zeta horth hnorm hz0 H78.nu H78.nu_isometry hr
  change ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta r)) = H78.hyp76.d r
  rw [Hypothesis78.weightedNuSum,
    show H78.zetaDistinct = 0 from rfl, hprojection, div_eq_iff hz0]
  exact H78.hyp76.zeta_one_eq_d_mul r

end LocalCoefficient

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
