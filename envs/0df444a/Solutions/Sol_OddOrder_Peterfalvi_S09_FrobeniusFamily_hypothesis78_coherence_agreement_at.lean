-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_coherence_agreement_at
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:28:51.134791+00:00
-- url     : https://prove2.me/submissions/2b0de41a-df21-4255-968a-48820a7f16e4

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
/-- On every nonzero, non-principal member, the concrete coherent extension
agrees with the Dade map on the degree-zero source difference. -/
theorem _root_.solution
    {r : Fin ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).ind1H) :
    (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.hyp71.τ
        ⟨(localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta r -
            (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d r •
              (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta 0,
          (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.psi_support r⟩ =
      (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).nu
          ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta r) -
        (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d r •
          (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).nu
            ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta 0) := by
  have : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  classical
  let H78 := localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hzeta : ∀ s, H78.hyp76.zeta s =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ s : ClassFunction _ ℂ) :=
    fun s => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) s
  have hθ_ne : ∀ s, s ≠ pf.ind1H →
      pf.θ s ≠ trivialIrreducibleCharacter _ := by
    intro s hs h
    exact hs (pf.inj (by simp only [h, pf.triv]))
  have hr_mem : H78.hyp76.zeta r ∈
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S :=
    ⟨pf.θ r, hθ_ne r hr, hzeta r⟩
  have h0_mem : H78.hyp76.zeta 0 ∈
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S :=
    ⟨pf.θ 0, hθ_ne 0 (Ne.symm pf.ind1H_ne_zero), hzeta 0⟩
  obtain ⟨deg_r, -, hdeg_r⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (pf.θ r)
  obtain ⟨deg_0, hdeg_0_pos, hdeg_0⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (pf.θ
      (0 : Fin (H78.hyp76.n + 1)))
  have hdeg_0_ne : (deg_0 : ℂ) ≠ 0 := by
    exact_mod_cast hdeg_0_pos.ne'
  have hidx_ne : (((F.H i).subgroupOf (F.L i)).index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  have hzr :
      H78.hyp76.zeta r (1 : ↥(F.L i)) =
        (((F.H i).subgroupOf (F.L i)).index : ℂ) * (deg_r : ℂ) := by
    rw [hzeta r, ClassFunction.induce_apply_one, hdeg_r]
  have hz0 :
      H78.hyp76.zeta 0 (1 : ↥(F.L i)) =
        (((F.H i).subgroupOf (F.L i)).index : ℂ) * (deg_0 : ℂ) := by
    rw [hzeta 0, ClassFunction.induce_apply_one]
    exact congrArg (((((F.H i).subgroupOf (F.L i)).index : ℂ)) * ·) hdeg_0
  have hd : H78.hyp76.d r = (deg_r : ℂ) / (deg_0 : ℂ) := by
    have h := H78.hyp76.zeta_one_eq_d_mul r
    rw [hzr, hz0] at h
    rw [eq_div_iff hdeg_0_ne]
    apply mul_left_cancel₀ hidx_ne
    linear_combination -h
  have hagree := Cert.coherence_hagree_dadeMap
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
    (F.coherence i hodd hnilp C hFrob) hr_mem h0_mem
    (m0 := deg_0) (mi := deg_r) hdeg_0_ne hd
    (H78.hyp76.psi_support r)
  rw [F.hypothesis78_nu_eq i hodd hnilp C hFrob]
  exact hagree

end LocalCoefficient

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
