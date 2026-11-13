-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Q_sharp_tau_eq_induce
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:55:38.294467+00:00
-- url     : https://prove2.me/submissions/945ae013-1585-49f9-9607-ad198c6d473d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/TISubsetCounting.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Theorems.Thm_OddOrder_GroupTheory_IsTISubset_induce_apply_of_mem_conj

-- ===== OddOrder/GroupTheory/TISubsetCounting.lean =====
namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

open scoped Pointwise

/-- **Induced value off the TI-saturation**: an `A`-supported class function of `L` induces to
a function vanishing off the conjugacy saturation `A^G` — every induction summand lands
outside the support. -/
theorem induce_apply_of_not_mem_conjClassSet {k : Type*} [Field k] [Fintype G]
    {A : Set G} {L : Subgroup G} [Invertible (Nat.card ↥L : k)]
    (α : OddOrder.RepresentationTheory.ClassFunction ↥L k)
    (hsupp : ∀ w : ↥L, (w : G) ∉ A → α w = 0)
    {g : G} (hg : g ∉ conjClassSet A) :
    OddOrder.RepresentationTheory.ClassFunction.induce L α g = 0 := by
  classical
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply]
  have hterm : ∀ x : G, OddOrder.RepresentationTheory.ClassFunction.induceTerm L α x g = 0 := by
    intro x
    by_cases hmemL : x⁻¹ * g * x ∈ L
    · rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_mem α hmemL]
      refine hsupp _ (fun hmemA => hg ?_)
      rw [mem_conjClassSet]
      exact ⟨x⁻¹ * g * x, hmemA, x, by group⟩
    · exact OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_not_mem α hmemL
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const_zero, mul_zero]

end IsTISubset

end OddOrder.GroupTheory

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

open scoped FiniteInduce in
/-- **Peterfalvi (13.2.e)/(7.2)-for-`T`: the `(T, Q^#)` Dade isometry is `Ind_T^G`** (mirror of
`H_sharp_tau_eq_induce`, issue 2035 #22 T-side twin): for the TI-subset construction (all local
subgroups trivial) the Dade map and the induction agree pointwise — on the conjugacy saturation
of `Q^#` both take the base value, and both vanish off it.  This is the link between the
`T`-side (7.7.a) coefficients `c_i = ⟨τψ_i, χ⟩` and the τ₁T-coherence
(`coherentIndT_pinned .extends_on_supported`). -/
theorem _root_.solution [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T) :
    (Q_sharp_hypothesis71 hG hyp hvd).τ α
      = ClassFunction.induce hyp.T (α : ClassFunction ↥hyp.T ℂ) := by
  classical
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hAL : OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) ⊆ (hyp.T : Set G) := fun x hx =>
    hQT (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1
  have hsupp : ∀ w : ↥hyp.T, (w : G) ∉ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) →
      (α : ClassFunction ↥hyp.T ℂ) w = 0 := by
    intro w hw
    by_contra hne
    exact hw (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp
      (α.2 (ClassFunction.mem_support.mpr hne)))
  have hstab : ∀ l ∈ hyp.T,
      MulAut.conj l • (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G))
        = OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) := by
    intro l hl
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      simp only [MulAut.smul_def, MulAut.conj_apply]
      exact T_normalizes_Q_sharp hG hyp ⟨l, hl⟩ ha
    · intro hx
      refine ⟨l⁻¹ * x * l, ?_, ?_⟩
      · have := T_normalizes_Q_sharp hG hyp (⟨l, hl⟩ : ↥hyp.T)⁻¹ hx
        simpa using this
      · simp only [MulAut.smul_def, MulAut.conj_apply]
        group
  ext g
  by_cases hg : g ∈ OddOrder.GroupTheory.conjClassSet
      (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G))
  · obtain ⟨a, ha, y, hy⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hg
    rw [OddOrder.Peterfalvi.S04.map_eq_of_isConj_of_forall_H_eq_bot
        (Q_sharp_hypothesis71 hG hyp hvd).isDadeMap (fun _ => rfl) α ha
        (isConj_iff.mpr ⟨y, hy⟩),
      OddOrder.GroupTheory.IsTISubset.induce_apply_of_mem_conj (Q_sharp_isTISubset hG hyp hvd)
        hAL hstab (α : ClassFunction ↥hyp.T ℂ) hsupp ha hy.symm]
  · have hg' : g ∉ Group.conjugatesOfSet (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) := by
      intro hmem
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hmem
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      exact hg (OddOrder.GroupTheory.mem_conjClassSet.mpr ⟨a, ha, c, hc⟩)
    rw [OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
        (Q_sharp_hypothesis71 hG hyp hvd).isDadeMap (fun _ => rfl) α hg',
      OddOrder.GroupTheory.IsTISubset.induce_apply_of_not_mem_conjClassSet
        (α : ClassFunction ↥hyp.T ℂ) hsupp hg]

end CountingLayer

end OddOrder.Peterfalvi.S15
