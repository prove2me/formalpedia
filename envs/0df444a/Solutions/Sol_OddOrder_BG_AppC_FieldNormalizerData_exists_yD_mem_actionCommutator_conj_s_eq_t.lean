-- Prove2me | solution 1 for OddOrder.BG.AppC.FieldNormalizerData.exists_yD_mem_actionCommutator_conj_s_eq_t
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:21:57.476216+00:00
-- url     : https://prove2.me/submissions/74f10d47-670d-4dc4-b9c7-7c12f5142f60

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine

-- ===== OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean =====
namespace OddOrder.BG.AppC

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The orders of `W₂ = σ(P₀)` and `Q` are coprime: `|W₂| = p` is prime, `|Q|`
is a power of `q`, and `p ≠ q`.  This is the coprimality input to BG Appendix C
Remark (X)'s coprime decomposition `Q = C_Q(P₀) × ⁅Q, P₀⁆` (Isaacs Thm 4.34 /
BG Prop 1.6(d)), used in the Lemma C.3 Step 4 kernel argument. -/
theorem W2_card_coprime_Q_card (data : FieldNormalizerData p q G) :
    Nat.Coprime (Nat.card ↥data.W2) (Nat.card ↥data.Q) := by
  rw [data.card_W2]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr data.Q_pPrime

/-- The `W₂`-conjugation action on `Q`, read in the ambient group `G`: it is
genuine conjugation `w x w⁻¹`. -/
theorem w2ConjQAut_apply_coe (data : FieldNormalizerData p q G)
    (w : ↥data.W2) (x : ↥data.Q) :
    ((data.w2ConjQAut w x : ↥data.Q) : G) = (w : G) * (x : G) * (w : G)⁻¹ := rfl

/-- **BG Appendix C, Remark (XI)**: we may assume `y ∈ ⁅Q, P₀⁆`.  Writing the
coprime decomposition `Q = ⁅Q,W₂⁆ · C_Q(W₂)`, the centralizer component `yC` of
`y` commutes with `s ∈ W₂`, so the conjugate generator `t = y s y⁻¹` is already
produced by the action-commutator component `yD ∈ ⁅Q, W₂⁆`: `t = yD s yD⁻¹`. -/
theorem _root_.solution
    (data : FieldNormalizerData p q G) :
    ∃ yD : ↥data.Q,
      yD ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ∧
        MulAut.conj (yD : G) data.s = data.t := by
  have := data.Q_commutative
  let : CommGroup ↥data.Q :=
    { (inferInstance : Group ↥data.Q) with
      mul_comm := fun a b => Subtype.ext (setLike_mul_comm (s := data.Q) a.2 b.2) }
  have hsup : OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ⊔
      Subgroup.fixedPointsOfMulAut data.w2ConjQAut = ⊤ := by
    rw [sup_comm]
    exact OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      data.W2_card_coprime_Q_card (Or.inr inferInstance)
  have hmem : (⟨data.y, data.y_mem_Q⟩ : ↥data.Q) ∈
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ⊔
        Subgroup.fixedPointsOfMulAut data.w2ConjQAut := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨yD, hyD, yC, hyC, hyDyC⟩ := hmem
  refine ⟨yD, hyD, ?_⟩
  have hyC_s : (yC : G) * data.s = data.s * (yC : G) := by
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hyC ⟨data.s, data.s_mem_W2⟩
    have hcoe := congrArg (Subtype.val) hfix
    rw [data.w2ConjQAut_apply_coe] at hcoe
    exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
  have hconj_raw : (yC : G) * data.s * (yC : G)⁻¹ = data.s := by
    rw [hyC_s]; group
  have hy_coe : (data.y : G) = (yD : G) * (yC : G) := by
    have h := congrArg (Subtype.val) hyDyC
    simpa using h.symm
  change MulAut.conj (yD : G) data.s = MulAut.conj data.y data.s
  rw [MulAut.conj_apply, MulAut.conj_apply, hy_coe, mul_inv_rev,
    show (yD : G) * (yC : G) * data.s * ((yC : G)⁻¹ * (yD : G)⁻¹)
        = (yD : G) * ((yC : G) * data.s * (yC : G)⁻¹) * (yD : G)⁻¹ by group,
    hconj_raw]

end FieldNormalizerData

end OddOrder.BG.AppC
