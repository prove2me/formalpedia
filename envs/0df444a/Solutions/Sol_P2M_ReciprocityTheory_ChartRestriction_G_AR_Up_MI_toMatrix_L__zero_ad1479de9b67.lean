-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_toMatrix_L__zero_ad1479de9b67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:23.605881+00:00
-- url     : https://prove2.me/submissions/fcfa66e0-11f3-474c-81c0-9a3ccbc31984

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
private lemma toMatrix_entry_lemma (β : ι → Matrix (Fin r) (Fin r) ℂ) (i j : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i j =
      if j.1.1 = i.1.1 ∧ j.1.2.2 = i.1.2.2 then β i.1.1 i.1.2.1 j.1.2.1 else 0 := by
  obtain ⟨⟨τ, a, b⟩, hi⟩ := i
  obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
  rw [LinearMap.toMatrix'_apply]
  simp only [Lβ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Umat, Matrix.of_apply]
  rw [Finset.sum_eq_single a']
  · by_cases h : τ' = τ ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hj, Pi.single_apply]
    · rw [if_neg h]
      split_ifs with h'
      · simp
      · rw [Pi.single_apply, if_neg, mul_zero]
        intro heq
        apply h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.2.symm⟩
  · intro c _ hc
    split_ifs with h'
    · simp
    · rw [Pi.single_apply, if_neg, mul_zero]
      intro heq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
      exact hc heq.2.1
  · simp
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (e : ι ≃ Fin (Fintype.card ι)) (β : ι → Matrix (Fin r) (Fin r) ℂ)
    (hβ : ∀ τ, (β τ).BlockTriangular id) (i j : UpI ι r) (hij : keyU e i < keyU e j) :
    LinearMap.toMatrix' (Lβ β) i j = 0 := by
  rw [toMatrix_entry_lemma]
  split_ifs with h
  · obtain ⟨⟨τ, a, b⟩, hi⟩ := i
    obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
    obtain ⟨rfl, rfl⟩ := h
    simp only [keyU, Prod.Lex.toLex_lt_toLex, lt_irrefl, false_or, and_false, or_false,
      true_and] at hij
    apply hβ _
    have := a.isLt; have := a'.isLt
    show (a' : ℕ) < a
    omega
  · rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
