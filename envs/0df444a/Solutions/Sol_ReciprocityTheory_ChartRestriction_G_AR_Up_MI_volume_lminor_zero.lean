-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.volume_lminor_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:25.658195+00:00
-- url     : https://prove2.me/submissions/9c5ff1d3-94f8-46c0-8710-18abebf03851

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_volume_null_of_slice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_diff_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_continuous_lminor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (τ : ι) :
    ∀ k (h : k < r + 1), volume {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k, h⟩ = 0} = 0 := by
  intro k
  induction k with
  | zero =>
    intro h
    have hempty : {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨0, h⟩ = 0} = ∅ := by
      ext v
      simp [lminor]
    rw [hempty, measure_empty]
  | succ k ih =>
    intro h
    have hk : k < r + 1 := by omega
    have hkr : k < r := by omega
    have hl : (Fin.castLE (Nat.le_of_lt_succ h) (Fin.last k) : Fin r) = ⟨k, hkr⟩ :=
      Fin.ext (by simp)
    have key : ∀ w : Ix ι r → ℂ, lminor (Mt w τ) ⟨k, hk⟩ =
        (((Mt w τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h))).submatrix
          Fin.castSucc Fin.castSucc).det := fun w => rfl
    have hmeas : MeasurableSet {v : Ix ι r → ℂ |
        lminor (Mt v τ) ⟨k + 1, h⟩ = 0 ∧ lminor (Mt v τ) ⟨k, hk⟩ ≠ 0} :=
      (isClosed_eq (continuous_lminor τ _) continuous_const).measurableSet.inter
        (isClosed_eq (continuous_lminor τ _) continuous_const).isOpen_compl.measurableSet
    refine measure_mono_null (t := {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k, hk⟩ = 0} ∪
      {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k + 1, h⟩ = 0 ∧ lminor (Mt v τ) ⟨k, hk⟩ ≠ 0}) ?_ ?_
    · intro v hv
      by_cases h0 : lminor (Mt v τ) ⟨k, hk⟩ = 0
      · exact Or.inl h0
      · exact Or.inr ⟨hv, h0⟩
    refine measure_union_null (ih hk) ?_
    refine volume_null_of_slice (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) hmeas ?_
    intro v hv v' hv' hagree
    have dd := det_diff_last
      ((Mt v τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h)))
      ((Mt v' τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h)))
      (by
        intro a b hab
        refine hagree _ fun heq => hab ?_
        simp only [Prod.mk.injEq, Fin.ext_iff, Fin.coe_castLE] at heq
        exact ⟨Fin.ext (by simp [heq.2.1]), Fin.ext (by simp [heq.2.2])⟩)
    have h1 : lminor (Mt v τ) ⟨k + 1, h⟩ = 0 := hv.1
    have h2 : lminor (Mt v' τ) ⟨k + 1, h⟩ = 0 := hv'.1
    have hm : lminor (Mt v τ) ⟨k, hk⟩ ≠ 0 := hv.2
    rw [key v] at hm
    simp only [lminor] at h1 h2
    rw [h1, h2, sub_zero] at dd
    simp only [Matrix.submatrix_apply, hl] at dd
    have hz : v (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) - v' (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) = 0 := by
      rcases mul_eq_zero.1 dd.symm with hz | hz
      · exact hz
      · exact absurd hz hm
    funext j
    by_cases hj : j = (τ, ⟨k, hkr⟩, ⟨k, hkr⟩)
    · subst hj; exact sub_eq_zero.1 hz
    · exact hagree j hj
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
