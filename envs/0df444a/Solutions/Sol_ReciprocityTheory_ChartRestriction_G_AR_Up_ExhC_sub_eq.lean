-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC.sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:38.556613+00:00
-- url     : https://prove2.me/submissions/3cd7e85d-1389-4bbc-9a4b-195cf0988ca5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_re_pos_im


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
variable {f p q N' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
theorem _root_.solution (a : ℝ) :
    {v : V (nD f p q + N') | v ∈ OmSet f p q N' ∧ eOm v ≤ a} =
      {v | (∀ k, (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).PosSemidef) ∧
        Real.exp (Real.log (1 + ‖tPart v‖ ^ 2) - a) ≤ ∏ k, dk (zPart v) k} := by
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hv, he⟩
    have hpos : ∀ k, 0 < dk (zPart v) k := fun k => (det_re_pos_im (hv k)).1
    have hG : 0 < ∏ k, dk (zPart v) k := Finset.prod_pos fun k _ => hpos k
    have hr : rh (zPart v) = -Real.log (∏ k, dk (zPart v) k) := by
      rw [Real.log_prod (fun k _ => (hpos k).ne')]; rfl
    refine ⟨fun k => (hv k).posSemidef, ?_⟩
    unfold eOm at he
    rw [hr] at he
    calc Real.exp (Real.log (1 + ‖tPart v‖ ^ 2) - a) ≤ Real.exp (Real.log (∏ k, dk (zPart v) k)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = _ := Real.exp_log hG
  · rintro ⟨hpsd, hle⟩
    have hG : 0 < ∏ k, dk (zPart v) k := (Real.exp_pos _).trans_le hle
    have hne : ∀ k, dk (zPart v) k ≠ 0 := by
      intro k hk
      have := Finset.prod_eq_zero (Finset.mem_univ k) hk
      rw [this] at hG; exact lt_irrefl _ hG
    have hv : v ∈ OmSet f p q N' := by
      intro k
      refine (hpsd k).posDef_iff_det_ne_zero.2 fun h => hne k ?_
      simp [dk, h]
    have hpos : ∀ k, 0 < dk (zPart v) k := fun k => (det_re_pos_im (hv k)).1
    have hr : rh (zPart v) = -Real.log (∏ k, dk (zPart v) k) := by
      rw [Real.log_prod (fun k _ => (hpos k).ne')]; rfl
    refine ⟨hv, ?_⟩
    unfold eOm
    rw [hr]
    have := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at this
    linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
