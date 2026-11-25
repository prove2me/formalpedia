-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBNum.netHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:54.272834+00:00
-- url     : https://prove2.me/submissions/b10f80ab-871b-4c97-8eab-34b62bcae99a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ScaledBoundInequalityHypothesesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_SchwarzBallNumerics_NetForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBNum
open ComplexConjugate
namespace PI.UnitaryGroupMassFormula.TBNum
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.NetHermSt := by
  intro V _ _ ι _ ev
  have hF : ∀ F, ReciprocityTheory.ChartRestriction.G.TB.netForm ev F F
      = (((Fintype.card ι : ℝ)⁻¹ * ∑ y, Complex.normSq (ev y F) : ℝ) : ℂ) := by
    intro F
    simp only [ReciprocityTheory.ChartRestriction.G.TB.netForm, Complex.mul_conj]
    push_cast
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro F G
    simp only [ReciprocityTheory.ChartRestriction.G.TB.netForm, map_mul, map_sum, map_inv₀, map_natCast,
      Complex.conj_conj]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  · intro F
    rw [hF, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨rfl, mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun y _ => Complex.normSq_nonneg _)⟩
  · intro hinj F h0
    apply hinj F
    intro y
    rw [hF, Complex.ofReal_eq_zero] at h0
    have hne : (Fintype.card ι : ℝ) ≠ 0 := by
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨y⟩
      exact_mod_cast this.ne'
    have hs : ∑ y, Complex.normSq (ev y F) = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (inv_eq_zero.1 h) hne
      · exact h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => Complex.normSq_nonneg (ev y F))).1 hs y
      (Finset.mem_univ y)
    exact Complex.normSq_eq_zero.1 this
end PI.UnitaryGroupMassFormula.TBNum
