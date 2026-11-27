-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.iOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:29.564805+00:00
-- url     : https://prove2.me/submissions/020af349-9062-427a-97df-f31970258f6f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_contDiff_of_differentiable_fd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_l2_sum_eq_sum_norm_sq_of_orthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (hJ : JStatement) (hN : NStatement) : IStatement := by
  unfold IStatement
  intro E _ _ _ X n nb bs hbs P π hπ s hs hs0 K hK
  obtain ⟨hmem, horth, hl2, hspan⟩ := hN E X P.q n π P.hq hπ s hs hs0 K hK
  obtain ⟨F, hF, hF1, hJF⟩ := hJ E X n nb bs hbs P
  have hUd : ∀ b ∈ K, Differentiable ℂ (X.U P.q b (s0 X π s)) := fun b hb => (hmem b hb).1
  have hUc : ∀ b ∈ K, Continuous (X.U P.q b (s0 X π s)) := fun b hb => (hUd b hb).continuous
  have hFspan := hspan hF
  rw [Finsupp.mem_span_image_iff_linearCombination] at hFspan
  obtain ⟨l, hl, hlF⟩ := hFspan
  have hsub : l.support ⊆ K := by
    have h := (Finsupp.mem_supported ℂ l).1 hl
    exact Finset.coe_subset.1 h
  have hFsum : F = fun v => ∑ b ∈ K, l b * X.U P.q b (s0 X π s) v := by
    rw [← hlF, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset l hsub (fun b a => a • X.U P.q b (s0 X π s))
        (fun b _ => zero_smul ℂ _)]
    funext v
    simp [Finset.sum_apply, smul_eq_mul]
  have hl2F : X.l2 P.q F = ∑ b ∈ K, ‖l b‖ ^ 2 * X.l2 1 s ^ n := by
    rw [hFsum, X.l2_sum_eq_sum_norm_sq_of_orthogonal P.q K l (fun b => X.U P.q b (s0 X π s)) hUc
      (fun b hb b' hb' hne => horth b hb b' hb' hne)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hl2 b hb]
  have hpd : polyDeriv (P1 bs) dir F 0 =
      ∑ b ∈ K, l b * polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0 := by
    rw [hFsum]
    exact polyDeriv_sum _ _ K l (fun b => X.U P.q b (s0 X π s))
      (fun b hb k => contDiff_of_differentiable_fd (hUd b hb) k) 0
  have hS : X.l2 1 s ^ n * ∑ b ∈ K, ‖l b‖ ^ 2 = 1 := by
    rw [← hF1, hl2F, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hSnn : 0 ≤ ∑ b ∈ K, ‖l b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hLpos : 0 < X.l2 1 s ^ n := by
    rcases le_or_gt (X.l2 1 s ^ n) 0 with h | h
    · nlinarith
    · exact h
  have hnorm : ‖polyDeriv (P1 bs) dir F 0‖ ≤
      ∑ b ∈ K, ‖l b‖ * ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ := by
    rw [hpd]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq K (fun b => ‖l b‖)
    (fun b => ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖)
  have h1 : ‖polyDeriv (P1 bs) dir F 0‖ ^ 2 ≤ (∑ b ∈ K, ‖l b‖ ^ 2) *
      ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2 := by
    refine le_trans ?_ hcs
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc P.Jbound n * X.l2 1 s ^ n ≤ ‖polyDeriv (P1 bs) dir F 0‖ ^ 2 * X.l2 1 s ^ n :=
        mul_le_mul_of_nonneg_right hJF hLpos.le
    _ ≤ ((∑ b ∈ K, ‖l b‖ ^ 2) *
          ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2) * X.l2 1 s ^ n :=
        mul_le_mul_of_nonneg_right h1 hLpos.le
    _ = ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2 := by
        rw [mul_comm (∑ b ∈ K, ‖l b‖ ^ 2), mul_assoc, mul_comm (∑ b ∈ K, ‖l b‖ ^ 2), hS, mul_one]
end ReciprocityTheory.ChartRestriction.G.I2
