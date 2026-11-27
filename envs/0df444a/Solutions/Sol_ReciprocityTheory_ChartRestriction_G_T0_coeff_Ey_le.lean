-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeff_Ey_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:43:16.353667+00:00
-- url     : https://prove2.me/submissions/0f99f4dc-8fd5-4716-8cf3-9ca60ff017fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLeSqrtCardMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_card_support_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sum_le_sqrt_card_mul
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_torus_l2_cauchy_inequality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {D N n n' : ℕ} (R : MvPolynomial (UXVar D N) ℂ) (hx : XHom n R)
    (hu : UDegLE n' R) (y : Fin (N + 1) → ℂ) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    ‖coeff β (Ey y R)‖ ≤ ReciprocityTheory.MultiplicativeHeights.polyL2 R *
      Real.sqrt ((n + D + 1).choose (D + 1) *
        (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) * (∑ j, ‖y j‖) ^ n := by
  obtain ⟨θ, hθ⟩ := (ReciprocityTheory.MultiplicativeHeights.Closed.torus_l2_cauchy_inequality _ (Ey y R)).2 β
  set z := ReciprocityTheory.MultiplicativeHeights.torusPoint θ with hzdef
  have hz : ∀ p, ‖z p‖ = 1 := by
    intro p
    simp only [hzdef, ReciprocityTheory.MultiplicativeHeights.torusPoint]
    rw [Complex.norm_exp]
    simp
  set Y := ∑ j, ‖y j‖ with hY
  set pt : UXVar D N → ℂ := fun v => eval z (Sum.elim X (fun i => ∑ j, X (i, j) * C (y j)) v)
    with hpt
  have hev : eval z (Ey y R) = eval pt R := by
    have := congrArg (fun φ => φ R)
      (MvPolynomial.comp_aeval (R := ℂ) (Sum.elim X fun i => ∑ j, X (i, j) * C (y j))
        (aeval z))
    simp only [AlgHom.comp_apply] at this
    calc eval z (Ey y R) = aeval z (Ey y R) := by simp
      _ = _ := this
      _ = eval pt R := by simp [hpt]
  have hpt1 : ∀ p, ‖pt (Sum.inl p)‖ = 1 := fun p => by simp [hpt, hz]
  have hpt2 : ∀ i, ‖pt (Sum.inr i)‖ ≤ Y := by
    intro i
    simp only [hpt, Sum.elim_inr, map_sum, map_mul, eval_X, eval_C]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, hz, one_mul]
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hmono : ∀ α ∈ R.support, ‖∏ v, pt v ^ α v‖ ≤ Y ^ n := by
    intro α hα
    rw [norm_prod, Fintype.prod_sum_type]
    simp only [norm_pow, hpt1, one_pow, Finset.prod_const_one, one_mul]
    calc ∏ i, ‖pt (Sum.inr i)‖ ^ α (Sum.inr i) ≤ ∏ i, Y ^ α (Sum.inr i) :=
          Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hpt2 i) _
      _ = Y ^ n := by rw [Finset.prod_pow_eq_pow_sum, ← hx α hα]; rfl
  have hcard := card_support_le R hx hu
  calc ‖coeff β (Ey y R)‖ ≤ ‖eval z (Ey y R)‖ := hθ
    _ = ‖∑ α ∈ R.support, coeff α R * ∏ v, pt v ^ α v‖ := by rw [hev, eval_eq']
    _ ≤ ∑ α ∈ R.support, ‖coeff α R‖ * Y ^ n := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmono α hα) (norm_nonneg _)
    _ = (∑ α ∈ R.support, ‖coeff α R‖) * Y ^ n := by rw [Finset.sum_mul]
    _ ≤ (Real.sqrt R.support.card * ReciprocityTheory.MultiplicativeHeights.polyL2 R) * Y ^ n := by
        gcongr
        exact sum_le_sqrt_card_mul _ _
    _ ≤ _ := by
        rw [mul_comm (Real.sqrt _) (ReciprocityTheory.MultiplicativeHeights.polyL2 R)]
        gcongr
        unfold ReciprocityTheory.MultiplicativeHeights.polyL2; positivity
end ReciprocityTheory.ChartRestriction.G.T0
