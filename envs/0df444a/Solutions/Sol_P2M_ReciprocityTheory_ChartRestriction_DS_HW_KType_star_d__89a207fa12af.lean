-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_star_d__89a207fa12af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:55:34.702803+00:00
-- url     : https://prove2.me/submissions/69aae61d-7a17-4451-8be1-114cd699eec4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_curve


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
namespace KType
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : star (T.dτ X) = -T.dτ X := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := T.dτ X
  have key : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • star A) * NormedSpace.exp ((t : ℂ) • A) = 1 := by
    intro t
    have h1 := KType.op_curve T hX γ hγ t
    have h2 : star (T.op (γ t)) * T.op (γ t) = 1 := Unitary.coe_star_mul_self _
    rw [h1, NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal] at h2
    exact h2
  have hd0 := (hasDerivAt_exp_smul_const (star A) ((0 : ℝ) : ℂ)).mul
    (hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ))
  have hd2 := hasDerivAt_real_of_complex' hd0
  have hf : (fun y : ℝ => ((fun u : ℂ => NormedSpace.exp (u • star A)) *
      fun u : ℂ => NormedSpace.exp (u • A)) (y : ℂ)) = fun _ => 1 := funext fun t => by
    simpa using key t
  rw [hf] at hd2
  have := hd2.unique (hasDerivAt_const _ _)
  simp at this
  exact eq_neg_of_add_eq_zero_left this
end KType
end ReciprocityTheory.ChartRestriction.DS.HW
