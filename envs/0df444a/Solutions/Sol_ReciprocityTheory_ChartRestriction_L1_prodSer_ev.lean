-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.prodSer_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:07.050541+00:00
-- url     : https://prove2.me/submissions/08389cfb-2319-4443-9c47-f2cfc748ae94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_summable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_facSer_conv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_facSer_ev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {m : ℕ} (hm : 0 < m) (τ : ℍ) : ev (prodSer m) (qm m τ) = Gm m τ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : ‖qm m τ‖ < 1 := by
    unfold qm
    rw [Complex.norm_exp]
    have e : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / (m : ℂ)).re = -(2 * Real.pi * τ.im) / m := by
      rw [Complex.div_natCast_re]
      simp
    rw [e, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos, τ.im_pos]) hm')
  have h1 : Conv (1 : PowerSeries ℂ) := by
    intro x _
    refine (hasSum_single 0 fun n hn => ?_).summable
    simp [PowerSeries.coeff_one, hn]
  have key : ∀ s ⊆ Tm m, Conv (∏ t ∈ s, facSer m t) ∧
      ev (∏ t ∈ s, facSer m t) (qm m τ) = ∏ t ∈ s, fac t τ := by
    intro s
    classical
    refine Finset.induction_on s ?_ ?_
    · intro _
      refine ⟨by simpa using h1, ?_⟩
      simp only [Finset.prod_empty]
      unfold ev
      rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]
      simp
    · intro a s ha ih hs
      have has : a ∈ Tm m := hs (Finset.mem_insert_self a s)
      obtain ⟨c1, c2⟩ := ih fun y hy => hs (Finset.mem_insert_of_mem hy)
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact ⟨(facSer_conv hm has).mul c1, by
        rw [ev_mul (facSer_conv hm has) c1 hx, facSer_ev hm has, c2]⟩
  unfold prodSer Gm
  exact (key _ subset_rfl).2
end ReciprocityTheory.ChartRestriction.L1
