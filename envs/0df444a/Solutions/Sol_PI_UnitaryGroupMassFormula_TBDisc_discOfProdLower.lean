-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBDisc.discOfProdLower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:32.864788+00:00
-- url     : https://prove2.me/submissions/3ae4b6d0-6a8e-48d7-ade8-9f4cf1f55b5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBDisc
open NumberField ReciprocityTheory.ChartRestriction.G.TB
namespace PI.UnitaryGroupMassFormula.TBDisc
theorem _root_.solution : DiscOfProdLowerSt := by
  intro K _ _ V _ _ _ Nf M A h
  refine ⟨Real.exp (-|A|), Real.exp_pos _, fun f hf hs => ?_⟩
  by_contra hne
  have hA := h f hf hne
  have hpos : ∀ σ, 0 < Nf.N σ f := fun σ =>
    lt_of_le_of_ne (Nf.nonneg σ f) (fun h0 => hne (Nf.eq_zero σ f h0.symm))
  have hlt : ∑ σ : K →+* ℂ, Real.log (Nf.N σ f) < ∑ _σ : K →+* ℂ, (-|A|) := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun σ _ => ?_)
    have := Real.log_lt_log (hpos σ) (hs σ)
    rwa [Real.log_exp] at this
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  have hc : (1 : ℝ) ≤ (Fintype.card (K →+* ℂ) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1 : (Fintype.card (K →+* ℂ) : ℝ) * (-|A|) ≤ -|A| := by
    nlinarith [abs_nonneg A]
  linarith [le_abs_self A]
end PI.UnitaryGroupMassFormula.TBDisc
