-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.int_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:55.176145+00:00
-- url     : https://prove2.me/submissions/5888abdb-55cc-4e74-ab40-6f7f473bc65f

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_val_pow_le
import Theorems.Thm_PositivityTheory_ThKG_Std_int_ind_pow
import Theorems.Thm_PositivityTheory_ThKG_Std_res_eq_iff
import Theorems.Thm_GlobalTheory_Doubling_IsRightSmooth_continuous
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_PositivityTheory_ThKG_Std_lc_ind
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hm : IsVol m) (hϖ : IsUnif ϖ) (c : ℕ) (f : k → ℂ) (h0 : ∀ x, ¬ valuation k x ≤ 1 → f x = 0)
    (hf : ∀ x t, valuation k t ≤ valuation k ((ϖ : k) ^ c) → f (x + t) = f x) :
    ∫ x, f x ∂m = ((resCard k : ℂ) ^ c)⁻¹ * ∑ᶠ y : Res k c, f ((Quotient.out y : 𝒪[k]) : k) := by
  haveI := hm.haar
  haveI := Fintype.ofFinite (Res k c)
  have e : f = fun x => ∑ y : Res k c, f ((Quotient.out y : 𝒪[k]) : k) * ind ((ϖ : k) ^ c) (x - (Quotient.out y : 𝒪[k])) := by
    funext x
    by_cases hx : valuation k x ≤ 1
    · rw [Finset.sum_eq_single (Ideal.Quotient.mk _ (⟨x, hx⟩ : 𝒪[k]))]
      · have := (res_eq_iff hϖ c ⟨x, hx⟩ _).1 (Ideal.Quotient.mk_out _).symm
        rw [ind, if_pos this, mul_one]
        exact ((hf _ _ this).symm.trans (by rw [add_sub_cancel])).symm
      · intro y _ hy
        rw [ind, if_neg, mul_zero]
        intro h
        exact hy (((res_eq_iff hϖ c ⟨x, hx⟩ _).2 h).trans (Ideal.Quotient.mk_out _)).symm
      · simp
    · rw [h0 x hx]
      refine (Finset.sum_eq_zero fun y _ => ?_).symm
      rw [ind, if_neg, mul_zero]
      intro h
      have := Valuation.map_add_le _ (h.trans (val_pow_le hϖ c)) (Quotient.out y : 𝒪[k]).2
      rw [sub_add_cancel] at this
      exact hx this
  have hi : Integrable (ind ((ϖ : k) ^ c)) m :=
    (lc_ind (pow_ne_zero _ ϖ.ne_zero)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k ((ϖ : k) ^ c)))
        fun x hx => by unfold ind; exact if_neg hx)
  conv_lhs => rw [e]
  rw [integral_finset_sum _ fun y _ => (hi.comp_sub_right _).const_mul _, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_const_mul, integral_sub_right_eq_self, int_ind_pow hm hϖ, mul_comm]
end PositivityTheory.ThKG.Std
