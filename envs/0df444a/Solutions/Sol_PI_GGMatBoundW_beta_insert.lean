-- Prove2me | solution 1 for PI.GGMatBoundW.beta_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:45.008188+00:00
-- url     : https://prove2.me/submissions/dc684cee-1238-488b-bbf8-a7c1a447ee64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_ProdFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
namespace PI.GGMatBoundW
theorem _root_.solution (ψ : ∀ v, AddChar (Fq v) ℂ) {a : ι} {s : Finset ι} (ha : a ∉ s)
    (z : ∀ v, GL (Fin k) (Fq v)) :
    beta ψ (insert a s) z =
      ∑ y : GL (Fin k) (Fq a), gam (ψ a) y * beta ψ s ((Pi.mulSingle a y)⁻¹ * z) := by
  have hz : ∀ w, ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = if w = a then 1 else z w := by
    intro w
    by_cases hw : w = a
    · subst hw
      simp
    · simp [hw, Pi.mulSingle_eq_of_ne hw]
  rw [Finset.sum_eq_single (z a)]
  · unfold beta
    have hcond : (∀ w, w ∉ insert a s → z w = 1) ↔
        (∀ w, w ∉ s → ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = 1) := by
      constructor
      · intro h w hw
        rw [hz]
        by_cases hwa : w = a
        · rw [if_pos hwa]
        · rw [if_neg hwa]
          exact h w (by simp [hwa, hw])
      · intro h w hw
        simp only [Finset.mem_insert, not_or] at hw
        have := h w hw.2
        rwa [hz, if_neg hw.1] at this
    have hprod : ∏ v ∈ s, gam (ψ v) (((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) v) =
        ∏ v ∈ s, gam (ψ v) (z v) := by
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [hz, if_neg (fun (h : v = a) => ha (h ▸ hv))]
    by_cases h : ∀ w, w ∉ insert a s → z w = 1
    · rw [if_pos h, if_pos (hcond.mp h), hprod, Finset.prod_insert ha]
    · rw [if_neg h, if_neg (fun h' => h (hcond.mpr h')), mul_zero]
  · intro y _ hy
    unfold beta
    rw [if_neg, mul_zero]
    intro h
    apply hy
    have := h a ha
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at this
    exact inv_mul_eq_one.mp this
  · intro h
    exact absurd (Finset.mem_univ _) h
end PI.GGMatBoundW
