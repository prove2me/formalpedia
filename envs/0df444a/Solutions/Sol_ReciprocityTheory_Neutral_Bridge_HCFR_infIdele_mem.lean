-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:55.962832+00:00
-- url     : https://prove2.me/submissions/2b2d40fa-0606-4584-87cd-c577ce05bb1e

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (N : Subgroup (Ideles K)) (m : ℕ) (hm : 0 < m) (hpow : ∀ x : Ideles K, x ^ m ∈ N)
    (hneg : ∀ w : InfinitePlace K, w.IsReal → infIdele K w (-1) ∈ N) (w : InfinitePlace K)
    (y : (w.Completion)ˣ) : infIdele K w y ∈ N := by
  have key : ∀ z : (w.Completion)ˣ, infIdele K w (z ^ m) ∈ N := fun z => by
    rw [map_pow]
    exact hpow _
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  ·
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hr : e (y : w.Completion) ≠ 0 := (map_ne_zero e).2 y.ne_zero
    have hs : (|e (y : w.Completion)| ^ ((m : ℝ)⁻¹)) ^ m = |e (y : w.Completion)| :=
      Real.rpow_inv_natCast_pow (abs_nonneg _) hm.ne'
    have hs0 : e.symm (|e (y : w.Completion)| ^ ((m : ℝ)⁻¹)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ e.symm.injective]
      intro h0
      rw [h0, zero_pow hm.ne'] at hs
      exact hr (abs_eq_zero.1 hs.symm)
    let z : (w.Completion)ˣ := Units.mk0 _ hs0
    rcases lt_or_gt_of_ne hr with hneg' | hpos
    · have hy : y = -1 * z ^ m := by
        apply Units.ext
        apply e.injective
        simp only [z, Units.val_mul, Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val,
          Units.val_mk0, map_mul, map_neg, map_one, map_pow, RingEquiv.apply_symm_apply]
        rw [hs, abs_of_neg hneg']
        ring
      rw [hy, map_mul]
      exact N.mul_mem (hneg w hw) (key z)
    · have hy : y = z ^ m := by
        apply Units.ext
        apply e.injective
        simp only [z, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, RingEquiv.apply_symm_apply]
        rw [hs, abs_of_pos hpos]
      rw [hy]
      exact key z
  ·
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hm
    have hc0 : e.symm c ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ e.symm.injective]
      rintro rfl
      rw [zero_pow hm.ne'] at hc
      exact (map_ne_zero e).2 y.ne_zero hc.symm
    let z : (w.Completion)ˣ := Units.mk0 _ hc0
    have hy : y = z ^ m := by
      apply Units.ext
      apply e.injective
      simp only [z, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, RingEquiv.apply_symm_apply, hc]
    rw [hy]
    exact key z
end ReciprocityTheory.Neutral.Bridge.HCFR
