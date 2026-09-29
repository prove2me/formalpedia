-- Prove2me | solution 1 for PhiDivRobust.Counterpart.scaledConj_eq_perspConj
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:59:13.443355+00:00
-- url     : https://prove2.me/submissions/8436ea2c-cda3-46d8-8420-ddb611b05127

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_conj
import Definitions.Def_PhiDivRobust_Counterpart_scaledConj
import Definitions.Def_PhiDivRobust_Counterpart_perspConj
open Matrix

namespace PhiDivRobust.Counterpart

lemma aux_scpc_key (φ : ℝ → EReal) (lam s t : ℝ) (hlam : 0 < lam) :
    (lam : EReal) * (((s / lam * t : ℝ) : EReal) - φ t) = ((s * t : ℝ) : EReal) - (lam : EReal) * φ t := by
  rw [EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hlam.le) (EReal.coe_ne_top _)]
  congr 1
  rw [← EReal.coe_mul]
  congr 1
  field_simp

lemma aux_scpc_zero (φ : ℝ → EReal) (s : ℝ) :
    scaledConj φ 0 s = if s ≤ 0 then 0 else ⊤ := by
  unfold scaledConj
  simp only [EReal.coe_zero, zero_mul, sub_zero]
  split_ifs with hs
  · apply le_antisymm
    · refine iSup₂_le fun t ht => ?_
      exact EReal.coe_nonpos.2 (mul_nonpos_of_nonpos_of_nonneg hs ht)
    · refine le_trans ?_ (le_iSup₂ (f := fun t (_ : t ∈ Set.Ici (0:ℝ)) => ((s * t : ℝ) : EReal)) 0 (Set.mem_Ici.2 le_rfl))
      simp
  · replace hs : 0 < s := lt_of_not_ge hs
    refine (EReal.eq_top_iff_forall_lt _).2 fun y => ?_
    have ht : (0:ℝ) ≤ (|y| + 1) / s := div_nonneg (by positivity) hs.le
    refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun t (_ : t ∈ Set.Ici (0:ℝ)) => ((s * t : ℝ) : EReal)) _ ht)
    rw [EReal.coe_lt_coe_iff, mul_div_cancel₀ _ hs.ne']
    linarith [le_abs_self y]

lemma aux_scpc_pos (φ : ℝ → EReal) (lam s : ℝ) (hlam : 0 < lam) :
    scaledConj φ lam s = (lam : EReal) * conj φ (s / lam) := by
  unfold scaledConj conj
  have h0 : (0 : EReal) < lam := EReal.coe_pos.2 hlam
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    rw [← aux_scpc_key φ lam s t hlam]
    exact mul_le_mul_of_nonneg_left
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Ici (0:ℝ)) => ((s / lam * t : ℝ) : EReal) - φ t) t ht) h0.le
  · rw [mul_comm, ← EReal.le_div_iff_mul_le h0 (EReal.coe_ne_top _)]
    refine iSup₂_le fun t ht => ?_
    rw [EReal.le_div_iff_mul_le h0 (EReal.coe_ne_top _), mul_comm, aux_scpc_key φ lam s t hlam]
    exact le_iSup₂ (f := fun t (_ : t ∈ Set.Ici (0:ℝ)) => ((s * t : ℝ) : EReal) - (lam : EReal) * φ t) t ht

end PhiDivRobust.Counterpart

open PhiDivRobust.Counterpart
open Matrix

theorem solution (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (lam s : ℝ) (hlam : 0 ≤ lam) :
    scaledConj φ lam s = perspConj φ lam s := by
  unfold perspConj
  by_cases h1 : 0 < lam
  · rw [if_pos h1]
    exact aux_scpc_pos φ lam s h1
  · rw [if_neg h1]
    have : lam = 0 := le_antisymm (not_lt.1 h1) hlam
    subst this
    exact aux_scpc_zero φ s
