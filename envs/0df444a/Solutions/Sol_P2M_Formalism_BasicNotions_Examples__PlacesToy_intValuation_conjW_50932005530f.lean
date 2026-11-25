-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__PlacesToy_intValuation_conjW_50932005530f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:09.598313+00:00
-- url     : https://prove2.me/submissions/f8e1acc0-c8ab-4180-bb45-6444f6098f3e

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_mem_conjW_pow_c73c9fbba4a3
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions.Examples₂.PlacesToy
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.BasicNotions.Examples₂.PlacesToy
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    (conjW w).intValuation r = w.intValuation (starO r) := by
  by_cases hr : r = 0
  · subst hr; simp
  have hr' : starO r ≠ 0 := by
    intro h; apply hr; rw [← starO_starO r, h, map_zero]
  rw [(conjW w).intValuation_eq_exp_neg_multiplicity hr, w.intValuation_eq_exp_neg_multiplicity hr']
  set k := multiplicity (conjW w).asIdeal (Ideal.span {r})
  set k' := multiplicity w.asIdeal (Ideal.span {starO r})
  have h : ∀ n : ℕ, n ≤ k ↔ n ≤ k' := by
    intro n
    have h1 := (conjW w).intValuation_le_pow_iff_mem r n
    have h2 := w.intValuation_le_pow_iff_mem (starO r) n
    rw [(conjW w).intValuation_eq_exp_neg_multiplicity hr, WithZero.exp_le_exp] at h1
    rw [w.intValuation_eq_exp_neg_multiplicity hr', WithZero.exp_le_exp] at h2
    rw [mem_conjW_pow] at h1
    have e1 : n ≤ k ↔ -(k : ℤ) ≤ -(n : ℤ) := by omega
    have e2 : n ≤ k' ↔ -(k' : ℤ) ≤ -(n : ℤ) := by omega
    rw [e1, e2, h1, h2]
  have hk : k = k' := le_antisymm ((h k).1 le_rfl) ((h k').2 le_rfl)
  rw [hk]
end Formalism.BasicNotions.Examples₂.PlacesToy
