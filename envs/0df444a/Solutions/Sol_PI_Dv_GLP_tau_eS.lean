-- Prove2me | solution 1 for PI.Dv.GLP.tau_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:56.97364+00:00
-- url     : https://prove2.me/submissions/a42e02bf-06df-429e-aa0b-5fc0efaecb49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_scalar_of_comm
import Theorems.Thm_PI_Dv_GLP_card_ne_zero
import Theorems.Thm_PI_Dv_GLP_char_orth
import Theorems.Thm_PI_Dv_GLP_asAlg_eS
import Theorems.Thm_PI_Dv_GLP_tau_eS_comm
import Theorems.Thm_P2M_PI_Dv_GLP_finrank_pos__1b37fc6de94c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution [CharZero K] (T : GoodSet K G) (s t : T.S) :
    (T.tau t).asAlgebraHom (eS T s) = if s = t then 1 else 0 := by
  obtain ⟨c, hc⟩ := scalar_of_comm T t _ (tau_eS_comm T s t)
  have htr : LinearMap.trace K _ ((T.tau t).asAlgebraHom (eS T s)) =
      ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
        (if s = t then ((Fintype.card G : ℕ) : K) else 0) := by
    rw [asAlg_eS, map_sum, ← char_orth T s t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_eq_mul, cS]
    ring
  rw [hc, Module.algebraMap_end_eq_smul_id, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  have hd : ((Module.finrank K (T.W t) : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (finrank_pos' T t).ne'
  rw [hc]
  split_ifs with h
  · subst h
    rw [if_pos rfl, div_mul_cancel₀ _ (card_ne_zero (K := K) (G := G))] at htr
    have : c = 1 := by
      have := mul_right_cancel₀ hd (htr.trans (one_mul _).symm)
      exact this
    rw [this, map_one]
  · rw [if_neg h, mul_zero] at htr
    have : c = 0 := by
      rcases mul_eq_zero.1 htr with h1 | h1
      · exact h1
      · exact absurd h1 hd
    rw [this, map_zero]
end PI.Dv.GLP
