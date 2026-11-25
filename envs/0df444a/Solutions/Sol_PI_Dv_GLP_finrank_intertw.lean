-- Prove2me | solution 1 for PI.Dv.GLP.finrank_intertw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:02.5838+00:00
-- url     : https://prove2.me/submissions/68cc4bb4-598e-448a-89a3-9713b2e0d155

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_scalar_of_comm
import Theorems.Thm_PI_Dv_GLP_intertw_zero

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
theorem _root_.solution (T : GoodSet K G) (s t : T.S) :
    Module.finrank K (IntertwiningMap (T.tau s) (T.tau t)) = if s = t then 1 else 0 := by
  split_ifs with h
  · subst h
    have hne : (IntertwiningMap.id (T.tau s)) ≠ 0 := by
      intro h0
      obtain ⟨x, hx⟩ := exists_ne (0 : T.W s)
      apply hx
      have := congrArg (fun f : IntertwiningMap (T.tau s) (T.tau s) => f x) h0
      simpa using this
    rw [finrank_eq_one_iff_of_nonzero' _ hne]
    intro f
    obtain ⟨c, hc⟩ := scalar_of_comm T s f.toLinearMap (fun g => f.isIntertwining' g)
    refine ⟨c, ?_⟩
    ext x
    rw [IntertwiningMap.toLinearMap_smul, LinearMap.smul_apply, IntertwiningMap.toLinearMap_id,
      LinearMap.id_apply, hc, Module.algebraMap_end_apply]
  · have : Subsingleton (IntertwiningMap (T.tau s) (T.tau t)) := ⟨fun f g => by
      ext1
      rw [intertw_zero T h f.toLinearMap (fun g x => LinearMap.congr_fun (f.isIntertwining' g) x),
        intertw_zero T h g.toLinearMap (fun g' x => LinearMap.congr_fun (g.isIntertwining' g') x)]⟩
    exact Module.finrank_zero_of_subsingleton
end PI.Dv.GLP
