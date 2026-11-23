-- Prove2me | solution 1 for PI.Dv.GLP.scalar_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:58.671882+00:00
-- url     : https://prove2.me/submissions/96eda237-5a7f-44e0-beb4-c65c75fa94df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_intertw_alg

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
theorem _root_.solution (T : GoodSet K G) (s : T.S) (F : Module.End K (T.W s))
    (hF : ∀ g, F * T.tau s g = T.tau s g * F) : ∃ c : K, F = algebraMap K _ c := by
  have hc : F ∈ Subalgebra.center K (Module.End K (T.W s)) := by
    rw [Subalgebra.mem_center_iff]
    intro b
    obtain ⟨a, rfl⟩ := T.irr s b
    ext x
    simp only [Module.End.mul_apply]
    exact (intertw_alg (T.tau s) (T.tau s) F (fun g x => LinearMap.congr_fun (hF g) x) a x).symm
  rw [Algebra.IsCentral.center_eq_bot] at hc
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 hc
  exact ⟨c, hc.symm⟩
end PI.Dv.GLP
