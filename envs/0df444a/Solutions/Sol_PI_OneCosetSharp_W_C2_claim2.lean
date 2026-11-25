-- Prove2me | solution 1 for PI.OneCosetSharp.W.C2.claim2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:41.160901+00:00
-- url     : https://prove2.me/submissions/55fb52f5-96e8-4a14-9fb4-e3b242a539da

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
import Theorems.Thm_PI_OneCosetSharp_W_C2_facts
import Theorems.Thm_P2M_PI_OneCosetSharp_W_C2_ent__0_9e2df1bf3f49
import Theorems.Thm_PI_OneCosetSharp_W_C2_term_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
namespace PI.OneCosetSharp.W.C2
theorem _root_.solution : Claim2 := by
  unfold PI.OneCosetSharp.W.Claim2
  intro k _ _ ψ₀ χ k₀ m t j n' c n hN
  classical
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  refine ⟨xj0 k₀ n' n, ?_⟩
  unfold PI.OneCosetSharp.Loc.E1
  simp only [one_pow, one_mul, term_eq hN ψ₀ χ]
  rw [Finset.sum_boole, Nat.cast_ne_zero, Finset.card_ne_zero]
  refine ⟨τ0 k₀ n' c n, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, ?_⟩⟩
  refine ⟨fun p' hp' => ?_, fun p p' hp hp' hne h0 => ?_⟩
  · rw [ent_τ0 hN (by omega) (by omega), if_pos rfl]
  · exact absurd (by rw [ent_τ0 hN hp (by omega), if_neg hne]) h0
end PI.OneCosetSharp.W.C2
