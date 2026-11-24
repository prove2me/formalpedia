-- Prove2me | solution 1 for PI.WAU.B.common_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:45:17.606415+00:00
-- url     : https://prove2.me/submissions/34322808-7ca0-4f94-88cd-66282807fa5d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.UG Matrix
open scoped TensorProduct
namespace PI.WAU.B
theorem _root_.solution {ι : Type} [Fintype ι] (P : ι → ℕ → Prop)
    (hP : ∀ i N M, P i N → P i (N * M)) (h : ∀ i, ∃ N, 0 < N ∧ P i N) :
    ∃ N, 0 < N ∧ ∀ i, P i N := by
  classical
  choose f hf0 hf using h
  refine ⟨∏ i, f i, Finset.prod_pos fun i _ => hf0 i, fun i => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  rw [hk]
  exact hP i _ _ (hf i)
end PI.WAU.B
