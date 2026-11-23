-- Prove2me | solution 1 for PI.GalTorsConj.W.st_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:52.036511+00:00
-- url     : https://prove2.me/submissions/93f908f4-9fc8-42c2-bf7a-2b9d4fa6396c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight
import Theorems.Thm_PI_GalTorsConj_W_wp_add_mem
import Theorems.Thm_PI_GalTorsConj_W_dwp_add_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
variable {L L' : PeriodPair} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
namespace PI.GalTorsConj.W
theorem _root_.solution {t t' ω : ℂ} (h : St L L' M ρ t t') (hω : ω ∈ L'.lattice) :
    St L L' M ρ t (t' + ω) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, hx, hy, e1, e2⟩
  · exact Or.inl ⟨h1, L'.lattice.add_mem h2 hω⟩
  · refine Or.inr ⟨h1, fun hh => h2 (by simpa using L'.lattice.sub_mem hh hω), hx, hy, ?_, ?_⟩
    · rw [wp_add_mem L' t' hω, e1]
    · rw [dwp_add_mem L' t' hω, e2]
end PI.GalTorsConj.W
