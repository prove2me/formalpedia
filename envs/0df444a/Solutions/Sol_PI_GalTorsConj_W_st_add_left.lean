-- Prove2me | solution 1 for PI.GalTorsConj.W.st_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:48.814955+00:00
-- url     : https://prove2.me/submissions/f0ed0670-4d98-46ac-943a-00dd94081b76

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
theorem _root_.solution {t t' ω : ℂ} (h : St L L' M ρ t t') (hω : ω ∈ L.lattice) :
    St L L' M ρ (t + ω) t' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, hx, hy, e1, e2⟩
  · exact Or.inl ⟨L.lattice.add_mem h1 hω, h2⟩
  · have ex : L.weierstrassP (t + ω) = L.weierstrassP t := wp_add_mem L t hω
    have ey : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t := dwp_add_mem L t hω
    have hx' : L.weierstrassP (t + ω) ∈ M := by rw [ex]; exact hx
    have hy' : L.derivWeierstrassP (t + ω) ∈ M := by rw [ey]; exact hy
    refine Or.inr ⟨fun hh => h1 (by simpa using L.lattice.sub_mem hh hω), h2, hx', hy', ?_, ?_⟩
    · rw [e1]
      congr 1
      exact Subtype.ext ex.symm
    · rw [e2]
      congr 1
      exact Subtype.ext ey.symm
end PI.GalTorsConj.W
