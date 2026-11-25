-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.span_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:51.941921+00:00
-- url     : https://prove2.me/submissions/ee3712e1-a7eb-4df2-b408-3d25646b3255

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_SpanIsMaximal
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_nontriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
namespace PI.ParahoricIdxZ.W
theorem _root_.solution {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)
    (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) : (Ideal.span {(⟨ϖ, hϖ⟩ : O)}).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, ?_⟩
  · intro h1
    have := Formalism.DoubleCosetMeasures.P.GLRed.nontriv O ϖ hϖ hloc
    rw [← Ideal.eq_top_iff_one] at h1
    exact (Ideal.Quotient.nontrivial_iff.mp this) h1
  · intro I x hle hx hxI
    have hne : ∀ o ∈ O, (x : F) ≠ ϖ * o := by
      intro o ho he
      apply hx
      rw [Ideal.mem_span_singleton']
      exact ⟨⟨o, ho⟩, Subtype.ext (by simp [he, mul_comm])⟩
    have hinv : (x : F)⁻¹ ∈ O := hloc.2 _ x.2 hne
    have hx0 : (x : F) ≠ 0 := by simpa using hne 0 O.zero_mem
    have e : (1 : O) = ⟨(x : F)⁻¹, hinv⟩ * x := by
      apply Subtype.ext
      simp [hx0]
    rw [e]
    exact I.mul_mem_left _ hxI
end PI.ParahoricIdxZ.W
