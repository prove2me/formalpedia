-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.wa_exists_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:37.316339+00:00
-- url     : https://prove2.me/submissions/43cdfc3d-1516-409f-9267-5da4464cc225

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary
import Theorems.Thm_PI_UnitaryApproxFinWork_wa_isOpen_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
variable {F : Type} [Field F] [NumberField F]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ b : F, Valued.v (x - algebraMap F (v.adicCompletion F) b) < 1 := by
  have hd : DenseRange (algebraMap F (v.adicCompletion F)) := by
    first
      | exact denseRange_algebraMap F v
      | exact UniformSpace.Completion.denseRange_coe
      | exact (UniformSpace.Completion.denseRange_coe).comp (WithVal.equiv (v.valuation F)).symm.surjective.denseRange
          (UniformSpace.Completion.continuous_coe _)
      | exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap_adicCompletion v
  obtain ⟨b, hb⟩ := hd.exists_mem_open (wa_isOpen_lt_one v x) ⟨x, by simp⟩
  refine ⟨b, ?_⟩
  rw [Valuation.map_sub_swap]
  exact hb
end PI.UnitaryApproxFinWork
