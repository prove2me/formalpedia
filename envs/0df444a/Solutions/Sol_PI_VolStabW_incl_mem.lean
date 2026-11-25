-- Prove2me | solution 1 for PI.VolStabW.incl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:01.505953+00:00
-- url     : https://prove2.me/submissions/d999e8ec-7d73-4165-b1be-5a6bd74a0a4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Theorems.Thm_PI_VolStabW_repr_incl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
variable {σ : E →ₐ[F] E} (A : AntiB F E σ)
variable (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
namespace PI.VolStabW
theorem _root_.solution (e : E) (he : ∀ j, algebraMap F (Fv F v) (A.c.repr e j) ∈ v.adicCompletionIntegers F) :
    inclR (Fv F v) e ∈ lamC v A hD := by
  rw [mem_lamC, Xc, Yc, repr_incl, repr_incl]
  exact ⟨he 0, he 1⟩
end PI.VolStabW
