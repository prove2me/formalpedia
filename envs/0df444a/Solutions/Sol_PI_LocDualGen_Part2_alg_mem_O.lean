-- Prove2me | solution 1 for PI.LocDualGen.Part2.alg_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:31.642806+00:00
-- url     : https://prove2.me/submissions/89ccc59c-577f-4ffe-9130-17ff048a5f33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocDualGen PI.LocDualGen.Part2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)
namespace PI.LocDualGen.Part2
theorem _root_.solution (r : 𝒪[A.Fp]) : algebraMap A.Fp A.Ep (r : A.Fp) ∈ A.O := by
  rw [A.O_def]
  have : algebraMap A.Fp A.Ep (r : A.Fp) = algebraMap 𝒪[A.Fp] A.Ep r := rfl
  rw [this]
  exact isIntegral_algebraMap
end PI.LocDualGen.Part2
