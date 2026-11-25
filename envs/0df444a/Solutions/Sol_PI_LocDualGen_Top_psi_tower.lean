-- Prove2me | solution 1 for PI.LocDualGen.Top.psi_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:22.29671+00:00
-- url     : https://prove2.me/submissions/46aef160-8456-427d-a064-99b1b61682f8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_PsiTower
import Theorems.Thm_PI_LocDualGen_Top_trQ_eq

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
open PI PI.LocDualGen PI.LocDualGen.Top
open PI.LocDualGen.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} [Fact (resChar p).Prime]
namespace PI.LocDualGen.Top
theorem _root_.solution (hK : PsiKer) (A : LocAt F E sig p) (z : A.Ep) :
    A.psiE z = 1 ↔ ‖Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep z)‖ ≤ 1 := by
  obtain ⟨a, ha, hle, hpsi⟩ := A.psiE_def z
  have hle' : ‖Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep z) - (a : ℚ_[resChar p])‖ ≤ 1 := by
    rw [← trQ_eq]; exact hle
  rw [hpsi]
  exact hK _ _ a ha hle'
end PI.LocDualGen.Top
