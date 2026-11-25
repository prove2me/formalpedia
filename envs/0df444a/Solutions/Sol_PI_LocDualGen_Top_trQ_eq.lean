-- Prove2me | solution 1 for PI.LocDualGen.Top.trQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:20.490717+00:00
-- url     : https://prove2.me/submissions/518eb28c-40e0-4ae6-93c4-41e6bcb7d650

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_PsiTower

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
theorem _root_.solution (A : LocAt F E sig p) (z : A.Ep) :
    (letI := qAlg A; Algebra.trace ℚ_[resChar p] A.Ep z) =
      Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep z) := by
  letI := qAlg A
  have : IsScalarTower ℚ_[resChar p] A.Fp A.Ep := IsScalarTower.of_algebraMap_eq' (R := ℚ_[resChar p]) (S := A.Fp) (A := A.Ep) rfl
  haveI := A.free
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  haveI := A.qlFin
  exact (Algebra.trace_trace (R := ℚ_[resChar p]) (S := A.Fp) z).symm
end PI.LocDualGen.Top
