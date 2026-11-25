-- Prove2me | solution 1 for PI.LocDualGen.Top.stmt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:53.086511+00:00
-- url     : https://prove2.me/submissions/8e3dd526-8160-4dc7-89bb-546f8a961c45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_PsiTower
import Theorems.Thm_PI_LocDualGen_Top_assemble
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_LocDualGen_Part2_dualAtL_mul_unit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocDualGen PI.LocDualGen.Top
open PI.LocDualGen.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} [Fact (resChar p).Prime]
namespace PI.LocDualGen.Top
theorem _root_.solution (hK : PsiKer) (h1 : FpDual) (h2 : FpDualUnram) (h3 : EpSelfDual) :
    PI.LocDualGen.Stmt := by
  intro F E _ _ _ _ _ sig p A
  haveI := A.ellPrime
  have hE : IsReduced A.Ep → UnramL A → ∀ x : A.Ep,
      (∀ y ∈ A.O, Algebra.trace A.Fp A.Ep (x * y) ∈ 𝒪[A.Fp]) ↔ x ∈ A.O :=
    fun hr hu => h3 A.Fp A.Ep A.lf A.char0 A.free A.rank hr A.O A.O_def hu
  refine ⟨fun hr hu => ?_, fun δ u hu h => Part2.dualAtL_mul_unit A δ u hu h, fun hr hu hl => ?_⟩
  · obtain ⟨d, hd0, hd⟩ := h1 A.Fp (resChar p) A.lf A.char0 A.qlCont A.qlFin
    exact ⟨d, hd0, assemble hK A d hd (hE hr hu)⟩
  · refine assemble hK A 1 (fun a => ?_) (hE hr hu)
    simpa [inv_one, mul_one] using h2 A.Fp (resChar p) A.lf A.char0 A.qlCont A.qlFin hl a
end PI.LocDualGen.Top
