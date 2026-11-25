-- Prove2me | solution 1 for PI.LocDualGen.Top.assemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:03:40.21426+00:00
-- url     : https://prove2.me/submissions/548de5fa-d19b-48de-b20f-b86f4ef455c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_PsiTower
import Theorems.Thm_PI_LocDualGen_Top_psi_tower
import Theorems.Thm_PI_LocDualGen_Top_tr_smul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_LocDualGen_Part2_alg_mem_O
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
theorem _root_.solution (hK : PsiKer) (A : LocAt F E sig p) (d : A.Fp)
    (hd : ∀ a : A.Fp, (∀ b : 𝒪[A.Fp],
      ‖Algebra.trace ℚ_[resChar p] A.Fp (a * (b : A.Fp) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[A.Fp])
    (hE : ∀ x : A.Ep, (∀ y ∈ A.O, Algebra.trace A.Fp A.Ep (x * y) ∈ 𝒪[A.Fp]) ↔ x ∈ A.O) :
    DualAtL A d := by
  have key : ∀ x y : A.Ep, A.psiE (-(x * y * algebraMap A.Fp A.Ep d⁻¹)) = 1 ↔
      ‖Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep (x * y) * d⁻¹)‖ ≤ 1 := by
    intro x y
    rw [psi_tower hK]
    simp only [map_neg, norm_neg]
    rw [tr_smul]
  unfold DualAtL
  intro x
  simp_rw [key]
  constructor
  · intro H
    rw [← hE]
    intro y hy
    rw [← hd]
    intro b
    have hyb : y * algebraMap A.Fp A.Ep (b : A.Fp) ∈ A.O :=
      A.O.mul_mem hy (Part2.alg_mem_O A b)
    have := H _ hyb
    rwa [← mul_assoc, tr_smul] at this
  · intro hx y hy
    have ha := (hE x).2 hx y hy
    have := (hd _).2 ha 1
    simpa using this
end PI.LocDualGen.Top
