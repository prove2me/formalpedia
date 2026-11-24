-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.lattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:56:39.657012+00:00
-- url     : https://prove2.me/submissions/8687457e-9842-44aa-ba05-7f48e2666bb4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (L : PeriodPair) (z : ℂ) : z ∈ L.lattice ↔ ∃ p q : ℤ, z = (p : ℝ) • L.ω₁ + (q : ℝ) • L.ω₂ := by
  rw [PeriodPair.lattice, Submodule.mem_span_pair]
  constructor
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [← h]
    simp [zsmul_eq_mul, Complex.real_smul]
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [h]
    simp [zsmul_eq_mul, Complex.real_smul]
end PI.UnitaryGroupMassFormula.UnimodLocStd
