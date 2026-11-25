-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.decompV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:38.069368+00:00
-- url     : https://prove2.me/submissions/2336a257-ebe2-4aeb-b7bc-ba26c7ea458a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Hensel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowD
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_decompE
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (θ : I.E) (hθ : star θ ≠ θ)
    (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    ∃ p q : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v, x = p ⊗ₜ 1 + q ⊗ₜ θ := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a e =>
    obtain ⟨f, g, rfl⟩ := decompE I θ hθ e
    exact ⟨f • a, g • a, by rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp only [TensorProduct.add_tmul]; abel⟩
end PI.UnitaryGroupMassFormula.AdIndexEq
