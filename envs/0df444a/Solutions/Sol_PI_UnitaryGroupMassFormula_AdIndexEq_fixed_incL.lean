-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.fixed_incL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:29:37.517198+00:00
-- url     : https://prove2.me/submissions/db902f8f-1b2f-45a3-820a-747451b153df

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Hensel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowD
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_exists_nonfixed
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_decompV
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_incL_apply
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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (hv : IsFieldAt I v)
    (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) (hx : sigV I v x = x) :
    ∃ p, x = incL I v p := by
  obtain ⟨θ, hθ⟩ := exists_nonfixed I
  obtain ⟨p, q, rfl⟩ := decompV I v θ hθ x
  refine ⟨p, ?_⟩
  haveI : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := ⟨hv.exists_pair_ne⟩
  have hsig : I.cm.sig θ = star θ := rfl
  have hs : sigV I v (p ⊗ₜ 1 + q ⊗ₜ θ) = p ⊗ₜ 1 + q ⊗ₜ star θ := by
    simp [sigV, hsig]
  have hq : q ⊗ₜ[I.F] (θ - star θ) = 0 := by
    rw [TensorProduct.tmul_sub, sub_eq_zero]
    have h2 := hx
    rw [hs] at h2
    exact (add_left_cancel h2).symm
  have hu : θ - star θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hq1 : incL I v q = 0 := by
    rw [incL_apply]
    calc q ⊗ₜ[I.F] (1 : I.E)
        = (q ⊗ₜ[I.F] (θ - star θ)) * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] (θ - star θ)⁻¹) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hu]
      _ = 0 := by rw [hq, zero_mul]
  have hq0 : q = 0 := (incL I v).injective (hq1.trans (map_zero _).symm)
  rw [hq0, TensorProduct.zero_tmul, add_zero, incL_apply]
end PI.UnitaryGroupMassFormula.AdIndexEq
