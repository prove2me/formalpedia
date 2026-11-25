-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.chiV_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:16.395325+00:00
-- url     : https://prove2.me/submissions/32d090e4-3ece-49ef-ac16-73fee062dc00

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Assemble
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_mod_q_hom
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_liftHom_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
section Lift
variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
private theorem modQ_eq_one_of_central {G : Type} [Group G] (K : Subgroup G) (y : G)
    (hy : ∀ x : G, y * x * y⁻¹ = x) : modQ K y = 1 := by
  have h1 : ∀ z : G, (∀ x : G, z * x * z⁻¹ = x) → dIdx K z = 1 := by
    intro z hz
    unfold dIdx
    rw [Subgroup.relIndex_eq_one]
    intro k hk
    exact Subgroup.mem_map.2 ⟨k, hk, by simp [MulAut.conj_apply, hz k]⟩
  have h2 : ∀ x : G, y⁻¹ * x * y⁻¹⁻¹ = x := by
    intro x
    have hx := hy x
    rw [inv_inv]
    calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [hx]
      _ = x := by group
  unfold modQ
  rw [h1 y hy, h1 y⁻¹ h2]
  norm_num
end Lift
end PI.UnitaryGroupMassFormula.AdIndexEq
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob) :
    (∀ g, 0 < chiV I v hC hL hJ g) ∧
    (∀ s : Uv I v, (∀ t : Uv I v, s * t = t * s) → chiV I v hC hL hJ s = 1) ∧
    (∀ s : Uv I v, (∃ m : ℕ, 1 ≤ m ∧
        (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)) →
        chiV I v hC hL hJ s = 1) := by
  have hM := mod_q_hom I.Gf (PI.AdIndexEq.Ksub I) (hC I)
  have hpos : ∀ g, 0 < chiV I v hC hL hJ g := by
    intro g
    show 0 < modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ g)
    unfold modQ
    apply div_pos
    · exact_mod_cast Nat.pos_of_ne_zero (hC I _)
    · exact_mod_cast Nat.pos_of_ne_zero (hC I _)
  refine ⟨hpos, fun s hs => ?_, fun s hs => ?_⟩
  · show modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ s) = 1
    have hyv : matV I v ((liftHom I v hL hJ s : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = s := by
      rw [liftHom_apply]
      exact (liftFn_spec I v hL s).1
    have hys : SuppAt I v (liftHom I v hL hJ s) := by
      rw [liftHom_apply]
      exact (liftFn_spec I v hL s).2
    apply modQ_eq_one_of_central
    intro x
    apply hJ I
    intro w
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    by_cases hw : w = v
    · rw [hw]
      have hc := congrArg Subtype.val (hs ⟨_, hU I v x⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_mk] at hc
      rw [hyv, hc, mul_inv_cancel_right]
    · rw [hys w hw, one_mul, inv_one, mul_one]
  · obtain ⟨m, hm, hsm⟩ := hs
    have hpow : chiV I v hC hL hJ (s ^ m) = 1 := by
      show modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ (s ^ m)) = 1
      apply hM.2.1
      refine (hK I _).2 fun w => ?_
      rw [liftHom_apply]
      by_cases hw : w = v
      · rw [hw, (liftFn_spec I v hL (s ^ m)).1]
        exact hsm
      · rw [(liftFn_spec I v hL (s ^ m)).2 w hw]
        exact (Kv I w).one_mem
    rw [map_pow] at hpow
    exact (pow_eq_one_iff_of_nonneg (hpos s).le (by omega)).1 hpow
end PI.UnitaryGroupMassFormula.AdIndexEq
