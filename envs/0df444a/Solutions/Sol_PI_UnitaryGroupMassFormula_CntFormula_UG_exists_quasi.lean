-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.UG.exists_quasi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:39.715536+00:00
-- url     : https://prove2.me/submissions/f5e82f1a-df26-420e-83be-9c98a45ed803

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_star_h
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
theorem _root_.solution (hs : h.IsSymm) (w : V) {a : K} (ha : a + star a = a * star a * h w w) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ v, τ v = v - (a * h w v) • w := by
  let f : K → V →ₗ[K] V := fun b =>
    { toFun := fun v => v - (b * h w v) • w
      map_add' := fun x y => by
        simp only [map_add, mul_add, add_smul]
        abel
      map_smul' := fun c x => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply, smul_sub, smul_smul]
        rw [mul_left_comm] }
  have hf : ∀ b v, f b v = v - (b * h w v) • w := fun _ _ => rfl
  have hcomp : ∀ b c : K, b + c = b * c * h w w → ∀ v : V,
      (v - (c * h w v) • w) - (b * h w (v - (c * h w v) • w)) • w = v := by
    intro b c hbc v
    rw [map_sub, map_smul, smul_eq_mul, sub_sub, ← add_smul]
    have : c * h w v + b * (h w v - c * h w v * h w w) = 0 := by
      linear_combination (h w v) * hbc
    rw [this, zero_smul, sub_zero]
  have ha' : star a + a = star a * a * h w w := by linear_combination ha
  let τ : V ≃ₗ[K] V := LinearEquiv.ofLinear (f a) (f (star a))
    (LinearMap.ext fun v => hcomp a (star a) ha v)
    (LinearMap.ext fun v => hcomp (star a) a ha' v)
  refine ⟨τ, ?_, fun v => rfl⟩
  intro x y
  change h (x - (a * h w x) • w) (y - (a * h w y) • w) = h x y
  have hsx : star (h w x) = h x w := star_h hs w x
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply, star_mul', hsx]
  linear_combination (-(h w y * h x w)) * ha
end PI.UnitaryGroupMassFormula.CntFormula.UG
