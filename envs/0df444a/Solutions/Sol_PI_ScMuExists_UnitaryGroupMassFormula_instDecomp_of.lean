-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.instDecomp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:23.156806+00:00
-- url     : https://prove2.me/submissions/0e6337c2-d738-42b2-8242-2420c5a31bb0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstTop
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_fix_of
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_fixB_of
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



set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (hP : InstPlaceDecomp) (hG : InstFrameGram) : InstDecomp := by
  intro I r e f z hF h hh
  have key := fun v : InfinitePlace I.F =>
    hP I.n (I.ε v) (Fin r ⊕ Fin r ⊕ Unit) (instBmat I v e f z) (hG I r e f z hF v)
      (Formalism.MainNotions.S.uMat (h v)) (h v).2 (inst_fixB_of v e f z _ (hh v))
  choose k p σ hk hp hσ hkB hpB hσB hkp hσσ hσp C hCc hC1 hCk using key
  have Jsq : ∀ v, Formalism.REAL.Jm (I.ε v) * Formalism.REAL.Jm (I.ε v) = 1 := by
    intro v
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hε : I.ε v a <;> simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, hε]
    · simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.one_apply, hab]
  have hU : ∀ v (m : Matrix (Fin I.n) (Fin I.n) ℂ), Formalism.REAL.inUJ (I.ε v) m →
      ∃ u : Formalism.REAL.UJ (I.ε v), (((u : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) = m := by
    intro v m hm
    have hl : (Formalism.REAL.Jm (I.ε v) * mᴴ * Formalism.REAL.Jm (I.ε v)) * m = 1 := by
      have : Formalism.REAL.Jm (I.ε v) * mᴴ * Formalism.REAL.Jm (I.ε v) * m =
          Formalism.REAL.Jm (I.ε v) * (mᴴ * Formalism.REAL.Jm (I.ε v) * m) := by
        simp only [Matrix.mul_assoc]
      rw [this, show mᴴ * Formalism.REAL.Jm (I.ε v) * m = Formalism.REAL.Jm (I.ε v) from hm, Jsq v]
    have hr : m * (Formalism.REAL.Jm (I.ε v) * mᴴ * Formalism.REAL.Jm (I.ε v)) = 1 := by
      first
      | exact mul_eq_one_comm.1 hl
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hl
    exact ⟨⟨⟨m, _, hr, hl⟩, hm⟩, rfl⟩
  choose ku hku using fun v => hU v (k v) (hk v)
  choose pu hpu using fun v => hU v (p v) (hp v)
  choose su hsu using fun v => hU v (σ v) (hσ v)
  let K : I.Ginf := fun v => ku v
  let P : I.Ginf := fun v => pu v
  let S : I.Ginf := fun v => su v
  have memH : ∀ (X : I.Ginf) (m : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ),
      (∀ v, (((X v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) = m v) →
      (∀ v, m v * instBmat I v e f z = instBmat I v e f z) → X ∈ Hset I (frameSet I e f z) := by
    intro X m hX hmB v x hx
    show (((X v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) *ᵥ _ = _
    rw [hX v]
    exact inst_fix_of v e f z (m v) (hmB v) x hx
  have ext' : ∀ X Y : I.Ginf, (∀ v, (((X v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (((Y v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ)) → X = Y := by
    intro X Y hXY
    funext v
    exact Subtype.ext (Units.ext (hXY v))
  have hSS : S * S = 1 := ext' _ _ fun v => by
    simp only [Pi.mul_apply, Pi.one_apply, Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one, S, hsu]
    exact hσσ v
  have hSPSP : S * P * S * P = 1 := ext' _ _ fun v => by
    simp only [Pi.mul_apply, Pi.one_apply, Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one, S, P, hsu, hpu]
    exact hσp v
  refine ⟨K, memH K k hku hkB, P, memH P p hpu hpB, S, memH S σ hsu hσB, ?_, ?_, ?_⟩
  · refine ext' _ _ fun v => ?_
    simp only [Pi.mul_apply, Subgroup.coe_mul, Units.val_mul, K, P, hku, hpu]
    exact hkp v
  · have hSi : S⁻¹ = S := inv_eq_of_mul_eq_one_right hSS
    rw [hSi]
    exact eq_inv_of_mul_eq_one_left hSPSP
  · refine ⟨Set.pi Set.univ C, isCompact_univ_pi hCc, ?_, ?_⟩
    · rw [interior_pi_set Set.finite_univ]
      intro v _
      exact hC1 v
    · intro x
      simp only [Set.mem_univ_pi]
      refine forall_congr' fun v => hCk v _ _ ?_
      have hg : (K * x * K⁻¹) v * ku v = ku v * x v := by
        simp [K]
      have := congrArg (fun g : Formalism.REAL.UJ (I.ε v) =>
        (((g : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ)) hg
      simp only [Subgroup.coe_mul, Units.val_mul, hku] at this
      exact this
end PI.ScMuExists.UnitaryGroupMassFormula
