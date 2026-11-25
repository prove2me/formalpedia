-- Prove2me | solution 1 for PI.IsoFunVW.mem_Vnu_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:18.611897+00:00
-- url     : https://prove2.me/submissions/d9dcb1cb-00cf-407a-86cc-3fff9f39ef1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
import Theorems.Thm_PI_IsoFunVW_minY_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MvPolynomial
noncomputable section
open PI PI.IsoFunVW
open PI.IsoFunV
namespace PI.IsoFunVW
theorem _root_.solution {Lt σ : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (y : Lt → Fin N → ℕ → MvPolynomial σ ℂ) :
    (fun I => L (minY N nu I y)) ∈ Vnu N nu := by
  classical
  rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := Vnu N nu),
    Submodule.mem_dualCoannihilator]
  intro f hf
  rw [Submodule.mem_dualAnnihilator] at hf
  rw [LinearMap.pi_apply_eq_sum_univ f]
  set e : ColChoice N nu → ℂ := fun I => f (fun J => if I = J then 1 else 0) with he
  have hQ : (∑ I : ColChoice N nu, e I • minY N nu I y) = 0 := by
    apply MvPolynomial.funext
    intro p
    have hv : hvC N nu (fun z a j => eval p (y z a j)) ∈ Vnu N nu :=
      Submodule.subset_span ⟨_, rfl⟩
    have h0 := hf _ hv
    rw [LinearMap.pi_apply_eq_sum_univ f] at h0
    rw [map_sum, map_zero, ← h0]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    simp only [MvPolynomial.smul_eval, smul_eq_mul]
    rw [mul_comm]
    congr 1
    exact minY_map (eval p) N nu I y
  have := congrArg L hQ
  rw [map_sum, map_zero] at this
  refine Eq.trans (Finset.sum_congr rfl (fun I _ => ?_)) this
  simp only [map_smul, smul_eq_mul, he]
  ring
end PI.IsoFunVW
