-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:17.533352+00:00
-- url     : https://prove2.me/submissions/4d8ef844-d780-4ecf-b5eb-32e3b79b473a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable {K : Type*} [Field K]
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution {n k : ℕ} (δ : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin k) (Fin n) K)
    (h : ∀ w, M *ᵥ w = 0 → δ *ᵥ w = 0) : ∃ X : Matrix (Fin n) (Fin k) K, δ = X * M := by
  have hrow : ∀ i, ∃ t : Fin k → K, ∀ z, (δ *ᵥ z) i = t ⬝ᵥ (M *ᵥ z) := by
    intro i
    let f : (Fin n → K) →ₗ[K] (Fin k → K) := M.mulVecLin
    let g : Module.Dual K (Fin n → K) :=
      { toFun := fun z => (δ *ᵥ z) i
        map_add' := fun x y => by simp [Matrix.mulVec_add]
        map_smul' := fun c x => by simp [Matrix.mulVec_smul] }
    have hg : g ∈ (LinearMap.ker f).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro z hz
      show (δ *ᵥ z) i = 0
      rw [h z (LinearMap.mem_ker.mp hz)]
      rfl
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hg
    obtain ⟨hd, hh⟩ := hg
    refine ⟨fun c => hd (fun j => if c = j then 1 else 0), fun z => ?_⟩
    have h1 : hd (f z) = g z := by
      rw [← hh]
      rfl
    have h2 : hd (M *ᵥ z) = (fun c => hd (fun j => if c = j then 1 else 0)) ⬝ᵥ (M *ᵥ z) := by
      rw [LinearMap.pi_apply_eq_sum_univ hd (M *ᵥ z)]
      simp only [dotProduct, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    exact h1.symm.trans h2
  choose X hX using hrow
  refine ⟨Matrix.of X, ?_⟩
  ext i j
  have := hX i (Pi.single j 1)
  rw [Matrix.dotProduct_mulVec] at this
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Pi.single_apply] using this
end PI.UnitaryGroupMassFormula.LCG
