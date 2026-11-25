-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.gaXi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:45.406805+00:00
-- url     : https://prove2.me/submissions/dcbeb314-48bc-4746-9457-c58e223261ee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
import Theorems.Thm_P2M_RH_PI_UnitaryGroupMassFormula_UsCost_det_zjH_ne_3b4c561a80972532
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UsCost_rn_mem__52f76f729929
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section smoothAt
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
end smoothAt
section slice
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
private lemma mul_mem_GV' {k r : ℕ} {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) :
    a * b ∈ B.GV k r := by
  simp only [B.GV, Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at ha hb ⊢
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha, hb]
end slice
end PI.UnitaryGroupMassFormula.UsCost
end
end

set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (hSM : SliceMem) (hRP : RadicalParam) (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) {Z : G.Mat s}
    (γ : B.Mat k ρ) (hZ : G.detM Z ≠ 0) (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  exact mul_mem_GV' (mul_mem_GV' (P.BetaSesquilinearity.gv_inv (rn_mem' hRP (p + s) ξ.1.1))
    ((hSM k (p + s) ρ).1 _ γ (det_zjH_ne hd ξ.2 hZ) hγ)) (rn_mem' hRP (p + s) ξ.1.2)
end PI.UnitaryGroupMassFormula.UsCost
