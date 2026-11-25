-- Prove2me | solution 1 for P2M_GlobalTheory_classicalTheta_level_and_linearIndependent__6b643778a469
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:15.590115+00:00
-- url     : https://prove2.me/submissions/11a3522c-c7df-468f-8d19-5714c5cbf00c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ClassicalThetaLevelAndLinearIndependent
import Theorems.Thm_GlobalTheory_bijective_fin_zmod
import Theorems.Thm_GlobalTheory_levelTheta_zero_zero_mem
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (hτ : τ ∈ SiegelH (Fin g)) (N : ℕ) (hN : 1 ≤ N) :
    (∀ c : Fin g → Fin N,
      (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧
        ∀ (n n' : Fin g → ℤ) z,
          (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))
              (z + τ *ᵥ ofIntVec n + ofIntVec n') =
            eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) *
              (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧
    LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) := by
  have e (c : Fin g → Fin N) : levelTheta 0 0 N τ (fun i => ((c i : ℕ) : ℤ)) =
      fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
    funext z
    rw [levelTheta_zero_zero]
    simp only [Int.cast_natCast]
  refine ⟨fun c => ?_, ?_⟩
  · have h := levelTheta_zero_zero_mem hτ hN (fun i => ((c i : ℕ) : ℤ))
    rw [e] at h
    exact mem_thetaLevel.1 h
  · have h := linearIndependent_levelTheta (a := 0) (b := 0) hτ hN
      (r := fun (c : Fin g → Fin N) i => ((c i : ℕ) : ℤ)) (bijective_fin_zmod hN).1
    simpa only [e] using h
end GlobalTheory
