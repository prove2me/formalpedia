-- Prove2me | solution 1 for PI.GGMatBoundW.joint_eigenvector_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:36.098668+00:00
-- url     : https://prove2.me/submissions/53b629ea-5d91-4c89-b86b-38bb2ba7adf0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_JointEigenvectorExists
import Theorems.Thm_PI_GGMatBoundW_totOp_comm
import Theorems.Thm_PI_GGMatBoundW_placeOp_comm
import Theorems.Thm_PI_GGMatBoundW_placeOp_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
namespace PI.GGMatBoundW
theorem _root_.solution : JointEig := by
  intro ι _ Fq _ _ k ψ V _ _ _ π w μ hw hμ
  let E : Submodule ℂ V := LinearMap.ker (totOp ψ π - μ • LinearMap.id)
  have memE : ∀ x, x ∈ E ↔ totOp ψ π x = μ • x := by
    intro x
    show x ∈ LinearMap.ker _ ↔ _
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    simp
  have Einv : ∀ g, ∀ x ∈ E, π g x ∈ E := by
    intro g x hx
    rw [memE] at hx ⊢
    have h1 := congrArg (fun e : V →ₗ[ℂ] V => e x) (totOp_comm ψ π g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hx, map_smul]
  have hex : ∃ n, ∃ W : Submodule ℂ V, W ≠ ⊥ ∧ W ≤ E ∧ (∀ g, ∀ x ∈ W, π g x ∈ W) ∧
      Module.finrank ℂ W = n := by
    refine ⟨_, E, ?_, le_rfl, Einv, rfl⟩
    intro h
    apply hw
    have : w ∈ E := (memE w).2 hμ
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  obtain ⟨W, hW, hWE, hWinv, hWn⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ V, W' ≠ ⊥ → W' ≤ W → (∀ g, ∀ x ∈ W', π g x ∈ W') → W' = W := by
    intro W' hW' hle hinv
    have h1 : Nat.find hex ≤ Module.finrank ℂ W' :=
      Nat.find_min' hex ⟨W', hW', hle.trans hWE, hinv, rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨W, hW, hWinv, fun x hx => (memE x).1 (hWE hx), fun v => ?_⟩
  have hmaps : ∀ x ∈ W, placeOp ψ π v x ∈ W := fun x hx => placeOp_mem ψ π v W hWinv x hx
  let A : W →ₗ[ℂ] W := (placeOp ψ π v).restrict hmaps
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨u, hu⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  let W' : Submodule ℂ V := W ⊓ LinearMap.ker (placeOp ψ π v - c • LinearMap.id)
  have memW' : ∀ x, x ∈ W' ↔ x ∈ W ∧ placeOp ψ π v x = c • x := by
    intro x
    simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      LinearMap.smul_apply, LinearMap.id_apply]
  have hu' : (u : V) ∈ W' := by
    rw [memW']
    refine ⟨u.2, ?_⟩
    have h2 := congrArg Subtype.val hu.apply_eq_smul
    exact h2
  have hW'ne : W' ≠ ⊥ := by
    intro h
    rw [h] at hu'
    exact hu.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hu'))
  have hW'inv : ∀ g, ∀ x ∈ W', π g x ∈ W' := by
    intro g x hx
    rw [memW'] at hx ⊢
    refine ⟨hWinv g x hx.1, ?_⟩
    have h1 := congrArg (fun e : V →ₗ[ℂ] V => e x) (placeOp_comm ψ π v g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hx.2, map_smul]
  have heq := hmin W' hW'ne inf_le_left hW'inv
  intro x hx
  have hx' : x ∈ W' := heq ▸ hx
  exact ((memW' x).1 hx').2
end PI.GGMatBoundW
