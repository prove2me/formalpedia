-- Prove2me | solution 1 for PIW.AdelicOrbitU.stFix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:49.173027+00:00
-- url     : https://prove2.me/submissions/dcb8de2d-ab52-44f4-ba9a-9f9ddc74b691

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StFix
import Theorems.Thm_PIW_AdelicOrbitU_quad_decomp
import Theorems.Thm_PIW_AdelicOrbitU_quad_exists_theta
import Theorems.Thm_PIW_AdelicOrbitU_quad_sig
import Theorems.Thm_PIW_AdelicOrbitU_quad_sig_sig
import Theorems.Thm_PIW_AdelicOrbitU_quad_sigma_sigma
import Theorems.Thm_PIW_AdelicOrbitU_quad_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution : StFix := by
  intro F E _ _ _ _ σ h2 hfix R _ _
  have hσσ : ∀ a : E, σ (σ a) = a := fun a => quad_sigma_sigma (σ := σ) (h2 := h2) (hfix := hfix) a
  refine ⟨fun z => quad_sig_sig σ R hσσ z, ?_⟩
  intro z hz
  obtain ⟨θ, _hθ0, hσθ, ⟨d, _hd0, hd⟩, hli⟩ := quad_exists_theta (σ := σ) (h2 := h2) (hfix := hfix)
  obtain ⟨a, b, rfl⟩ : ∃ a b : R, z = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ :=
    ⟨_, _, quad_decomp (h2 := h2) (hli := hli) (R := R) z⟩
  rw [quad_sig (R := R) (σ := σ) (hσθ := hσθ)] at hz
  have h1 : (-b) ⊗ₜ[F] θ = b ⊗ₜ[F] θ := add_left_cancel hz
  have hb : b ⊗ₜ[F] θ = 0 := by
    have h2' : (2 : F) • (b ⊗ₜ[F] θ) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      rw [TensorProduct.neg_tmul, neg_add_cancel]
    exact (smul_eq_zero.mp h2').resolve_left two_ne_zero
  have h12 : algebraMap F R (1 / 2) * (2 * a) = a := by
    rw [← mul_assoc, show (2 : R) = algebraMap F R 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  rw [quad_trace (R := R) (hd := hd), hb, add_zero, h12]
  · simp [Algebra.TensorProduct.algebraMap_apply]
  · exact h2
  · exact hli
end PIW.AdelicOrbitU
