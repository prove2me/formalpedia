-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.fibreOrbit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:29:14.910107+00:00
-- url     : https://prove2.me/submissions/1d6d3156-8799-4a64-89c1-c3d7be9090f4

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_det_Hpk
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_UH_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_UH_det
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_UH_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_Gf_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FibOrbAsmW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
namespace PI.UnitaryGroupMassFormula.FibOrbAsmW
theorem _root_.solution (hW : WittExt) (hF : FixFrame) (hG : GramBlocks) (hC : GramIndependentSignature) : FibreOrbit := by
  intro k r z z' hstd g₁ hg₁ g₂ hg₂ hpos hZ
  have hpos₂ : 0 < Gf k r z z' g₂ := by rw [Gf_congr hZ]; exact hpos
  have hli₁ := (hC k r z z' g₁ hstd ⟨hg₁, hpos⟩).1
  have hli₂ := (hC k r z z' g₂ hstd ⟨hg₂, hpos₂⟩).1
  have hgram : gramM k r z z' g₁ = gramM k r z z' g₂ := by
    rw [hG k r z z' hstd.2.1 hstd.2.2 g₁ hg₁, hG k r z z' hstd.2.1 hstd.2.2 g₂ hg₂, hZ]
  obtain ⟨h, hh, hhx⟩ := hW k r (Fin (r + 1) ⊕ Fin (r + 1)) (gramVec k r z z' g₁) (gramVec k r z z' g₂)
    hli₁ hli₂ (fun i j => by
      have := congrFun (congrFun hgram j) i
      exact this)
  have hfix : ∀ a, h *ᵥ fvec k r z a = fvec k r z a := fun a => hhx (Sum.inl a)
  have hmove : ∀ b, h *ᵥ (g₁ *ᵥ fvec k r z' b) = g₂ *ᵥ fvec k r z' b := fun b => hhx (Sum.inr b)
  have hH := det_Hpk k r
  have hdh : IsUnit h.det := UH_det hH hh
  have hd₁ : IsUnit g₁.det := UH_det hH hg₁
  refine ⟨h⁻¹, ?_, g₁⁻¹ * h⁻¹ * g₂, ?_, ?_⟩
  · rw [← hF k r z hstd.2.1]
    refine ⟨UH_inv hH hh, fun a => ?_⟩
    calc h⁻¹ *ᵥ fvec k r z a = h⁻¹ *ᵥ (h *ᵥ fvec k r z a) := by rw [hfix a]
      _ = fvec k r z a := by rw [mulVec_mulVec, nonsing_inv_mul _ hdh, one_mulVec]
  · rw [← hF k r z' hstd.2.2]
    refine ⟨UH_mul (UH_mul (UH_inv hH hg₁) (UH_inv hH hh)) hg₂, fun b => ?_⟩
    calc (g₁⁻¹ * h⁻¹ * g₂) *ᵥ fvec k r z' b = g₁⁻¹ *ᵥ (h⁻¹ *ᵥ (g₂ *ᵥ fvec k r z' b)) := by
          rw [mulVec_mulVec, mulVec_mulVec]
      _ = g₁⁻¹ *ᵥ (h⁻¹ *ᵥ (h *ᵥ (g₁ *ᵥ fvec k r z' b))) := by rw [hmove b]
      _ = fvec k r z' b := by
          have e₁ : h⁻¹ *ᵥ (h *ᵥ (g₁ *ᵥ fvec k r z' b)) = g₁ *ᵥ fvec k r z' b := by
            rw [mulVec_mulVec, nonsing_inv_mul _ hdh, one_mulVec]
          rw [e₁, mulVec_mulVec, nonsing_inv_mul _ hd₁, one_mulVec]
  · rw [nonsing_inv_nonsing_inv _ hdh]
    calc g₂ = h * (g₁ * g₁⁻¹) * (h⁻¹ * g₂) := by
          rw [mul_nonsing_inv _ hd₁, Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ hdh,
            Matrix.one_mul]
      _ = h * g₁ * (g₁⁻¹ * h⁻¹ * g₂) := by simp only [Matrix.mul_assoc]
end PI.UnitaryGroupMassFormula.FibOrbAsmW
