-- Prove2me | solution 1 for QInfo.exists_orthogonalProjector
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T14:45:21.051443+00:00
-- url     : https://prove2.me/submissions/ea526bd3-9caf-4cd1-8d65-fd0ed9a0bc77

import Mathlib
import Theorems.Thm_QInfo_exists_rangeProjector_mul_conjTranspose
open Matrix
open scoped ComplexOrder

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Submodule ℂ (ι → ℂ)) :
    ∃ P : Matrix ι ι ℂ, P.IsHermitian ∧ P * P = P ∧ (∀ v, P *ᵥ v ∈ C) ∧
      ∀ v ∈ C, P *ᵥ v = v := by
  let b := Module.finBasis ℂ C
  let V : Matrix ι (Fin (Module.finrank ℂ C)) ℂ := Matrix.of fun x i => (b i : ι → ℂ) x
  obtain ⟨Gp, hGp, hc, hW⟩ := QInfo.exists_rangeProjector_mul_conjTranspose V
  have hcol : ∀ u, V *ᵥ u = ∑ i, u i • (b i : ι → ℂ) := by
    intro u; ext x
    simp [V, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hmem : ∀ u, V *ᵥ u ∈ C := by
    intro u; rw [hcol]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
  refine ⟨V * Vᴴ * Gp, ?_, ?_, ?_, ?_⟩
  · show (V * Vᴴ * Gp)ᴴ = V * Vᴴ * Gp
    rw [conjTranspose_mul, hGp.eq, (isHermitian_mul_conjTranspose_self V).eq, hc]
  · calc V * Vᴴ * Gp * (V * Vᴴ * Gp) = (V * Vᴴ * Gp * V) * Vᴴ * Gp := by
          simp only [Matrix.mul_assoc]
      _ = V * Vᴴ * Gp := by rw [hW]
  · intro v
    rw [show V * Vᴴ * Gp = V * (Vᴴ * Gp) by simp only [Matrix.mul_assoc], ← mulVec_mulVec]
    exact hmem _
  · intro v hv
    have hv' : v = V *ᵥ (fun i => b.repr ⟨v, hv⟩ i) := by
      rw [hcol]
      have := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hv', mulVec_mulVec, hW]

