-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesQuotDegreeBound_proof_61110a0b3b52
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:59.071803+00:00
-- url     : https://prove2.me/submissions/c2ed9973-25c1-4861-86ad-eedfcfea9da6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotDegreeBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
namespace GroundTheory.Heights₂.Heights
namespace LinesQuotDegreeBound
theorem _root_.solution (h1 : LinesExtendBasis.Statement)
    (h2 : LinesQuotIndexLog.Statement) (h3 : LinesQuotGramLog.Statement) :
    LinesQuotDegreeBound.Statement := by
  intro K _ _ n a d ha hd m k b c hbc hmk
  have hb : LinearIndependent K b := hbc.comp Sum.inl Sum.inl_injective
  obtain ⟨τ, hτ, hbs⟩ := h1 K n m k b hb hmk
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) := by
    simp [hmk]
  let B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hbs hcard
  have hBl : ∀ i, B (Sum.inl i) = b i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank']
  have hBr : ∀ j, B (Sum.inr j) = Pi.single (τ j) 1 := fun j => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank']
  refine ⟨τ, hτ, ?_⟩
  set D := (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det with hD
  have hI := h2 K n m k a B b c τ ha hBl hBr hτ hbc
  have hG : ∀ σ : K →+* ℂ,
      Real.log (gramAt (diagMetric d σ) σ (Sum.elim b c)).det.re -
          Real.log (gramAt (diagMetric d σ) σ b).det.re ≤
        ∑ j, Real.log (d σ (τ j)) + 2 * Real.log ‖σ D‖ := fun σ =>
    h3 K n m k (d σ) σ B b c τ (hd σ) hBl hBr hτ hbc
  have hGs := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hG σ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm] at hGs
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold quotDegree
  linarith
end LinesQuotDegreeBound
end GroundTheory.Heights₂.Heights
