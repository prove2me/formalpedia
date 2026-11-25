-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_DiagonalChange_proof_8ff81c4b2bba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:43.033187+00:00
-- url     : https://prove2.me/submissions/9bfbd4d0-5cac-4320-8d97-c0997b1dbbdf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_eq_of_norm_eq_284c59650304

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace DiagonalChange
theorem _root_.solution : DiagonalChange.Statement := by
  intro K _ _ M h' T hT _
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) M.carrier)) =
      Module.finrank (𝓞 K) M.carrier := Fintype.card_fin _
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet h' σ s) =
      2 * Real.log ‖LinearMap.det (T σ)‖ + Real.log (gramDet M.metric σ s) := by
    intro σ
    have hp := gramDet_pos h' σ hs
    have hp0 := gramDet_pos M.metric σ hs
    rw [gramDet_eq_of_norm_eq M.metric h' σ (T σ) (hT σ) hs hcard] at hp ⊢
    have hd : ‖LinearMap.det (T σ)‖ ≠ 0 := by
      intro h0
      rw [h0] at hp
      simp at hp
    rw [Real.log_mul (pow_ne_zero 2 hd) hp0.ne', Real.log_pow]
    push_cast
    ring
  simp only [HermitianBundle.deg, HermitianBundle.arithDegree]
  rw [arithDegree_eq h' hs hcard, arithDegree_eq M.metric hs hcard]
  simp only [degreeWith, hlog, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
end DiagonalChange
end GroundTheory.Heights₂.Heights.LatticeLemmas
