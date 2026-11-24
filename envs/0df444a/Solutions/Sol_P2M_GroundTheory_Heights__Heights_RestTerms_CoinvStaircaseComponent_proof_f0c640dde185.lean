-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CoinvStaircaseComponent_proof_f0c640dde185
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:13.264576+00:00
-- url     : https://prove2.me/submissions/39ae6739-752d-4147-aa0a-ffb9cd2cde21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Coinv
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CoinvStaircaseComponent
theorem _root_.solution (h1 : CoinvStaircaseDegree.Statement) :
    CoinvStaircaseComponent.Statement := by
  intro K _ f n v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    have hhom : monomial e (1 : K) ∈ homogeneousSubmodule (Fin f × Fin n) K e.degree :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial 1 rfl)
    obtain ⟨hle, heq⟩ := h1 f n e he
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [homogeneousComponent_of_mem hhom, if_neg (by omega)]
    · rw [homogeneousComponent_of_mem hhom]
      by_cases h : coinvTop f n = e.degree
      · refine ⟨1, ?_⟩
        rw [if_pos h, heq h.symm, C_1, one_mul]
      · exact ⟨0, by rw [if_neg h, C_0, zero_mul]⟩
  | zero => exact ⟨fun d _ => map_zero _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    obtain ⟨hy1, cy, hy2⟩ := hy
    refine ⟨fun d hd => by rw [map_add, hx1 d hd, hy1 d hd, add_zero], cx + cy, ?_⟩
    rw [map_add, hx2, hy2, C_add, add_mul]
  | smul a x _ hx =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    refine ⟨fun d hd => by rw [map_smul, hx1 d hd, smul_zero], a * cx, ?_⟩
    rw [map_smul, hx2, smul_eq_C_mul, C_mul, mul_assoc]
end CoinvStaircaseComponent
end GroundTheory.Heights₂.Heights.RestTerms
