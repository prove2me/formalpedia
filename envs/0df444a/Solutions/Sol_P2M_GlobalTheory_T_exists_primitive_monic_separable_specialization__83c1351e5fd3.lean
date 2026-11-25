-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_primitive_monic_separable_specialization__83c1351e5fd3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:04.14557+00:00
-- url     : https://prove2.me/submissions/02fa95fb-5d2d-4d0b-8bb8-985dba0c14d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecialization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecializationStatement
import Theorems.Thm_GlobalTheory_PrimTransc_exists_primitive_monic_separable_specialization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℚ x → ∀ (J : Type) [Finite J] (e : J → K), ∃ (P : Polynomial (MvPolynomial (Fin D) ℚ)) (ψ : AdjoinRoot P →ₐ[ℚ] K) (g : K) (c : Fin D → ℚ), P.Monic ∧ Function.Injective ψ ∧ (∀ i, ψ (AdjoinRoot.of P (MvPolynomial.X i)) = x i) ∧ g ≠ 0 ∧ (∀ j, g * e j ∈ ψ.range) ∧ (P.map (MvPolynomial.eval c)).Separable := by
  first | exact @GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization | exact GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization | (intros; apply GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization <;> assumption)
end _root_.GlobalTheory.T
