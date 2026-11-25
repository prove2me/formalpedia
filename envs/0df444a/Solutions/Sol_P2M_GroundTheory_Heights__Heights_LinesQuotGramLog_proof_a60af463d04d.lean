-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesQuotGramLog_proof_a60af463d04d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:45.645884+00:00
-- url     : https://prove2.me/submissions/c601d858-aabc-4c80-be82-dfc1470c96b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotGramLog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_basis_eq_elim_c623a59c968c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_diag_posDef_5ddf34fbf3d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329


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
open Matrix
open scoped ComplexOrder
open KLinesQuotGramLog
namespace GroundTheory.Heights₂.Heights
namespace LinesQuotGramLog
theorem _root_.solution (h1 : LinesGramDetChange.Statement) (h2 : LinesCoordDet.Statement)
    (h3 : LinesGramFischerBound.Statement) (h4 : LinesGramPosDef.Statement) :
    LinesQuotGramLog.Statement := by
  intro K _ n m k d σ B b c τ hd hBl hBr hτ hli
  classical
  set H : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun x => (d x : ℂ) with hH
  have hHpd : H.PosDef := diag_posDef d hd
  have hBe := basis_eq_elim B b τ hBl hBr

  have hchg := h1 K n H σ (Fin m ⊕ Fin k) B (Sum.elim b c)
  obtain ⟨hdetP, hV⟩ := h2 K n m k B b c hBl hli
  set z : ℂ := σ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det with hz
  rw [hdetP] at hchg
  have hzc : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  rw [hzc] at hchg
  have hGu : (gramAt H σ (Sum.elim b c)).det.re = ‖z‖ ^ 2 * (gramAt H σ (⇑B)).det.re := by
    rw [hchg, Complex.re_ofReal_mul]

  have hliB : LinearIndependent K (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K)) := by
    rw [← hBe]; exact B.linearIndependent
  have hFis := h3 K n m k d σ b τ hd hτ hliB
  rw [← hBe] at hFis

  have hlib : LinearIndependent K b := hli.comp Sum.inl Sum.inl_injective
  have hGb : 0 < (gramAt H σ b).det.re :=
    MCDet.re_det_pos (h4 K n H σ (Fin m) b hHpd hlib)
  have hGB : 0 < (gramAt H σ (⇑B)).det.re :=
    MCDet.re_det_pos (h4 K n H σ (Fin m ⊕ Fin k) (⇑B) hHpd B.linearIndependent)
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hV)
  have hprod : 0 < ∏ j, d (τ j) := Finset.prod_pos fun j _ => hd (τ j)

  rw [hGu, Real.log_mul (pow_pos hz0 2).ne' hGB.ne', Real.log_pow]
  have hlog := Real.log_le_log hGB hFis
  rw [Real.log_mul hGb.ne' hprod.ne', Real.log_prod fun j _ => (hd (τ j)).ne'] at hlog
  push_cast
  linarith
end LinesQuotGramLog
end GroundTheory.Heights₂.Heights
