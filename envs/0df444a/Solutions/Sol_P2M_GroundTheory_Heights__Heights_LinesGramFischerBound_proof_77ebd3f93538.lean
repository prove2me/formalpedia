-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesGramFischerBound_proof_77ebd3f93538
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:34.840118+00:00
-- url     : https://prove2.me/submissions/c79b96ed-b1c1-41f8-91a3-aa41a75a6341

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramFischerBound

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
namespace GroundTheory.Heights₂.Heights
namespace LinesGramFischerBound
theorem _root_.solution (h1 : LinesGramPosDef.Statement)
    (h2 : LinesFischer.Statement) (h3 : LinesDiagGram.Statement) :
    LinesGramFischerBound.Statement := by
  intro K _ n m k d σ b τ hd hτ hli
  set t : Fin k → Fin n → K := fun j => Pi.single (τ j) 1 with ht
  set h : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun x => (d x : ℂ) with hh
  have hpos : h.PosDef := Matrix.PosDef.diagonal fun x => Complex.zero_lt_real.mpr (hd x)
  have hG := h1 K n h σ (Fin m ⊕ Fin k) (Sum.elim b t) hpos hli
  have hF := h2 (Fin m) (Fin k) _ hG
  have hB1 : (gramAt h σ (Sum.elim b t)).toBlocks₁₁ = gramAt h σ b := by
    ext i j; rfl
  have hB2 : (gramAt h σ (Sum.elim b t)).toBlocks₂₂ = gramAt h σ t := by
    ext i j; rfl
  have hD : gramAt h σ t = Matrix.diagonal fun j => (d (τ j) : ℂ) := h3 K n d σ k τ hτ
  rw [hB1, hB2, hD, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re] at hF
  exact hF
end LinesGramFischerBound
end GroundTheory.Heights₂.Heights
