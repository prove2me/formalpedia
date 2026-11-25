-- Prove2me | solution 1 for PIW.AdelClassFin.hmk_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:38.7448+00:00
-- url     : https://prove2.me/submissions/1d4625c1-7d98-4c14-b6c8-ed60e558848f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HmkFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open MeasureTheory Matrix Module
open scoped MatrixOrder
namespace PIW.AdelClassFin
theorem _root_.solution {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef) :
    ∃ B : Matrix (Fin N) (Fin N) ℝ, G = Bᵀ * B := by
  refine ⟨CFC.sqrt G, ?_⟩
  have h0 : (0 : Matrix (Fin N) (Fin N) ℝ) ≤ G := hG.posSemidef.nonneg
  have hsa : IsSelfAdjoint (CFC.sqrt G) := (CFC.sqrt_nonneg G).isSelfAdjoint
  have ht : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsa.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [ht, CFC.sqrt_mul_sqrt_self G h0]
end PIW.AdelClassFin
