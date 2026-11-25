-- Prove2me | solution 1 for PI.SqPair.LCP.blk_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:27:57.192371+00:00
-- url     : https://prove2.me/submissions/deeb9923-16c5-42b5-a02a-1710a8914637

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.SqPair.LCP
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (ϖ : R) (k : ℕ)
    (A A' h u u' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (A₁ A₁' h₂ : Matrix κ κ R) (d : Fin 2 → R)
    (hrel : hᴴ * A * h = (ϖ ^ (2 * k)) • A')
    (hA : uᴴ * A * u = fromBlocks hyp 0 0 A₁) (hA' : u'ᴴ * A' * u' = fromBlocks hyp 0 0 A₁')
    (hh : h * u' = u * fromBlocks (diagonal d) 0 0 h₂) :
    h₂ᴴ * A₁ * h₂ = (ϖ ^ (2 * k)) • A₁' := by
  have e1 : (h * u')ᴴ * A * (h * u') = (ϖ ^ (2 * k)) • fromBlocks hyp 0 0 A₁' := by
    rw [← hA', conjTranspose_mul]
    calc u'ᴴ * hᴴ * A * (h * u') = u'ᴴ * (hᴴ * A * h) * u' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hrel, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : (h * u')ᴴ * A * (h * u') = (fromBlocks (diagonal d) 0 0 h₂)ᴴ *
      (uᴴ * A * u) * fromBlocks (diagonal d) 0 0 h₂ := by
    rw [hh, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e2, hA, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_smul] at e1
  have := (fromBlocks_inj.1 e1).2.2.2
  simpa using this
end PI.SqPair.LCP
