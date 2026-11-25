-- Prove2me | solution 1 for P2M_GlobalTheory_RootEx_ParabolicEntries_toBlocks___mul_ddd2957152e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:34.739052+00:00
-- url     : https://prove2.me/submissions/b18a46b0-8a7d-41e1-9d79-4cb0a0c9d1bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ParabolicEntries
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.ParabolicEntries
theorem _root_.solution {L : ℕ} {b : Fin c → ℕ} {g h : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b)
    (hh : h ∈ parGroup k n L b) : (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  ext r s
  simp only [Units.val_mul, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [add_eq_left]
  refine Finset.sum_eq_zero fun t _ => ?_
  rcases le_total (b t) L with ht | ht
  · rw [hg (Sum.inl r) (Sum.inr t) (by simp) ht, Matrix.one_apply_ne (by simp), zero_mul]
  · rw [hh (Sum.inr t) (Sum.inl s) (by simp) ht, Matrix.one_apply_ne (by simp), mul_zero]
end GlobalTheory.RootEx.ParabolicEntries
