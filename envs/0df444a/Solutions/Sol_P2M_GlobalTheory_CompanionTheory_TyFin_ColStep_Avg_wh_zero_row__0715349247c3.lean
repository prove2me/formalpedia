-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_wh_zero_row__0715349247c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:37.756332+00:00
-- url     : https://prove2.me/submissions/5005093a-1abe-4cc9-8df0-76e451afb342

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_wh_zero_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d j : ℕ}
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ),
    (∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) →
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  intro K _ _ _ d j ψ₀ χ hs
  exact wh_zero_row K d j ψ₀ χ hs
end GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
