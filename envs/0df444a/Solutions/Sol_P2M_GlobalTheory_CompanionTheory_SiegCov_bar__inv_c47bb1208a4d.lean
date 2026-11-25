-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SiegCov_bar__inv_c47bb1208a4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:48.916786+00:00
-- url     : https://prove2.me/submissions/bedd4c1b-a26e-4649-8a6f-d3e186757eef

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumCongrInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegCov
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegCov
theorem _root_.solution (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (hσ : ∀ a, σ (σ a) = a) (k : ℕ)
    (a : R ⧸ lev ϖ k) : barσ σ ϖ hf k (barσ σ ϖ hf k a) = a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [barσ_mk, barσ_mk, hσ]
end GlobalTheory.CompanionTheory.SiegCov
