-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_red_one__e5dbbbbc4a56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:30:10.93198+00:00
-- url     : https://prove2.me/submissions/f6ee98ed-cf80-4437-b865-cdaf430e5f80

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicityReductionDiagonalProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.NuDiag
namespace GlobalTheory.CompanionTheory.SiegLoc.NuDiag
theorem _root_.solution {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} :
    red ϖ k (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp only [PositivityTheory.PfSWUS.Loc.red]
  exact Matrix.map_one _ (map_zero _) (map_one _)
end GlobalTheory.CompanionTheory.SiegLoc.NuDiag
