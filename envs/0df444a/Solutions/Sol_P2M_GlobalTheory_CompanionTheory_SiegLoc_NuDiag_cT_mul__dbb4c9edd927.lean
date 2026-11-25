-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_cT_mul__dbb4c9edd927
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:30:02.54488+00:00
-- url     : https://prove2.me/submissions/24f3147e-131d-4621-aa3d-3c6fb1102046

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
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    cT σ (a * b) = cT σ b * cT σ a := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_mul, Matrix.transpose_mul]
end GlobalTheory.CompanionTheory.SiegLoc.NuDiag
