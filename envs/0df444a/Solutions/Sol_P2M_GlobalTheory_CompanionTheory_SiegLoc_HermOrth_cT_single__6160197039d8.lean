-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_single__6160197039d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:53.413581+00:00
-- url     : https://prove2.me/submissions/93611df9-c4d1-4adf-91d8-eb069139a299

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.HermOrth
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.HermOrth
theorem _root_.solution (σ : R →+* R) {n : ℕ} (i j : Fin n) (c : R) :
    cT σ (Matrix.single i j c) = Matrix.single j i (σ c) := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_single, Matrix.transpose_single]
end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
