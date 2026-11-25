-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_red_neg__9b7cf759e7aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:57.539884+00:00
-- url     : https://prove2.me/submissions/bc378d1a-e5a8-44dc-b717-650e4b99979e

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
theorem _root_.solution (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = -red ϖ k x := by
  ext i j
  simp [red]
end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
