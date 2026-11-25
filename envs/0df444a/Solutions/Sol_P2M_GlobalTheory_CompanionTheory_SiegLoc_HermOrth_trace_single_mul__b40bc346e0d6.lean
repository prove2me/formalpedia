-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_trace_single_mul__b40bc346e0d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:59.53101+00:00
-- url     : https://prove2.me/submissions/95bc5753-8ec0-400a-8dee-7842d2970f92

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
theorem _root_.solution {n : ℕ} (i j : Fin n) (c : R) (y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (Matrix.single i j c * y) = c * y j i := by
  rw [Matrix.trace_single_mul, smul_eq_mul]
end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
