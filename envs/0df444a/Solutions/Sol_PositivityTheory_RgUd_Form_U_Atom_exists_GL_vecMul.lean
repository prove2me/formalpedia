-- Prove2me | solution 1 for PositivityTheory.RgUd.Form.U.Atom.exists_GL_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:40.661704+00:00
-- url     : https://prove2.me/submissions/33a6cce4-1b6f-47df-95cf-3bc9157dc12b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenAdditiveCharacterKernelStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCompactOpenSubgroupMemStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactSupAddSubgroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCosetRepresentativesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexOpenCompactNeZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenCharacterAnnihilatorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorCompactWithinNhdsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComapMulVecCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLVecMulEqLastBasisStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSemidefiniteNullRadicalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SesquilinearEqZeroOfDiagZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumTranslateInvariantStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumsProportionalCard
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_HermitianForms_UnitaryLattices_IsotropicAtoms_ChartRestriction
import Theorems.Thm_GlobalTheory_T_exists_GL_vecMul_eq_last_basis


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
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd.Form.U.Atom
namespace PositivityTheory.RgUd.Form.U.Atom
theorem _root_.solution {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k) (hξ : ξ ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 :=
  GlobalTheory.T.exists_GL_vecMul_eq_last_basis n ξ hξ
end PositivityTheory.RgUd.Form.U.Atom
