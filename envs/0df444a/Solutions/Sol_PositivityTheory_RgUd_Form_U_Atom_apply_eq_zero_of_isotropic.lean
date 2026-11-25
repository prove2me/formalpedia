-- Prove2me | solution 1 for PositivityTheory.RgUd.Form.U.Atom.apply_eq_zero_of_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:56:05.476388+00:00
-- url     : https://prove2.me/submissions/e3dc3307-1b6d-4c00-90f7-e17ed9ab8198

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
import Theorems.Thm_GlobalTheory_T_hermitian_semidefinite_null_radical


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
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.RgUd.Form.U.Atom
theorem _root_.solution (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hB' : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 :=
  GlobalTheory.T.hermitian_semidefinite_null_radical B hB hB' x hx w
end PositivityTheory.RgUd.Form.U.Atom
