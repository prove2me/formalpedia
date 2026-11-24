-- Prove2me | solution 1 for PositivityTheory.RgUd.Form.U.Atom.sum_transversal_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:26.556464+00:00
-- url     : https://prove2.me/submissions/c2f76496-1526-46fa-989a-4f70466ec46d

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
import Theorems.Thm_PositivityTheory_RgUd_Form_U_Atom_sum_transversal_add

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
variable {X : Type} [AddCommGroup X]
namespace PositivityTheory.RgUd.Form.U.Atom
theorem _root_.solution {A H : AddSubgroup X} (hHA : H ≤ A) {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (χ : X → ℂ)
    (hχ : ∀ a b, χ (a + b) = χ a * χ b) (hH : ∀ h ∈ H, χ h = 1) {a : X} (ha : a ∈ A) (hne : χ a ≠ 1) :
    ∑ t ∈ T, χ t = 0 := by
  have key := sum_transversal_add hHA hT hTr χ (fun b h hh => by rw [hχ, hH h hh, mul_one]) ha
  simp only [hχ] at key
  rw [← Finset.sum_mul] at key
  have h0 : (∑ t ∈ T, χ t) * (χ a - 1) = 0 := by rw [mul_sub, mul_one, key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne
end PositivityTheory.RgUd.Form.U.Atom
