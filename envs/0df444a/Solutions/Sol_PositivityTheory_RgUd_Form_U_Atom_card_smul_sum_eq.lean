-- Prove2me | solution 1 for PositivityTheory.RgUd.Form.U.Atom.card_smul_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:24.733244+00:00
-- url     : https://prove2.me/submissions/60d5ef07-e398-4ae0-b6e3-d245060b41f9

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
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] {A H H' : AddSubgroup X} (hH : H ≤ A) (hH' : H' ≤ A)
    {T T' : Finset X} (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (hT' : ∀ t ∈ T', t ∈ A) (hTr' : ∀ a ∈ A, ∃! t, t ∈ T' ∧ a - t ∈ H') (F : X → M)
    (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) (hF' : ∀ a, ∀ h ∈ H', F (a + h) = F a) :
    (T'.card : ℂ) • ∑ t ∈ T, F t = (T.card : ℂ) • ∑ t ∈ T', F t := by
  have h1 : ∀ s ∈ T', ∑ t ∈ T, F (t + s) = ∑ t ∈ T, F t := fun s hs =>
    sum_transversal_add hH hT hTr F hF (hT' s hs)
  have h2 : ∀ t ∈ T, ∑ s ∈ T', F (s + t) = ∑ s ∈ T', F s := fun t ht =>
    sum_transversal_add hH' hT' hTr' F hF' (hT t ht)
  have e1 : ∑ s ∈ T', ∑ t ∈ T, F (t + s) = T'.card • ∑ t ∈ T, F t := by
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
  have e2 : ∑ t ∈ T, ∑ s ∈ T', F (s + t) = T.card • ∑ s ∈ T', F s := by
    rw [Finset.sum_congr rfl h2, Finset.sum_const]
  have e3 : ∑ s ∈ T', ∑ t ∈ T, F (t + s) = ∑ t ∈ T, ∑ s ∈ T', F (s + t) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [add_comm]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← e1, ← e2, e3]
end PositivityTheory.RgUd.Form.U.Atom
