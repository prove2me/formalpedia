-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.N3.Pus.sigmaUnique_eq_stdBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:33.955521+00:00
-- url     : https://prove2.me/submissions/25d1465c-2eb6-47d8-9ddd-e08cdac05735

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_SphericalEmbeddings_SigmaUniqueEqStdBlocks
import Theorems.Thm_GlobalTheory_SmGL_stdBlocks_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pus
namespace PositivityTheory.Rg.BcB.N3.Pus
theorem _root_.solution (N : ℕ) (h : ∑ _ : Fin N, 1 = N) :
    (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) = stdBlocks (fun _ => 1) h := by
  ext ⟨a, i⟩
  rw [stdBlocks_val]
  simp [Fin.eq_zero i]
end PositivityTheory.Rg.BcB.N3.Pus
