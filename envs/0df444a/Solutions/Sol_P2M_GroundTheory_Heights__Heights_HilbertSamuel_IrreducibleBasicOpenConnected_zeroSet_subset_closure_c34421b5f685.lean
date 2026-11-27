-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_zeroSet_subset_closure_c34421b5f685
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:04:00.982824+00:00
-- url     : https://prove2.me/submissions/97886337-18ef-4a93-b0e4-b29b1a9b5137

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_BasicOpenSteps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_linPoly_e958af14dbe7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_dense_ne_zero_1de0df4f6e8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_proof_223c44725f20


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace IrreducibleBasicOpenConnected
theorem _root_.solution {n d : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hW : W.IsPrime) (hA : ComplexSets.IsFiniteProjection W A)
    {R : MvPolynomial (Fin d) ℂ} (hR : R ≠ 0) :
    ComplexSets.zeroSet W ⊆ closure {x | x ∈ ComplexSets.zeroSet W ∧ eval (A.mulVec x) R ≠ 0} := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro U hU
  have hN := IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof n d W (ComplexSets.linPoly A) hW hA.injective
    hA.finite x hx U hU
  have hfun : (fun z : Fin n → ℂ => fun i => eval z (ComplexSets.linPoly A i)) = fun z => A.mulVec z :=
    funext fun z => IrreducibleBasicOpenConnected.eval_linPoly A z
  rw [hfun, IrreducibleBasicOpenConnected.eval_linPoly] at hN
  obtain ⟨y, ⟨z, ⟨hzW, hzU⟩, rfl⟩, hyR⟩ :=
    mem_closure_iff_nhds.mp (IrreducibleBasicOpenConnected.dense_ne_zero hR (A.mulVec x)) _ hN
  exact ⟨z, hzU, hzW, hyR⟩
end IrreducibleBasicOpenConnected
end GroundTheory.Heights₂.Heights.HilbertSamuel
