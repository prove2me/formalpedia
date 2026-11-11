-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.full_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:15:40.9982+00:00
-- url     : https://prove2.me/submissions/27e83123-18b3-4c54-9c4f-bb4481ae7b63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_xRowCode
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_global_normal_form
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
private theorem generator_scalar (c : ZMod 2) :
    (BDL26FiniteCohomology.generator S (n+2) c).val = c • xWord S n := by
  let e : BDL26FiniteCohomology.Cocycle S 0 := BDL26SeedCohomology.seedElement
  have hlin : BDL26FiniteCohomology.prefixCocycle S (n+2) (c • e) =
      c • BDL26FiniteCohomology.prefixCocycle S (n+2) e :=
    map_smul (BDL26FiniteCohomology.prefixCocycle S (n+2)) c e
  have hx : (BDL26FiniteCohomology.prefixCocycle S (n+2) e).val = xWord S n := by
    have hu : e = (1 : ZMod 2) • e := (one_smul (ZMod 2) e).symm
    exact congrArg (fun w : BDL26FiniteCohomology.Cocycle S 0 =>
      (BDL26FiniteCohomology.prefixCocycle S (n+2) w).val) hu
  calc
    (BDL26FiniteCohomology.generator S (n+2) c).val =
        (BDL26FiniteCohomology.prefixCocycle S (n+2) (c • e)).val := rfl
    _ = c • (BDL26FiniteCohomology.prefixCocycle S (n+2) e).val :=
      congrArg (fun w : BDL26FiniteCohomology.Cocycle S (n+2) => w.val) hlin
    _ = c • xWord S n := congrArg (fun w : W S n => c • w) hx
end QEC.Coding.BDL26LogicalDefectProtection
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_23
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_24
namespace QEC.Coding.BDL26LogicalDefectProtection
theorem _root_.solution (a : BDL26FiniteCohomology.Cocycle S (n+2)) :
    ∃ g : W S n, g ∈ xRows S n ∧ a.val = g + h1Coordinate S n a • xWord S n := by
  obtain ⟨f, hf⟩ := BDL26FiniteCohomology.global_normal_form S (n+2) a
  refine ⟨BDL26RZMap1CoordinateBridge.tannerCoboundary0
    (BDL26DecodingGraph.state S (n+2)).presentation f, ?_, ?_⟩
  · rw [xRows, xRowCode]
    exact (BDL26RZCohomology.mem_boundary_iff _ _).mpr ⟨f, rfl⟩
  · exact hf.trans (congrArg (fun w : W S n =>
      BDL26RZMap1CoordinateBridge.tannerCoboundary0
        (BDL26DecodingGraph.state S (n+2)).presentation f + w) (generator_scalar S n _))
end QEC.Coding.BDL26LogicalDefectProtection
