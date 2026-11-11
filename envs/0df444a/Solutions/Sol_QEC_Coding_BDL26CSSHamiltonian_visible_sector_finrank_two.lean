-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.visible_sector_finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:44:31.179627+00:00
-- url     : https://prove2.me/submissions/ad40fba5-6f0c-4b35-9840-0c29f860fa8d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_realizable_sector_finrank_two
import Theorems.Thm_QEC_Coding_CSSGibbs_mem_realizableSyndromes_iff
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_118
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_119
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution
    (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n)))
    (hs : s ∈ visibleRealizable S n) : Module.finrank ℂ (sector S n s) = 2 := by
  have huv := (CSSGibbs.mem_realizableSyndromes_iff (zSyndrome S n) (xSyndrome S n) s).mp hs
  let u : LinearMap.range (zSyndrome S n) := ⟨fun z => s (.inl z), huv.1⟩
  let v : LinearMap.range (xSyndrome S n) := ⟨fun x => s (.inr x), huv.2⟩
  have hword : CSSGibbs.joinSyndrome u.val v.val = s := by
    funext j
    cases j <;> rfl
  have hr := realizable_sector_finrank_two S n u v
  exact (congrArg (fun t : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n)) =>
    Module.finrank ℂ (sector S n t)) hword).symm.trans hr
end QEC.Coding.BDL26CSSHamiltonian
