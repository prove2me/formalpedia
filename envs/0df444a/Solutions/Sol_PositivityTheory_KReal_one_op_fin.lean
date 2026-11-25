-- Prove2me | solution 1 for PositivityTheory.KReal.one_op_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:23.916102+00:00
-- url     : https://prove2.me/submissions/1af7894b-3f30-4413-b9e2-4bcb61ff0cd2

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpectrumNonemptyOfCountableRank
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
import Theorems.Thm_PositivityTheory_KReal_one_op_tprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KReal
variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
namespace PositivityTheory.KReal
theorem _root_.solution (i : ι) (x : PiTensorProduct ℂ M) :
    ∃ s : Finset (M i), ∀ f g : Module.End ℂ (M i), (∀ m ∈ s, f m = g m) → one_op i f x = one_op i g x := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    refine ⟨{y i}, fun f g h => ?_⟩
    rw [map_smul, map_smul, one_op_tprod, one_op_tprod, h _ (Finset.mem_singleton_self _)]
  | add y z hy hz =>
    obtain ⟨s, hs⟩ := hy
    obtain ⟨t, ht⟩ := hz
    refine ⟨s ∪ t, fun f g h => ?_⟩
    rw [map_add, map_add, hs f g fun m hm => h m (Finset.mem_union_left _ hm),
      ht f g fun m hm => h m (Finset.mem_union_right _ hm)]
end PositivityTheory.KReal
