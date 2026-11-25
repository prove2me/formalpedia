-- Prove2me | solution 1 for PositivityTheory.KReal.dense_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:02.506509+00:00
-- url     : https://prove2.me/submissions/fc571941-89ea-46c4-8f7a-77938a1abcaf

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpectrumNonemptyOfCountableRank
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
import Theorems.Thm_UpperTheory_Reformulated_B_DYhd6_main


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
namespace PositivityTheory.KReal
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (h : Module.rank ℂ V ≤ Cardinal.aleph0) (B : Subalgebra ℂ (Module.End ℂ V))
    (hB : ∀ N : Submodule ℂ V, (∀ b ∈ B, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End ℂ V) (s : Finset V) : ∃ b ∈ B, ∀ m ∈ s, f m = b m :=
  _root_.UpperTheory.Reformulated.B.DYhd6.main h B hB f s
end PositivityTheory.KReal
