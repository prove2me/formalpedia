-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditEncodedCode_carrier_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:37:54.196063+00:00
-- url     : https://prove2.me/submissions/8a9270d1-5fc6-4613-9e41-95452724058a

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_encodingLinearMap_apply_logical_basis
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_encodingLinearMap_apply_logical_basis


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry.F256GarciaStichtenoth Semantics
open Ngu24MultiplicativeCCZ
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_24
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ) :
    (f256QuditEncodedCode i).code.carrier =
      Submodule.span Complex (Set.range (f256SourceInput i).shortenedCosetKet) := by
  apply le_antisymm
  · rintro x ⟨psi, rfl⟩
    change (∑ u : Word F256 (Fin (f256MultiplicationLogicalCount i)),
      psi u • (f256SourceInput i).shortenedCosetKet u) ∈ _
    apply Submodule.sum_mem
    intro u _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨u, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨u, rfl⟩
    exact ⟨registerBasisKet u, (f256SourceInput i).encodingLinearMap_apply_logical_basis u⟩
end QEC.Distillation.Ngu24MultiplicativeCSS
