-- Prove2me | solution 1 for QEC.QLDPC.hasUniformLDPC_of_region_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:21.654199+00:00
-- url     : https://prove2.me/submissions/c1f46fcc-84c4-4c0e-a8b4-71a3c8f1c2d9

import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_boundedLocality_of_region_bounds
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_boundedLocality_of_region_bounds


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC
theorem _root_.solution
    (F : QuantumCodeFamily A ι κ) (B : Nat)
    (hcheck : ∀ a checkIndex,
      ((F.presentation a).checks checkIndex).region.selected.card ≤ B)
    (hcoordinate : ∀ a coordinate,
      ((F.presentation a).incidence.variableSupport coordinate).card ≤ B) :
    HasUniformLDPC F := by
  exact ⟨B, fun a =>
    F.boundedLocality_of_region_bounds a (hcheck a) (hcoordinate a)⟩
end QEC.QLDPC
