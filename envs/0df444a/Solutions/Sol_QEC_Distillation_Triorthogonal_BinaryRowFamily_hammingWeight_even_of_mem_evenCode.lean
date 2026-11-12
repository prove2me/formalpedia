-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_even_of_mem_evenCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:52:19.559093+00:00
-- url     : https://prove2.me/submissions/08bb9a56-fd1d-4178-8dad-72dbc91e31f2

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordPairing_evenCode_rowCode

section
noncomputable section
namespace QEC
namespace Distillation
namespace Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
namespace CliffordCorrectionAtom
end CliffordCorrectionAtom
universe uO uE uC
namespace BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
private theorem evenCode_mem_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier) :
    x ∈ R.rowCode.carrier := by
  rw [R.rowCode_eq_evenCode_sup_oddCode]
  exact Submodule.mem_sup_left hx
universe v
end BinaryRowFamily
end Triorthogonal
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier) :
    Even (HammingWeight x) := by
  rw [← ZMod.natCast_eq_zero_iff_even, ← pairOverlap_self_eq_hammingWeight,
    pairOverlap_cast]
  exact R.wordPairing_evenCode_rowCode hR hx (evenCode_mem_rowCode R hx)
end QEC.Distillation.Triorthogonal.BinaryRowFamily
