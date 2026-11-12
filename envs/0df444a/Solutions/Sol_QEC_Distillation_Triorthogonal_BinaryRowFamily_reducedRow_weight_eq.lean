-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRow_weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:54:49.071098+00:00
-- url     : https://prove2.me/submissions/0b134335-bbab-497d-b6d6-83b49ae95911

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_hammingWeight_even_of_mem_evenCode

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
    (r : R.ReducedRowIndex) :
    HammingWeight (R.reducedRow r) =
      R.reducedRowParity r + 2 * R.rowGamma r := by
  rcases r with a | e
  · obtain ⟨k, hk⟩ := hR.odd_weight a
    change HammingWeight (R.oddRow a) =
      R.reducedRowParity (.inl a) + 2 * R.rowGamma (.inl a)
    change HammingWeight (R.oddRow a) =
      1 + 2 * ((HammingWeight (R.oddRow a) - 1) / 2)
    rw [hk]
    omega
  · have heven := R.hammingWeight_even_of_mem_evenCode hR (R.evenBasis e).property
    obtain ⟨k, hk⟩ := heven
    change HammingWeight (R.evenBasis e : Word (ZMod 2) Col) =
      R.reducedRowParity (.inr e) + 2 * R.rowGamma (.inr e)
    change HammingWeight (R.evenBasis e : Word (ZMod 2) Col) =
      0 + 2 * ((HammingWeight (R.evenBasis e : Word (ZMod 2) Col) - 0) / 2)
    rw [hk]
    omega
end QEC.Distillation.Triorthogonal.BinaryRowFamily
