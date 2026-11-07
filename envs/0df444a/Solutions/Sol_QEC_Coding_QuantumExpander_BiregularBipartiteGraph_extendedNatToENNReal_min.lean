-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.extendedNatToENNReal_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:40:55.118924+00:00
-- url     : https://prove2.me/submissions/b3cb730b-f57d-4053-87ff-a077e0e5f8ed

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_extendedNatToENNReal_mono

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
open QEC.Coding.QuantumExpander.BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
namespace QEC.Coding.QuantumExpander.BiregularBipartiteGraph
theorem _root_.solution (m n : WithTop Nat) :
    extendedNatToENNReal (min m n) =
      min (extendedNatToENNReal m) (extendedNatToENNReal n) := by
  by_cases hmn : m ≤ n
  · rw [min_eq_left hmn, min_eq_left (extendedNatToENNReal_mono hmn)]
  · have hnm : n ≤ m := le_of_not_ge hmn
    rw [min_eq_right hnm, min_eq_right (extendedNatToENNReal_mono hnm)]
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph
