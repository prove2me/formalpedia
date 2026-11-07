-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.extendedNatToENNReal_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:23:12.985756+00:00
-- url     : https://prove2.me/submissions/c7537375-fcf3-41f1-9112-8f71eb5c96de

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander

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
theorem _root_.solution : Monotone extendedNatToENNReal := by
  intro m n hmn
  induction m using WithTop.recTopCoe with
  | top =>
      have hn : n = ⊤ := top_unique hmn
      subst n
      exact le_rfl
  | coe m =>
      induction n using WithTop.recTopCoe with
      | top => exact le_top
      | coe n =>
          change (m : ENNReal) ≤ (n : ENNReal)
          exact_mod_cast (WithTop.coe_le_coe.mp hmn)
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph
