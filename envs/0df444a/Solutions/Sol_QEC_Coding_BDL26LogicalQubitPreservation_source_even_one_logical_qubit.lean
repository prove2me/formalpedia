-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.source_even_one_logical_qubit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:39:37.014206+00:00
-- url     : https://prove2.me/submissions/e00bb7aa-bf87-4c53-b6cb-3fafa1e1b065

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_even_binary_logical_exponent_one
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_even_code_dimension_two
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_labelled_code_carrier_finrank_two


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (k : Nat) :
    Nonempty ((complex S (2*k)).middleCohomology ≃ₗ[Field] Field) ∧
      Module.finrank ℂ (BDL26CSSHamiltonian.labelledCode S (2*k)).carrier = 2 ∧
      (BDL26CSSHamiltonian.labelledCode S (2*k)).dimension = 2 ∧
      Fintype.card (BDL26CSSHamiltonian.Physical S (2*k)) -
        CSSGibbs.checkRank (BDL26CSSHamiltonian.zSyndrome S (2*k)) -
        CSSGibbs.checkRank (BDL26CSSHamiltonian.xSyndrome S (2*k)) = 1 :=
  ⟨⟨BDL26FiniteCohomology.finiteH1Equiv S (2*k)⟩,
    BDL26CSSHamiltonian.labelled_code_carrier_finrank_two S (2*k),
    BDL26CSSHamiltonian.even_code_dimension_two S k,
    BDL26CSSHamiltonian.even_binary_logical_exponent_one S k⟩
end QEC.Coding.BDL26LogicalQubitPreservation
