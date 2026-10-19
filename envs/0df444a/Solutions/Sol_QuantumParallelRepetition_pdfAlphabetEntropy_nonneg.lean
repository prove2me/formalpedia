-- Prove2me | solution 1 for QuantumParallelRepetition.pdfAlphabetEntropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/556bc3d9-f468-4c13-8120-fe4b2f32f2f3

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {A B : Type} [Fintype A] [Fintype B]
    (alice : Nonempty A) (bob : Nonempty B) :
    0 ≤ Real.log
      ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := by
  have alice_card : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr alice
  have bob_card : 0 < Fintype.card B :=
    Fintype.card_pos_iff.mpr bob
  have alice_real : (1 : ℝ) ≤ (Fintype.card A : ℝ) := by
    exact_mod_cast alice_card
  have bob_real : (1 : ℝ) ≤ (Fintype.card B : ℝ) := by
    exact_mod_cast bob_card
  apply Real.log_nonneg
  nlinarith [mul_nonneg (sub_nonneg.mpr alice_real)
    (sub_nonneg.mpr bob_real)]
end QuantumParallelRepetition
