-- Prove2me | solution 1 for QuantumLTF.Majority.lemma_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:46:55.643193+00:00
-- url     : https://prove2.me/submissions/812d6ec7-9186-4ad2-9b62-fbf82ff4eec2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_intersection_rank_one_posSemidef
import Theorems.Thm_QuantumLTF_Majority_intersection_transform_adversary_identity

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∀ n r : ℕ, 1≤r → r≤n → ∀ p q : Fin (r+1) → ℝ,
    p 0*q 0=1/2 →
    (∀ t : Fin (r+1), 1≤t.1 → t.1<r → (p t=0 ↔ q t≠0)) →
    let W:=intersectionTransform r p q
    let X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ :=
      fun S A B => (2:ℝ)^(-n:ℤ)*W (intersectionIndex A S)*W (intersectionIndex B S)
    DualFeasible (fun A : ExactSupports n r => A.1) X := by
  intro n r hr hrn p q hnorm hsupp
  dsimp only
  constructor
  · intro S
    exact intersection_rank_one_posSemidef n r (intersectionTransform r p q) S
  · exact intersection_transform_adversary_identity n r hr hrn p q hnorm hsupp

