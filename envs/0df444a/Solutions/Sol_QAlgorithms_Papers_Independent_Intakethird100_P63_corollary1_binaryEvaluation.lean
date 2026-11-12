-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P63.corollary1_binaryEvaluation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:46:55.384702+00:00
-- url     : https://prove2.me/submissions/b7a74f0c-e62f-414f-b75d-088477bcddb5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

namespace Aux_P63_binEval
open QAlgorithms.Papers.Independent.Intakethird100.P63

theorem info_eq {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) :
    ∀ t : BinaryTree n, t.Valid → t.information rho = clusterInformation rho t.parties := by
  intro t
  induction t with
  | leaf i =>
    intro _
    simp [BinaryTree.information, BinaryTree.parties, clusterInformation]
  | split l r ihl ihr =>
    intro ht
    obtain ⟨hl, hr, hd⟩ := ht
    simp only [BinaryTree.information, BinaryTree.parties]
    rw [ihl hl, ihr hr]
    unfold clusterInformation clusterMutualInformation
    rw [Finset.sum_union hd]
    ring

end Aux_P63_binEval

open QAlgorithms.Papers.Independent.Intakethird100.P63 in
theorem solution {n : ℕ} (hn : 2 ≤ n)
    (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho)
    (t : BinaryTree n) (ht : t.Valid) (hroot : t.parties = Finset.univ) :
    clusterInformation rho Finset.univ = t.information rho := by
  rw [Aux_P63_binEval.info_eq rho t ht, hroot]

end
