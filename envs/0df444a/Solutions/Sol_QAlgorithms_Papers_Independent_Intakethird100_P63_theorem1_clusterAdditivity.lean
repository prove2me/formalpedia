-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P63.theorem1_clusterAdditivity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:11:20.055617+00:00
-- url     : https://prove2.me/submissions/770a280c-2505-44ca-b076-f5d39e02eecc

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

open QAlgorithms.Papers.Independent.Intakethird100.P63 in
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho)
    (P : Finset (Cluster n)) (hP : IsPartition P) :
    clusterInformation rho Finset.univ = amongCorrelation rho P + ∑ C ∈ P, clusterInformation rho C := by
  unfold clusterInformation amongCorrelation
  rw [Finset.sum_sub_distrib]
  have hdisj : (P : Set (Cluster n)).PairwiseDisjoint (fun C => C) :=
    fun C hC D hD hne => hP.2.1 C hC D hD hne
  have hU : P.biUnion (fun C => C) = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    exact hP.2.2 i
  have key : ∑ C ∈ P, ∑ i ∈ C, herbutMarginalEntropy rho {i} =
      ∑ i, herbutMarginalEntropy rho {i} := by
    rw [← hU, Finset.sum_biUnion hdisj]
  rw [key]
  ring

end
