-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P63.eq20_equivalentEqualities
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:30:12.742202+00:00
-- url     : https://prove2.me/submissions/72240dcc-b9fe-4bd4-99b3-2c48723c55e0

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

open scoped ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

open QAlgorithms.Papers.Independent.Intakethird100.P63 in
theorem solution (rho : (Matrix (Fin 3 → ℕ) (Fin 3 → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho) :
    clusterMutualInformation rho {0} {1} = clusterMutualInformation rho {0} {1, 2} ↔
      clusterMutualInformation rho {1} {2} = clusterMutualInformation rho {0, 1} {2} := by
  have h01 : ({0} ∪ {1} : Cluster 3) = {0, 1} := by
    ext x; fin_cases x <;> simp
  have h12 : ({1} ∪ {2} : Cluster 3) = {1, 2} := by
    ext x; fin_cases x <;> simp
  have h3 : ({0} ∪ {1, 2} : Cluster 3) = {0, 1} ∪ {2} := by
    ext x; fin_cases x <;> simp
  unfold clusterMutualInformation
  rw [h01, h12, h3]
  constructor <;> intro h <;> linarith
