-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P63.eq19_pairedExcesses
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:38:39.510195+00:00
-- url     : https://prove2.me/submissions/ab8bdeaa-f190-4ae8-bd5a-c5729c77bd1a

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

open scoped ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

open QAlgorithms.Papers.Independent.Intakethird100.P63 in
theorem solution (rho : (Matrix (Fin 3 → ℕ) (Fin 3 → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho) (p : Equiv.Perm (Fin 3)) :
    clusterMutualInformation rho {p 0} {p 1, p 2} - clusterMutualInformation rho {p 0} {p 1} =
      clusterMutualInformation rho {p 0, p 1} {p 2} - clusterMutualInformation rho {p 1} {p 2} := by
  unfold clusterMutualInformation
  have e1 : ∀ (a : Fin 3) (s : Finset (Fin 3)), ({a} ∪ s) = insert a s :=
    fun a s => (Finset.insert_eq a s).symm
  simp only [e1, Finset.insert_union]
  ring
