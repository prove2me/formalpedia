-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.tightSets_unionIntersection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:25:07.642219+00:00
-- url     : https://prove2.me/submissions/8f53a661-ed9d-42bb-8cb5-5904d3e3434b

import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_entropyThreshold_supermodular
import Mathlib.Tactic.Linarith

noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    [hD : ∀ i, Nonempty (D i)] {R : Type} [Fintype R] [hR : Nonempty R]
    (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1) (hm : 0 < m) (Q : Fin m → ℝ)
    (hQ : Q ∈ entropyPolyhedron (pureDensity phi)) (K L : Finset (Fin m))
    (hK : (∑ i ∈ K, Q i) = entropyThreshold (pureDensity phi) K)
    (hL : (∑ i ∈ L, Q i) = entropyThreshold (pureDensity phi) L) :
    (∑ i ∈ K ∪ L, Q i) = entropyThreshold (pureDensity phi) (K ∪ L) ∧
    (∑ i ∈ K ∩ L, Q i) = entropyThreshold (pureDensity phi) (K ∩ L) := by
  have hs := entropyThreshold_supermodular phi hphi hm K L
  have hu := hQ (K ∪ L)
  have hi := hQ (K ∩ L)
  have hadd : (∑ i ∈ K ∪ L, Q i) + (∑ i ∈ K ∩ L, Q i) =
      (∑ i ∈ K, Q i) + (∑ i ∈ L, Q i) := Finset.sum_union_inter
  constructor <;> linarith
