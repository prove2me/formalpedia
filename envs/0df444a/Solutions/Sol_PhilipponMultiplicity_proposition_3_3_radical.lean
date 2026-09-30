-- Prove2me | solution 1 for PhilipponMultiplicity.proposition_3_3_radical
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T10:47:34.693678+00:00
-- url     : https://prove2.me/submissions/7979fec7-ac94-484e-a9d5-b080f2b5be4b

import Theorems.Thm_PhilipponMultiplicity_RadicalIntersection_radical_componentSum_cut_le
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_descending_cut_chain
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport RadicalIntersection

/-- The first inequality of Proposition 3.3, strengthened to every open locus
and every infinite field. The finite chain uses the original bounded-degree
equations; only its auxiliary cuts have exact degree D. -/
theorem proposition_3_3_radical {K : Type*} [Field K] [Infinite K]
    (M : MultiProjectiveSpace K)
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (U : MaximalOpenLocus M) :
    componentHilbertSum M (I₀ ⊔ Ideal.span (Set.range P)).radical U D ≤
      componentHilbertSum M I₀.radical U D := by
  let a := idealDimension M I₀
  obtain ⟨J, F, hJ0, hJ, hF, _, hend⟩ := exists_descending_cut_chain M I₀ hI₀ m P D hP
  have hchain (t : ℕ) (ht : t ≤ a) :
      componentHilbertSum M (J t).radical U D ≤ componentHilbertSum M I₀.radical U D := by
    induction t with
    | zero => rw [hJ0]
    | succ t ih =>
      obtain ⟨heq, _, hh, _, _⟩ := hF t (by omega)
      rw [show t + 1 = Nat.succ t from rfl] at heq
      rw [heq]
      exact (radical_componentSum_cut_le M (J t) (hJ t (by omega)).1
        (F t) D hh U).trans (ih (by omega))
  exact (hend U D).trans (hchain a le_rfl)

end PhilipponMultiplicity

end

theorem solution {K : Type*} [Field K] [Infinite K]
    (M : MultiProjectiveSpace K)
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (U : MaximalOpenLocus M) :
    componentHilbertSum M (I₀ ⊔ Ideal.span (Set.range P)).radical U D ≤
      componentHilbertSum M I₀.radical U D := by
  exact PhilipponMultiplicity.proposition_3_3_radical M I₀ hI₀ m P D hP U
