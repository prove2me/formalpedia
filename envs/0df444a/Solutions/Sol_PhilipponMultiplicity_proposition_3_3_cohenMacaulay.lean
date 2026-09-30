-- Prove2me | solution 1 for PhilipponMultiplicity.proposition_3_3_cohenMacaulay
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T12:16:42.768845+00:00
-- url     : https://prove2.me/submissions/14177830-72ff-4cdd-abb9-53be326d1c17

import Definitions.Def_PhilipponMultiplicity_CutLocus
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_cutLocus_step
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_cut_le_on_cutLocus
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_descending_cut_chain
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_le_of_discarded_zero
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Pointwise
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem cutLocus_le (J I : Ideal M.CoordinateRing) (U : MaximalOpenLocus M) :
    cutLocus M J I U ≤ U := inf_le_left.trans inf_le_left

theorem homogeneous_sup_equations (I₀ : Ideal M.CoordinateRing)
    (hI₀ : IsMultihomogeneousIdeal M I₀) (m : ℕ) (P : Fin m → M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    IsMultihomogeneousIdeal M (I₀ ⊔ Ideal.span (Set.range P)) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hIg : I₀.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I₀
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI₀ f hf d
  have hPg : (Ideal.span (Set.range P)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    rintro f ⟨j, rfl⟩
    obtain ⟨d, _, hd⟩ := hP j
    exact ⟨d, hd⟩
  intro f hf d
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d


end PhilipponMultiplicity.SectionThreeSupport

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K)

/-- All of the remaining induction is proved from the one-cut numerical
comparison. CM is propagated on the actual changing loci, not assumed for
the whole original open set at each intermediate ideal. -/
theorem componentSum_le_of_cutLocus_cut_bound
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (U : MaximalOpenLocus M) (hCM : IsLocallyCohenMacaulayOn M I₀ U)
    (hcut : ∀ J : Ideal M.CoordinateRing,
      IsMultihomogeneousIdeal M J → J ≤ I₀ ⊔ Ideal.span (Set.range P) →
      ∀ F : M.CoordinateRing, M.IsHomogeneous F D → F ∈ I₀ ⊔ Ideal.span (Set.range P) →
      (∀ q ∈ J.minimalPrimes,
        Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
        q ∉ associatedPrimes M.CoordinateRing
          (M.CoordinateRing ⧸ (I₀ ⊔ Ideal.span (Set.range P))) → F ∉ q) →
      IsLocallyCohenMacaulayOn M J (cutLocus M J (I₀ ⊔ Ideal.span (Set.range P)) U) →
      componentHilbertSum M (J ⊔ Ideal.span {F}) U D ≤ componentHilbertSum M J U D) :
    componentHilbertSum M (I₀ ⊔ Ideal.span (Set.range P)) U D ≤
      componentHilbertSum M I₀ U D := by
  let I := I₀ ⊔ Ideal.span (Set.range P)
  let a := idealDimension M I₀
  obtain ⟨J, F, hJ0, hJ, hF, _, _⟩ := exists_descending_cut_chain M I₀ hI₀ m P D hP
  have hstages (t : ℕ) (ht : t ≤ a) :
      IsLocallyCohenMacaulayOn M (J t) (cutLocus M (J t) I U) ∧
      componentHilbertSum M (J t) U D ≤ componentHilbertSum M I₀ U D := by
    induction t with
    | zero =>
      rw [hJ0]
      exact ⟨fun n hn => hCM n (cutLocus_le M I₀ I U hn), le_rfl⟩
    | succ t ih =>
      obtain ⟨hcurrent, hbound⟩ := ih (by omega)
      obtain ⟨hJh, _, hJI, _, _⟩ := hJ t (by omega)
      obtain ⟨hstep, hFin, hFh, hFavoid, hFreg⟩ := hF t (by omega)
      have hFI : F t ∈ I := (le_sup_right : Ideal.span (Set.range P) ≤ I) hFin
      have hnext := (cutLocus_step M (J t) I hJh hJI (F t) hFI U hcurrent hFreg).2.2.1
      rw [show t + 1 = t.succ from rfl] at hstep
      rw [hstep]
      exact ⟨hnext, (hcut (J t) hJh hJI (F t) hFh hFI hFavoid hcurrent).trans hbound⟩
  have hterminal := componentSum_le_of_discarded_zero M (J a) I (hJ a le_rfl).1
    (homogeneous_sup_equations M I₀ hI₀ m P D hP) (hJ a le_rfl).2.2.1
    (by simpa only [a, I, Nat.sub_self] using (hJ a le_rfl).2.2.2.1) U D
  exact hterminal.trans (hstages a le_rfl).2

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (U : MaximalOpenLocus M) (hCM : IsLocallyCohenMacaulayOn M I₀ U) :
    componentHilbertSum M (I₀ ⊔ Ideal.span (Set.range P)) U D ≤
      componentHilbertSum M I₀ U D := by
  apply componentSum_le_of_cutLocus_cut_bound M I₀ hI₀ m P D hP U hCM
  intro J hJ hJI F hF hFI havoid hcurrent
  exact componentSum_cut_le_on_cutLocus M J (I₀ ⊔ Ideal.span (Set.range P))
    hJ hJI F D hF hFI U hcurrent havoid
