-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_IncidenceNull_proof_16442ed8c79d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:48.112854+00:00
-- url     : https://prove2.me/submissions/d72507c6-1078-48ef-a899-bf434810d539

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PIncidenceNull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Vertical
namespace IncidenceNull
theorem _root_.solution : IncidenceNull.Statement := by
  intro F _ n k I f hf
  have hvan : ∀ j : Fin n, rename Sum.inr f * X (Sum.inl j) ∈
      MvPolynomial.vanishingIdeal F
        (MvPolynomial.zeroLocus (AlgebraicClosure F) (incIdeal I k)) := by
    intro j z hz
    have hI : ∀ g ∈ I, aeval (z ∘ Sum.inl) g = 0 := by
      intro g hg
      have hmem : rename Sum.inl g ∈ incIdeal I k :=
        Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg)
      have h := hz _ hmem
      rwa [aeval_rename] at h
    have hlin : ∀ i : Fin k, ∑ j, (z ∘ Sum.inr) (i, j) * (z ∘ Sum.inl) j = 0 := by
      intro i
      have hmem : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) :
          MvPolynomial (Fin n ⊕ (Fin k × Fin n)) F) ∈ incIdeal I k :=
        Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
      have h := hz _ hmem
      simpa using h
    rw [map_mul, aeval_rename, aeval_X]
    by_cases hx : z ∘ Sum.inl = 0
    · have h0 : z (Sum.inl j) = 0 := congrFun hx j
      rw [h0, mul_zero]
    · have hu : z ∘ Sum.inr ∈ incidence I k := ⟨z ∘ Sum.inl, hx, hI, hlin⟩
      rw [(hf.2 f).2 dvd_rfl _ hu, zero_mul]
  have hrad : ∀ j : Fin n, ∃ m, (rename Sum.inr f * X (Sum.inl j)) ^ m ∈ incIdeal I k := by
    intro j
    have h := hvan j
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at h
    exact h
  choose m hm using hrad
  exact ⟨Finset.univ.sup m, fun j =>
    Ideal.pow_mem_of_pow_mem _ (hm j) (Finset.le_sup (Finset.mem_univ j))⟩
end IncidenceNull
end GroundTheory.Heights₂.Heights.Vertical
