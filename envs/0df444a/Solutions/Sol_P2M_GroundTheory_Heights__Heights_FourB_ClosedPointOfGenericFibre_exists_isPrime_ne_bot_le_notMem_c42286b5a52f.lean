-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_exists_isPrime_ne_bot_le_notMem_c42286b5a52f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:08:17.339808+00:00
-- url     : https://prove2.me/submissions/5b9611d5-93eb-431a-add0-0d3092091021

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PClosedPointOfGenericFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_lt_edc3bc8cef46

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
open GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
namespace GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (M : Ideal R) [M.IsPrime] (hM : 2 ≤ M.height) (t : R) (ht : t ≠ 0) :
    ∃ P : Ideal R, P.IsPrime ∧ P ≠ ⊥ ∧ P ≤ M ∧ t ∉ P := by
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {t})
  set s := insert (⊥ : Ideal R) hfin.toFinset with hs
  have hprime : ∀ i ∈ s, i ≠ ⊥ → i ≠ ⊥ → (id i).IsPrime := by
    intro i hi h1 _
    rcases Finset.mem_insert.mp hi with h | h
    · exact absurd h h1
    · exact (hfin.mem_toFinset.mp h).1.1
  have hnot : ¬ ((M : Set R) ⊆ ⋃ i ∈ (↑s : Set (Ideal R)), ((id i : Ideal R) : Set R)) := by
    rw [Ideal.subset_union_prime (f := id) ⊥ ⊥ hprime]
    rintro ⟨i, hi, hMi⟩
    rcases Finset.mem_insert.mp hi with h | h
    · subst h
      have h0 : M = ⊥ := le_bot_iff.mp hMi
      rw [h0, Ideal.height_bot] at hM
      exact absurd hM (by decide)
    · have hmin := hfin.mem_toFinset.mp h
      have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ i hmin
      have h3 := hM.trans ((Ideal.height_mono hMi).trans h1)
      exact absurd h3 (by decide)
  obtain ⟨u, huM, hu⟩ := Set.not_subset.mp hnot
  have hu' : ∀ i ∈ s, u ∉ i := fun i hi hui =>
    hu (Set.mem_biUnion (x := i) (by simpa using hi) hui)
  have hu0 : u ≠ 0 := fun h => hu' ⊥ (Finset.mem_insert_self _ _) (by rw [h]; exact Ideal.zero_mem _)
  have huQ : ∀ Q ∈ (Ideal.span {t}).minimalPrimes, u ∉ Q := fun Q hQ =>
    hu' Q (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hQ))
  obtain ⟨P, hP, hPM⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {u}) (J := M)
    ((Ideal.span_singleton_le_iff_mem M).mpr huM)
  have hPp : P.IsPrime := hP.1.1
  have huP : u ∈ P := hP.1.2 (Ideal.mem_span_singleton_self u)
  refine ⟨P, hPp, fun h => hu0 (by rw [h, Ideal.mem_bot] at huP; exact huP), hPM, fun htP => ?_⟩
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {t}) (J := P)
    ((Ideal.span_singleton_le_iff_mem P).mpr htP)
  have hQp : Q.IsPrime := hQ.1.1
  have htQ : t ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self t)
  have hQ0 : Q ≠ ⊥ := fun h => ht (by rw [h, Ideal.mem_bot] at htQ; exact htQ)
  rcases hQP.lt_or_eq with hlt | heq
  · have h2 := two_le_height_of_lt hQ0 hlt
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {u}) P hP
    exact absurd (h2.trans h1) (by decide)
  · exact huQ Q hQ (heq ▸ huP)
end GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
