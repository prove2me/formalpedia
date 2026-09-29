-- Prove2me | solution 1 for PrimeSpectrum.exists_completeOrthogonalIdempotents_forall_apply_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1b96a175-65f6-5084-862e-7e914a7514ba

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PrimeSpectrum_exists_completeOrthogonalIdempotents_forall_apply_eq_iff

set_option autoImplicit false

open PrimeSpectrum

theorem solution
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (f : LocallyConstant (PrimeSpectrum R) ι) :
    ∃ e : ι → R, CompleteOrthogonalIdempotents e ∧
      ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal := by
  classical

  have hfib : ∀ i : ι, ∃ e : R, IsIdempotentElem e ∧ {x | f x = i} = (basicOpen e : Set (PrimeSpectrum R)) :=
    fun i => exists_idempotent_basicOpen_eq_of_isClopen (f.isLocallyConstant.isClopen_fiber i)
  choose e he hfe using hfib
  have hmem : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal := fun i x => by
    have := congrArg (x ∈ ·) (hfe i)
    simpa using this

  have hortho : Pairwise (fun i j => e i * e j = 0) := by
    intro i j hij
    have hnil : IsNilpotent (e i * e j) := by
      rw [← basicOpen_eq_bot_iff]
      ext x
      simp only [basicOpen_mul, TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
        mem_basicOpen, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
      intro hi hj
      exact hij (((hmem i x).mpr hi).symm.trans ((hmem j x).mpr hj))
    exact ((he i).mul (he j)).eq_zero_of_isNilpotent hnil
  have hoi : OrthogonalIdempotents e := ⟨he, hortho⟩

  have hsum : IsIdempotentElem (∑ i, e i) := hoi.isIdempotentElem_sum
  have hcov : ∀ x : PrimeSpectrum R, (∑ i, e i) ∉ x.asIdeal := by
    intro x hx
    have hi : e (f x) ∉ x.asIdeal := (hmem (f x) x).mp rfl
    apply hi

    have : e (f x) * ∑ i, e i = e (f x) := by
      rw [Finset.mul_sum, Finset.sum_eq_single (f x) (fun j _ hj => hoi.ortho (Ne.symm hj)) (by simp),
        (he _).eq]
    rw [← this]
    exact x.asIdeal.mul_mem_left _ hx
  have hcompl : IsNilpotent (1 - ∑ i, e i) := by
    rw [← basicOpen_eq_bot_iff]
    ext x
    simp only [SetLike.mem_coe, mem_basicOpen, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false,
      iff_false, not_not]

    have h0 : (∑ i, e i) * (1 - ∑ i, e i) = 0 := by rw [mul_sub, mul_one, hsum.eq, sub_self]
    rcases x.isPrime.mem_or_mem (h0 ▸ x.asIdeal.zero_mem : (∑ i, e i) * (1 - ∑ i, e i) ∈ x.asIdeal) with h | h
    · exact absurd h (hcov x)
    · exact h
  have hone : ∑ i, e i = 1 := by
    have := hsum.one_sub.eq_zero_of_isNilpotent hcompl
    exact (sub_eq_zero.mp this).symm
  exact ⟨e, ⟨hoi, hone⟩, hmem⟩

end S_PrimeSpectrum_exists_completeOrthogonalIdempotents_forall_apply_eq_iff
end P2MW
export P2MW.S_PrimeSpectrum_exists_completeOrthogonalIdempotents_forall_apply_eq_iff (solution)
