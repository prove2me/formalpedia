-- Prove2me | solution 1 for PrimeSpectrum.exists_locallyConstant_forall_apply_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c8010ac9-a947-5e65-9d57-c6c9ff578f61

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PrimeSpectrum_exists_locallyConstant_forall_apply_eq_iff

set_option autoImplicit false

open PrimeSpectrum

theorem solution
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (e : ι → R) (he : CompleteOrthogonalIdempotents e) :
    ∃ f : LocallyConstant (PrimeSpectrum R) ι,
      ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal := by
  classical

  have hex : ∀ x : PrimeSpectrum R, ∃ i, e i ∉ x.asIdeal := by
    intro x
    by_contra! h
    have : (∑ i, e i) ∈ x.asIdeal := x.asIdeal.sum_mem fun i _ => h i
    rw [he.complete] at this
    exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have huniq : ∀ (x : PrimeSpectrum R) (i j : ι), e i ∉ x.asIdeal → e j ∉ x.asIdeal → i = j := by
    intro x i j hi hj
    by_contra hij
    have : e i * e j ∈ x.asIdeal := by rw [he.ortho hij]; exact x.asIdeal.zero_mem
    rcases x.isPrime.mem_or_mem this with h | h
    · exact hi h
    · exact hj h
  choose g hg using hex
  have hchar : ∀ (i : ι) (x : PrimeSpectrum R), g x = i ↔ e i ∉ x.asIdeal :=
    fun i x => ⟨fun h => h ▸ hg x, fun h => huniq x _ _ (hg x) h⟩
  refine ⟨⟨g, ?_⟩, hchar⟩

  refine (IsLocallyConstant.iff_isOpen_fiber).mpr fun i => ?_
  have : g ⁻¹' {i} = (basicOpen (e i) : Set (PrimeSpectrum R)) := by
    ext x; simpa using hchar i x
  rw [this]
  exact (basicOpen (e i)).isOpen

end S_PrimeSpectrum_exists_locallyConstant_forall_apply_eq_iff
end P2MW
export P2MW.S_PrimeSpectrum_exists_locallyConstant_forall_apply_eq_iff (solution)
