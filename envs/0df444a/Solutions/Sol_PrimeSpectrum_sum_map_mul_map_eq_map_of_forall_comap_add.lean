-- Prove2me | solution 1 for PrimeSpectrum.sum_map_mul_map_eq_map_of_forall_comap_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7c435c01-1558-50d7-8669-bf2fdd607e2e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add

set_option autoImplicit false

p2m_open "PrimeSpectrum P2MW.S_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add.PrimeSpectrum"

namespace PrimeSpectrum
p2m_export "PrimeSpectrum" "asIdeal comap isPrime mem_basicOpen basicOpen_injOn_isIdempotentElem"
p2m_open "PrimeSpectrum"

variable {R : Type*} [CommRing R] {ι : Type*}

private theorem completeOrthogonalIdempotents_unique_of_forall_apply_eq_iff [Fintype ι]
    (f : PrimeSpectrum R → ι) (e e' : ι → R)
    (he : CompleteOrthogonalIdempotents e) (he' : CompleteOrthogonalIdempotents e')
    (hfe : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal)
    (hfe' : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e' i ∉ x.asIdeal) : e = e' := by
  funext i
  apply basicOpen_injOn_isIdempotentElem (he.idem i) (he'.idem i)
  ext x
  simp only [SetLike.mem_coe, mem_basicOpen]
  rw [← hfe i x, ← hfe' i x]

private theorem forall_comp_comap_apply_eq_iff {S : Type*} [CommRing S] (φ : R →+* S)
    (f : PrimeSpectrum R → ι) (e : ι → R)
    (hfe : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal) :
    ∀ (i : ι) (y : PrimeSpectrum S), f (comap φ y) = i ↔ φ (e i) ∉ y.asIdeal :=
  fun i y => by rw [hfe]; rfl

private theorem forall_add_apply_eq_iff [Fintype ι] [AddCommGroup ι]
    (f g : PrimeSpectrum R → ι) (e e' : ι → R)
    (hfe : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal)
    (hge : ∀ (i : ι) (x : PrimeSpectrum R), g x = i ↔ e' i ∉ x.asIdeal) :
    ∀ (k : ι) (x : PrimeSpectrum R), f x + g x = k ↔ (∑ i, e i * e' (k - i)) ∉ x.asIdeal := by
  classical
  intro k x
  have hf : e (f x) ∉ x.asIdeal := (hfe _ x).mp rfl
  have hg : e' (g x) ∉ x.asIdeal := (hge _ x).mp rfl

  have hterm : ∀ i, i ≠ f x → e i * e' (k - i) ∈ x.asIdeal := by
    intro i hi
    have : e i ∈ x.asIdeal := by
      by_contra h
      exact hi ((hfe i x).mpr h).symm
    exact x.asIdeal.mul_mem_right _ this
  have hsplit : (∑ i, e i * e' (k - i)) ∉ x.asIdeal ↔ e (f x) * e' (k - f x) ∉ x.asIdeal := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (f x))]
    have hrest : (∑ i ∈ Finset.univ.erase (f x), e i * e' (k - i)) ∈ x.asIdeal :=
      x.asIdeal.sum_mem fun i hi => hterm i (Finset.ne_of_mem_erase hi)
    constructor
    · intro h hmain
      exact h (x.asIdeal.add_mem hmain hrest)
    · intro h hsum
      exact h (by simpa using x.asIdeal.sub_mem hsum hrest)
  rw [hsplit]
  constructor
  · intro hk
    rw [← hk, add_sub_cancel_left]
    intro hmem
    rcases x.isPrime.mem_or_mem hmem with h | h
    · exact hf h
    · exact hg h
  · intro h
    have h2 : e' (k - f x) ∉ x.asIdeal := fun hm => h (x.asIdeal.mul_mem_left _ hm)
    have : g x = k - f x := (hge _ x).mpr h2
    rw [this, add_sub_cancel]

end PrimeSpectrum

namespace CompleteOrthogonalIdempotents p2m_export "CompleteOrthogonalIdempotents" "map iff_ortho_complete complete" end CompleteOrthogonalIdempotents
namespace CompleteOrthogonalIdempotents
p2m_open_scoped "CompleteOrthogonalIdempotents" in

private theorem _root_.CompleteOrthogonalIdempotents.convolution
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [AddCommGroup ι]
    {e e' : ι → R} (he : CompleteOrthogonalIdempotents e) (he' : CompleteOrthogonalIdempotents e') :
    CompleteOrthogonalIdempotents (fun k => ∑ i, e i * e' (k - i)) := by
  classical
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  constructor
  · intro k l hkl
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      have hne : k - i ≠ l - i := fun h => hkl (sub_left_injective h)
      calc e i * e' (k - i) * (e i * e' (l - i))
          = e i * e i * (e' (k - i) * e' (l - i)) := by ring
        _ = 0 := by rw [he'.ortho hne, mul_zero]
    · calc e i * e' (k - i) * (e j * e' (l - j))
          = e i * e j * (e' (k - i) * e' (l - j)) := by ring
        _ = 0 := by rw [he.ortho hij, zero_mul]
  · rw [Finset.sum_comm]
    have : ∀ i : ι, ∑ k, e i * e' (k - i) = e i := fun i => by
      rw [← Finset.mul_sum]
      have h : ∑ k, e' (k - i) = ∑ k, e' k :=
        Fintype.sum_equiv (Equiv.subRight i) _ _ (fun k => rfl)
      rw [h, he'.complete, mul_one]
    simp_rw [this, he.complete]

end CompleteOrthogonalIdempotents
p2m_export "" "CompleteOrthogonalIdempotents.convolution"
open _root_.PrimeSpectrum _root_.P2MW.S_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add.PrimeSpectrum in

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] {ι : Type*} [Fintype ι] [AddCommGroup ι]
    (φ₁₂ φ₂₃ φ₁₃ : R →+* S) (f : PrimeSpectrum R → ι) (e : ι → R)
    (he : CompleteOrthogonalIdempotents e)
    (hfe : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal)
    (hf : ∀ y : PrimeSpectrum S, f (comap φ₁₂ y) + f (comap φ₂₃ y) = f (comap φ₁₃ y)) :
    ∀ k : ι, ∑ i, φ₁₂ (e i) * φ₂₃ (e (k - i)) = φ₁₃ (e k) := by
  classical

  have h₁₂ : ∀ (i : ι) (y : PrimeSpectrum S), f (comap φ₁₂ y) = i ↔ (φ₁₂ ∘ e) i ∉ y.asIdeal :=
    fun i y => by rw [hfe]; rfl
  have h₂₃ : ∀ (i : ι) (y : PrimeSpectrum S), f (comap φ₂₃ y) = i ↔ (φ₂₃ ∘ e) i ∉ y.asIdeal :=
    fun i y => by rw [hfe]; rfl
  have h₁₃ : ∀ (i : ι) (y : PrimeSpectrum S), f (comap φ₁₃ y) = i ↔ (φ₁₃ ∘ e) i ∉ y.asIdeal :=
    fun i y => by rw [hfe]; rfl
  have hL : ∀ (k : ι) (y : PrimeSpectrum S),
      f (comap φ₁₃ y) = k ↔ (∑ i, (φ₁₂ ∘ e) i * (φ₂₃ ∘ e) (k - i)) ∉ y.asIdeal := by
    intro k y
    rw [← hf y]
    exact PrimeSpectrum.forall_add_apply_eq_iff _ _ _ _ h₁₂ h₂₃ k y
  have key := PrimeSpectrum.completeOrthogonalIdempotents_unique_of_forall_apply_eq_iff
    (fun y => f (comap φ₁₃ y)) _ _ ((he.map φ₁₂).convolution (he.map φ₂₃)) (he.map φ₁₃) hL h₁₃
  intro k
  exact congrFun key k

end S_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add
end P2MW
export P2MW.S_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add (solution)
