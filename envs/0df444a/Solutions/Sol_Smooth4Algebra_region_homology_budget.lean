-- Prove2me | solution 1 for Smooth4Algebra.region_homology_budget
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:23:09.707968+00:00
-- url     : https://prove2.me/submissions/e6ba3d73-d388-4217-ae24-5ae40e8cbccd

import Mathlib
import Definitions.Def_Smooth4AlgebraHomology
set_option autoImplicit false
open scoped BigOperators
theorem solution
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (W : ι → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)]
    (d : V →ₗ[K] V) (h_square : d.comp d = 0)
    (inc : ∀ i, W i →ₗ[K] V) (proj : ∀ i, V →ₗ[K] W i)
    (h_retract : ∀ i, (proj i).comp (inc i) = LinearMap.id)
    (h_distinct : ∀ i j, i ≠ j → (proj i).comp (inc j) = 0)
    (outgoing incoming : ι → ℕ)
    (h_outgoing : ∀ i, Module.finrank K (LinearMap.range (d.comp (inc i))) ≤ outgoing i)
    (h_incoming : ∀ i, Module.finrank K (LinearMap.range ((proj i).comp d)) ≤ incoming i) :
    (∑ i, (Module.finrank K (W i) - outgoing i - incoming i)) ≤
      Module.finrank K (Smooth4Algebra.Homology d) := by
  classical
  let Z (i : ι) : Submodule K (W i) := LinearMap.ker (d.comp (inc i))
  let B (i : ι) : Submodule K (W i) := LinearMap.range ((proj i).comp d)
  let C (i : ι) : Submodule K (Z i) := (B i).comap (Z i).subtype
  choose T hT using fun i => Submodule.exists_isCompl (C i)
  have hdim (i : ι) :
      Module.finrank K (W i) - outgoing i - incoming i ≤ Module.finrank K (T i) := by
    have hz := (d.comp (inc i)).finrank_range_add_finrank_ker
    have ht := Submodule.finrank_add_eq_of_isCompl (hT i)
    let bmap : C i →ₗ[K] B i :=
      ((Z i).subtype.comp (C i).subtype).codRestrict (B i) (fun x => x.property)
    have hbinj : Function.Injective bmap := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : B i => (z : W i)) h
    have hb := LinearMap.finrank_le_finrank_of_injective hbinj
    have ho := h_outgoing i
    have hi := h_incoming i
    change Module.finrank K (LinearMap.range (d.comp (inc i))) + Module.finrank K (Z i) = Module.finrank K (W i) at hz
    change Module.finrank K (B i) ≤ incoming i at hi
    omega
  let u : (∀ i, T i) →ₗ[K] V :=
    { toFun := fun x => ∑ i, inc i ((x i).val.val)
      map_add' := by intro x y; simp [Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum] }
  have huproj (x : ∀ i, T i) (i : ι) : proj i (u x) = (x i).val.val := by
    change proj i (∑ j, inc j ((x j).val.val)) = _
    rw [map_sum, Finset.sum_eq_single i]
    · exact LinearMap.congr_fun (h_retract i) _
    · intro j hj hji
      have h := LinearMap.congr_fun (h_distinct i j hji.symm) ((x j).val.val)
      simpa using h
    · simp
  have hucycles (x : ∀ i, T i) : u x ∈ LinearMap.ker d := by
    change d (∑ i, inc i ((x i).val.val)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    exact (x i).val.property
  let z : (∀ i, T i) →ₗ[K] LinearMap.ker d := u.codRestrict (LinearMap.ker d) hucycles
  let H : (∀ i, T i) →ₗ[K] Smooth4Algebra.Homology d :=
    (Smooth4Algebra.boundariesInCycles d).mkQ.comp z
  have hH : Function.Injective H := by
    apply (injective_iff_map_eq_zero H).mpr
    intro x hx
    have hxB : z x ∈ Smooth4Algebra.boundariesInCycles d := by
      change (Smooth4Algebra.boundariesInCycles d).mkQ (z x) = 0 at hx
      simpa using hx
    have hxrange : u x ∈ LinearMap.range d := hxB
    obtain ⟨v, hv⟩ := hxrange
    funext i
    have hxi : (x i).val ∈ C i := by
      change (x i).val.val ∈ LinearMap.range ((proj i).comp d)
      refine ⟨v, ?_⟩
      change proj i (d v) = (x i).val.val
      rw [hv, huproj]
    exact (Submodule.mem_left_iff_eq_zero_of_disjoint (hT i).disjoint).mp hxi
  have hle := LinearMap.finrank_le_finrank_of_injective hH
  rw [Module.finrank_pi_fintype] at hle
  exact le_trans (Finset.sum_le_sum fun i hi => hdim i) hle

#print axioms solution
