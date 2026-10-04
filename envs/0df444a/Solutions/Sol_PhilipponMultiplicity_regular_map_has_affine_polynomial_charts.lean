-- Prove2me | solution 1 for PhilipponMultiplicity.regular_map_has_affine_polynomial_charts
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T17:11:13.842705+00:00
-- url     : https://prove2.me/submissions/41cf74fc-3f24-4624-b395-500946e7e732

import Theorems.Thm_PhilipponMultiplicity_regular_map_has_affine_rational_charts
import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib

section
-- Included implementation: Solutions.PhilipponAffineClosedPoints

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints

open MvPolynomial
open Topology

variable {K : Type*} [Field K] {σ τ : Type*}

/-- The ordinary Zariski topology on an affine algebraic zero set, induced by its
evaluation ideals in the polynomial prime spectrum. -/
@[instance_reducible] def locusTopology (I : Ideal (MvPolynomial σ K)) :
    TopologicalSpace (zeroLocus K I) :=
  TopologicalSpace.induced (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
    inferInstance

theorem nonzero_sets_basis (I : Ideal (MvPolynomial σ K)) :
    letI := locusTopology I
    TopologicalSpace.IsTopologicalBasis
      (Set.range (fun P : MvPolynomial σ K => {x : zeroLocus K I | aeval x.val P ≠ 0})) := by
  let _ := locusTopology I
  have hb := PrimeSpectrum.isTopologicalBasis_basic_opens.induced
    (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
  have hpre (P : MvPolynomial σ K) :
      (fun x : zeroLocus K I => pointToPoint (k := K) x.val) ⁻¹'
        (PrimeSpectrum.basicOpen P : Set (PrimeSpectrum (MvPolynomial σ K))) =
      {x : zeroLocus K I | aeval x.val P ≠ 0} := by
    ext x
    change (P ∉ vanishingIdeal K {x.val}) ↔ aeval x.val P ≠ 0
    rw [mem_vanishingIdeal_singleton_iff]
  simpa only [← Set.range_comp, Function.comp_def, hpre] using hb

end PhilipponMultiplicity.AffineClosedPoints
end
end

section
-- Included implementation: Solutions.PhilipponAffineRegularFunctions

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace PhilipponMultiplicity.AffineRegularFunctions
open MvPolynomial

variable {K σ X : Type*} [Field K]

/-- Polynomials whose product with a given function is a polynomial function. -/
def clearingIdeal (a : X → σ → K) (f : X → K) : Ideal (MvPolynomial σ K) where
  carrier := {P | ∃ Q : MvPolynomial σ K, ∀ x, f x * aeval (a x) P = aeval (a x) Q}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro P Q ⟨P', hP⟩ ⟨Q', hQ⟩
    refine ⟨P' + Q', ?_⟩
    intro x
    simp only [map_add, mul_add, hP x, hQ x]
  smul_mem' := by
    rintro P Q ⟨Q', hQ⟩
    refine ⟨P * Q', ?_⟩
    intro x
    simp only [smul_eq_mul, map_mul]
    calc
      f x * (aeval (a x) P * aeval (a x) Q) =
          aeval (a x) P * (f x * aeval (a x) Q) := by ring
      _ = aeval (a x) P * aeval (a x) Q' := by rw [hQ x]

theorem ideal_le_clearingIdeal (J : Ideal (MvPolynomial σ K))
    (a : X → zeroLocus K J) (f : X → K) :
    J ≤ clearingIdeal (fun x => (a x).val) f := by
  intro P hP
  refine ⟨0, ?_⟩
  intro x
  rw [(a x).property P hP, mul_zero, map_zero]

theorem local_fraction_clears [TopologicalSpace X]
    (J : Ideal (MvPolynomial σ K))
    (a : @Homeomorph X (zeroLocus K J) _ (AffineClosedPoints.locusTopology J))
    (f : X → K) (x : X)
    (hloc : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ P Q : MvPolynomial σ K, ∀ z ∈ U,
        aeval (a z).val Q ≠ 0 ∧ f z = aeval (a z).val P / aeval (a z).val Q) :
    ∃ H ∈ clearingIdeal (fun z => (a z).val) f, aeval (a x).val H ≠ 0 := by
  let _ := AffineClosedPoints.locusTopology J
  obtain ⟨U, hU, hx, P, Q, hPQ⟩ := hloc
  have hopen : IsOpen (a.symm ⁻¹' U) := hU.preimage a.symm.continuous
  have hmem : a x ∈ a.symm ⁻¹' U := by simpa using hx
  obtain ⟨W, ⟨H, rfl⟩, hHx, hHU⟩ :=
    (AffineClosedPoints.nonzero_sets_basis J).isOpen_iff.mp hopen (a x) hmem
  have hin (z : X) (hz : aeval (a z).val H ≠ 0) : z ∈ U := by
    have h := hHU hz
    simpa using h
  refine ⟨H * Q, ⟨H * P, ?_⟩, ?_⟩
  · intro z
    simp only [map_mul]
    by_cases hHz : aeval (a z).val H = 0
    · simp [hHz]
    · obtain ⟨hQ, hf⟩ := hPQ z (hin z hHz)
      have heq := (eq_div_iff hQ).mp hf
      calc
        f z * (aeval (a z).val H * aeval (a z).val Q) =
            aeval (a z).val H * (f z * aeval (a z).val Q) := by ring
        _ = aeval (a z).val H * aeval (a z).val P := by rw [heq]
  · rw [map_mul]
    exact mul_ne_zero hHx (hPQ x hx).1

/-- An ideal containing the equations of a zero set and avoiding every point of
that zero set is the unit ideal. -/
theorem eq_top_of_no_zero [IsAlgClosed K] [Finite σ]
    (J D : Ideal (MvPolynomial σ K)) (hJD : J ≤ D)
    (hnz : ∀ x : zeroLocus K J, ∃ P ∈ D, aeval x.val P ≠ 0) : D = ⊤ := by
  have hempty : zeroLocus K D = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxJ : x ∈ zeroLocus K J := zeroLocus_anti_mono hJD hx
    obtain ⟨P, hP, hnP⟩ := hnz ⟨x, hxJ⟩
    exact hnP (hx P hP)
  apply Ideal.radical_eq_top.mp
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), hempty, vanishingIdeal_empty]

/-- Every locally rational function on an affine algebraic set is polynomial. -/
theorem locally_rational_is_polynomial [IsAlgClosed K] [Finite σ] [TopologicalSpace X]
    (J : Ideal (MvPolynomial σ K))
    (a : @Homeomorph X (zeroLocus K J) _ (AffineClosedPoints.locusTopology J))
    (f : X → K)
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ P Q : MvPolynomial σ K, ∀ z ∈ U,
        aeval (a z).val Q ≠ 0 ∧ f z = aeval (a z).val P / aeval (a z).val Q) :
    ∃ P : MvPolynomial σ K, ∀ x, f x = aeval (a x).val P := by
  let _ := AffineClosedPoints.locusTopology J
  have hD : clearingIdeal (fun z => (a z).val) f = ⊤ := by
    apply eq_top_of_no_zero J _ (ideal_le_clearingIdeal J a f)
    intro y
    obtain ⟨P, hP, hnP⟩ := local_fraction_clears J a f (a.symm y) (hloc _)
    exact ⟨P, hP, by simpa using hnP⟩
  have hone : (1 : MvPolynomial σ K) ∈ clearingIdeal (fun z => (a z).val) f := by
    rw [hD]
    trivial
  obtain ⟨P, hP⟩ := hone
  exact ⟨P, fun x => by simpa using hP x⟩

end PhilipponMultiplicity.AffineRegularFunctions

end
end

section
-- Included implementation: Solutions.PhilipponRationalChartsReduction

set_option autoImplicit false
noncomputable section
namespace PhilipponMultiplicity.AffineRegularFunctions
universe u

theorem polynomial_charts_of_rational_charts
    (K : Type u) [Field K] [IsAlgClosed K]
    (M N : MultiProjectiveSpace K) (X Y : Type u)
    (e : X → M.Point) (j : Y → N.Point) (f : X → Y) (x : X)
    (hcharts :
      letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
      letI : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
      ∃ (S : Set X) (T : Set Y), IsOpen S ∧ x ∈ S ∧ IsOpen T ∧
        ∃ hST : Set.MapsTo f S T,
        ∃ (m n : ℕ) (I : Ideal (MvPolynomial (Fin m) K))
          (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
        ∃ (a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
            (AffineClosedPoints.locusTopology J))
          (b : @Homeomorph T (MvPolynomial.zeroLocus K I) inferInstance
            (AffineClosedPoints.locusTopology I)),
          ∀ (z : S) (i : Fin m), ∃ U : Set S, IsOpen U ∧ z ∈ U ∧
            ∃ P Q : MvPolynomial (Fin n) K, ∀ w ∈ U,
              MvPolynomial.aeval (a w).val Q ≠ 0 ∧
              (b ⟨f w.val, hST w.property⟩).val i =
                MvPolynomial.aeval (a w).val P / MvPolynomial.aeval (a w).val Q) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    letI : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
    ∃ (S : Set X) (T : Set Y), IsOpen S ∧ x ∈ S ∧ IsOpen T ∧
      ∃ hST : Set.MapsTo f S T,
      ∃ (m n : ℕ) (I : Ideal (MvPolynomial (Fin m) K))
        (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
      ∃ (a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
          (AffineClosedPoints.locusTopology J))
        (b : @Homeomorph T (MvPolynomial.zeroLocus K I) inferInstance
          (AffineClosedPoints.locusTopology I))
        (P : Fin m → MvPolynomial (Fin n) K),
        ∀ (z : S) (i : Fin m),
          (b ⟨f z.val, hST z.property⟩).val i = MvPolynomial.aeval (a z).val (P i) := by
  let _ : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  let _ : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
  obtain ⟨S, T, hS, hx, hT, hST, m, n, I, J, hJ, a, b, hloc⟩ := hcharts
  have hpoly (i : Fin m) : ∃ P : MvPolynomial (Fin n) K, ∀ z : S,
      (b ⟨f z.val, hST z.property⟩).val i = MvPolynomial.aeval (a z).val P :=
    locally_rational_is_polynomial J a (fun z => (b ⟨f z.val, hST z.property⟩).val i)
      (fun z => hloc z i)
  choose P hP using hpoly
  exact ⟨S, T, hS, hx, hT, hST, m, n, I, J, hJ, a, b, P, fun z i => hP i z⟩

end PhilipponMultiplicity.AffineRegularFunctions

end
end

open PhilipponMultiplicity
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K]
    (M N : MultiProjectiveSpace K) (X Y : Type u)
    (e : X → M.Point) (j : Y → N.Point) (f : X → Y)
    (he : Function.Injective e) (hj : Function.Injective j)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (hY : @IsLocallyClosed _ N.zariskiTopology (Set.range j))
    (hf : M.IsRegularAlong N e (j ∘ f)) (x : X) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    letI : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
    ∃ (S : Set X) (T : Set Y), IsOpen S ∧ x ∈ S ∧ IsOpen T ∧
      ∃ hST : Set.MapsTo f S T,
      ∃ (m n : ℕ) (I : Ideal (MvPolynomial (Fin m) K))
        (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
      ∃ (a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance))
        (b : @Homeomorph T (MvPolynomial.zeroLocus K I) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K I => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance))
        (P : Fin m → MvPolynomial (Fin n) K),
        ∀ (z : S) (i : Fin m),
          (b ⟨f z.val, hST z.property⟩).val i = MvPolynomial.aeval (a z).val (P i) := by
  exact AffineRegularFunctions.polynomial_charts_of_rational_charts K M N X Y e j f x
    (regular_map_has_affine_rational_charts K M N X Y e j f he hj hX hY hf x)
