-- Prove2me | solution 1 for PhilipponMultiplicity.regular_map_has_affine_closed_point_charts
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T16:09:09.540986+00:00
-- url     : https://prove2.me/submissions/e16dec57-70a9-4287-9c71-575f7ab22111

import Theorems.Thm_PhilipponMultiplicity_regular_map_has_affine_polynomial_charts
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

def evaluation (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    (MvPolynomial σ K ⧸ I) →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (aeval x.val) x.property

@[simp] theorem evaluation_mk (I : Ideal (MvPolynomial σ K))
    (x : zeroLocus K I) (P : MvPolynomial σ K) :
    evaluation I x (Ideal.Quotient.mk I P) = aeval x.val P := rfl

theorem evaluation_surjective (I : Ideal (MvPolynomial σ K))
    (x : zeroLocus K I) : Function.Surjective (evaluation I x) := by
  intro c
  exact ⟨Ideal.Quotient.mk I (C c), by simp⟩

def point (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    MaximalSpectrum (MvPolynomial σ K ⧸ I) :=
  ⟨RingHom.ker (evaluation I x).toRingHom,
    RingHom.ker_isMaximal_of_surjective _ (evaluation_surjective I x)⟩

theorem comap_point (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    Ideal.comap (Ideal.Quotient.mk I) (point I x).asIdeal =
      vanishingIdeal K {x.val} := by
  ext P
  change evaluation I x (Ideal.Quotient.mk I P) = 0 ↔
    P ∈ vanishingIdeal K {x.val}
  rw [evaluation_mk, mem_vanishingIdeal_singleton_iff]

theorem point_injective (I : Ideal (MvPolynomial σ K)) :
    Function.Injective (point I) := by
  intro x y h
  have heq : vanishingIdeal K {x.val} = vanishingIdeal K {y.val} := by
    rw [← comap_point I x, ← comap_point I y, h]
  apply Subtype.ext
  funext i
  have hx : X i - C (x.val i) ∈ vanishingIdeal K {x.val} := by
    simp
  rw [heq, mem_vanishingIdeal_singleton_iff] at hx
  simpa using (sub_eq_zero.mp (by simpa using hx)).symm

theorem point_surjective [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) : Function.Surjective (point I) := by
  intro m
  let q := Ideal.Quotient.mk I
  have hm : (Ideal.comap q m.asIdeal).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective q Ideal.Quotient.mk_surjective
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hm
  have hIx : x ∈ zeroLocus K I := by
    intro P hP
    have hmem : P ∈ Ideal.comap q m.asIdeal := by
      change Ideal.Quotient.mk I P ∈ m.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hP]
      exact m.asIdeal.zero_mem
    rw [hx, mem_vanishingIdeal_singleton_iff] at hmem
    exact hmem
  refine ⟨⟨x, hIx⟩, ?_⟩
  apply MaximalSpectrum.ext
  apply Ideal.comap_injective_of_surjective q Ideal.Quotient.mk_surjective
  exact (comap_point I ⟨x, hIx⟩).trans hx.symm

theorem point_isInducing (I : Ideal (MvPolynomial σ K)) :
    letI := locusTopology I
    IsInducing (point I) := by
  let _ := locusTopology I
  have hq : IsInducing (fun m : MaximalSpectrum (MvPolynomial σ K ⧸ I) =>
      PrimeSpectrum.comap (Ideal.Quotient.mk I) m.toPrimeSpectrum) :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isInducing.comp ⟨rfl⟩
  apply hq.of_comp_iff.mp
  have heq : (fun x : zeroLocus K I =>
      PrimeSpectrum.comap (Ideal.Quotient.mk I) (point I x).toPrimeSpectrum) =
      (fun x => pointToPoint (k := K) x.val) := by
    funext x
    exact PrimeSpectrum.ext (comap_point I x)
  change IsInducing (fun x : zeroLocus K I =>
    PrimeSpectrum.comap (Ideal.Quotient.mk I) (point I x).toPrimeSpectrum)
  rw [heq]
  exact ⟨rfl⟩

def homeomorph [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) :
    letI := locusTopology I
    zeroLocus K I ≃ₜ MaximalSpectrum (MvPolynomial σ K ⧸ I) := by
  letI := locusTopology I
  exact (Equiv.ofBijective (point I) ⟨point_injective I, point_surjective I⟩).toHomeomorphOfIsInducing
    (point_isInducing I)

@[simp] theorem homeomorph_apply [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    homeomorph I x = point I x := rfl

/-- Polynomial substitution commutes with evaluation. -/
theorem evaluate_substitution (P : τ → MvPolynomial σ K) (x : σ → K)
    (F : MvPolynomial τ K) :
    aeval x (aeval P F) = aeval (fun i => aeval x (P i)) F := by
  have h : (aeval x).comp (aeval P) = aeval (fun i => aeval x (P i)) := by
    ext i
    simp
  exact DFunLike.congr_fun h F

/-- On a reduced source zero set, preservation of points implies preservation
of the defining ideal. -/
theorem substitution_mem [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i))
    (F : MvPolynomial τ K) (hF : F ∈ I) : aeval P F ∈ J := by
  have hvan : aeval P F ∈ vanishingIdeal K (zeroLocus K J) := by
    intro x hx
    rw [evaluate_substitution]
    have heq : (fun i => aeval x (P i)) = (g ⟨x, hx⟩).val :=
      funext (fun i => (hg ⟨x, hx⟩ i).symm)
    rw [heq]
    exact (g ⟨x, hx⟩).property F hF
  rwa [vanishingIdeal_zeroLocus_eq_radical, hJ.radical] at hvan

def quotientMap [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i)) :
    (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J) :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ K J).comp (aeval P)) (by
    intro F hF
    change Ideal.Quotient.mk J (aeval P F) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (substitution_mem I J hJ g P hg F hF))

@[simp] theorem quotientMap_mk [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i)) (F : MvPolynomial τ K) :
    quotientMap I J hJ g P hg (Ideal.Quotient.mk I F) =
      Ideal.Quotient.mk J (aeval P F) := rfl

theorem point_map_compatibility [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i)) (x : zeroLocus K J) :
    (point I (g x)).asIdeal =
      Ideal.comap (quotientMap I J hJ g P hg).toRingHom (point J x).asIdeal := by
  ext q
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective q
  change evaluation I (g x) (Ideal.Quotient.mk I F) = 0 ↔
    evaluation J x (quotientMap I J hJ g P hg (Ideal.Quotient.mk I F)) = 0
  rw [evaluation_mk, quotientMap_mk, evaluation_mk, evaluate_substitution]
  have heq : (fun i => aeval x.val (P i)) = (g x).val :=
    funext (fun i => (hg x i).symm)
  rw [heq]

/-- Polynomial coordinate charts give compatible maximal-spectrum charts. -/
theorem charts_of_polynomial_charts [IsAlgClosed K] [Finite σ] [Finite τ]
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (f : S → T) (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical)
    (a : @Homeomorph S (zeroLocus K J) _ (locusTopology J))
    (b : @Homeomorph T (zeroLocus K I) _ (locusTopology I))
    (P : τ → MvPolynomial σ K)
    (hf : ∀ z i, (b (f z)).val i = aeval (a z).val (P i)) :
    ∃ (a' : S ≃ₜ MaximalSpectrum (MvPolynomial σ K ⧸ J))
      (b' : T ≃ₜ MaximalSpectrum (MvPolynomial τ K ⧸ I))
      (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J)),
      ∀ z, (b' (f z)).asIdeal = Ideal.comap φ.toRingHom (a' z).asIdeal := by
  let _ := locusTopology J
  let _ := locusTopology I
  let g : zeroLocus K J → zeroLocus K I := fun x => b (f (a.symm x))
  have hg : ∀ x i, (g x).val i = aeval x.val (P i) := by
    intro x i
    simpa only [g, a.apply_symm_apply] using hf (a.symm x) i
  refine ⟨a.trans (homeomorph J), b.trans (homeomorph I),
    quotientMap I J hJ g P hg, ?_⟩
  intro z
  simpa only [Homeomorph.trans_apply, homeomorph_apply, g, a.symm_apply_apply] using
    point_map_compatibility I J hJ g P hg (a z)

end PhilipponMultiplicity.AffineClosedPoints

end
end

section
-- Included implementation: Solutions.PhilipponPolynomialChartsReduction

set_option autoImplicit false
noncomputable section
namespace PhilipponMultiplicity.AffineClosedPoints
universe u

theorem closed_point_charts_of_polynomial_charts
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
        ∃ (a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance (locusTopology J))
          (b : @Homeomorph T (MvPolynomial.zeroLocus K I) inferInstance (locusTopology I))
          (P : Fin m → MvPolynomial (Fin n) K),
          ∀ (z : S) (i : Fin m),
            (b ⟨f z.val, hST z.property⟩).val i = MvPolynomial.aeval (a z).val (P i)) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    letI : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
    ∃ (S : Set X) (T : Set Y), IsOpen S ∧ x ∈ S ∧ IsOpen T ∧
      ∃ hST : Set.MapsTo f S T,
      ∃ (m n : ℕ) (I : Ideal (MvPolynomial (Fin m) K))
        (J : Ideal (MvPolynomial (Fin n) K))
        (a : S ≃ₜ MaximalSpectrum (MvPolynomial (Fin n) K ⧸ J))
        (b : T ≃ₜ MaximalSpectrum (MvPolynomial (Fin m) K ⧸ I))
        (φ : (MvPolynomial (Fin m) K ⧸ I) →ₐ[K] (MvPolynomial (Fin n) K ⧸ J)),
        ∀ z : S, (b ⟨f z.val, hST z.property⟩).asIdeal =
          Ideal.comap φ.toRingHom (a z).asIdeal := by
  let _ : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  let _ : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
  obtain ⟨S, T, hS, hx, hT, hST, m, n, I, J, hJ, a, b, P, hP⟩ := hcharts
  obtain ⟨a', b', φ, hφ⟩ := charts_of_polynomial_charts
    (fun z : S => (⟨f z.val, hST z.property⟩ : T)) I J hJ a b P hP
  exact ⟨S, T, hS, hx, hT, hST, m, n, I, J, a', b', φ, hφ⟩

end PhilipponMultiplicity.AffineClosedPoints

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
        (J : Ideal (MvPolynomial (Fin n) K))
        (a : S ≃ₜ MaximalSpectrum (MvPolynomial (Fin n) K ⧸ J))
        (b : T ≃ₜ MaximalSpectrum (MvPolynomial (Fin m) K ⧸ I))
        (φ : (MvPolynomial (Fin m) K ⧸ I) →ₐ[K] (MvPolynomial (Fin n) K ⧸ J)),
        ∀ z : S, (b ⟨f z.val, hST z.property⟩).asIdeal =
          Ideal.comap φ.toRingHom (a z).asIdeal := by
  exact AffineClosedPoints.closed_point_charts_of_polynomial_charts K M N X Y e j f x
    (regular_map_has_affine_polynomial_charts K M N X Y e j f he hj hX hY hf x)
