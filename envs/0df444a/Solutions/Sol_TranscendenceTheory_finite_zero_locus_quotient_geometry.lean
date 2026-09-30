-- Prove2me | solution 1 for TranscendenceTheory.finite_zero_locus_quotient_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T01:49:55.671595+00:00
-- url     : https://prove2.me/submissions/55f58480-1ae7-4521-988d-16d317b987d0

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

noncomputable section

namespace TranscendenceTheory

open MvPolynomial

variable {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]

theorem quotient_finite_of_finite_zeroLocus (I : Ideal (MvPolynomial σ K))
    (hZ : (zeroLocus K I).Finite) : Module.Finite K (MvPolynomial σ K ⧸ I) := by
  classical
  let f := Ideal.Quotient.mkₐ K I
  have hgen : Algebra.adjoin K (Set.range fun i : σ => f (X i)) = ⊤ := by
    rw [show (Set.range fun i : σ => f (X i)) = f '' Set.range X from
      (Set.range_comp f X), ← AlgHom.map_adjoin, adjoin_range_X,
      Algebra.map_top, (AlgHom.range_eq_top f).mpr Ideal.Quotient.mk_surjective]
  have hint (i : σ) : IsIntegral K (f (X i)) := by
    let P : Polynomial K := ∏ z ∈ hZ.toFinset, (Polynomial.X - Polynomial.C (z i))
    have hP : P.Monic := Polynomial.monic_prod_of_monic _ _
      (fun z _ => Polynomial.monic_X_sub_C (z i))
    have hrad : Polynomial.aeval (X i : MvPolynomial σ K) P ∈ I.radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
      intro z hz
      rw [← Polynomial.aeval_algHom_apply]
      simp only [aeval_X]
      simp only [P, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_self]
      exact Finset.prod_eq_zero (hZ.mem_toFinset.mpr hz) (sub_self (z i))
    obtain ⟨n, hn⟩ := hrad
    refine ⟨P ^ n, hP.pow n, ?_⟩
    change Polynomial.aeval (f (X i)) (P ^ n) = 0
    rw [Polynomial.aeval_algHom_apply, map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn
  let A := Algebra.adjoin K (Set.range fun i : σ => f (X i))
  let : Module.Finite K A := Algebra.finite_adjoin_of_finite_of_isIntegral
    (Set.finite_range _) (by rintro _ ⟨i, rfl⟩; exact hint i)
  exact Module.Finite.of_surjective A.val.toLinearMap (by
    intro x
    exact ⟨⟨x, by rw [show A = ⊤ from hgen]; trivial⟩, rfl⟩)

omit [IsAlgClosed K] [Finite σ] in
theorem pointToPoint_injective :
    Function.Injective (pointToPoint (k := K) (K := K) (σ := σ)) := by
  intro x y h
  funext i
  have he := congrArg PrimeSpectrum.asIdeal h
  have hx : X i - C (x i) ∈ (pointToPoint (k := K) x).asIdeal := by
    change X i - C (x i) ∈ vanishingIdeal K {x}
    rw [mem_vanishingIdeal_singleton_iff]
    simp
  rw [he] at hx
  change X i - C (x i) ∈ vanishingIdeal K {y} at hx
  rw [mem_vanishingIdeal_singleton_iff] at hx
  simpa using (sub_eq_zero.mp (by simpa using hx : y i - x i = 0)).symm

omit [IsAlgClosed K] [Finite σ] in
theorem finite_zeroLocus_of_quotient_finite (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)] : (zeroLocus K I).Finite := by
  let : IsArtinianRing (MvPolynomial σ K ⧸ I) := IsArtinianRing.of_finite K _
  have hp (z : zeroLocus K I) : I ≤ (pointToPoint (k := K) z.val).asIdeal :=
    pointToPoint_zeroLocus_le I ⟨z.val, z.property, rfl⟩
  let q : zeroLocus K I → PrimeSpectrum (MvPolynomial σ K ⧸ I) := fun z =>
    ⟨(pointToPoint (k := K) z.val).asIdeal.map (Ideal.Quotient.mk I),
      Ideal.isPrime_map_quotientMk_of_isPrime (hp z)⟩
  have hq : Function.Injective q := by
    intro z w h
    apply Subtype.ext
    apply pointToPoint_injective
    apply PrimeSpectrum.ext
    have he := congrArg (fun t : PrimeSpectrum (MvPolynomial σ K ⧸ I) =>
      t.asIdeal.comap (Ideal.Quotient.mk I)) h
    simpa only [q, Ideal.comap_map_mk (hp z), Ideal.comap_map_mk (hp w)] using he
  let : Finite (zeroLocus K I) := Finite.of_injective q hq
  exact Set.toFinite _

theorem quotient_finite_iff_finite_zeroLocus (I : Ideal (MvPolynomial σ K)) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ↔ (zeroLocus K I).Finite :=
  ⟨fun _ => finite_zeroLocus_of_quotient_finite I, quotient_finite_of_finite_zeroLocus I⟩

theorem support_prime_eq_point (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial σ K)) (hIp : I ≤ p.asIdeal) :
    ∃ x : σ → K, x ∈ zeroLocus K I ∧ pointToPoint (k := K) x = p := by
  let : IsArtinianRing (MvPolynomial σ K ⧸ I) := IsArtinianRing.of_finite K _
  let q := p.asIdeal.map (Ideal.Quotient.mk I)
  let : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIp
  have hm : p.asIdeal.IsMaximal := by
    have h : (q.comap (Ideal.Quotient.mk I)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    simpa only [q, Ideal.comap_map_mk hIp] using h
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hm
  refine ⟨x, ?_, ?_⟩
  · intro r hr
    exact (mem_vanishingIdeal_singleton_iff x r).mp (hx ▸ hIp hr)
  · exact PrimeSpectrum.ext hx.symm

end TranscendenceTheory

open TranscendenceTheory MvPolynomial

theorem solution
    (K σ : Type*) [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) :
    (Module.Finite K (MvPolynomial σ K ⧸ I) ↔ (zeroLocus K I).Finite) ∧
    Function.Injective (pointToPoint (k := K) (K := K) (σ := σ)) ∧
    (Module.Finite K (MvPolynomial σ K ⧸ I) →
      ∀ p : PrimeSpectrum (MvPolynomial σ K), I ≤ p.asIdeal →
        ∃ x : σ → K, x ∈ zeroLocus K I ∧ pointToPoint (k := K) x = p) := by
  refine ⟨quotient_finite_iff_finite_zeroLocus I, pointToPoint_injective, ?_⟩
  intro h p hp
  let : Module.Finite K (MvPolynomial σ K ⧸ I) := h
  exact support_prime_eq_point I p hp
