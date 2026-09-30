-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_jet_span_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T02:35:37.067907+00:00
-- url     : https://prove2.me/submissions/391c740b-cd50-40b7-bdaa-88728e16fcc8

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section

theorem solution
    (K σ ι : Type*) [Field K]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (v : ι → σ → K) (N : ℕ) (S : Finset (σ →₀ ℕ)) (p : MvPolynomial σ K) :
    (∃ q : MvPolynomial σ K, q.support ⊆ S ∧
      ∀ a : ι, ∀ k : Fin N, MvPolynomial.eval (v a) (D^[k.val] (p - q)) = 0) ↔
    (fun (a : ι) (k : Fin N) => MvPolynomial.eval (v a) (D^[k.val] p)) ∈
      Submodule.span K
        ((fun d : σ →₀ ℕ => fun (a : ι) (k : Fin N) =>
          MvPolynomial.eval (v a) (D^[k.val] (MvPolynomial.monomial d 1))) ''
            (S : Set (σ →₀ ℕ))) := by
  classical
  let E : MvPolynomial σ K →ₗ[K] (ι → Fin N → K) :=
    LinearMap.pi fun a => LinearMap.pi fun k =>
      (MvPolynomial.aeval (v a)).toLinearMap.comp (D.toLinearMap ^ k.val)
  have hE (q : MvPolynomial σ K) (a : ι) (k : Fin N) :
      E q a k = MvPolynomial.eval (v a) (D^[k.val] q) := by
    change MvPolynomial.aeval (v a) ((D.toLinearMap ^ k.val) q) = _
    rw [MvPolynomial.aeval_eq_eval, Module.End.pow_apply]
    rfl
  have hsupport (q : MvPolynomial σ K) :
      q ∈ MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ)) ↔ q.support ⊆ S := by
    rw [MvPolynomial.mem_restrictSupport_iff, Finset.coe_subset]
  have himage : (MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ))).map E =
      Submodule.span K ((fun d => E (MvPolynomial.monomial d 1)) ''
        (S : Set (σ →₀ ℕ))) := by
    simp only [MvPolynomial.restrictSupport_eq_span, Submodule.map_span, Set.image_image]
  simp_rw [← hE]
  rw [← himage]
  constructor
  · rintro ⟨q, hq, hzero⟩
    refine Submodule.mem_map.mpr ⟨q, (hsupport q).mpr hq, ?_⟩
    apply Eq.symm
    apply sub_eq_zero.mp
    rw [← map_sub]
    funext a k
    exact hzero a k
  · intro hp
    obtain ⟨q, hq, heq⟩ := Submodule.mem_map.mp hp
    refine ⟨q, (hsupport q).mp hq, ?_⟩
    intro a k
    simp only [map_sub, heq, sub_self, Pi.zero_apply]
