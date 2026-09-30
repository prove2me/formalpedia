-- Prove2me | solution 1 for WeierstrassEllipticZeta.supported_relations_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T03:23:34.238555+00:00
-- url     : https://prove2.me/submissions/5d8eb043-e4f4-45a8-bda2-e83476cc798b

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section

theorem solution
    (K σ V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (E : MvPolynomial σ K →ₗ[K] V) (S : Finset (σ →₀ ℕ))
    (R : Submodule K (MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ))))
    (hR : ∀ p : R, E p.val.val = 0) :
    Module.finrank K (Submodule.span K
      ((fun d : σ →₀ ℕ => E (MvPolynomial.monomial d 1)) '' (S : Set (σ →₀ ℕ)))) +
      Module.finrank K R ≤ S.card := by
  classical
  let A := MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ))
  let F : A →ₗ[K] V := E.comp A.subtype
  let : FiniteDimensional K A :=
    (MvPolynomial.basisRestrictSupport K (S : Set (σ →₀ ℕ))).finiteDimensional_of_finite
  have hdim : Module.finrank K A = S.card :=
    Module.finrank_eq_card_finset_basis (MvPolynomial.basisRestrictSupport K (S : Set (σ →₀ ℕ)))
  have hrange : LinearMap.range F = Submodule.span K
      ((fun d : σ →₀ ℕ => E (MvPolynomial.monomial d 1)) '' (S : Set (σ →₀ ℕ))) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    change (MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ))).map E = _
    simp only [MvPolynomial.restrictSupport_eq_span, Submodule.map_span, Set.image_image]
  have hker : R ≤ LinearMap.ker F := by
    intro p hp
    exact hR ⟨p, hp⟩
  rw [← hrange]
  calc
    Module.finrank K (LinearMap.range F) + Module.finrank K R ≤
        Module.finrank K (LinearMap.range F) + Module.finrank K (LinearMap.ker F) :=
      Nat.add_le_add_left (Submodule.finrank_mono hker) _
    _ = S.card := F.finrank_range_add_finrank_ker.trans hdim
