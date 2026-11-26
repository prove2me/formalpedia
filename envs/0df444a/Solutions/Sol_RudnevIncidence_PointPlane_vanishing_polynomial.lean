-- Prove2me | solution 1 for RudnevIncidence.PointPlane.vanishing_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:53:48.31979+00:00
-- url     : https://prove2.me/submissions/e81b79a6-84ea-4913-8925-307ca576293c

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting
namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem _root_.solution {F : Type*} [Field F] (X : Finset (ℙ F (Fin 4 → F))) (d : ℕ)
    (hX : X.card < (d + 3).choose 3) :
    ∃ Q : MvPolynomial (Fin 4) F, Q ≠ 0 ∧ Q.IsHomogeneous d ∧
      ∀ x ∈ X, MvPolynomial.eval x.rep Q = 0 := by
  classical
  set mon : Sym (Fin 4) d → (Fin 4 →₀ ℕ) := fun m => Multiset.toFinsupp m.1 with hmon
  have hinj : Function.Injective mon := fun a b h => Subtype.ext (Multiset.toFinsupp.injective h)
  set L : (Sym (Fin 4) d → F) →ₗ[F] MvPolynomial (Fin 4) F :=
    Fintype.linearCombination F (fun m => MvPolynomial.monomial (mon m) (1:F)) with hL
  set Ev : (Sym (Fin 4) d → F) →ₗ[F] (X → F) :=
    LinearMap.pi (fun x : X => (MvPolynomial.aeval (x.1.rep)).toLinearMap.comp L) with hEv
  have hlt : Module.finrank F (X → F) < Module.finrank F (Sym (Fin 4) d → F) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, Sym.card_sym_eq_choose]
    refine lt_of_lt_of_le hX (le_of_eq ?_)
    rw [Fintype.card_fin, show 4 + d - 1 = d + 3 by omega]
    exact Nat.choose_symm_add.symm
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := Ev) hlt
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hk
  have hLc : L c = ∑ m, c m • MvPolynomial.monomial (mon m) (1:F) := by
    rw [hL, Fintype.linearCombination_apply]
  refine ⟨L c, ?_, ?_, ?_⟩
  · intro h
    apply hc0
    funext m
    have := congrArg (MvPolynomial.coeff (mon m)) h
    rw [hLc, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single m] at this
    · simpa [MvPolynomial.coeff_monomial] using this
    · intro b _ hb
      simp [MvPolynomial.coeff_monomial, hinj.ne hb]
    · simp
  · rw [hLc]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m _ => ?_
    rw [MvPolynomial.smul_eq_C_mul]
    refine MvPolynomial.IsHomogeneous.C_mul ?_ _
    apply MvPolynomial.isHomogeneous_monomial
    rw [Finsupp.degree_eq_sum, hmon]
    simp only [Multiset.toFinsupp_apply]
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
    exact m.2
  · intro x hx
    have h := LinearMap.mem_ker.1 hc
    have := congrFun h ⟨x, hx⟩
    simpa [hEv, MvPolynomial.aeval_eq_eval] using this

end RudnevIncidence.PointPlane

