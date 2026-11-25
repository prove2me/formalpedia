-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_finite_of_pow_mem_d0bf03a092a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:19.110347+00:00
-- url     : https://prove2.me/submissions/5582cbae-6b95-4352-b76b-dd3caf10631d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) R))
    (M : Fin n → ℕ) (q : Fin n → MvPolynomial (Fin n) R) (hq : ∀ j, (q j).totalDegree < M j)
    (hQ : ∀ j, X j ^ M j - q j ∈ Q) : Module.Finite R (MvPolynomial (Fin n) R ⧸ Q) := by
  classical
  let S : Set (MvPolynomial (Fin n) R ⧸ Q) :=
    Set.range fun α : (j : Fin n) → Fin (M j) =>
      Ideal.Quotient.mk Q (monomial (Finsupp.equivFunOnFinite.symm fun j => (α j : ℕ)) 1)
  have hC : ∀ (r : R) (p : MvPolynomial (Fin n) R),
      Ideal.Quotient.mk Q (C r * p) = r • Ideal.Quotient.mk Q p := by
    intro r p
    rw [← MvPolynomial.smul_eq_C_mul, ← Ideal.Quotient.mkₐ_eq_mk R, map_smul]
  have key : ∀ d (s : Fin n →₀ ℕ), s.degree ≤ d →
      Ideal.Quotient.mk Q (monomial s 1) ∈ Submodule.span R S := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro s hs
    by_cases hsmall : ∀ j, s j < M j
    · refine Submodule.subset_span ⟨fun j => ⟨s j, hsmall j⟩, ?_⟩
      show Ideal.Quotient.mk Q (monomial (Finsupp.equivFunOnFinite.symm fun j => s j) 1) = _
      rw [Finsupp.equivFunOnFinite_symm_coe]
    · push Not at hsmall
      obtain ⟨j, hj⟩ := hsmall
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single j (M j) :=
        ⟨s - Finsupp.single j (M j), (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)).symm⟩
      have hmk : Ideal.Quotient.mk Q (monomial (s' + Finsupp.single j (M j)) 1) =
          Ideal.Quotient.mk Q (monomial s' 1 * q j) := by
        have hmono : monomial (s' + Finsupp.single j (M j)) (1 : R) = monomial s' 1 * X j ^ M j := by
          rw [X_pow_eq_monomial, monomial_mul, one_mul]
        rw [hmono, Ideal.Quotient.eq, ← mul_sub]
        exact Q.mul_mem_left _ (hQ j)
      rw [hmk, (q j).as_sum, Finset.mul_sum, map_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      have hprod : monomial s' (1 : R) * monomial m (coeff m (q j)) =
          C (coeff m (q j)) * monomial (s' + m) 1 := by
        rw [monomial_mul, C_mul_monomial, one_mul, mul_one]
      rw [hprod, hC]
      refine Submodule.smul_mem _ _ (ih _ ?_ _ le_rfl)
      have hm' : m.degree ≤ (q j).totalDegree := le_totalDegree hm
      have hqj := hq j
      rw [map_add, Finsupp.degree_single] at hs
      rw [map_add]
      omega
  refine ⟨(Submodule.fg_def).mpr ⟨S, Set.finite_range _, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [← mul_one (coeff s p), ← C_mul_monomial, hC]
  exact Submodule.smul_mem _ _ (key _ s le_rfl)
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
