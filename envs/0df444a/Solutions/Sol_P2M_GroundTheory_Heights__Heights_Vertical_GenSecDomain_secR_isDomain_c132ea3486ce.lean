-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secR_isDomain_c132ea3486ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:24.725803+00:00
-- url     : https://prove2.me/submissions/9529383b-4d24-4157-a79f-9513afe47195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
variable {k : Type} [Field k] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
theorem _root_.solution (h₁ : ChartDomain.Statement) (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ)
    (hQ : IsProjPrime Q) {Ω : Type} [Field Ω] (Ψ : SecR Q e →+* Ω)
    (hΨ : ∀ l, X l ∉ Q → Ψ (xc Q e l) ≠ 0) : IsDomain (SecR Q e) := by
  classical
  have hQk : ∀ a : k, C a ∈ Q → a = 0 := fun a ha => by
    by_contra h
    exact hQ.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem Q ha ((isUnit_iff_ne_zero.mpr h).map C))
  have hdom : ∀ j, X j ∉ Q → IsDomain (Localization.Away (xc Q e j)) := fun j hj =>
    (h₁ k n e Q j hQ.isPrime hQk hj).1
  have hx0 : ∀ j, X j ∈ Q → xc Q e j = 0 := fun j hj => by
    rw [xc, secCoord, Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_sup_left (Ideal.mem_sup_left ?_)
    have := Ideal.mem_map_of_mem (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)) hj
    simpa using this
  have hspan : Ideal.span (Set.range (xc Q e)) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun j => Ideal.Quotient.mk _ (C (X (.inr j))), ?_⟩
    have h : Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
        (X : Par e n → MvPolynomial (Par e n) k)) (chartForm X - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [map_sub, map_one, sub_eq_zero, chartForm, linForm, map_sum] at h
    simpa [xc, secCoord] using h
  have hchart : ∀ j (a : SecR Q e), algebraMap _ (Localization.Away (xc Q e j)) a = 0 →
      ∃ N : ℕ, xc Q e j ^ N * a = 0 := by
    intro j a h
    obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (xc Q e j)) _ a).mp h
    exact ⟨N, hN⟩
  have hne : ∀ j l, X j ∉ Q → X l ∉ Q → algebraMap _ (Localization.Away (xc Q e j)) (xc Q e l) ≠ 0 := by
    intro j l hj hl h
    obtain ⟨N, hN⟩ := hchart j _ h
    have h' := congrArg Ψ hN
    rw [map_mul, map_pow, map_zero] at h'
    exact mul_ne_zero (pow_ne_zero _ (hΨ j hj)) (hΨ l hl) h'
  have hzero : ∀ a : SecR Q e, (∀ j, X j ∉ Q → ∃ N : ℕ, xc Q e j ^ N * a = 0) → a = 0 := by
    intro a ha
    have h' : ∀ j, ∃ N : ℕ, xc Q e j ^ N * a = 0 := fun j => by
      by_cases hj : X j ∈ Q
      · exact ⟨1, by rw [hx0 j hj, pow_one, zero_mul]⟩
      · exact ha j hj
    choose N hN using h'
    have hM : ∀ j, xc Q e j ^ (∑ i, N i) * a = 0 := fun j => by
      have : N j ≤ ∑ i, N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [← Nat.sub_add_cancel this, pow_add, mul_assoc, hN, mul_zero]
    have hone := Ideal.span_pow_eq_top _ hspan (∑ i, N i)
    rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at hone
    obtain ⟨c, hc⟩ := hone
    rw [← one_mul a, ← hc, Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => by simp only [Function.comp_apply, mul_assoc, hM, mul_zero]
  obtain ⟨j0, hj0⟩ := hQ.isRelevant
  have hkill : ∀ a : SecR Q e, algebraMap _ (Localization.Away (xc Q e j0)) a = 0 → a = 0 := by
    intro a ha
    obtain ⟨N, hN⟩ := hchart j0 a ha
    refine hzero a fun j hj => hchart j a ?_
    have := hdom j hj
    have h := congrArg (algebraMap _ (Localization.Away (xc Q e j))) hN
    rw [map_mul, map_pow, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hne j j0 hj hj0))
  have : Nontrivial (SecR Q e) := RingHom.domain_nontrivial Ψ
  have := hdom j0 hj0
  have : NoZeroDivisors (SecR Q e) := ⟨fun {a b} hab => by
    have h := congrArg (algebraMap _ (Localization.Away (xc Q e j0))) hab
    rw [map_mul, map_zero] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hkill a h)
    · exact Or.inr (hkill b h)⟩
  exact NoZeroDivisors.to_isDomain _
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
