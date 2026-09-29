-- Prove2me | solution 1 for RelaxationMethod.ConvexDomain.extremal_support_halfspace
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:55:10.711801+00:00
-- url     : https://prove2.me/submissions/e5e20535-950f-4a70-b477-3006af047c82

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
import Definitions.Def_RelaxationMethod_ConvexDomain_SupportHalfSpace



namespace RelaxationMethod.ConvexDomain

theorem rm_vi {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ A)
    {p q : EuclideanSpace ℝ (Fin n)} (hq : IsNearestPoint A p q) :
    ∀ a ∈ A, inner ℝ (p - q) (a - q) ≤ 0 := by
  have : Nonempty A := ⟨⟨q, hq.1⟩⟩
  refine (norm_eq_iInf_iff_real_inner_le_zero (F := EuclideanSpace ℝ (Fin n)) hconv hq.1).mp ?_
  apply le_antisymm
  · apply le_ciInf
    intro w
    have := hq.2 w w.2
    rwa [dist_eq_norm, dist_eq_norm] at this
  · have hb : BddBelow (Set.range (fun w : A => ‖p - (w : EuclideanSpace ℝ (Fin n))‖)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hb (⟨q, hq.1⟩ : A)

theorem es_core {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hconv : Convex ℝ A)
    (p q : EuclideanSpace ℝ (Fin n)) (hp : p ∉ A) (hq : IsNearestPoint A p q)
    (H₀ : Set (EuclideanSpace ℝ (Fin n)))
    (hH₀ : H₀ = {x | inner ℝ (q - p) q ≤ inner ℝ (q - p) x}) :
    IsSupportHalfSpace A H₀ ∧ p ∉ H₀ ∧ Metric.infDist p H₀ = dist p q ∧
      (∀ H, IsSupportHalfSpace A H → Metric.infDist p H ≤ Metric.infDist p H₀) ∧
      (∀ H, IsSupportHalfSpace A H → Metric.infDist p H = Metric.infDist p H₀ →
        ∀ q' ∈ H, dist p q' = Metric.infDist p H →
          p + (2 : ℝ) • (q' - p) = p + (2 : ℝ) • (q - p)) := by
  have hvi := rm_vi hconv hq
  have hpq : q - p ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; exact hp (h ▸ hq.1)
  have hAH : A ⊆ H₀ := by
    intro a ha
    rw [hH₀]
    show inner ℝ (q - p) q ≤ inner ℝ (q - p) a
    have := hvi a ha
    have e : inner ℝ (p - q) (a - q) = inner ℝ (q - p) q - inner ℝ (q - p) a := by
      rw [← neg_sub q p, inner_neg_left, inner_sub_right]; ring
    linarith
  have hqH : q ∈ H₀ := hAH hq.1
  have hpos : 0 < ‖q - p‖ := norm_pos_iff.mpr hpq
  have hinf : Metric.infDist p H₀ = dist p q := by
    apply le_antisymm (Metric.infDist_le_dist_of_mem hqH)
    rw [Metric.le_infDist ⟨q, hqH⟩]
    intro x hx
    rw [hH₀] at hx
    change inner ℝ (q - p) q ≤ inner ℝ (q - p) x at hx
    have h1 : ‖q - p‖ ^ 2 ≤ inner ℝ (q - p) (x - p) := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_right, inner_sub_right]; linarith
    have h2 : inner ℝ (q - p) (x - p) ≤ ‖q - p‖ * ‖x - p‖ := real_inner_le_norm _ _
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev p q, norm_sub_rev p x]
    nlinarith
  refine ⟨⟨q - p, hpq, inner ℝ (q - p) q, hH₀, hAH, q, hq.1, rfl⟩, ?_, hinf, ?_, ?_⟩
  · intro h
    rw [hH₀] at h
    change inner ℝ (q - p) q ≤ inner ℝ (q - p) p at h
    have : inner ℝ (q - p) (q - p) ≤ 0 := by rw [inner_sub_right]; linarith
    rw [real_inner_self_eq_norm_sq] at this
    nlinarith
  · intro H hH
    obtain ⟨u, -, c, -, hAH', -⟩ := hH
    rw [hinf]; exact Metric.infDist_le_dist_of_mem (hAH' hq.1)
  · intro H hH heq q' hq' hd
    obtain ⟨u, -, c, hHe, hAH', -⟩ := hH
    have hqH' : q ∈ H := hAH' hq.1
    have hmH : midpoint ℝ q q' ∈ H := by
      rw [hHe] at hqH' hq' ⊢
      change c ≤ inner ℝ u q at hqH'
      change c ≤ inner ℝ u q' at hq'
      change c ≤ inner ℝ u (midpoint ℝ q q')
      rw [midpoint_eq_smul_add, inner_smul_right, inner_add_right]
      norm_num; linarith
    have hm := Metric.infDist_le_dist_of_mem (x := p) hmH
    rw [heq, hinf] at hd hm
    -- parallelogram
    have key : dist p (midpoint ℝ q q') ^ 2 =
        (dist p q ^ 2 + dist p q' ^ 2) / 2 - ‖q - q'‖ ^ 2 / 4 := by
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
      have e1 : p - midpoint ℝ q q' = (2:ℝ)⁻¹ • ((p - q) + (p - q')) := by
        rw [midpoint_eq_smul_add, invOf_eq_inv]; module
      have e2 : q - q' = (p - q') - (p - q) := by abel
      rw [e1, e2, norm_smul, mul_pow, norm_add_sq_real (p - q) (p - q'),
        norm_sub_sq_real (p - q') (p - q), real_inner_comm (p - q') (p - q)]
      simp only [norm_inv, Real.norm_ofNat]
      ring
    have hqq : ‖q - q'‖ ^ 2 ≤ 0 := by
      have := dist_nonneg (x := p) (y := midpoint ℝ q q')
      nlinarith [dist_nonneg (x := p) (y := q)]
    have : q' = q := by
      have : ‖q - q'‖ = 0 := by nlinarith [norm_nonneg (q - q')]
      rw [norm_eq_zero, sub_eq_zero] at this; exact this.symm
    rw [this]

end RelaxationMethod.ConvexDomain

open RelaxationMethod.ConvexDomain


theorem solution {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p q : EuclideanSpace ℝ (Fin n)) (hp : p ∉ A) (hq : IsNearestPoint A p q)
    (H₀ : Set (EuclideanSpace ℝ (Fin n)))
    (hH₀ : H₀ = {x | inner ℝ (q - p) q ≤ inner ℝ (q - p) x}) :
    IsSupportHalfSpace A H₀ ∧ p ∉ H₀ ∧ Metric.infDist p H₀ = dist p q ∧
      (∀ H, IsSupportHalfSpace A H → Metric.infDist p H ≤ Metric.infDist p H₀) ∧
      (∀ H, IsSupportHalfSpace A H → Metric.infDist p H = Metric.infDist p H₀ →
        ∀ q' ∈ H, dist p q' = Metric.infDist p H →
          p + (2 : ℝ) • (q' - p) = p + (2 : ℝ) • (q - p)) := by
  exact es_core A hconv p q hp hq H₀ hH₀
