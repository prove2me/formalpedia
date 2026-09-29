-- Prove2me | solution 1 for RelaxationMethod.ConvexDomain.lemma1_case1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:52:11.797361+00:00
-- url     : https://prove2.me/submissions/15c2a986-a6f3-4240-8f4a-1df778f0faed

import Mathlib
import Definitions.Def_RelaxationMethod_Shared_FejerMonotone
open Filter Topology


namespace RelaxationMethod.ConvexDomain

theorem l1_eq_of_dist_eq {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hspan : affineSpan ℝ A = ⊤) (l l' : EuclideanSpace ℝ (Fin n))
    (h : ∀ a ∈ A, dist l a = dist l' a) : l = l' := by
  obtain ⟨a₀, ha₀⟩ : A.Nonempty := by
    rw [← affineSpan_nonempty (k := ℝ), hspan]; exact ⟨0, trivial⟩
  have key : ∀ a ∈ A, inner ℝ (l - l') (a - a₀) = 0 := by
    intro a ha
    have h1 := h a ha
    have h2 := h a₀ ha₀
    rw [dist_eq_norm, dist_eq_norm] at h1 h2
    have e1 : ‖(l - a₀) - (a - a₀)‖^2 = ‖(l' - a₀) - (a - a₀)‖^2 := by
      rw [sub_sub_sub_cancel_right, sub_sub_sub_cancel_right, h1]
    rw [norm_sub_sq_real (l - a₀) (a - a₀), norm_sub_sq_real (l' - a₀) (a - a₀), h2] at e1
    rw [inner_sub_left]
    have : inner ℝ (l - a₀) (a - a₀) - inner ℝ (l' - a₀) (a - a₀) = inner ℝ (l - l') (a - a₀) := by
      rw [← inner_sub_left]; congr 1; abel
    rw [inner_sub_left, inner_sub_left, inner_sub_left] at this
    simp only [inner_sub_left] at e1 ⊢
    linarith
  have hv : vectorSpan ℝ A = ⊤ := by
    rw [← direction_affineSpan, hspan, AffineSubspace.direction_top]
  rw [vectorSpan_eq_span_vsub_set_right ℝ ha₀] at hv
  have hle : Submodule.span ℝ ((· -ᵥ a₀) '' A) ≤ LinearMap.ker (innerₛₗ ℝ (l - l')) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub]
    exact key a ha
  rw [hv] at hle
  have hmem : l - l' ∈ LinearMap.ker (innerₛₗ ℝ (l - l')) := hle Submodule.mem_top
  simp only [LinearMap.mem_ker] at hmem
  change inner ℝ (l - l') (l - l') = 0 at hmem
  rw [inner_self_eq_zero, sub_eq_zero] at hmem
  exact hmem

theorem lemma1_case1_core {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hspan : affineSpan ℝ A = ⊤) (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hq : RelaxationMethod.Shared.IsFejerMonotone A q) :
    ∃ l : EuclideanSpace ℝ (Fin n), Tendsto q atTop (𝓝 l) := by
  obtain ⟨a₀, ha₀⟩ : A.Nonempty := by
    rw [← affineSpan_nonempty (k := ℝ), hspan]; exact ⟨0, trivial⟩
  obtain ⟨-, -, hmono⟩ := hq
  have hanti : ∀ a ∈ A, Antitone (fun ν => dist (q ν) a) :=
    fun a ha => antitone_nat_of_succ_le (hmono a ha)
  have hconv : ∀ a ∈ A, Tendsto (fun ν => dist (q ν) a) atTop (𝓝 (⨅ ν, dist (q ν) a)) :=
    fun a ha => tendsto_atTop_ciInf (hanti a ha) ⟨0, by rintro _ ⟨ν, rfl⟩; exact dist_nonneg⟩
  have hbd : ∀ ν, q ν ∈ Metric.closedBall a₀ (dist (q 0) a₀) :=
    fun ν => hanti a₀ ha₀ (Nat.zero_le ν)
  have hlim : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ l', Tendsto (q ∘ φ) atTop (𝓝 l') →
      ∀ a ∈ A, dist l' a = ⨅ ν, dist (q ν) a := by
    intro φ hφ l' hl a ha
    exact tendsto_nhds_unique (hl.dist tendsto_const_nhds) ((hconv a ha).comp hφ)
  obtain ⟨l, -, ψ, hψ, hl⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  refine ⟨l, ?_⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨l', -, φ, hφ, hl'⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall (fun k => hbd (ns k))
  have : l' = l := l1_eq_of_dist_eq A hspan l' l (fun a ha => by
    rw [hlim (ns ∘ φ) (hns.comp hφ.tendsto_atTop) l' hl' a ha,
      hlim ψ hψ.tendsto_atTop l hl a ha])
  exact ⟨φ, this ▸ hl'⟩

end RelaxationMethod.ConvexDomain

open RelaxationMethod.ConvexDomain
open Filter Topology

theorem solution {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hspan : affineSpan ℝ A = ⊤) (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hq : RelaxationMethod.Shared.IsFejerMonotone A q) :
    ∃ l : EuclideanSpace ℝ (Fin n), Tendsto q atTop (𝓝 l) := by
  exact lemma1_case1_core A hspan q hq
