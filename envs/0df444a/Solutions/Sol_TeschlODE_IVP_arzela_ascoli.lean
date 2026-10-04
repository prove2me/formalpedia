-- Prove2me | solution 1 for TeschlODE.IVP.arzela_ascoli
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:18:08.04888+00:00
-- url     : https://prove2.me/submissions/44085234-206e-4fa8-8f6b-aef8ee857c6e

import Mathlib

theorem solution {n : ℕ} (a b : ℝ) (x : ℕ → ℝ → EuclideanSpace ℝ (Fin n))
    (hcont : ∀ m : ℕ, ContinuousOn (x m) (Set.Icc a b))
    (hequi : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℕ, ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b,
      |t - s| < δ → ‖x m t - x m s‖ ≤ ε)
    (hbdd : ∃ R : ℝ, ∀ m : ℕ, ∀ t ∈ Set.Icc a b, ‖x m t‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℝ → EuclideanSpace ℝ (Fin n),
      TendstoUniformlyOn (fun k => x (φ k)) y Filter.atTop (Set.Icc a b) := by
  obtain ⟨R, hR⟩ := hbdd
  let g : ℕ → BoundedContinuousFunction (Set.Icc a b) (EuclideanSpace ℝ (Fin n)) := fun m =>
    BoundedContinuousFunction.mkOfCompact ⟨(Set.Icc a b).domRestrict (x m), (hcont m).domRestrict⟩
  have hg : ∀ m (t : Set.Icc a b), g m t = x m t := fun m t => rfl
  have hUE : UniformEquicontinuous (fun m => ((g m : BoundedContinuousFunction _ _) :
      Set.Icc a b → EuclideanSpace ℝ (Fin n))) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hequi (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun t s hts m => ?_⟩
    rw [hg, hg, dist_eq_norm]
    have : |(t : ℝ) - s| < δ := by
      rw [Subtype.dist_eq, Real.dist_eq] at hts; exact hts
    have := h m t t.2 s s.2 this
    linarith
  have hEq : Equicontinuous ((↑) : Set.range g → Set.Icc a b → EuclideanSpace ℝ (Fin n)) := by
    have := hUE.equicontinuous.comp (Set.rangeSplitting g)
    have heq : ((↑) : Set.range g → Set.Icc a b → EuclideanSpace ℝ (Fin n)) =
        (fun m => ((g m : BoundedContinuousFunction _ _) :
          Set.Icc a b → EuclideanSpace ℝ (Fin n))) ∘ Set.rangeSplitting g := by
      funext f
      show ⇑(f : BoundedContinuousFunction _ _) = ⇑(g (Set.rangeSplitting g f))
      rw [Set.apply_rangeSplitting g f]
    rw [heq]
    exact this
  have hK : IsCompact (closure (Set.range g)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 R) (isCompact_closedBall _ _)
      (Set.range g) (by
        rintro f t ⟨m, rfl⟩
        rw [hg, Metric.mem_closedBall, dist_zero_right]
        exact hR m t t.2) hEq
  obtain ⟨L, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := g) (fun m => subset_closure ⟨m, rfl⟩)
  refine ⟨φ, hφ, fun t => if h : t ∈ Set.Icc a b then L ⟨t, h⟩ else 0, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have := (Metric.tendsto_nhds.mp hlim) ε hε
  filter_upwards [this] with k hk
  intro t ht
  simp only [dif_pos ht]
  have h1 := BoundedContinuousFunction.dist_coe_le_dist (f := (g ∘ φ) k) (g := L) ⟨t, ht⟩
  rw [dist_comm]
  have h2 : ((g ∘ φ) k) ⟨t, ht⟩ = x (φ k) t := rfl
  rw [h2] at h1
  exact lt_of_le_of_lt h1 hk
