-- Prove2me | solution 1 for ParamSDO.Transition.ranks_maximal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:23:14.325442+00:00
-- url     : https://prove2.me/submissions/fe98e3d0-95e4-44d0-b3ed-a6e2d558518e

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

open ParamSDO.Transition Matrix

/-- A point of the intrinsic interior can be pushed slightly beyond itself, away from any other
point of the set. -/
lemma psdo_ri_extend {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {s : Set V} {x x' : V}
    (hx : x ∈ intrinsicInterior ℝ s) (hx' : x' ∈ s) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - x') ∈ s := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hdir : (y : V) - x' ∈ (affineSpan ℝ s).direction :=
    AffineSubspace.vsub_mem_direction y.2 (subset_affineSpan ℝ s hx')
  let γ : ℝ → affineSpan ℝ s := fun t =>
    ⟨t • ((y : V) - x') + (y : V),
      AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hdir) y.2⟩
  have hγ : Continuous γ :=
    Continuous.subtype_mk ((continuous_id.smul continuous_const).add continuous_const) _
  have h0 : γ 0 = y := by ext; simp [γ]
  have hev : ∀ᶠ t in nhds (0 : ℝ), γ t ∈ interior ((↑) ⁻¹' s : Set (affineSpan ℝ s)) := by
    have := hγ.continuousAt (x := 0)
    rw [ContinuousAt, h0] at this
    exact this (isOpen_interior.mem_nhds hy)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, by positivity, ?_⟩
  have := interior_subset (hball (y := ε / 2) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith))
  simpa [γ, add_comm] using this

lemma psdo_ker_sub {n : ℕ} {X X' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (ht : 0 < t)
    (hX' : X'.PosSemidef) (hY : (X + t • (X - X')).PosSemidef) (v : Fin n → ℝ)
    (hv : X *ᵥ v = 0) : X' *ᵥ v = 0 := by
  have hYv : (X + t • (X - X')) *ᵥ v = -(t • (X' *ᵥ v)) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, hv]; simp
  have h1 := hY.dotProduct_mulVec_nonneg v
  have h2 := hX'.dotProduct_mulVec_nonneg v
  rw [hYv] at h1
  simp only [star_trivial, dotProduct_neg, dotProduct_smul, smul_eq_mul] at h1 h2
  have h3 : v ⬝ᵥ X' *ᵥ v = 0 := by nlinarith
  have := (hX'.dotProduct_mulVec_zero_iff v).1 (by simpa using h3)
  exact this

lemma psdo_rank_le_of_ker {n : ℕ} {X X' : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ v, X *ᵥ v = 0 → X' *ᵥ v = 0) : X'.rank ≤ X.rank := by
  have hk : LinearMap.ker X.mulVecLin ≤ LinearMap.ker X'.mulVecLin := fun v hv => by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢; exact h v hv
  have e1 := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
  have e2 := LinearMap.finrank_range_add_finrank_ker X'.mulVecLin
  have := Submodule.finrank_mono hk
  unfold Matrix.rank
  omega

lemma psdo_rank_le_ri {n : ℕ} {s : Set (Matrix (Fin n) (Fin n) ℝ)}
    (hs : ∀ X ∈ s, X.PosSemidef) {X X' : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ intrinsicInterior ℝ s) (hX' : X' ∈ s) : X'.rank ≤ X.rank := by
  obtain ⟨t, ht, hts⟩ := psdo_ri_extend hX hX'
  exact psdo_rank_le_of_ker fun v hv => psdo_ker_sub ht (hs _ hX') (hs _ hts) v hv

lemma psdo_rank_le_ri2 {n m : ℕ} {s : Set ((Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ)}
    (hs : ∀ p ∈ s, p.2.PosSemidef) {p p' : (Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ}
    (hp : p ∈ intrinsicInterior ℝ s) (hp' : p' ∈ s) : p'.2.rank ≤ p.2.rank := by
  obtain ⟨t, ht, hts⟩ := psdo_ri_extend hp hp'
  have := hs _ hts
  simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub] at this
  exact psdo_rank_le_of_ker fun v hv => psdo_ker_sub ht (hs _ hp') this v hv

theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar),
      (∀ X ∈ intrinsicInterior ℝ (Pstar A b C Cbar ϵ),
        (∀ X' ∈ Pstar A b C Cbar ϵ, X'.rank ≤ X.rank) ∧ X.rank = rkX A b C Cbar ϵ) ∧
      (∀ p ∈ intrinsicInterior ℝ (Dstar A b C Cbar ϵ),
        (∀ p' ∈ Dstar A b C Cbar ϵ, p'.2.rank ≤ p.2.rank) ∧
          p.2.rank = rkS A b C Cbar ϵ) := by
  intro ϵ _
  have hsP : ∀ X ∈ Pstar A b C Cbar ϵ, X.PosSemidef := fun X hX => hX.1.1
  have hsD : ∀ p ∈ Dstar A b C Cbar ϵ, p.2.PosSemidef := fun p hp => hp.1.2
  refine ⟨fun X hX => ⟨fun X' hX' => psdo_rank_le_ri hsP hX hX', ?_⟩,
    fun p hp => ⟨fun p' hp' => psdo_rank_le_ri2 hsD hp hp', ?_⟩⟩
  · symm
    apply IsGreatest.csSup_eq
    refine ⟨⟨X, hX, rfl⟩, ?_⟩
    rintro _ ⟨X', hX', rfl⟩
    exact psdo_rank_le_ri hsP hX (intrinsicInterior_subset hX')
  · symm
    apply IsGreatest.csSup_eq
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    rintro _ ⟨p', hp', rfl⟩
    exact psdo_rank_le_ri2 hsD hp (intrinsicInterior_subset hp')
