-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_complements
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:18:59.712003+00:00
-- url     : https://prove2.me/submissions/7946346d-fbdb-4a77-9d59-86c94e07a696

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Claimed50.P41

lemma g68k_rank {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsAlt) (W : Submodule ℝ V) :
    symplecticRank B W + Module.finrank ℝ (W ⊓ B.orthogonal W : Submodule ℝ V) =
      Module.finrank ℝ W := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (B.restrict W)
  have h3 : Submodule.map W.subtype (LinearMap.ker (B.restrict W)) = W ⊓ B.orthogonal W := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf,
      LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.IsOrtho, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun z hz => ?_⟩
      have := LinearMap.congr_fun hy ⟨z, hz⟩
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        LinearMap.zero_apply] at this
      rw [← hB.neg_eq]; simp [this]
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      ext z
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        LinearMap.zero_apply]
      rw [← hB.neg_eq, h z z.2, neg_zero]
  have h2 : Module.finrank ℝ (LinearMap.ker (B.restrict W)) =
      Module.finrank ℝ (W ⊓ B.orthogonal W : Submodule ℝ V) := by
    rw [← h3]
    exact (Submodule.equivMapOfInjective _ W.injective_subtype _).finrank_eq
  unfold symplecticRank
  omega

lemma g68k_iso_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (W : Submodule ℝ V) :
    IsIsotropic B W ↔ W ≤ B.orthogonal W := by
  constructor
  · intro h x hx y hy
    exact h y hy x hx
  · intro h x hx y hy
    exact h hy x hx



/-- PDF p.9, (3.10)–(3.13): complement involution, dimension, integer
rank identity, and existence of non-direct complements. Alternation identifies
Mathlib's right orthogonal with the source's left orthogonal. -/
theorem solution (n : ℕ) (hn : 0 < n)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2 * n) (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (W : Submodule ℝ V) :
    B.orthogonal (B.orthogonal W) = W ∧
    Module.finrank ℝ (B.orthogonal W) + Module.finrank ℝ W = 2 * n ∧
    (symplecticRank B (B.orthogonal W) : ℤ) =
      2 * ((n : ℤ) - (Module.finrank ℝ W : ℤ)) + (symplecticRank B W : ℤ) ∧
    (∃ L : Submodule ℝ V, L ⊓ B.orthogonal L ≠ ⊥ ∧ L ⊔ B.orthogonal L ≠ ⊤) := by
  have hoo := LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl W
  have hfo := fun U : Submodule ℝ V => LinearMap.BilinForm.finrank_orthogonal hnd U
  have hle := fun U : Submodule ℝ V => Submodule.finrank_le U
  refine ⟨hoo, ?_, ?_, ?_⟩
  · have := hfo W; have := hle W; omega
  · have r1 := g68k_rank B hB W
    have r2 := g68k_rank B hB (B.orthogonal W)
    rw [hoo, inf_comm] at r2
    have := hfo W; have := hle W
    omega
  · have hpos : 0 < Module.finrank ℝ V := by omega
    obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    -- actually use a nonzero vector
    have hL : ℝ ∙ v ≤ B.orthogonal (ℝ ∙ v) := by
      intro x hx y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
      simp [LinearMap.BilinForm.IsOrtho, hB.self_eq_zero]
    refine ⟨ℝ ∙ v, ?_, ?_⟩
    · rw [inf_eq_left.2 hL]
      simpa using hv
    · rw [sup_eq_right.2 hL]
      intro htop
      have h1 := hfo (ℝ ∙ v)
      rw [htop, finrank_top, finrank_span_singleton hv] at h1
      omega



end
