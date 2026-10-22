-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.isotropic_coisotropic_lagrangian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:19:15.324213+00:00
-- url     : https://prove2.me/submissions/9f994662-84d9-41c3-a0f4-2175378f25b0

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



/-- PDF p.10, (3.14)–(3.15): all isotropic/co-isotropic equivalences,
dimension bounds and the Lagrangian case. -/
theorem solution (n : ℕ) (hn : 0 < n)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2 * n) (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (W : Submodule ℝ V) :
    (symplecticRank B W = 0 ↔ IsIsotropic B W) ∧
    (IsIsotropic B W ↔ W ≤ B.orthogonal W) ∧
    (IsIsotropic B W → Module.finrank ℝ W ≤ n) ∧
    (IsCoisotropic B W ↔ B.orthogonal W ≤ W) ∧
    (IsCoisotropic B W → n ≤ Module.finrank ℝ W) ∧
    (IsLagrangian B W ↔ IsIsotropic B W ∧ Module.finrank ℝ W = n) ∧
    (IsLagrangian B W → IsIsotropic B W ∧ IsCoisotropic B W) := by
  have hoo := LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl W
  have hfo := LinearMap.BilinForm.finrank_orthogonal hnd W
  have hlw := Submodule.finrank_le W
  have hco : IsCoisotropic B W ↔ B.orthogonal W ≤ W := by
    rw [IsCoisotropic, g68k_iso_iff, hoo]
  have r := g68k_rank B hB W
  refine ⟨?_, g68k_iso_iff B W, ?_, hco, ?_, ?_, ?_⟩
  · rw [g68k_iso_iff]
    constructor
    · intro h0
      rw [h0, zero_add] at r
      have := Submodule.eq_of_le_of_finrank_eq (inf_le_left : W ⊓ B.orthogonal W ≤ W) r
      exact inf_eq_left.1 this
    · intro h
      rw [inf_eq_left.2 h] at r
      omega
  · intro h
    have := Submodule.finrank_mono ((g68k_iso_iff B W).1 h)
    omega
  · intro h
    have := Submodule.finrank_mono (hco.1 h)
    omega
  · rw [g68k_iso_iff]
    constructor
    · intro h
      have h' : Module.finrank ℝ W = Module.finrank ℝ (B.orthogonal W) := by
        rw [IsLagrangian] at h; exact congrArg (fun U : Submodule ℝ V => Module.finrank ℝ U) h
      refine ⟨h.le, by omega⟩
    · rintro ⟨h1, h2⟩
      exact Submodule.eq_of_le_of_finrank_eq h1 (by omega)
  · intro h
    rw [IsLagrangian] at h
    refine ⟨(g68k_iso_iff B W).2 h.le, hco.2 h.ge⟩



end
