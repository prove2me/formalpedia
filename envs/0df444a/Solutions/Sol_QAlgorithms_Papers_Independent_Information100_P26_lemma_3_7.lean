-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:27:38.689911+00:00
-- url     : https://prove2.me/submissions/df7b2125-d22c-4326-b601-ad6873e5140c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

open Module
open scoped Matrix ComplexOrder

namespace X6P26L

/-- Sylvester rank inequality for linear maps -/
theorem sylv {K V W Z : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] [AddCommGroup Z] [Module K Z]
    [FiniteDimensional K Z] (f : W →ₗ[K] Z) (g : V →ₗ[K] W) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.range g) ≤
      finrank K W + finrank K (LinearMap.range (f ∘ₗ g)) := by
  set R := LinearMap.range g
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict R)
  have h2 : LinearMap.range (f.domRestrict R) = LinearMap.range (f ∘ₗ g) := by
    rw [LinearMap.range_comp, LinearMap.range_domRestrict]
  have h3 : finrank K (LinearMap.ker (f.domRestrict R)) ≤ finrank K (LinearMap.ker f) := by
    rw [LinearMap.ker_domRestrict]
    rw [← Submodule.finrank_map_subtype_eq]
    exact Submodule.finrank_mono (Submodule.map_comap_le _ _)
  have h4 := LinearMap.finrank_range_add_finrank_ker f
  rw [h2] at h1
  omega

theorem msylv {s d : ℕ} (A : Matrix (Fin d) (Fin s) ℂ) (B : Matrix (Fin s) (Fin d) ℂ) :
    A.rank + B.rank ≤ s + (A * B).rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_mul]
  have := sylv A.mulVecLin B.mulVecLin
  simpa using this

theorem span_smul {s d : ℕ} (c : Fin s → ℂ) (hc : ∀ k, c k ≠ 0) (u : Fin s → Fin d → ℂ) :
    Submodule.span ℂ (Set.range fun k => c k • u k) = Submodule.span ℂ (Set.range u) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have : u k = (c k)⁻¹ • (c k • u k) := by rw [smul_smul, inv_mul_cancel₀ (hc k), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem main {d s : ℕ} (c : Fin s → ℂ) (u v : Fin s → Fin d → ℂ) (hc : ∀ k, c k ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range u)) +
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) ≤
      s + (Matrix.of (fun i j => ∑ k, c k * u k i * star (v k j)) : Matrix (Fin d) (Fin d) ℂ).rank := by
  set A : Matrix (Fin d) (Fin s) ℂ := Matrix.of fun i k => c k * u k i
  set V : Matrix (Fin d) (Fin s) ℂ := Matrix.of fun j k => v k j
  have hAB : (Matrix.of (fun i j => ∑ k, c k * u k i * star (v k j)) :
      Matrix (Fin d) (Fin d) ℂ) = A * Vᴴ := by
    ext i j; simp [A, V, Matrix.mul_apply]
  have hA : A.rank = Module.finrank ℂ (Submodule.span ℂ (Set.range u)) := by
    rw [Matrix.rank_eq_finrank_span_cols, ← span_smul c hc u]
    congr
  have hV : Vᴴ.rank = Module.finrank ℂ (Submodule.span ℂ (Set.range v)) := by
    rw [Matrix.rank_conjTranspose, Matrix.rank_eq_finrank_span_cols]
    congr
  rw [hAB, ← hA, ← hV]
  exact msylv A Vᴴ

end X6P26L

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d s : ℕ} (hd : 0 < d) (X : Mat d)
    (c : Fin s → ℂ) (u v : Fin s → Vec d) (hc : ∀ k, c k ≠ 0)
    (hX : X = ∑ k, c k • outer (u k) (v k)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range u)) +
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) ≤ s + X.rank := by
  have hX' : X = (Matrix.of (fun i j => ∑ k, c k * u k i * star (v k j)) :
      Matrix (Fin d) (Fin d) ℂ) := by
    rw [hX]; ext i j
    simp [outer, Matrix.sum_apply, mul_assoc]
  rw [hX']
  exact X6P26L.main c u v hc
