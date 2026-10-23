-- Prove2me | solution 1 for PermInvConvex.Sparsity.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T05:57:29.931714+00:00
-- url     : https://prove2.me/submissions/09d0ae1d-da76-445f-ac76-bc3ea12236b0

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting
import Theorems.Thm_ModernConvex_Spectral_majorization_principle

open PermInvConvex.Sparsity ModernConvex.Spectral

theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsPermInvNorm f)
    (x y : Fin n → ℝ) (hxy : Majorizes x y) : f y ≤ f x := by
  have hy : y ∈ permHull x := by
    rw [majorization_principle]
    exact hxy
  have hconv : Convex ℝ {z : Fin n → ℝ | f z ≤ f x} := by
    intro u hu v hv a b ha hb hab
    change f (a • u + b • v) ≤ f x
    calc
      f (a • u + b • v) ≤ f (a • u) + f (b • v) := hf.add_le _ _
      _ = a * f u + b * f v := by
        rw [hf.smul, hf.smul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * f x + b * f x :=
        add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
      _ = f x := by rw [← add_mul, hab, one_mul]
  have hperm : Set.range (fun σ : Equiv.Perm (Fin n) => x ∘ σ) ⊆
      {z : Fin n → ℝ | f z ≤ f x} := by
    rintro _ ⟨σ, rfl⟩
    exact le_of_eq (hf.perm σ x)
  exact convexHull_min hperm hconv hy
