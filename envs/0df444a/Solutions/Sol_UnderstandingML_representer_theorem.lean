-- Prove2me | solution 1 for UnderstandingML.representer_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:56:23.357733+00:00
-- url     : https://prove2.me/submissions/56428255-120c-4911-9072-9ab96da0f176

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

universe u

open UnderstandingML

theorem solution {X : Type u} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {m : ℕ} (ψ : X → F) (x : Fin m → X)
    (f : (Fin m → ℝ) → ℝ) (R : ℝ → ℝ) (hR : MonotoneOn R (Set.Ici 0)) (wstar : F)
    (hopt : ∀ w, kernelObjective ψ x f R wstar ≤ kernelObjective ψ x f R w) :
    ∃ α : Fin m → ℝ, ∀ w,
      kernelObjective ψ x f R (∑ i, α i • ψ (x i)) ≤ kernelObjective ψ x f R w := by
  -- `U` is the span of the mapped examples and `p` the orthogonal projection of `wstar` onto it.
  let U : Submodule ℝ F := Submodule.span ℝ (Set.range fun i => ψ (x i))
  haveI : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  let p : F := U.starProjection wstar
  have hpU : p ∈ U := U.starProjection_apply_mem wstar
  have hperp : wstar - p ∈ Uᗮ := U.sub_starProjection_mem_orthogonal wstar
  have hnorm : ‖p‖ ≤ ‖wstar‖ := U.norm_starProjection_apply_le wstar
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hpU
  refine ⟨α, fun w => le_trans ?_ (hopt w)⟩
  rw [hα]
  unfold kernelObjective
  have hinner : ∀ i, ⟪p, ψ (x i)⟫_ℝ = ⟪wstar, ψ (x i)⟫_ℝ := by
    intro i
    have hmem : ψ (x i) ∈ U := Submodule.subset_span ⟨i, rfl⟩
    have h0 : ⟪ψ (x i), wstar - p⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hmem hperp
    rw [inner_sub_right] at h0
    have h1 := real_inner_comm wstar (ψ (x i))
    have h2 := real_inner_comm p (ψ (x i))
    linarith
  have hf : (fun i ↦ ⟪p, ψ (x i)⟫_ℝ) = fun i ↦ ⟪wstar, ψ (x i)⟫_ℝ := funext hinner
  rw [hf]
  have hR' : R ‖p‖ ≤ R ‖wstar‖ :=
    hR (Set.mem_Ici.2 (norm_nonneg _)) (Set.mem_Ici.2 (norm_nonneg _)) hnorm
  linarith
