-- Prove2me | solution 1 for UnifiedMEstimator.General.section24_regularizer_bound_on_C
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:25:28.891179+00:00
-- url     : https://prove2.me/submissions/ba2236b8-abae-4a21-a6f1-9e71c4f81c70

import Definitions.Def_UnifiedMEstimator_General_Core
import Mathlib.Tactic

open Finset
open UnifiedMEstimator.General
namespace CUnified
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem norm_bound (R : E → ℝ) (hR : IsNormFn R) : ∃ L : ℝ,0 ≤ L ∧ ∀ x,R x ≤ L*‖x‖ := by
  classical
  let b:=stdOrthonormalBasis ℝ E
  have hsum (s : Finset (Fin (Module.finrank ℝ E))) (x : Fin (Module.finrank ℝ E) → E) : R (∑ i∈s,x i) ≤ ∑ i∈s,R (x i) := by
    induction s using Finset.induction with
    | empty => simpa using (le_of_eq ((hR.eq_zero_iff 0).mpr rfl))
    | insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi]
      have htri:=hR.triangle (x i) (∑ j∈s,x j)
      linarith
  refine ⟨∑ i,R (b i),Finset.sum_nonneg (fun i _=>hR.nonneg _),fun x=>?_⟩
  calc
    R x=R (∑ i,b.repr x i • b i) := by rw [b.sum_repr]
    _ ≤ ∑ i,R (b.repr x i • b i) := hsum _ _
    _ ≤ ∑ i,‖x‖*R (b i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hR.smul_abs,b.repr_apply_apply]
      apply mul_le_mul_of_nonneg_right _ (hR.nonneg _)
      simpa [b.norm_eq_one] using abs_real_inner_le_norm (b i) x
    _=(∑ i,R (b i))*‖x‖ := by rw [←Finset.mul_sum,mul_comm]

theorem compat_bdd (R : E → ℝ) (hR : IsNormFn R) (S : Submodule ℝ E) :
    BddAbove {r : ℝ | ∃ u∈S,u≠0 ∧ r=R u/‖u‖} := by
  obtain ⟨L,hL,hb⟩:=norm_bound R hR
  refine ⟨L,?_⟩
  rintro r ⟨u,hu,hune,rfl⟩
  exact (div_le_iff₀ (norm_pos_iff.mpr hune)).mpr (hb u)

theorem compat_nonneg (R : E → ℝ) (hR : IsNormFn R) (S : Submodule ℝ E) : 0 ≤ compat R S := by
  classical
  by_cases hs : ({r : ℝ | ∃ u∈S,u≠0 ∧ r=R u/‖u‖} : Set ℝ).Nonempty
  · obtain ⟨r,u,hu,hun,rfl⟩:=hs
    apply le_trans (div_nonneg (hR.nonneg u) (norm_nonneg u))
    exact le_csSup (compat_bdd R hR S) ⟨u,hu,hun,rfl⟩
  · have he : ({r : ℝ | ∃ u∈S,u≠0 ∧ r=R u/‖u‖} : Set ℝ)=∅ := Set.not_nonempty_iff_eq_empty.mp hs
    simp [compat,he]

theorem le_compat (R : E → ℝ) (hR : IsNormFn R) (S : Submodule ℝ E) (u : E) (hu : u∈S) :
    R u ≤ compat R S*‖u‖ := by
  by_cases h : u=0
  · subst u
    simp [(hR.eq_zero_iff 0).mpr rfl]
  · have hh : R u/‖u‖ ≤ compat R S:=le_csSup (compat_bdd R hR S) ⟨u,hu,h,rfl⟩
    exact (div_le_iff₀ (norm_pos_iff.mpr h)).mp hh

end CUnified

theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (R : E → ℝ) (M Mbar : Submodule ℝ E) (θstar Δ : E)
    (hR : IsNormFn R) (hle : M ≤ Mbar) (hθ : θstar ∈ M)
    (hΔ : Δ ∈ setC R M Mbar θstar) :
    R (Mbarᗮ.starProjection Δ) ≤ 3 * R (Mbar.starProjection Δ) ∧
    R Δ ≤ R (Mbarᗮ.starProjection Δ) + R (Mbar.starProjection Δ) ∧
    R (Mbarᗮ.starProjection Δ) + R (Mbar.starProjection Δ) ≤ 4 * R (Mbar.starProjection Δ) ∧
    4 * R (Mbar.starProjection Δ) ≤ 4 * compat R Mbar * ‖Δ‖ := by
  have hzero := (hR.eq_zero_iff 0).mpr rfl
  have ht := M.starProjection_orthogonal_apply_eq_zero hθ
  change R (Mbarᗮ.starProjection Δ) ≤ 3*R (Mbar.starProjection Δ)+4*R (Mᗮ.starProjection θstar) at hΔ
  rw [ht,hzero,mul_zero,add_zero] at hΔ
  have htriangle := hR.triangle (Mbar.starProjection Δ) (Mbarᗮ.starProjection Δ)
  rw [Mbar.starProjection_add_starProjection_orthogonal] at htriangle
  have hcompat := CUnified.le_compat R hR Mbar (Mbar.starProjection Δ) (Mbar.starProjection_apply_mem Δ)
  have hproj := Mbar.norm_starProjection_apply_le Δ
  have hbound:=hcompat.trans (mul_le_mul_of_nonneg_left hproj (CUnified.compat_nonneg R hR Mbar))
  exact ⟨hΔ,by linarith,by linarith,by nlinarith⟩
