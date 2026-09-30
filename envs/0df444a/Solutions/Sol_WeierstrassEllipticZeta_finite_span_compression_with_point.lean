-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_span_compression_with_point
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T03:13:33.253801+00:00
-- url     : https://prove2.me/submissions/029b742f-4e4a-4c87-b2ce-2908768e9ef7

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

noncomputable section

theorem solution
    (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V]
    (f : ι → V) (S : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ S) :
    ∃ T : Finset ι, T ⊆ S ∧ i₀ ∈ T ∧
      Submodule.span K (f '' (T : Set ι)) = Submodule.span K (f '' (S : Set ι)) ∧
      T.card ≤ Module.finrank K (Submodule.span K (f '' (S : Set ι))) + 1 := by
  classical
  let : FiniteDimensional K (Submodule.span K (f '' (S : Set ι))) :=
    FiniteDimensional.span_of_finite K (S.finite_toSet.image f)
  obtain ⟨v, hv, hvspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (f '' (S : Set ι))
  have hchoices (i : Fin (Module.finrank K (Submodule.span K (f '' (S : Set ι))))) :
      ∃ j ∈ S, f j = v i := hv i
  choose g hg hfg using hchoices
  let T₀ : Finset ι := Finset.univ.image g
  have himage : f '' (T₀ : Set ι) = Set.range v := by
    ext w
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, (hfg i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hfg i⟩
  have hspan₀ : Submodule.span K (f '' (T₀ : Set ι)) =
      Submodule.span K (f '' (S : Set ι)) := by
    rw [himage]
    exact hvspan
  have hsub : insert i₀ T₀ ⊆ S := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi₀
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact hg i
  refine ⟨insert i₀ T₀, hsub, Finset.mem_insert_self _ _, ?_, ?_⟩
  · apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hsub)
    · rw [← hspan₀]
      exact Submodule.span_mono (Set.image_mono (Finset.subset_insert _ _))
  · calc
      (insert i₀ T₀).card ≤ T₀.card + 1 := Finset.card_insert_le _ _
      _ ≤ Module.finrank K (Submodule.span K (f '' (S : Set ι))) + 1 := by
        apply Nat.add_le_add_right
        simpa only [Finset.card_univ, Fintype.card_fin] using
          (Finset.card_image_le (s := Finset.univ) (f := g))
