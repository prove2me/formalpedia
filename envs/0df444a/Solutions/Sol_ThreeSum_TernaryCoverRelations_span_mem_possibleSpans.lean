-- Prove2me | solution 1 for ThreeSum.TernaryCoverRelations.span_mem_possibleSpans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:30.157255+00:00
-- url     : https://prove2.me/submissions/a6a62531-d6d8-4da6-a2e3-075f02c941ea

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRelations
open Finset
variable {K : Type*} [Field K]
namespace ThreeSum.TernaryCoverRelations
theorem _root_.solution {d : ℕ} {σ : Type*} (columns : σ → Fin d → Fin 3) :
    Submodule.span K (Set.range fun j => digitVector (K := K) (columns j)) ∈
      possibleSpans K d := by
  classical
  let S := Submodule.span K (Set.range fun j => digitVector (K := K) (columns j))
  let r := Module.finrank K S
  have hr : r ≤ d := by
    have h := Submodule.finrank_le S
    simpa [r, Module.finrank_fintype_fun_eq_card] using h
  obtain ⟨f, hf, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq K
    (Set.range fun j => digitVector (K := K) (columns j))
  have hspanS : Submodule.span K (Set.range f) = S := hspan
  let chosen : Fin r → Fin d → Fin 3 := fun i => columns (Classical.choose (hf i))
  have hchosen (i : Fin r) : digitVector (K := K) (chosen i) = f i :=
    Classical.choose_spec (hf i)
  let code : Fin d → Fin d → Fin 3 := fun i =>
    if hi : i.val < r then chosen ⟨i.val, hi⟩ else fun _ => 0
  have hcode : spanCode (K := K) d code = S := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      dsimp [code]
      split_ifs with hi
      · rw [hchosen]
        rw [← hspanS]
        exact Submodule.subset_span (Set.mem_range_self _)
      · have hz : digitVector (K := K) (fun _ : Fin d => (0 : Fin 3)) = 0 := by
          funext i
          simp [digitVector]
        rw [hz]
        exact S.zero_mem
    · rw [← hspanS]
      apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      let j : Fin d := ⟨i.val, lt_of_lt_of_le i.isLt hr⟩
      have heq : digitVector (K := K) (code j) = f i := by
        have hi : i.val < r := i.isLt
        simp only [code, j, dif_pos hi]
        exact hchosen i
      rw [← heq]
      exact Submodule.subset_span (Set.mem_range_self j)
  apply mem_image.mpr
  exact ⟨code, mem_univ _, hcode⟩
end ThreeSum.TernaryCoverRelations
