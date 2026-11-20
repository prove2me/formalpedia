-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck151_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T21:12:02.512407+00:00
-- url     : https://prove2.me/submissions/0211dd72-4d51-47fb-ace3-b2f7b6861d50

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 151. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

set_option Elab.async false

theorem degreeCheck151_2_2_p0 : degreeP151 [13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 12, 4] := by
  decide +kernel

theorem degreeCheck151_2_2_p1 : degreeP151 [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 4] := by
  decide +kernel

theorem degreeCheck151_2_2_p2 : degreeP151 [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 3] := by
  decide +kernel

theorem degreeCheck151_2_2_rows : ∀ rs ∈ ([[13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 12, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 3]] : List (List ℕ)), degreeP151 rs := by
  intro rs hrs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrs
  rcases hrs with rfl | rfl | rfl
  · exact degreeCheck151_2_2_p0
  · exact degreeCheck151_2_2_p1
  · exact degreeCheck151_2_2_p2

theorem degreeCheck151_2_2_r0 : ∀ c ∈ List.range 6, ∀ rs ∈ rowsWithin 151 (prefixBounds 14 23 3 3 ++ [(0+1,(degreeRows151_0.take (0+1)).sum-1)]) (prefixBounds 14 23 3 3 ++ [(c+1,(degreeRows151_0.take (c+1)).sum-1)]), rs ∈ ([[13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 12, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 3]] : List (List ℕ)) := by
  decide +kernel

theorem degreeCheck151_2_2_r1 : ∀ c ∈ List.range 6, ∀ rs ∈ rowsWithin 151 (prefixBounds 14 23 3 3 ++ [(1+1,(degreeRows151_0.take (1+1)).sum-1)]) (prefixBounds 14 23 3 3 ++ [(c+1,(degreeRows151_0.take (c+1)).sum-1)]), rs ∈ ([[13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 12, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 3]] : List (List ℕ)) := by
  decide +kernel

theorem degreeCheck151_2_2_r2 : ∀ c ∈ List.range 6, ∀ rs ∈ rowsWithin 151 (prefixBounds 14 23 3 3 ++ [(2+1,(degreeRows151_0.take (2+1)).sum-1)]) (prefixBounds 14 23 3 3 ++ [(c+1,(degreeRows151_0.take (c+1)).sum-1)]), rs ∈ ([[13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 12, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 3]] : List (List ℕ)) := by
  decide +kernel

theorem degreeCheck151_2_2_r3 : ∀ c ∈ List.range 6, ∀ rs ∈ rowsWithin 151 (prefixBounds 14 23 3 3 ++ [(3+1,(degreeRows151_0.take (3+1)).sum-1)]) (prefixBounds 14 23 3 3 ++ [(c+1,(degreeRows151_0.take (c+1)).sum-1)]), rs ∈ ([[13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 12, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 3]] : List (List ℕ)) := by
  decide +kernel

theorem degreeCheck151_2_2_r4 : ∀ c ∈ List.range 6, ∀ rs ∈ rowsWithin 151 (prefixBounds 14 23 3 3 ++ [(4+1,(degreeRows151_0.take (4+1)).sum-1)]) (prefixBounds 14 23 3 3 ++ [(c+1,(degreeRows151_0.take (c+1)).sum-1)]), rs ∈ ([[13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 12, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 3]] : List (List ℕ)) := by
  decide +kernel

theorem degreeCheck151_2_2_r5 : ∀ c ∈ List.range 6, ∀ rs ∈ rowsWithin 151 (prefixBounds 14 23 3 3 ++ [(5+1,(degreeRows151_0.take (5+1)).sum-1)]) (prefixBounds 14 23 3 3 ++ [(c+1,(degreeRows151_0.take (c+1)).sum-1)]), rs ∈ ([[13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 12, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 4], [13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12, 3]] : List (List ℕ)) := by
  decide +kernel

theorem degreeCheck151_2_2_easy : ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
    ¬(a < 6 ∧ c < 6) → impossibleBounds 151 (prefixBounds 14 23 3 3 ++ [(a+1,(degreeRows151_0.take (a+1)).sum-1)]) (prefixBounds 14 23 3 3 ++ [(c+1,(degreeRows151_0.take (c+1)).sum-1)]) := by
  decide +kernel

lemma degreeCheck151_2_2_oai :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 3 3 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  intro a ha c hc
  by_cases hac : a < 6 ∧ c < 6
  · refine Or.inr (Or.inr (Or.inr fun rs hrs => degreeCheck151_2_2_rows rs ?_))
    obtain ⟨h1, h2⟩ := hac
    interval_cases a
    · exact degreeCheck151_2_2_r0 c (List.mem_range.2 h2) rs hrs
    · exact degreeCheck151_2_2_r1 c (List.mem_range.2 h2) rs hrs
    · exact degreeCheck151_2_2_r2 c (List.mem_range.2 h2) rs hrs
    · exact degreeCheck151_2_2_r3 c (List.mem_range.2 h2) rs hrs
    · exact degreeCheck151_2_2_r4 c (List.mem_range.2 h2) rs hrs
    · exact degreeCheck151_2_2_r5 c (List.mem_range.2 h2) rs hrs
  · exact Or.inr (Or.inr (Or.inl (degreeCheck151_2_2_easy a ha c hc hac)))

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck151_2_2_oai := @OAI.UniversalTensorSquare.degreeCheck151_2_2_oai
