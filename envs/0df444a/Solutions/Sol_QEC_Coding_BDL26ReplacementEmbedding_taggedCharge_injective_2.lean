-- Prove2me | solution 2 for QEC.Coding.BDL26ReplacementEmbedding.taggedCharge_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:59:32.897793+00:00
-- url     : https://prove2.me/submissions/025a9423-8a43-44ea-ba77-5cc73f9feeea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (S : OddScale) :
    Function.Injective (fun c : FlatCell S => (chargeTag S c, charge S c)) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (congrArg (fun p => p.2) hab)
  · rcases b with b | b <;> simp [chargeTag] at hab
  · rcases a with a | a <;> simp [chargeTag] at hab
  · rcases a with a | a <;> rcases b with b | b
    · have h := congrArg (fun p : Fin 3 × PositiveCell S => (p.2.1, p.2.2.1)) hab
      have h' : a = b := by simpa [charge] using h
      exact congrArg (fun x => Sum.inr (Sum.inl x)) h'
    · simp [chargeTag] at hab
    · simp [chargeTag] at hab
    · have h := congrArg (fun p : Fin 3 × PositiveCell S => (p.2.1, p.2.2.2)) hab
      have h' : a = b := by simpa [charge] using h
      exact congrArg (fun x => Sum.inr (Sum.inr x)) h'
end QEC.Coding.BDL26ReplacementEmbedding
