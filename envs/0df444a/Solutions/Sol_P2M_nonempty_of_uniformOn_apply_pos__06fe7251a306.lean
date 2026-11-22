-- Prove2me | solution 1 for P2M_nonempty_of_uniformOn_apply_pos__06fe7251a306
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:03.831614+00:00
-- url     : https://prove2.me/submissions/978a989e-8b00-436c-9371-9219cdee9f56

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] {s t : Set Ω}
    (h : 0 < uniformOn s t) (hs : MeasurableSet s) :
    (s ∩ t).Nonempty := by
  rw [uniformOn, cond_apply hs] at h
  have : Measure.count (s ∩ t) ≠ 0 := by contrapose! h; simp [h]
  rwa [Measure.count_ne_zero_iff] at this
