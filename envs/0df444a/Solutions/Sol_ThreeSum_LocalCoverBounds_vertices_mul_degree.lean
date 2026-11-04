-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.vertices_mul_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:12.324103+00:00
-- url     : https://prove2.me/submissions/a5dd3b5f-fc55-41b3-9093-eb65196b96de

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Theorems.Thm_ThreeSum_LayerCounts_vertex_degree_identity


set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (L h : ℕ) :
    vertexCount L h * degree L h = outputCount L h * groupSize h :=
  LayerCounts.vertex_degree_identity L h
end ThreeSum.LocalCoverBounds
