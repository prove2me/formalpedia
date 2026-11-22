-- Prove2me | solution 1 for Paper.Hypergraph.convex_modularCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:11.492912+00:00
-- url     : https://prove2.me/submissions/acee9f80-9313-4490-a923-4f94973160bd

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) : Convex ℝ H.modularCube := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_Icc (0 : ℕ → ℝ) 1 hx.1 hy.1 ha hb hab, ?_⟩
  intro e he
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
  have h1 := mul_le_mul_of_nonneg_left (hx.2 e he) ha
  have h2 := mul_le_mul_of_nonneg_left (hy.2 e he) hb
  nlinarith
end Paper.Hypergraph
