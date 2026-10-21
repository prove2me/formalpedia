-- Prove2me | solution 1 for ShortestGCS.MICP.remark_5_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:23:41.92965+00:00
-- url     : https://prove2.me/submissions/69109455-36ff-4fd8-a6a0-9ebc7c8528f2

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_ShortestGCS_MICP_Setting

set_option autoImplicit false
open ShortestGCS.MICP

theorem sgm_key {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n) (v : V)
    (hloop : (v, v) ∉ G.E) (c : V × V → ℝ) (d : ℝ) (y : V × V → ℝ) (x : V → Fin n → ℝ)
    (z z' : V × V → Fin n → ℝ) (h : IsFeasible52 G y x z z') :
    ∑ e ∈ inEdges G v, c e • z' e + ∑ e ∈ outEdges G v, c e • z e + d • x v =
      (∑ e ∈ edgesAt G v, c e * y e + d) • x v := by
  have hdisj : Disjoint (inEdges G v) (outEdges G v) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [inEdges, outEdges, Finset.mem_filter] at he1 he2
    apply hloop
    have : e = (v, v) := Prod.ext he2.2 he1.2
    rw [← this]; exact he1.1
  have hunion : edgesAt G v = inEdges G v ∪ outEdges G v := by
    ext e
    simp only [edgesAt, inEdges, outEdges, Finset.mem_filter, Finset.mem_union]
    tauto
  have h1 : ∑ e ∈ inEdges G v, c e • z' e = (∑ e ∈ inEdges G v, c e * y e) • x v := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro e he
    simp only [inEdges, Finset.mem_filter] at he
    rw [(h.bilinear e he.1).2, he.2, smul_smul]
  have h2 : ∑ e ∈ outEdges G v, c e • z e = (∑ e ∈ outEdges G v, c e * y e) • x v := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro e he
    simp only [outEdges, Finset.mem_filter] at he
    rw [(h.bilinear e he.1).1, he.2, smul_smul]
  rw [h1, h2, hunion, Finset.sum_union hdisj, add_smul, add_smul]

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n) (hG : IsGCS G)
    (v : V) (hloop : (v, v) ∉ G.E) (c : V × V → ℝ) (d : ℝ)
    (hvalid : ∀ (y : V × V → ℝ) (x : V → Fin n → ℝ) (z z' : V × V → Fin n → ℝ),
      IsFeasible52 G y x z z' → ∑ e ∈ edgesAt G v, c e * y e + d = 0) :
    ∀ (y : V × V → ℝ) (x : V → Fin n → ℝ) (z z' : V × V → Fin n → ℝ),
      IsFeasible52 G y x z z' →
        ∑ e ∈ inEdges G v, c e • z' e + ∑ e ∈ outEdges G v, c e • z e + d • x v = 0 := by
  intro y x z z' hf
  rw [sgm_key G v hloop c d y x z z' hf, hvalid y x z z' hf, zero_smul]
