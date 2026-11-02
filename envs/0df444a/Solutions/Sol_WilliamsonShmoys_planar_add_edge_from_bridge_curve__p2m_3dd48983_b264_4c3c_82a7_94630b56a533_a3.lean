-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_edge_from_bridge_curve__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T02:05:22.558901+00:00
-- url     : https://prove2.me/submissions/5662254a-c28a-48ad-afa6-67e4286487e4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_union_of_bridge_setup__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V}
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (gamma : ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hedge : ∀ a b, a < b → G.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hdisjoint : ∀ a b c d, a < b → c < d → G.Adj a b → G.Adj c d →
      (a, b) ≠ (c, d) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc c d s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn gamma (Set.Icc 0 1))
    (hstart : gamma 0 = p u) (hend : gamma 1 = p v)
    (hvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (hedge_intersections : ∀ a b, a < b → G.Adj a b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        gamma t = arc a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by
  let K : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))
  have huv : u ≠ v := by
    intro huv
    have hEq : gamma 0 = gamma 1 := by
      calc
        gamma 0 = p u := hstart
        _ = p v := by rw [huv]
        _ = gamma 1 := hend.symm
    have h01 : (0 : ℝ) = 1 :=
      hinj (by norm_num) (by norm_num) hEq
    norm_num at h01
  have hdata :
      ∃ (p₀ : V → ℝ × ℝ) (arc₀ : V → V → ℝ → ℝ × ℝ)
        (bridge : ℝ → ℝ × ℝ),
        Function.Injective p₀ ∧
        (∀ a b, a < b → G.Adj a b →
          ContinuousOn (arc₀ a b) (Set.Icc 0 1) ∧
          Set.InjOn (arc₀ a b) (Set.Icc 0 1) ∧
          arc₀ a b 0 = p₀ a ∧ arc₀ a b 1 = p₀ b ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc₀ a b t ≠ p₀ w) ∧
        (∀ a b x y, a < b → x < y → G.Adj a b → G.Adj x y →
          (a, b) ≠ (x, y) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            arc₀ a b t = arc₀ x y s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
        ContinuousOn bridge (Set.Icc 0 1) ∧
        Set.InjOn bridge (Set.Icc 0 1) ∧
        bridge 0 = p₀ u ∧ bridge 1 = p₀ v ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p₀ w) ∧
        (∀ a b, a < b → G.Adj a b →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            bridge t = arc₀ a b s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
    exact ⟨p, arc, gamma, hp, hedge, hdisjoint,
      hcont, hinj, hstart, hend, hvertices, hedge_intersections⟩
  have hKdraw : HasPlanarDrawingOn K := by
    dsimp [K]
    exact WilliamsonShmoys.planar_drawing_union_of_bridge_setup__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
      G u v hdata
  refine ⟨K, ?_, hKdraw, ?_⟩
  · exact le_sup_left
  · have hEdge : (SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Adj u v := by
      simp [SimpleGraph.fromEdgeSet, huv]
    have hle : SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V)) ≤ K := le_sup_right
    exact hle hEdge
