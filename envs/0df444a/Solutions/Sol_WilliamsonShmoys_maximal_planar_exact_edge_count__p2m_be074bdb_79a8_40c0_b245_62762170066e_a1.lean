-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-02T09:55:06.707481+00:00
-- url     : https://prove2.me/submissions/c980e239-c63e-4231-9a79-0f923e352ee6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (K : SimpleGraph V) (dK : DecidableRel K.Adj)
        (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
        (hmax : ∀ L : SimpleGraph V, K ≤ L →
          WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K),
        (letI : DecidableRel K.Adj := dK;
          3 * Fintype.card V - 6 = K.edgeFinset.card)) := by
  intro h
  let p : Bool → ℝ × ℝ := fun b => if b = false then (0, 0) else (1, 0)
  let arc : Bool → Bool → ℝ → ℝ × ℝ := fun _ _ t => (t, 0)
  have hdrawing : WilliamsonShmoys.HasPlanarDrawingOn (⊤ : SimpleGraph Bool) := by
    refine ⟨p, arc, ?_, ?_, ?_⟩
    · intro a b hab
      cases a <;> cases b <;> simp [p] at hab ⊢
    · intro u v huv hadj
      have huv' : u = false ∧ v = true := Bool.lt_iff.mp huv
      rcases huv' with ⟨rfl, rfl⟩
      refine ⟨(continuous_id.prodMk continuous_const).continuousOn, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy heq
        exact congrArg Prod.fst heq
      · simp [arc, p]
      · simp [arc, p]
      · intro t ht w
        have ht' : 0 < t ∧ t < 1 := by simpa only [Set.mem_Ioo] using ht
        cases w <;> simp [arc, p] <;> linarith
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      have huv' : u = false ∧ v = true := Bool.lt_iff.mp huv
      have hxy' : x = false ∧ y = true := Bool.lt_iff.mp hxy
      rcases huv' with ⟨rfl, rfl⟩
      rcases hxy' with ⟨rfl, rfl⟩
      exact (hne rfl).elim
  have hmaximal : ∀ L : SimpleGraph Bool, (⊤ : SimpleGraph Bool) ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ ⊤ := by
    intro L htop hL
    exact le_top
  let d : DecidableRel (⊤ : SimpleGraph Bool).Adj := inferInstance
  have hbad := h (V := Bool) (⊤ : SimpleGraph Bool) d hdrawing hmaximal
  letI : DecidableRel (⊤ : SimpleGraph Bool).Adj := d
  change 3 * Fintype.card Bool - 6 = (⊤ : SimpleGraph Bool).edgeFinset.card at hbad
  have hcard : (⊤ : SimpleGraph Bool).edgeFinset.card = 1 := by
    simpa [Fintype.card_bool, Nat.choose] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Bool))
  rw [Fintype.card_bool, hcard] at hbad
  norm_num at hbad
