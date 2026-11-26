-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_restrict_induced__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T00:34:52.055289+00:00
-- url     : https://prove2.me/submissions/826e0a6c-9002-410f-86be-3251ad73a17b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

namespace P2MHole01_9318962e
theorem solution (f : ℝ → ℝ × ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) (1 : ℝ))) :
  ContinuousOn (fun (t : ℝ) => f ((1 : ℝ) - t)) (Set.Icc (0 : ℝ) (1 : ℝ)) := by
  exact hf.comp (continuousOn_const.sub continuousOn_id) (fun x hx => ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩)
end P2MHole01_9318962e

-- riskiest
/-- Reversing an arc, `t ↦ f (1 - t)`, preserves continuity on `Icc 0 1`
    (pre-proved step, bench-v12b outline 1 step 3). -/
theorem arc_rev_continuousOn (f : ℝ → ℝ × ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) (1 : ℝ))) :
  ContinuousOn (fun (t : ℝ) => f ((1 : ℝ) - t)) (Set.Icc (0 : ℝ) (1 : ℝ)) := by
  (first | exact P2MHole01_9318962e.solution f hf | (apply P2MHole01_9318962e.solution <;> assumption))

namespace P2MHole02_03a7b940
theorem solution (f : ℝ → ℝ × ℝ) (hf : Set.InjOn f (Set.Icc (0 : ℝ) (1 : ℝ))) :
  Set.InjOn (fun (t : ℝ) => f ((1 : ℝ) - t)) (Set.Icc (0 : ℝ) (1 : ℝ)) := by
  intro x hx y hy h
  rcases hx with ⟨h0x, hx1⟩
  rcases hy with ⟨h0y, hy1⟩
  have h1 : (1 : ℝ) - x ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by refine ⟨?_, ?_⟩ <;> linarith
  have h2 : (1 : ℝ) - y ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by refine ⟨?_, ?_⟩ <;> linarith
  have h3 : (1 : ℝ) - x = (1 : ℝ) - y := hf (x₁ := 1 - x) (x₂ := 1 - y) h1 h2 (by simpa using h)
  exact (by linarith)
end P2MHole02_03a7b940

/-- Reversing an arc preserves injectivity on `Icc 0 1`
    (pre-proved step, bench-v12b outline 1 step 4). -/
theorem arc_rev_injOn (f : ℝ → ℝ × ℝ)
    (hf : Set.InjOn f (Set.Icc (0 : ℝ) (1 : ℝ))) :
  Set.InjOn (fun (t : ℝ) => f ((1 : ℝ) - t)) (Set.Icc (0 : ℝ) (1 : ℝ)) := by
  (first | exact P2MHole02_03a7b940.solution f hf | (apply P2MHole02_03a7b940.solution <;> assumption))

/-- `1 - t` stays in `Ioo 0 1` for `t ∈ Ioo 0 1` (glue lemma, closed here). -/
theorem one_sub_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 1 - t ∈ Set.Ioo 0 1 := by
  exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- `1 - t` stays in `Icc 0 1` for `t ∈ Icc 0 1` (glue lemma, closed here). -/
theorem one_sub_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : 1 - t ∈ Set.Icc 0 1 := by
  exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- `t` is an endpoint of `Icc 0 1` iff `1 - t` is (glue lemma, closed here). -/
theorem one_sub_endpoint_iff {t : ℝ} :
    (t = (0 : ℝ) ∨ t = (1 : ℝ)) ↔ ((1 : ℝ) - t = (0 : ℝ) ∨ (1 : ℝ) - t = (1 : ℝ)) := by
  refine ⟨fun h => h.elim (fun h0 => Or.inr (by linarith [h0])) (fun h1 => Or.inl (by linarith [h1])),
    fun h => h.elim (fun h0 => Or.inr (by linarith [h0])) (fun h1 => Or.inl (by linarith [h1]))⟩

/-- Coercion to `V` reflects distinctness of ordered pairs. (glue lemma) -/
theorem coe_pair_ne {V : Type} {s : Set V} {u v x y : {x // x ∈ s}} (hne : (u, v) ≠ (x, y)) :
    (Subtype.val u, Subtype.val v) ≠ (Subtype.val x, Subtype.val y) := by
  intro h
  exact hne (Prod.ext (Subtype.ext ((Prod.ext_iff.1 h).1)) (Subtype.ext ((Prod.ext_iff.1 h).2)))

/-- From `u < v` in the subtype order, `↑u ≠ ↑v` in `V`. (glue lemma) -/
theorem sub_ne_of_lt_co {V : Type} {s : Set V} [LinearOrder {x // x ∈ s}]
    {u v : {x // x ∈ s}} (huv : u < v) : (↑u : V) ≠ (↑v : V) := by
  intro heq
  exact lt_irrefl _ ((Subtype.ext heq).symm ▸ huv)

/-- In V's linear order, `¬ a < b` and `a ≠ b` give `b < a`. (glue lemma) -/
theorem sub_lt_of_not_lt_co {V : Type} [LinearOrder V] {a b : V}
    (h : ¬ a < b) (hne : a ≠ b) : b < a := by
  exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)

/-- With `u < v` and `x < y` in the subtype order, `(u, v) ≠ (y, x)`. (glue lemma) -/
theorem rev_ne {V : Type} {s : Set V} [LinearOrder {x // x ∈ s}]
    {u v x y : {x // x ∈ s}} (huv : u < v) (hxy : x < y) : (u, v) ≠ (y, x) := by
  intro h
  rcases Prod.ext_iff.1 h with ⟨rfl, rfl⟩
  exact lt_irrefl _ (huv.trans hxy)

/-- With `u < v` and `x < y` in the subtype order, `(v, u) ≠ (x, y)`. (glue lemma) -/
theorem swap_ne {V : Type} {s : Set V} [LinearOrder {x // x ∈ s}]
    {u v x y : {x // x ∈ s}} (huv : u < v) (hxy : x < y) : (v, u) ≠ (x, y) := by
  intro h
  rcases Prod.ext_iff.1 h with ⟨rfl, rfl⟩
  exact lt_irrefl _ (huv.trans hxy)

/-- Swapping both components preserves distinctness. (glue lemma) -/
theorem swap_both_ne {V : Type} {s : Set V} {u v x y : {x // x ∈ s}} (hne : (u, v) ≠ (x, y)) :
    (v, u) ≠ (y, x) := by
  intro h
  rcases Prod.ext_iff.1 h with ⟨rfl, rfl⟩
  exact hne rfl

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (s : Set V)
    [Fintype {x // x ∈ s}] [LinearOrder {x // x ∈ s}] :
    HasPlanarDrawingOn (G.induce s) := by
  obtain ⟨p, arc, hp, he, hnc⟩ := hG
  let p' : {x // x ∈ s} → ℝ × ℝ := fun (w : {x // x ∈ s}) => p w.1
  let arc' (u v : {x // x ∈ s}) (t : ℝ) : ℝ × ℝ :=
    if _h : (↑u : V) < (↑v : V) then arc (↑u) (↑v) t else arc (↑v) (↑u) ((1 : ℝ) - t)
  refine ⟨p', arc', hp.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hadj
    have hadjV : G.Adj ↑u ↑v := SimpleGraph.induce_adj.mpr hadj
    by_cases hV : (↑u : V) < (↑v : V)
    · dsimp [p', arc']
      split_ifs <;> simp
      have hclause := he ↑u ↑v hV hadjV
      refine ⟨hclause.1, hclause.2.1, hclause.2.2.1, hclause.2.2.2.1, ?_⟩
      intro t h1 h2 a ha
      exact hclause.2.2.2.2 t ⟨h1, h2⟩ a
    · have hV' : (↑v : V) < (↑u : V) := sub_lt_of_not_lt_co hV (sub_ne_of_lt_co huv)
      have hhe := he ↑v ↑u hV' (by rwa [SimpleGraph.adj_comm] at hadjV)
      dsimp [p', arc']
      split_ifs <;> simp
      refine ⟨arc_rev_continuousOn (arc ↑v ↑u) hhe.1, arc_rev_injOn (arc ↑v ↑u) hhe.2.1, ?_, ?_, ?_⟩
      · simpa using hhe.2.2.2.1
      · simpa using hhe.2.2.1
      · intro t h1 h2 a ha
        exact hhe.2.2.2.2 (1 - t) (one_sub_mem_Ioo ⟨h1, h2⟩) a
  · intro u v x y huv hxy hadj1 hadj2 hne t ht s hs hmeet
    have hA1V : G.Adj ↑u ↑v := SimpleGraph.induce_adj.mpr hadj1
    have hA2V : G.Adj ↑x ↑y := SimpleGraph.induce_adj.mpr hadj2
    by_cases hV : (↑u : V) < (↑v : V)
    · by_cases hW : (↑x : V) < (↑y : V)
      · have hred1 : arc' u v t = arc (↑u) (↑v) t := by dsimp [arc']; split_ifs <;> simp
        have hred2 : arc' x y s = arc (↑x) (↑y) s := by dsimp [arc']; split_ifs <;> simp
        rw [hred1, hred2] at hmeet
        exact hnc ↑u ↑v ↑x ↑y hV hW hA1V hA2V (coe_pair_ne hne) t ht s hs hmeet
      · have hW' : (↑y : V) < (↑x : V) := sub_lt_of_not_lt_co hW (sub_ne_of_lt_co hxy)
        have hred1 : arc' u v t = arc (↑u) (↑v) t := by dsimp [arc']; split_ifs <;> simp
        have hred2 : arc' x y s = arc (↑y) (↑x) ((1 : ℝ) - s) := by dsimp [arc']; split_ifs <;> simp
        rw [hred1, hred2] at hmeet
        have hnc2 := hnc ↑u ↑v ↑y ↑x hV hW' hA1V (by rwa [SimpleGraph.adj_comm] at hA2V)
          (coe_pair_ne (rev_ne huv hxy)) t ht ((1 : ℝ) - s) (one_sub_mem_Icc hs) hmeet
        exact ⟨hnc2.1, one_sub_endpoint_iff.mpr hnc2.2⟩
    · have hV' : (↑v : V) < (↑u : V) := sub_lt_of_not_lt_co hV (sub_ne_of_lt_co huv)
      by_cases hW : (↑x : V) < (↑y : V)
      · have hred1 : arc' u v t = arc (↑v) (↑u) ((1 : ℝ) - t) := by dsimp [arc']; split_ifs <;> simp
        have hred2 : arc' x y s = arc (↑x) (↑y) s := by dsimp [arc']; split_ifs <;> simp
        rw [hred1, hred2] at hmeet
        have hnc2 := hnc ↑v ↑u ↑x ↑y hV' hW (by rwa [SimpleGraph.adj_comm] at hA1V) hA2V
          (coe_pair_ne (swap_ne huv hxy)) ((1 : ℝ) - t) (one_sub_mem_Icc ht) s hs hmeet
        exact ⟨one_sub_endpoint_iff.mpr hnc2.1, hnc2.2⟩
      · have hW' : (↑y : V) < (↑x : V) := sub_lt_of_not_lt_co hW (sub_ne_of_lt_co hxy)
        have hred1 : arc' u v t = arc (↑v) (↑u) ((1 : ℝ) - t) := by dsimp [arc']; split_ifs <;> simp
        have hred2 : arc' x y s = arc (↑y) (↑x) ((1 : ℝ) - s) := by dsimp [arc']; split_ifs <;> simp
        rw [hred1, hred2] at hmeet
        have hnc2 := hnc ↑v ↑u ↑y ↑x hV' hW' (by rwa [SimpleGraph.adj_comm] at hA1V)
          (by rwa [SimpleGraph.adj_comm] at hA2V) (coe_pair_ne (swap_both_ne hne))
          ((1 : ℝ) - t) (one_sub_mem_Icc ht) ((1 : ℝ) - s) (one_sub_mem_Icc hs) hmeet
        exact ⟨one_sub_endpoint_iff.mpr hnc2.1, one_sub_endpoint_iff.mpr hnc2.2⟩
