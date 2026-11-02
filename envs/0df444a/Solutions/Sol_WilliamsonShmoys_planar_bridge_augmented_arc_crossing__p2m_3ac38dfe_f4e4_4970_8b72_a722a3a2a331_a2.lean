-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_augmented_arc_crossing__p2m_3ac38dfe_f4e4_4970_8b72_a722a3a2a331_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:14:05.03688+00:00
-- url     : https://prove2.me/submissions/8c137e2e-9a79-4a1f-9444-680a2a071cff

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (bridge : ℝ → ℝ × ℝ)
    (hne : u ≠ v) (hnew : ¬ H.Adj u v)
    (hdraw : Function.Injective p ∧
      (∀ a b, a < b → H.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
        (a, b) ≠ (x, y) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hbridge : ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc 0 1) ∧ bridge 0 = p u ∧ bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) :
    ∀ a b x y, a < b → x < y →
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Adj a b →
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Adj x y →
      (a, b) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (fun a b t => if u < v then
          if a = u ∧ b = v then bridge t else arc a b t
        else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b t =
        (fun a b t => if u < v then
          if a = u ∧ b = v then bridge t else arc a b t
        else if a = v ∧ b = u then bridge (1 - t) else arc a b t) x y s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
  classical
  rcases hdraw with ⟨_, _, hCross⟩
  rcases hbridge with ⟨_, _, _, _, _, hBridgeCross⟩
  intro a b x y hab hxy hab' hxy' hpairs t ht s hs heq
  by_cases huv : u < v
  · have edge_cases (r q : V) (hrq : r < q)
        (hedge : (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Adj r q) :
        H.Adj r q ∨ (r = u ∧ q = v) := by
      have h := hedge
      simp only [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj] at h
      rcases h with hold | ⟨hmem, _⟩
      · exact Or.inl hold
      · simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
        rcases hmem with hpair | hpair
        · exact Or.inr hpair
        · rcases hpair with ⟨rfl, rfl⟩
          exact False.elim (lt_asymm hrq huv)
    rcases edge_cases a b hab hab' with ha | haNew
    · rcases edge_cases x y hxy hxy' with hx | hxNew
      · have hnotA : ¬ (a = u ∧ b = v) := by
          rintro ⟨rfl, rfl⟩
          exact hnew ha
        have hnotX : ¬ (x = u ∧ y = v) := by
          rintro ⟨rfl, rfl⟩
          exact hnew hx
        simp [huv, hnotA, hnotX] at heq
        exact hCross a b x y hab hxy ha hx hpairs t ht s hs heq
      · rcases hxNew with ⟨hxU, hyV⟩
        have hnotA : ¬ (a = u ∧ b = v) := by
          rintro ⟨rfl, rfl⟩
          exact hnew ha
        simp [huv, hnotA, hxU, hyV] at heq
        have hc := hBridgeCross a b hab ha s hs t ht heq.symm
        exact ⟨hc.2, hc.1⟩
    · rcases haNew with ⟨haU, hbV⟩
      rcases edge_cases x y hxy hxy' with hx | hxNew
      · have hnotX : ¬ (x = u ∧ y = v) := by
          rintro ⟨rfl, rfl⟩
          exact hnew hx
        simp [huv, hnotX, haU, hbV] at heq
        exact hBridgeCross x y hxy hx t ht s hs heq
      · rcases hxNew with ⟨hxU, hyV⟩
        have hp : (a, b) = (x, y) := by
          exact Prod.ext (haU.trans hxU.symm) (hbV.trans hyV.symm)
        exact False.elim (hpairs hp)
  · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) hne.symm
    have edge_cases (r q : V) (hrq : r < q)
        (hedge : (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Adj r q) :
        H.Adj r q ∨ (r = v ∧ q = u) := by
      have h := hedge
      simp only [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj] at h
      rcases h with hold | ⟨hmem, _⟩
      · exact Or.inl hold
      · simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
        rcases hmem with hpair | hpair
        · rcases hpair with ⟨rfl, rfl⟩
          exact False.elim (lt_asymm hrq hvu)
        · exact Or.inr hpair
    have revRange (z : ℝ) (hz : z ∈ Set.Icc 0 1) : 1 - z ∈ Set.Icc 0 1 := by
      rcases hz with ⟨hz0, hz1⟩
      constructor <;> linarith
    have revEnds (z : ℝ) (hz : 1 - z = 0 ∨ 1 - z = 1) :
        z = 0 ∨ z = 1 := by
      rcases hz with h | h
      · right
        linarith
      · left
        linarith
    rcases edge_cases a b hab hab' with ha | haNew
    · rcases edge_cases x y hxy hxy' with hx | hxNew
      · have hnotA : ¬ (a = v ∧ b = u) := by
          rintro ⟨rfl, rfl⟩
          exact hnew (ha.symm)
        have hnotX : ¬ (x = v ∧ y = u) := by
          rintro ⟨rfl, rfl⟩
          exact hnew (hx.symm)
        simp [huv, hnotA, hnotX] at heq
        exact hCross a b x y hab hxy ha hx hpairs t ht s hs heq
      · rcases hxNew with ⟨hxV, hyU⟩
        have hnotA : ¬ (a = v ∧ b = u) := by
          rintro ⟨rfl, rfl⟩
          exact hnew (ha.symm)
        simp [huv, hnotA, hxV, hyU] at heq
        have hc := hBridgeCross a b hab ha (1 - s) (revRange s hs) t ht heq.symm
        rcases hc with ⟨hc1, hc2⟩
        exact ⟨hc2, revEnds s hc1⟩
    · rcases haNew with ⟨haV, hbU⟩
      rcases edge_cases x y hxy hxy' with hx | hxNew
      · have hnotX : ¬ (x = v ∧ y = u) := by
          rintro ⟨rfl, rfl⟩
          exact hnew (hx.symm)
        simp [huv, hnotX, haV, hbU] at heq
        have hc := hBridgeCross x y hxy hx (1 - t) (revRange t ht) s hs heq
        rcases hc with ⟨hc1, hc2⟩
        exact ⟨revEnds t hc1, hc2⟩
      · rcases hxNew with ⟨hxV, hyU⟩
        have hp : (a, b) = (x, y) := by
          exact Prod.ext (haV.trans hxV.symm) (hbU.trans hyU.symm)
        exact False.elim (hpairs hp)
