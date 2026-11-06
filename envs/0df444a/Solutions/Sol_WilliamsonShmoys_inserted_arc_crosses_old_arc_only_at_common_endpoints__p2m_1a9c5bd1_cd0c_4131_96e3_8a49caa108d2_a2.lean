-- Prove2me | solution 1 for WilliamsonShmoys.inserted_arc_crosses_old_arc_only_at_common_endpoints__p2m_1a9c5bd1_cd0c_4131_96e3_8a49caa108d2_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:33:32.691419+00:00
-- url     : https://prove2.me/submissions/ee348891-fd78-49d6-87b3-2fcaaee4d0d5

-- ID: e6166acf-8ae9-4caa-9fd9-af658866bc01 | NAME: WilliamsonShmoys.inserted_arc_crosses_old_arc_only_at_common_endpoints__p2m_1a9c5bd1_cd0c_4131_96e3_8a49caa108d2_a2 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (u v a b : V)
    (gamma : ℝ → ℝ × ℝ) (huv : u < v) (hab : a < b)
    (hp : Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y c d, x < y → c < d → H.Adj x y → H.Adj c d →
        (x, y) ≠ (c, d) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          arc x y t = arc c d s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hgamma : ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.InjOn gamma (Set.Icc 0 1) ∧ gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → H.Adj x y →
        ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s))
    (hAdj : H.Adj a b) (hne : (u, v) ≠ (a, b)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
      gamma t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
  classical
  rcases hp with ⟨_, hp_edge, _⟩
  rcases hgamma with ⟨_, _, hg0, hg1, _, hg_avoidE⟩
  have hsplit : ∀ {r : ℝ}, r ∈ Set.Icc (0 : ℝ) 1 →
      r = 0 ∨ r = 1 ∨ r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    rcases (Set.mem_Icc.mp hr) with ⟨hr0, hr1⟩
    by_cases h0 : r = 0
    · exact Or.inl h0
    · by_cases h1 : r = 1
      · exact Or.inr (Or.inl h1)
      · right; right
        exact Set.mem_Ioo.mpr ⟨by
          by_contra hlt
          exact h0 (le_antisymm (le_of_not_gt hlt) hr0),
          by
          by_contra hlt
          exact h1 (le_antisymm hr1 (le_of_not_gt hlt))⟩
  intro t ht s hs heq
  have ht_end : t = 0 ∨ t = 1 := by
    rcases hsplit ht with h0 | h1 | hi
    · exact Or.inl h0
    · exact Or.inr h1
    · exact False.elim ((hg_avoidE t hi a b hab hAdj s hs) heq)
  have hs_end : s = 0 ∨ s = 1 := by
    rcases hsplit hs with h0 | h1 | hi
    · exact Or.inl h0
    · exact Or.inr h1
    · exfalso
      rcases hp_edge a b hab hAdj with ⟨_, _, _, _, havV⟩
      have hw : gamma t = p u ∨ gamma t = p v := by
        rcases ht_end with rfl | rfl
        · exact Or.inl hg0
        · exact Or.inr hg1
      rcases hw with hw | hw
      · exact (havV s hi u) (heq.symm.trans hw)
      · exact (havV s hi v) (heq.symm.trans hw)
  exact ⟨ht_end, hs_end⟩
