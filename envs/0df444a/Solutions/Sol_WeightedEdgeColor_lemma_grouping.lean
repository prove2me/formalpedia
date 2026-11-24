-- Prove2me | solution 1 for WeightedEdgeColor.lemma_grouping
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:49:41.194626+00:00
-- url     : https://prove2.me/submissions/e9216187-edbc-497c-9a58-858d1cfdfab4

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Theorems.Thm_WeightedEdgeColor_proposition_A_4

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WECGroupAux
open WeightedEdgeColor WeightedEdgeColor.WGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Each edge at `v` is counted once, at its other endpoint. -/
theorem other_sum (G : WGraph V E) (v : V) (P : V → Prop) [DecidablePred P] :
    ∑ u, (if P u then ∑ e ∈ (G.inc v).filter (fun e => u ∈ G.ends e ∧ u ≠ v), G.w e else 0)
      = ∑ e ∈ (G.inc v).filter (fun e => ∃ u, u ≠ v ∧ u ∈ G.ends e ∧ P u), G.w e := by
  have h1 : ∀ u, (if P u then ∑ e ∈ (G.inc v).filter (fun e => u ∈ G.ends e ∧ u ≠ v), G.w e else 0)
      = ∑ e ∈ G.inc v, (if P u ∧ u ∈ G.ends e ∧ u ≠ v then G.w e else 0) := by
    intro u
    split_ifs with hP
    · rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro e _; simp [hP]
    · symm; apply Finset.sum_eq_zero; intro e _; simp [hP]
  rw [Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have hv : v ∈ G.ends e := by simpa [WGraph.inc] using he
  obtain ⟨u₀, hu₀⟩ := Sym2.mem_iff_exists.mp hv
  have hne : u₀ ≠ v := by
    have := G.loopless e
    rw [hu₀, Sym2.mk_isDiag_iff] at this
    exact fun h => this h.symm
  have hmem : ∀ u, (u ∈ G.ends e ∧ u ≠ v) ↔ u = u₀ := by
    intro u
    rw [hu₀, Sym2.mem_iff]
    constructor
    · rintro ⟨h | h, hne'⟩
      · exact absurd h hne'
      · exact h
    · rintro rfl; exact ⟨Or.inr rfl, hne⟩
  rw [Finset.sum_eq_single u₀]
  · have hex : (∃ u, u ≠ v ∧ u ∈ G.ends e ∧ P u) ↔ P u₀ := by
      constructor
      · rintro ⟨u, h1, h2, h3⟩
        have := (hmem u).mp ⟨h2, h1⟩
        rw [this] at h3; exact h3
      · intro h; exact ⟨u₀, hne, ((hmem u₀).mpr rfl).1, h⟩
    have hu0 := (hmem u₀).mpr rfl
    by_cases hP : P u₀
    · simp [hP, hu0, hex]
    · simp [hP, hex]
  · intro u _ hu
    have : ¬ (u ∈ G.ends e ∧ u ≠ v) := fun h => hu ((hmem u).mp h)
    simp only [this, and_false, if_false]
  · simp

theorem pair_le_one (G : WGraph V E) (hG : G.IsSimple) (v u : V) :
    ∑ e ∈ (G.inc v).filter (fun e => u ∈ G.ends e ∧ u ≠ v), G.w e ≤ 1 := by
  set s := (G.inc v).filter (fun e => u ∈ G.ends e ∧ u ≠ v)
  have hcard : s.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [s, WGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    apply hG
    have hva : G.ends a = s(v, u) := (Sym2.mem_and_mem_iff (Ne.symm ha.2.2)).mp ⟨ha.1, ha.2.1⟩
    have hvb : G.ends b = s(v, u) := (Sym2.mem_and_mem_iff (Ne.symm hb.2.2)).mp ⟨hb.1, hb.2.1⟩
    rw [hva, hvb]
  rcases s.eq_empty_or_nonempty with hs | ⟨a, has⟩
  · rw [hs]; simp
  have ha : s ⊆ {a} := by
    intro e he
    rw [Finset.mem_singleton]
    exact Finset.card_le_one.mp hcard e he a has
  calc ∑ e ∈ s, G.w e ≤ ∑ e ∈ {a}, G.w e :=
        Finset.sum_le_sum_of_subset_of_nonneg ha (fun e _ _ => (G.w_pos e).le)
    _ = G.w a := Finset.sum_singleton _ _
    _ ≤ 1 := G.w_le_one a

theorem sym_filter (G : WGraph V E) (v u : V) :
    (G.inc v).filter (fun e => u ∈ G.ends e ∧ u ≠ v)
      = (G.inc u).filter (fun e => v ∈ G.ends e ∧ v ≠ u) := by
  ext e
  simp only [WGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, Ne.symm h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, Ne.symm h3⟩

end WECGroupAux

open WeightedEdgeColor WeightedEdgeColor.WGraph WECGroupAux

theorem solution (r : ℕ) (hr : 0 < r) :
    ∃ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ n : ℝ, 2 ≤ n → (∀ v, G.W v ≤ n) →
      ∃ g : V → Fin r, ∀ (v : V) (j : Fin r),
        ∑ e ∈ (G.inc v).filter (fun e => ∃ u, u ≠ v ∧ u ∈ G.ends e ∧ g u = j), G.w e
          ≤ G.W v / r + K * Real.sqrt (n * Real.log n) := by
  obtain ⟨K₄, hK₄⟩ := proposition_A_4
  refine ⟨4 * |K₄|, ?_⟩
  intro V E _ _ _ _ G hG n hn hW
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let ω : V → Type := fun _ => Fin r
  let p : ∀ u : V, ω u → ℝ := fun _ _ => 1 / r
  let a : V → V → ℝ := fun v u => ∑ e ∈ (G.inc v).filter (fun e => u ∈ G.ends e ∧ u ≠ v), G.w e
  let f : V × Fin r → ∀ u : V, ω u → ℝ := fun t u z => if z = t.2 then a t.1 u else 0
  have ha0 : ∀ v u, 0 ≤ a v u := fun v u => Finset.sum_nonneg (fun e _ => (G.w_pos e).le)
  have ha1 : ∀ v u, a v u ≤ 1 := fun v u => pair_le_one G hG v u
  have haW : ∀ v, ∑ u, a v u = G.W v := by
    intro v
    have := other_sum G v (fun _ => True)
    simp only [if_true] at this
    rw [this]
    unfold WGraph.W
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext e
    simp only [Finset.mem_filter, and_true, and_iff_left_iff_imp]
    intro he
    have hv : v ∈ G.ends e := by simpa [WGraph.inc] using he
    obtain ⟨u₀, hu₀⟩ := Sym2.mem_iff_exists.mp hv
    have hne : u₀ ≠ v := by
      have := G.loopless e
      rw [hu₀, Sym2.mk_isDiag_iff] at this
      exact fun h => this h.symm
    exact ⟨u₀, hne, by rw [hu₀]; exact Sym2.mem_mk_right _ _⟩
  have hE : ∀ t : V × Fin r, ∑ u, ∑ z, p u z * f t u z = G.W t.1 / r := by
    intro t
    have : ∀ u, ∑ z, p u z * f t u z = a t.1 u / r := by
      intro u
      simp only [p, f]
      rw [Finset.sum_eq_single t.2]
      · simp; ring
      · intro z _ hz; simp [hz]
      · simp
    rw [Finset.sum_congr rfl (fun u _ => this u), ← Finset.sum_div, haW]
  obtain ⟨z, hz⟩ := hK₄ V (V × Fin r) ω p f (n / r) n
    (fun _ _ => by simp only [p]; positivity)
    (fun u => by simp only [p, ω]; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; field_simp)
    (fun t u z => by
      simp only [f]; split_ifs
      · exact ⟨ha0 _ _, ha1 _ _⟩
      · exact ⟨le_refl _, zero_le_one⟩)
    (fun t => by rw [hE t]; exact div_le_div_of_nonneg_right (hW t.1) hr'.le)
    (fun u z => by
      rw [Fintype.sum_prod_type]
      have : ∀ v, ∑ j : Fin r, f (v, j) u z = a v u := by
        intro v
        simp only [f]
        rw [Finset.sum_eq_single z]
        · simp
        · intro j _ hj; simp [Ne.symm hj]
        · simp
      rw [Finset.sum_congr rfl (fun v _ => this v)]
      have hsym : ∀ v, a v u = a u v := by
        intro v; simp only [a]; rw [sym_filter]
      rw [Finset.sum_congr rfl (fun v _ => hsym v), haW]
      exact hW u)
  refine ⟨z, fun v j => ?_⟩
  have h1 := hz (v, j)
  rw [hE (v, j)] at h1
  have hF : ∑ u, f (v, j) u (z u)
      = ∑ e ∈ (G.inc v).filter (fun e => ∃ u, u ≠ v ∧ u ∈ G.ends e ∧ z u = j), G.w e := by
    rw [← other_sum G v (fun u => z u = j)]
  rw [hF] at h1
  -- the error term
  have hn0 : 0 < n := by linarith
  have hC : max 2 (max (n / r) n) = n := by
    have : n / r ≤ n := div_le_self hn0.le (by exact_mod_cast hr)
    rw [max_eq_right this, max_eq_right hn]
  rw [hC] at h1
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hlog2 : Real.log (n + 2) ≤ 2 * Real.log n := by
    rw [← Real.log_rpow hn0]
    apply Real.log_le_log (by linarith)
    rw [Real.rpow_two]; nlinarith
  have hlogn : Real.log n ≤ n := le_trans (Real.log_le_sub_one_of_pos hn0) (by linarith)
  have hS : Real.sqrt (n / r * Real.log (n + 2)) ≤ 2 * Real.sqrt (n * Real.log n) := by
    have : n / r * Real.log (n + 2) ≤ 4 * (n * Real.log n) := by
      have h1 : n / r ≤ n := div_le_self hn0.le (by exact_mod_cast hr)
      have h2 : 0 ≤ Real.log (n + 2) := Real.log_nonneg (by linarith)
      nlinarith
    calc Real.sqrt (n / r * Real.log (n + 2)) ≤ Real.sqrt (4 * (n * Real.log n)) :=
          Real.sqrt_le_sqrt this
      _ = 2 * Real.sqrt (n * Real.log n) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hL : Real.log (n + 2) ≤ 2 * Real.sqrt (n * Real.log n) := by
    have : Real.log n ≤ Real.sqrt (n * Real.log n) := by
      rw [Real.le_sqrt hlogpos.le (by positivity)]; nlinarith
    linarith
  have hX : 0 ≤ Real.sqrt (n / r * Real.log (n + 2)) + Real.log (n + 2) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
  have hK : K₄ * (Real.sqrt (n / r * Real.log (n + 2)) + Real.log (n + 2))
      ≤ 4 * |K₄| * Real.sqrt (n * Real.log n) := by
    calc K₄ * (Real.sqrt (n / r * Real.log (n + 2)) + Real.log (n + 2))
        ≤ |K₄| * (Real.sqrt (n / r * Real.log (n + 2)) + Real.log (n + 2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hX
      _ ≤ |K₄| * (4 * Real.sqrt (n * Real.log n)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = 4 * |K₄| * Real.sqrt (n * Real.log n) := by ring
  linarith
