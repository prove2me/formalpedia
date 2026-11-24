-- Prove2me | solution 1 for WeightedEdgeColor.theorem_1_1_simple_graphs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:31:43.176111+00:00
-- url     : https://prove2.me/submissions/ab298433-db63-4287-a959-f50a06e105f6

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
import Definitions.Def_WeightedEdgeColor_WGraph_bp
import Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets
import Theorems.Thm_WeightedEdgeColor_theorem_3_1
import Theorems.Thm_WeightedEdgeColor_lemma_A_1

set_option autoImplicit false

namespace WECMainAux
open WeightedEdgeColor WeightedEdgeColor.WGraph

theorem sum_subtype_filter {E : Type} [Fintype E] (p : E → Prop) [DecidablePred p]
    (q : E → Prop) [DecidablePred q] (g : E → ℝ) :
    ∑ e ∈ (Finset.univ : Finset {e // p e}).filter (fun e => q e.1), g e.1
      = ∑ e ∈ Finset.univ.filter (fun e => p e ∧ q e), g e := by
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) (fun e => if q e then g e else 0)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hp : p e <;> by_cases hq : q e <;> simp [hp, hq]

theorem W_le_of_packs {V E : Type} [Fintype E] [DecidableEq V] (G : WGraph V E) (v : V) (m : ℕ)
    (h : G.PacksInto v m) : G.W v ≤ m := by
  obtain ⟨f, hf⟩ := h
  unfold WGraph.W
  rw [← Finset.sum_fiberwise (G.inc v) f]
  calc ∑ j, ∑ i ∈ G.inc v with f i = j, G.w i ≤ ∑ _j : Fin m, (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => hf j)
    _ = m := by simp

theorem inK_uniform {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V] (G : WGraph V E)
    (v : V) (m : ℕ) (hm : 0 < m) (h : G.PacksInto v m) :
    G.InK v (fun _ => (1 : ℝ) / m) := by
  classical
  obtain ⟨f, hf⟩ := h
  let T : Fin m → Finset (G.inc v) := fun j => Finset.univ.filter (fun e => f e.1 = j)
  refine ⟨fun S => ∑ j : Fin m, if S = T j then (1 : ℝ) / m else 0, ?_, ?_, ?_, ?_⟩
  · intro S
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity
  · rw [Finset.sum_comm]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [Finset.sum_ite_eq', hm']
  · intro S hS
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
    have hSj : S = T j := by
      by_contra hne
      exact hj (if_neg hne)
    subst hSj
    have key : ∑ e ∈ T j, G.w e.1 = ∑ e ∈ (G.inc v).filter (fun e => f e = j), G.w e := by
      simp only [T]
      rw [Finset.sum_filter, Finset.sum_filter]
      exact Finset.sum_coe_sort (G.inc v) (fun e => if f e = j then G.w e else 0)
    simpa [key] using hf j
  · intro e
    rw [Finset.sum_comm]
    have : ∀ j : Fin m, (∑ S ∈ Finset.univ.filter (fun S : Finset (G.inc v) => e ∈ S),
        if S = T j then (1 : ℝ) / m else 0) = if f e.1 = j then (1 : ℝ) / m else 0 := by
      intro j
      rw [Finset.sum_ite_eq']
      simp [T]
    rw [Finset.sum_congr rfl (fun j _ => this j)]
    simp
end WECMainAux

namespace WECMainAux
open WeightedEdgeColor WeightedEdgeColor.WGraph

/-- `K n^{3/4} ≤ ε' n` once `n ≥ (K/ε')^4`. -/
theorem rpow_bound (K ε' n : ℝ) (hK : 0 ≤ K) (hε : 0 < ε') (hn : (K / ε') ^ 4 ≤ n) (hn0 : 0 < n) :
    K * n ^ (3 / 4 : ℝ) ≤ ε' * n := by
  have h14 : K / ε' ≤ n ^ (1 / 4 : ℝ) := by
    have h1 : ((K / ε') ^ (4 : ℕ)) ^ ((((4 : ℕ) : ℝ))⁻¹) = K / ε' :=
      Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    have h2 : (((4 : ℕ) : ℝ))⁻¹ = (1 / 4 : ℝ) := by norm_num
    rw [h2] at h1
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) hn (by norm_num)
  have hsplit : n = n ^ (1 / 4 : ℝ) * n ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hn0]; norm_num
  have h34 : 0 ≤ n ^ (3 / 4 : ℝ) := by positivity
  have : K ≤ ε' * n ^ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ hε] at h14; linarith
  calc K * n ^ (3 / 4 : ℝ) ≤ (ε' * n ^ (1 / 4 : ℝ)) * n ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right this h34
    _ = ε' * n := by rw [mul_assoc, ← hsplit]

/-- The subgraph of edges satisfying `p`. -/
def subG {V E : Type} (G : WGraph V E) (p : E → Prop) : WGraph V {e // p e} where
  ends e := G.ends e.1
  loopless e := G.loopless e.1
  w e := G.w e.1
  w_pos e := G.w_pos e.1
  w_le_one e := G.w_le_one e.1

end WECMainAux

open WeightedEdgeColor WeightedEdgeColor.WGraph WECMainAux

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple →
      ∃ k : ℕ, (k : ℝ) ≤ (1 + ε) * (G.bp : ℝ) + Cε ∧ ∃ φ : E → Fin k, G.IsProperColoring φ := by
  set ε' : ℝ := ε / 8 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨n₀, Kc, h31⟩ := theorem_3_1 1 1 ε' one_pos one_pos hε'0
  set K : ℝ := max Kc 0
  set N₁ : ℝ := max (max n₀ 1) ((K / ε') ^ 4)
  refine ⟨4 * N₁ + 2, ?_⟩
  intro V E _ _ _ _ G hG
  set B : ℕ := G.bp with hBdef
  have hpack : ∀ v, G.PacksInto v B :=
    @Nat.find_spec (fun m => ∀ v, G.PacksInto v m) (fun _ => Classical.propDecidable _) G.exists_packsInto
  have hWB : ∀ v, G.W v ≤ B := fun v => W_le_of_packs G v B (hpack v)
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hN₁1 : (1 : ℝ) ≤ N₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  by_cases hsmall : (B : ℝ) < N₁
  · -- small case: greedy
    obtain ⟨φ, hφ⟩ := lemma_A_1 V E G (B : ℝ) hWB
    refine ⟨⌊4 * (B : ℝ)⌋₊ + 1, ?_, φ, hφ⟩
    have hfl : (⌊4 * (B : ℝ)⌋₊ : ℝ) ≤ 4 * B := Nat.floor_le (by positivity)
    push_cast
    nlinarith
  · push Not at hsmall
    set n : ℝ := (B : ℝ) with hn
    have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsmall
    have hn1 : 1 ≤ n := le_trans hN₁1 hsmall
    have hnpos : 0 < n := by linarith
    have hBpos : 0 < B := Nat.cast_pos.mp hnpos
    have hKn : (K / ε') ^ 4 ≤ n := le_trans (le_max_right _ _) hsmall
    set x : E → Fin B → ℝ := fun _ _ => (1 : ℝ) / B with hx
    have hcard : (Fintype.card (Fin B) : ℝ) ≤ 1 * n := by simp [hn]
    have hx1 : ∀ e c, 0 ≤ x e c ∧ x e c ≤ 1 / n := fun e c => ⟨by positivity, le_refl _⟩
    have hx2 : ∀ e, ∑ c, x e c ≤ 1 := by
      intro e; simp [hx]; rw [mul_inv_cancel₀]; exact_mod_cast hBpos.ne'
    have hx3 : ∀ v c, G.InK v (fun e => x e c) := fun v c => inK_uniform G v B hBpos (hpack v)
    obtain ⟨φ, hfeas, -, hcol⟩ := h31 V E G hG n hn0 hWB (Fin B) hcard x hx1 hx2 hx3
    -- the uncolored subgraph
    let p : E → Prop := fun e => φ e = none
    let J := subG G p
    set R : ℝ := ε' * n + Kc * n ^ (3 / 4 : ℝ) with hR
    have hJW : ∀ v, J.W v ≤ R := by
      intro v
      have hJ : J.W v = ∑ e ∈ (G.inc v).filter (fun e => φ e = none), G.w e := by
        show ∑ e ∈ (Finset.univ : Finset {e // p e}).filter (fun e => v ∈ G.ends e.1), G.w e.1 = _
        rw [sum_subtype_filter p (fun e => v ∈ G.ends e) G.w]
        unfold WGraph.inc
        rw [Finset.filter_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext e; simp [p, and_comm]
      have hsplit := Finset.sum_filter_add_sum_filter_not (G.inc v) (fun e => (φ e).isSome) G.w
      have hW : ∑ e ∈ G.inc v, G.w e * ∑ c, x e c = G.W v := by
        unfold WGraph.W
        apply Finset.sum_congr rfl
        intro e _
        simp [hx]; rw [mul_inv_cancel₀ (by exact_mod_cast hBpos.ne'), mul_one]
      have hnone : (G.inc v).filter (fun e => ¬ (φ e).isSome) = (G.inc v).filter (fun e => φ e = none) := by
        ext e; simp
      have hc := hcol v
      unfold WGraph.coloredWeight at hc
      rw [hnone] at hsplit
      unfold WGraph.W at hW
      rw [hJ]
      linarith
    set K' : ℕ := ⌊4 * R⌋₊ + 1 with hK'
    obtain ⟨ψ, hψ⟩ : ∃ ψ : {e // p e} → Fin K', J.IsProperColoring ψ := lemma_A_1 V {e // p e} J R hJW
    let χ : E → Fin (B + K') := fun e =>
      if h : φ e = none then Fin.natAdd B (ψ ⟨e, h⟩)
      else Fin.castAdd K' ((φ e).get (Option.ne_none_iff_isSome.mp h))
    refine ⟨B + K', ?_, χ, ?_⟩
    · -- counting
      have hKc : Kc * n ^ (3 / 4 : ℝ) ≤ ε' * n := by
        have h1 : Kc * n ^ (3 / 4 : ℝ) ≤ K * n ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        exact le_trans h1 (rpow_bound K ε' n (le_max_right _ _) hε'0 hKn hnpos)
      have hfl : (⌊4 * R⌋₊ : ℝ) ≤ 8 * ε' * n := by
        by_cases h4 : 0 ≤ 4 * R
        · have := Nat.floor_le h4; linarith
        · push Not at h4
          rw [Nat.floor_eq_zero.mpr (by linarith)]; simp; positivity
      have : ((B + K' : ℕ) : ℝ) = n + (⌊4 * R⌋₊ : ℝ) + 1 := by
        simp [K', hn]; ring
      have h8 : 8 * ε' * n = ε * n := by rw [hε']; ring
      rw [this]
      nlinarith
    · -- properness
      intro v d
      refine Fin.addCases (fun c => ?_) (fun j => ?_) d
      · -- old colour c
        have hset : (G.inc v).filter (fun e => χ e = Fin.castAdd K' c)
            = (G.inc v).filter (fun e => φ e = some c) := by
          ext e
          simp only [Finset.mem_filter, χ]
          constructor
          · rintro ⟨he, h⟩
            refine ⟨he, ?_⟩
            split_ifs at h with h0
            · exact absurd h (by
                intro h'; have := congrArg Fin.val h'; simp at this; omega)
            · have h' := Fin.castAdd_injective _ _ h
              rw [← h']; simp
          · rintro ⟨he, h⟩
            refine ⟨he, ?_⟩
            have h0 : ¬ φ e = none := by rw [h]; simp
            rw [dif_neg h0]
            congr 1
            simp [h]
        rw [hset]; exact hfeas v c
      · -- new colour j
        have hset : ∑ e ∈ (G.inc v).filter (fun e => χ e = Fin.natAdd B j), G.w e
            = ∑ e ∈ (J.inc v).filter (fun e => ψ e = j), J.w e := by
          show _ = ∑ e ∈ ((Finset.univ : Finset {e // p e}).filter (fun e => v ∈ G.ends e.1)).filter
              (fun e => ψ e = j), G.w e.1
          rw [Finset.filter_filter]
          -- turn the subtype sum into a sum over E
          have : ∀ e : {e // p e}, (v ∈ G.ends e.1 ∧ ψ e = j) ↔
              (v ∈ G.ends e.1 ∧ χ e.1 = Fin.natAdd B j) := by
            intro e
            have h0 : φ e.1 = none := e.2
            simp only [χ, dif_pos h0]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]⟩
            · rintro ⟨h1, h2⟩; exact ⟨h1, Fin.natAdd_injective _ _ h2⟩
          rw [Finset.filter_congr (fun e _ => this e)]
          rw [sum_subtype_filter p (fun e => v ∈ G.ends e ∧ χ e = Fin.natAdd B j) G.w]
          unfold WGraph.inc
          rw [Finset.filter_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, p]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨?_, h1, h2⟩
            by_contra h0
            simp only [χ, dif_neg h0] at h2
            have := congrArg Fin.val h2; simp at this; omega
          · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
        rw [hset]; exact hψ v j
