-- Prove2me | solution 1 for WeightedEdgeColor.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:47:40.212798+00:00
-- url     : https://prove2.me/submissions/7a392c6b-796c-41b1-8b23-ea3e5bae692b

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets
import Theorems.Thm_WeightedEdgeColor_lemma_grouping
import Theorems.Thm_WeightedEdgeColor_theorem_3_1_partite

set_option autoImplicit false

namespace WECThm31Aux
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

/-- The subgraph of edges satisfying `p`. -/
def subG {V E : Type} (G : WGraph V E) (p : E → Prop) : WGraph V {e // p e} where
  ends e := G.ends e.1
  loopless e := G.loopless e.1
  w e := G.w e.1
  w_pos e := G.w_pos e.1
  w_le_one e := G.w_le_one e.1

theorem isAvg_restrict {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : κ → ι) (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hf : Function.Injective f)
    (h : IsAvgOfFeasibleSets w x) : IsAvgOfFeasibleSets (fun k => w (f k)) (fun k => x (f k)) := by
  obtain ⟨p, hp0, hp1, hpf, hpx⟩ := h
  let g : Finset ι → Finset κ := fun S => Finset.univ.filter (fun k => f k ∈ S)
  refine ⟨fun S' => ∑ S ∈ Finset.univ.filter (fun S => g S = S'), p S, ?_, ?_, ?_, ?_⟩
  · intro S'; exact Finset.sum_nonneg (fun S _ => hp0 S)
  · rw [Finset.sum_fiberwise Finset.univ g p]; exact hp1
  · intro S' hS'
    obtain ⟨S, hS, hpS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS'
    have hgS : g S = S' := (Finset.mem_filter.mp hS).2
    subst hgS
    calc ∑ k ∈ g S, w (f k) = ∑ i ∈ (g S).map ⟨f, hf⟩, w i := by rw [Finset.sum_map]; rfl
      _ ≤ ∑ i ∈ S, w i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
            exact (Finset.mem_filter.mp hk).2
          · intro i _ _; exact hw i
      _ ≤ 1 := hpf S hpS
  · intro k
    show x (f k) = _
    rw [hpx (f k)]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun S : Finset ι => f k ∈ S))
      (t := Finset.univ.filter (fun S' : Finset κ => k ∈ S')) (g := g)]
    · apply Finset.sum_congr rfl
      intro S' hS'
      have hkS' : k ∈ S' := (Finset.mem_filter.mp hS').2
      apply Finset.sum_congr
      · ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h
          refine ⟨?_, h⟩
          rw [← h] at hkS'
          exact (Finset.mem_filter.mp hkS').2
      · intro _ _; rfl
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      simp [g, hS]

end WECThm31Aux

open WeightedEdgeColor WeightedEdgeColor.WGraph WECThm31Aux

theorem solution (C₀ C₁ ε : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hε : 0 < ε) :
    ∃ n₀ Kc : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ x : E → 𝒞 → ℝ, (∀ e c, 0 ≤ x e c ∧ x e c ≤ C₀ / n) → (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, G.InK v (fun e => x e c)) →
      ∃ φ : E → Option 𝒞, G.IsFeasiblePartialColoring φ ∧
        (∀ e c, φ e = some c → 0 < x e c) ∧
        ∀ v, (∑ e ∈ G.inc v, G.w e * ∑ c, x e c) - ε * n - Kc * n ^ (3 / 4 : ℝ) ≤
          G.coloredWeight φ v := by
  set r : ℕ := ⌈4 / ε⌉₊ + 1 with hr
  have hr0 : 0 < r := Nat.succ_pos _
  have hrε : (1 : ℝ) / r ≤ ε / 4 := by
    have h1 : 4 / ε ≤ (⌈4 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (r : ℝ) = ⌈4 / ε⌉₊ + 1 := by simp [hr]
    rw [div_le_iff₀ (by rw [h2]; positivity)]
    rw [div_le_iff₀ hε] at h1
    rw [h2]; nlinarith
  obtain ⟨K, hK⟩ := lemma_grouping r hr0
  obtain ⟨n₀', Kc', hcore⟩ := theorem_3_1_partite C₀ C₁ (ε / 2) hC₀ hC₁ (by positivity) r
  refine ⟨max n₀' 2, Kc' + 2 * |K|, ?_⟩
  intro V E _ _ _ _ G hG n hn hW 𝒞 _ _ hcard x hx hxs hxK
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : n₀' ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : 0 < n := by linarith
  obtain ⟨g, hg⟩ := hK V E G hG n hn2 hW
  -- edges between groups
  let p : E → Prop := fun e => ∀ u w, G.ends e = s(u, w) → g u ≠ g w
  let H := subG G p
  have hHs : H.IsSimple := by
    intro e₁ e₂ h
    exact Subtype.ext (hG h)
  have hHp : ∀ (e : {e // p e}) (u v : V), H.ends e = s(u, v) → g u ≠ g v :=
    fun e u v h => e.2 u v h
  have hHW : ∀ v, H.W v ≤ n := by
    intro v
    refine le_trans ?_ (hW v)
    show ∑ e ∈ (Finset.univ : Finset {e // p e}).filter (fun e => v ∈ G.ends e.1), G.w e.1 ≤ _
    rw [sum_subtype_filter p (fun e => v ∈ G.ends e) G.w]
    unfold WGraph.W WGraph.inc
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢; exact he.2
    · intro e _ _; exact (G.w_pos e).le
  let xH : {e // p e} → 𝒞 → ℝ := fun e c => x e.1 c
  have hxH : ∀ e c, 0 ≤ xH e c ∧ xH e c ≤ C₀ / n := fun e c => hx e.1 c
  have hxsH : ∀ e, ∑ c, xH e c ≤ 1 := fun e => hxs e.1
  have hxKH : ∀ v c, H.InK v (fun e => xH e c) := by
    intro v c
    have h := hxK v c
    unfold WGraph.InK at h ⊢
    let f : H.inc v → G.inc v := fun e => ⟨e.1.1, by
      have := e.2
      simp only [WGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and] at this ⊢
      exact this⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      have := congrArg Subtype.val hab
      exact this
    exact isAvg_restrict f (fun e : G.inc v => G.w e) (fun e : G.inc v => x e c)
      (fun e => (G.w_pos e).le) hf h
  obtain ⟨φH, hφf, hφs, hφc⟩ := hcore V {e // p e} H hHs g hHp n hn0 hHW 𝒞 hcard xH hxH hxsH hxKH
  let φ : E → Option 𝒞 := fun e => if h : p e then φH ⟨e, h⟩ else none
  -- translating sums
  have hsumH : ∀ (v : V) (q : E → Prop) [DecidablePred q] (h : E → ℝ),
      ∑ e ∈ (H.inc v).filter (fun e => q e.1), h e.1
        = ∑ e ∈ (G.inc v).filter (fun e => p e ∧ q e), h e := by
    intro v q _ h
    show ∑ e ∈ ((Finset.univ : Finset {e // p e}).filter (fun e => v ∈ G.ends e.1)).filter
      (fun e => q e.1), h e.1 = _
    rw [Finset.filter_filter, sum_subtype_filter p (fun e => v ∈ G.ends e ∧ q e) h]
    unfold WGraph.inc
    rw [Finset.filter_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro v c
    have h1 := hφf v c
    have : ∑ e ∈ (G.inc v).filter (fun e => φ e = some c), G.w e
        = ∑ e ∈ (H.inc v).filter (fun e => φH e = some c), H.w e := by
      have h2 : ∀ e : {e // p e}, φH e = some c ↔ φ e.1 = some c := by
        intro e; simp [φ, e.2]
      rw [Finset.filter_congr (fun e _ => h2 e)]
      show _ = ∑ e ∈ (H.inc v).filter (fun e => φ e.1 = some c), G.w e.1
      rw [hsumH v (fun e => φ e = some c) G.w]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, h⟩
        refine ⟨he, ?_, h⟩
        by_contra hp
        simp [φ, hp] at h
      · rintro ⟨he, -, h⟩; exact ⟨he, h⟩
    rw [this]; exact h1
  · intro e c h
    by_cases hp : p e
    · have : φH ⟨e, hp⟩ = some c := by simpa [φ, hp] using h
      exact hφs _ _ this
    · simp [φ, hp] at h
  · intro v
    have hc := hφc v
    -- colored weights agree
    have hcol : G.coloredWeight φ v = H.coloredWeight φH v := by
      unfold WGraph.coloredWeight
      have h2 : ∀ e : {e // p e}, (φH e).isSome ↔ (φ e.1).isSome := by
        intro e; simp [φ, e.2]
      rw [Finset.filter_congr (fun e _ => h2 e)]
      show _ = ∑ e ∈ (H.inc v).filter (fun e => (φ e.1).isSome), G.w e.1
      rw [hsumH v (fun e => (φ e).isSome = true) G.w]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, h⟩
        refine ⟨he, ?_, h⟩
        by_contra hp
        simp [φ, hp] at h
      · rintro ⟨he, -, h⟩; exact ⟨he, h⟩
    -- T^H
    have hTH : ∑ e ∈ H.inc v, H.w e * ∑ c, xH e c
        = ∑ e ∈ (G.inc v).filter p, G.w e * ∑ c, x e c := by
      have := hsumH v (fun _ => True) (fun e => G.w e * ∑ c, x e c)
      rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at this
      simp only [and_true] at this
      exact this
    -- T^G - T^H ≤ internal weight
    have hsplit := Finset.sum_filter_add_sum_filter_not (G.inc v) p (fun e => G.w e * ∑ c, x e c)
    have hint : ∑ e ∈ (G.inc v).filter (fun e => ¬ p e), G.w e * ∑ c, x e c
        ≤ ∑ e ∈ (G.inc v).filter (fun e => ∃ u, u ≠ v ∧ u ∈ G.ends e ∧ g u = g v), G.w e := by
      calc ∑ e ∈ (G.inc v).filter (fun e => ¬ p e), G.w e * ∑ c, x e c
          ≤ ∑ e ∈ (G.inc v).filter (fun e => ¬ p e), G.w e := by
            apply Finset.sum_le_sum
            intro e _
            have := G.w_pos e
            have h1 := hxs e
            nlinarith
        _ ≤ _ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro e he
              simp only [Finset.mem_filter] at he ⊢
              obtain ⟨hev, hnp⟩ := he
              refine ⟨hev, ?_⟩
              simp only [p, not_forall, not_not] at hnp
              obtain ⟨u, w', hends, hgg⟩ := hnp
              have hloop := G.loopless e
              rw [hends, Sym2.mk_isDiag_iff] at hloop
              have hv : v ∈ G.ends e := by
                simpa [WGraph.inc] using hev
              rw [hends, Sym2.mem_iff] at hv
              rcases hv with rfl | rfl
              · exact ⟨w', fun h => hloop h.symm, by rw [hends]; exact Sym2.mem_mk_right _ _, hgg.symm⟩
              · exact ⟨u, hloop, by rw [hends]; exact Sym2.mem_mk_left _ _, hgg⟩
            · intro e _ _; exact (G.w_pos e).le
    have hgv := hg v (g v)
    -- √(n log n) ≤ √2 n^{3/4} ≤ 2 n^{3/4}
    have hsq : Real.sqrt (n * Real.log n) ≤ 2 * n ^ (3 / 4 : ℝ) := by
      have hlog : Real.log n ≤ 2 * Real.sqrt n := by
        have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hnpos)
        rw [Real.log_sqrt hnpos.le] at h1
        linarith
      have h34 : n ^ (3 / 4 : ℝ) = Real.sqrt (n * Real.sqrt n) := by
        rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
        rw [← Real.rpow_add hnpos, Real.sqrt_eq_rpow]
        conv_rhs => rw [show n * n ^ (1/2:ℝ) = n ^ (1:ℝ) * n ^ (1/2:ℝ) by rw [Real.rpow_one]]
        rw [← Real.rpow_add hnpos]; norm_num
      rw [h34]
      have : Real.sqrt (n * Real.log n) ≤ Real.sqrt (n * (2 * Real.sqrt n)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hnpos.le)
      refine le_trans this ?_
      rw [show n * (2 * Real.sqrt n) = 2 * (n * Real.sqrt n) by ring, Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have h0 : 0 ≤ Real.sqrt (n * Real.sqrt n) := Real.sqrt_nonneg _
      nlinarith
    have hKsq : K * Real.sqrt (n * Real.log n) ≤ 2 * |K| * n ^ (3 / 4 : ℝ) := by
      have h0 : 0 ≤ Real.sqrt (n * Real.log n) := Real.sqrt_nonneg _
      calc K * Real.sqrt (n * Real.log n) ≤ |K| * Real.sqrt (n * Real.log n) :=
            mul_le_mul_of_nonneg_right (le_abs_self K) h0
        _ ≤ |K| * (2 * n ^ (3 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
        _ = 2 * |K| * n ^ (3 / 4 : ℝ) := by ring
    have hWr : G.W v / r ≤ ε / 4 * n := by
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
      rw [div_le_iff₀ hr']
      have := hW v
      have h1 : ε / 4 * n * r ≥ n := by
        have := hrε
        rw [div_le_iff₀ hr'] at this
        nlinarith
      linarith
    rw [hcol]
    rw [hTH] at hc
    have hεn : 0 ≤ ε * n := by positivity
    have hexp : (Kc' + 2 * |K|) * n ^ (3 / 4 : ℝ) = Kc' * n ^ (3 / 4 : ℝ) + 2 * |K| * n ^ (3 / 4 : ℝ) := by ring
    rw [hexp]
    linarith
