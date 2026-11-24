-- Prove2me | solution 1 for WeightedEdgeColor.lemma_whole_edge_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:07:56.320797+00:00
-- url     : https://prove2.me/submissions/6653e00d-2048-4be5-aeb5-88443914a5aa

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
import Theorems.Thm_WeightedEdgeColor_lemma_A_3
import Theorems.Thm_WeightedEdgeColor_lemma_large_edge_rounding

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WECWRAux
open WeightedEdgeColor WeightedEdgeColor.WGraph

theorem sum_subtype_dite {E : Type} [Fintype E] (p : E → Prop) [DecidablePred p]
    (F : {e // p e} → ℝ) :
    ∑ j, F j = ∑ e ∈ Finset.univ.filter p, (if h : p e then F ⟨e, h⟩ else 0) := by
  rw [Finset.sum_subtype (p := p) (Finset.univ.filter p) (by simp) (fun e => if h : p e then F ⟨e, h⟩ else 0)]
  apply Finset.sum_congr rfl
  intro j _
  simp [j.2]

theorem sum_pos_subtype {α : Type} [Fintype α] (pr h : α → ℝ) (hpr : ∀ o, 0 ≤ pr o) :
    ∑ o : {o // 0 < pr o}, pr o.1 * h o.1 = ∑ o, pr o * h o := by
  rw [← Finset.sum_subtype (p := fun o => 0 < pr o) (Finset.univ.filter (fun o => 0 < pr o)) (by simp) (fun o => pr o * h o)]
  apply Finset.sum_filter_of_ne
  intro o _ hne
  rcases (hpr o).lt_or_eq with h | h
  · exact h
  · exfalso; apply hne; rw [← h]; ring

end WECWRAux

open WeightedEdgeColor WeightedEdgeColor.WGraph WECWRAux

theorem solution (C₁ σ r₀ β Cm ε : ℝ) (Ks : ℕ)
    (hC₁ : 0 < C₁) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    (hβ0 : 0 < β) (hβ : β ≤ r₀) (hβσ : 2 * β ≤ σ * r₀) (hCm : 0 < Cm) (hε : 0 < ε) :
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ (b : V → 𝒞 → Fin Ks → ℝ) (R : V → 𝒞 → ℝ) (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ)
        (XS : E → 𝒞 → ℝ),
      (∀ v c, (∀ i, 0 ≤ b v c i) ∧ 0 ≤ R v c ∧ ∑ i, b v c i + R v c ≤ 1 ∧ (R v c = 0 ∨ r₀ ≤ R v c)) →
      (∀ e c i j, 0 ≤ XL e c i j) →
      (∀ e c, 0 ≤ XS e c) →
      (∀ e c i j, XL e c i j ≠ 0 → β ≤ G.w e ∧ G.w e ≤ b (src e) c i ∧ G.w e ≤ b (tgt e) c j) →
      (∀ e c, XS e c ≠ 0 → G.w e < β ∧ 0 < R (src e) c ∧ 0 < R (tgt e) c) →
      (∀ e, ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) ≤ 1) →
      (∀ e c, ∑ i, ∑ j, XL e c i j + XS e c ≤ Cm / n) →
      (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
         + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ) →
      (∀ v c, ∑ e ∈ G.inc v, G.w e * XS e c ≤ (1 - σ) * R v c) →
      ∃ φ : E → Option 𝒞, G.IsFeasiblePartialColoring φ ∧
        (∀ e c, φ e = some c → 0 < ∑ i, ∑ j, XL e c i j + XS e c) ∧
        ∀ v, (∑ e ∈ G.inc v, G.w e * ∑ c, (∑ i, ∑ j, XL e c i j + XS e c)) - ε * n
          - K * n ^ (2 / 3 : ℝ) ≤ G.coloredWeight φ v := by
  classical
  obtain ⟨n₀, K, hLR⟩ := lemma_large_edge_rounding C₁ σ β Cm ε Ks hC₁ hσ0 hσ1 hβ0 hCm hε
  set τ : ℝ := β / r₀ with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  have hβτ : β ≤ τ := le_div_self hβ0.le hr₀ hr₀1
  have h2τ : 2 * τ ≤ σ := by
    rw [hτdef, ← mul_div_assoc, div_le_iff₀ hr₀]; linarith
  refine ⟨max n₀ 1, K + 2 * τ, ?_⟩
  intro V E _ _ _ _ G hG src tgt hst n hn hW 𝒞 _ _ hcard b R XL XS hprof hXL0 hXS0 hXLc hXSc
    hsum hmass hslot hres
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  -- endpoints
  have hmem : ∀ e v, v ∈ G.ends e ↔ v = src e ∨ v = tgt e := by
    intro e v; rw [hst e, Sym2.mem_iff]
  have hst_ne : ∀ e, src e ≠ tgt e := by
    intro e h
    have := G.loopless e
    rw [hst e, Sym2.mk_isDiag_iff] at this
    exact this h
  -- small edges have no large options and vice versa
  have hXLsmall : ∀ e, G.w e < β → ∀ c i j, XL e c i j = 0 := by
    intro e he c i j
    by_contra h
    have := (hXLc e c i j h).1
    linarith
  have hXSlarge : ∀ e, ¬ G.w e < β → ∀ c, XS e c = 0 := by
    intro e he c
    by_contra h
    exact he (hXSc e c h).1
  -- the large-edge rounding
  have hsumL : ∀ e, ∑ c, ∑ i, ∑ j, XL e c i j ≤ 1 := by
    intro e
    refine le_trans (Finset.sum_le_sum (fun c _ => ?_)) (hsum e)
    exact le_add_of_nonneg_right (hXS0 e c)
  have hmassL : ∀ e c, ∑ i, ∑ j, XL e c i j ≤ Cm / n :=
    fun e c => le_trans (le_add_of_nonneg_right (hXS0 e c)) (hmass e c)
  obtain ⟨ψ, hψpos, hψslot, hψunc⟩ := hLR V E G hG src tgt hst n hn0 hW 𝒞 hcard b XL hXL0
    hXLc hsumL hmassL hslot
  -- the small-edge rounding via Lemma A.3
  let pr : E → Option 𝒞 → ℝ := fun e o => o.elim (1 - ∑ c, XS e c) (fun c => XS e c)
  have hsmall_sum : ∀ e, G.w e < β → ∑ c, XS e c ≤ 1 := by
    intro e he
    refine le_trans (le_of_eq ?_) (hsum e)
    apply Finset.sum_congr rfl
    intro c _
    simp [hXLsmall e he]
  have hpr0 : ∀ e, G.w e < β → ∀ o, 0 ≤ pr e o := by
    intro e he o
    cases o with
    | none => simp only [pr, Option.elim]; linarith [hsmall_sum e he]
    | some c => exact hXS0 e c
  let J := {e : E // G.w e < β}
  let O : J → Type := fun j => {o : Option 𝒞 // 0 < pr j.1 o}
  let Q := (V × 𝒞) ⊕ V
  let amt' : E → Option 𝒞 → Q → ℝ := fun e o q =>
    Sum.elim (fun vc : V × 𝒞 => if o = some vc.2 ∧ vc.1 ∈ G.ends e then G.w e / R vc.1 vc.2 else 0)
      (fun v : V => if o = none ∧ v ∈ G.ends e then G.w e else 0) q
  have hp : ∀ (j : J) (o : O j), 0 ≤ pr j.1 o.1 := fun j o => o.2.le
  have hp1 : ∀ j : J, ∑ o : O j, pr j.1 o.1 = 1 := by
    intro j
    have := sum_pos_subtype (pr j.1) (fun _ => (1 : ℝ)) (hpr0 j.1 j.2)
    simp only [mul_one] at this
    rw [this, Fintype.sum_option]
    simp [pr]
  have hRpos : ∀ e c v, 0 < XS e c → v ∈ G.ends e → r₀ ≤ R v c := by
    intro e c v hx hv
    have h := hXSc e c hx.ne'
    have hRv : 0 < R v c := by
      rcases (hmem e v).mp hv with rfl | rfl
      · exact h.2.1
      · exact h.2.2
    rcases (hprof v c).2.2.2 with h0 | h0
    · linarith
    · exact h0
  have hamt : ∀ (j : J) (o : O j) (q : Q), 0 ≤ amt' j.1 o.1 q ∧ amt' j.1 o.1 q ≤ τ := by
    intro j o q
    have hw := G.w_pos j.1
    cases q with
    | inl vc =>
      simp only [amt', Sum.elim_inl]
      split_ifs with h
      · obtain ⟨ho, hv⟩ := h
        have hx : 0 < XS j.1 vc.2 := by
          have := o.2
          rw [ho] at this
          simpa [pr] using this
        have hR := hRpos j.1 vc.2 vc.1 hx hv
        have hRp : 0 < R vc.1 vc.2 := lt_of_lt_of_le hr₀ hR
        constructor
        · positivity
        · rw [div_le_div_iff₀ hRp hr₀]
          have := j.2
          nlinarith
      · exact ⟨le_refl _, hτ0⟩
    | inr v =>
      simp only [amt', Sum.elim_inr]
      split_ifs with h
      · exact ⟨hw.le, le_trans j.2.le hβτ⟩
      · exact ⟨le_refl _, hτ0⟩
  have htwo : ∀ (j : J) (o : O j), ∃ s : Finset Q, s.card ≤ 2 ∧ ∀ q ∉ s, amt' j.1 o.1 q = 0 := by
    intro j o
    cases ho : o.1 with
    | none =>
      refine ⟨{Sum.inr (src j.1), Sum.inr (tgt j.1)}, Finset.card_le_two, ?_⟩
      intro q hq
      cases q with
      | inl vc => simp [amt', ho]
      | inr v =>
        simp only [amt', Sum.elim_inr, ho, true_and]
        rw [if_neg]
        intro hv
        apply hq
        rcases (hmem j.1 v).mp hv with rfl | rfl <;> simp
    | some c =>
      refine ⟨{Sum.inl (src j.1, c), Sum.inl (tgt j.1, c)}, Finset.card_le_two, ?_⟩
      intro q hq
      cases q with
      | inr v => simp [amt', ho]
      | inl vc =>
        simp only [amt', Sum.elim_inl, ho]
        rw [if_neg]
        rintro ⟨hc, hv⟩
        apply hq
        obtain ⟨v', c'⟩ := vc
        simp only [Option.some.injEq] at hc
        subst hc
        rcases (hmem j.1 v').mp hv with rfl | rfl <;> simp
  obtain ⟨σ', hσ'⟩ := lemma_A_3 J Q O (fun j o => pr j.1 o.1) (fun j o q => amt' j.1 o.1 q) τ
    hp hp1 hamt htwo hτ0
  -- the coloring
  let φ : E → Option 𝒞 := fun e =>
    if h : G.w e < β then (σ' ⟨e, h⟩).1 else (ψ e).map (fun t => t.1)
  have hφs : ∀ e (h : G.w e < β), φ e = (σ' ⟨e, h⟩).1 := fun e h => by simp [φ, h]
  have hφl : ∀ e, ¬ G.w e < β → φ e = (ψ e).map (fun t => t.1) := fun e h => by simp [φ, h]
  -- translating the sums of Lemma A.3
  have hLHS : ∀ q, ∑ j : J, amt' j.1 (σ' j).1 q
      = ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), amt' e (φ e) q := by
    intro q
    rw [Finset.sum_subtype (p := fun e => G.w e < β) (Finset.univ.filter (fun e => G.w e < β))
      (by simp) (fun e => amt' e (φ e) q)]
    apply Finset.sum_congr rfl
    intro j _
    rw [hφs j.1 j.2]
  have hRHS : ∀ q, ∑ j : J, ∑ o : O j, pr j.1 o.1 * amt' j.1 o.1 q
      = ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), ∑ o, pr e o * amt' e o q := by
    intro q
    rw [Finset.sum_subtype (p := fun e => G.w e < β) (Finset.univ.filter (fun e => G.w e < β))
      (by simp) (fun e => ∑ o, pr e o * amt' e o q)]
    apply Finset.sum_congr rfl
    intro j _
    exact sum_pos_subtype (pr j.1) (fun o => amt' j.1 o q) (hpr0 j.1 j.2)
  have hA3 : ∀ q, ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), amt' e (φ e) q
      ≤ ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), ∑ o, pr e o * amt' e o q + 2 * τ := by
    intro q; rw [← hLHS q, ← hRHS q]; exact hσ' q
  have hφsmall_pos : ∀ e (h : G.w e < β) c, φ e = some c → 0 < XS e c := by
    intro e h c hc
    have := (σ' ⟨e, h⟩).2
    rw [← hφs e h, hc] at this
    simpa [pr] using this
  have hφlarge : ∀ e, ¬ G.w e < β → ∀ c, φ e = some c → ∃ i j, ψ e = some (c, i, j) := by
    intro e h c hc
    rw [hφl e h, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c', i, j⟩, h1, h2⟩ := hc
    simp only at h2
    subst h2
    exact ⟨i, j, h1⟩
  -- sums over `inc v` and over the small edges, as sums over all edges
  have hinc : ∀ (v : V) (f : E → ℝ), ∑ e ∈ G.inc v, f e = ∑ e, if v ∈ G.ends e then f e else 0 := by
    intro v f; unfold WGraph.inc; rw [Finset.sum_filter]
  have hsm : ∀ (f : E → ℝ), ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), f e
      = ∑ e, if G.w e < β then f e else 0 := by
    intro f; rw [Finset.sum_filter]
  refine ⟨φ, ?_, ?_, ?_⟩
  · -- feasibility
    intro v c
    have hsplit := Finset.sum_filter_add_sum_filter_not ((G.inc v).filter (fun e => φ e = some c))
      (fun e => G.w e < β) G.w
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit
    rw [← hsplit]
    -- large part
    have hlarge : ∑ e ∈ (G.inc v).filter (fun e => φ e = some c ∧ ¬ G.w e < β), G.w e
        ≤ ∑ i, b v c i := by
      set L := (G.inc v).filter (fun e => φ e = some c ∧ ¬ G.w e < β) with hL
      rcases L.eq_empty_or_nonempty with hLe | ⟨e₀, he₀⟩
      · rw [hLe, Finset.sum_empty]
        exact Finset.sum_nonneg (fun i _ => (hprof v c).1 i)
      obtain ⟨i₀, -, -⟩ := hφlarge e₀ (Finset.mem_filter.mp he₀).2.2 c (Finset.mem_filter.mp he₀).2.1
      let sl : E → Fin Ks := fun e => (ψ e).elim i₀ (fun t => if src e = v then t.2.1 else t.2.2)
      have huse : ∀ e ∈ L, (∃ j, (src e = v ∧ ψ e = some (c, sl e, j)) ∨
          (tgt e = v ∧ ψ e = some (c, j, sl e))) ∧ G.w e ≤ b v c (sl e) := by
        intro e he
        obtain ⟨hev, hφe, hlg⟩ := Finset.mem_filter.mp he
        obtain ⟨i, j, hψe⟩ := hφlarge e hlg c hφe
        have hcomp := hXLc e c i j (hψpos e c i j hψe).ne'
        have hv : v ∈ G.ends e := by simpa [WGraph.inc] using hev
        by_cases hs : src e = v
        · have : sl e = i := by simp [sl, hψe, hs]
          rw [this]
          refine ⟨⟨j, Or.inl ⟨hs, hψe⟩⟩, ?_⟩
          rw [← hs]; exact hcomp.2.1
        · have ht : tgt e = v := by
            rcases (hmem e v).mp hv with h | h
            · exact absurd h.symm hs
            · exact h.symm
          have : sl e = j := by simp [sl, hψe, hs]
          rw [this]
          refine ⟨⟨i, Or.inr ⟨ht, hψe⟩⟩, ?_⟩
          rw [← ht]; exact hcomp.2.2
      have hinj : Set.InjOn sl L := by
        intro e he e' he' h
        have h1 := (huse e he).1
        have h2 := (huse e' he').1
        rw [h] at h1
        exact hψslot e e' v c (sl e') h1 h2
      calc ∑ e ∈ L, G.w e ≤ ∑ e ∈ L, b v c (sl e) := Finset.sum_le_sum (fun e he => (huse e he).2)
        _ = ∑ i ∈ L.image sl, b v c i := (Finset.sum_image hinj).symm
        _ ≤ ∑ i, b v c i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => (hprof v c).1 i)
    -- small part
    have hsmallp : ∑ e ∈ (G.inc v).filter (fun e => φ e = some c ∧ G.w e < β), G.w e ≤ R v c := by
      set S := (G.inc v).filter (fun e => φ e = some c ∧ G.w e < β) with hS
      rcases S.eq_empty_or_nonempty with hSe | ⟨e₀, he₀⟩
      · rw [hSe, Finset.sum_empty]; exact (hprof v c).2.1
      have he₀' := Finset.mem_filter.mp he₀
      have hR : r₀ ≤ R v c := hRpos e₀ c v (hφsmall_pos e₀ he₀'.2.2 c he₀'.2.1)
        (by simpa [WGraph.inc] using he₀'.1)
      have hRp : 0 < R v c := lt_of_lt_of_le hr₀ hR
      have h := hA3 (Sum.inl (v, c))
      have hl : ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), amt' e (φ e) (Sum.inl (v, c))
          = (∑ e ∈ S, G.w e) / R v c := by
        rw [hsm, Finset.sum_div, hS, Finset.sum_filter, hinc]
        apply Finset.sum_congr rfl
        intro e _
        simp only [amt', Sum.elim_inl]
        by_cases h1 : G.w e < β <;> by_cases h2 : v ∈ G.ends e <;> by_cases h3 : φ e = some c <;>
          simp [h1, h2, h3]
      have hr : ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), ∑ o, pr e o * amt' e o (Sum.inl (v, c))
          ≤ 1 - σ := by
        have hle : ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), ∑ o, pr e o * amt' e o (Sum.inl (v, c))
            ≤ (∑ e ∈ G.inc v, G.w e * XS e c) / R v c := by
          rw [hsm, Finset.sum_div, hinc]
          apply Finset.sum_le_sum
          intro e _
          rw [Fintype.sum_option]
          simp only [amt', Sum.elim_inl, pr, Option.elim]
          have hsum1 : ∑ x : 𝒞, XS e x * (if some x = some c ∧ v ∈ G.ends e then G.w e / R v c else 0)
              = XS e c * (if v ∈ G.ends e then G.w e / R v c else 0) := by
            rw [Finset.sum_eq_single c]
            · simp
            · intro c' _ hc'; simp [hc']
            · simp
          rw [hsum1]
          have hw0 := (G.w_pos e).le
          have hx0 := hXS0 e c
          by_cases h1 : G.w e < β <;> by_cases h2 : v ∈ G.ends e
          · apply le_of_eq; simp [h1, h2]; ring
          · simp [h1, h2]
          · simp only [h1, h2, if_true, if_false]; exact div_nonneg (mul_nonneg hw0 hx0) hRp.le
          · simp [h1, h2]
        refine le_trans hle ?_
        rw [div_le_iff₀ hRp]
        exact hres v c
      have : (∑ e ∈ S, G.w e) / R v c ≤ 1 := by
        rw [← hl]; linarith
      rwa [div_le_one hRp] at this
    have := (hprof v c).2.2.1
    linarith
  · -- support
    intro e c hc
    have hXL : 0 ≤ ∑ i, ∑ j, XL e c i j :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hXL0 e c i j))
    by_cases h : G.w e < β
    · have := hφsmall_pos e h c hc; linarith
    · obtain ⟨i, j, hψe⟩ := hφlarge e h c hc
      have hpos := hψpos e c i j hψe
      have h1 : XL e c i j ≤ ∑ j', XL e c i j' :=
        Finset.single_le_sum (f := fun j' => XL e c i j') (fun j' _ => hXL0 e c i j') (Finset.mem_univ j)
      have h2 : ∑ j', XL e c i j' ≤ ∑ i', ∑ j', XL e c i' j' :=
        Finset.single_le_sum (f := fun i' => ∑ j', XL e c i' j')
          (fun i' _ => Finset.sum_nonneg (fun j' _ => hXL0 e c i' j')) (Finset.mem_univ i)
      linarith [hXS0 e c]
  · -- colored weight
    intro v
    have hLRv := hψunc v
    have hA3v := hA3 (Sum.inr v)
    -- rewrite everything as sums over all edges
    rw [Finset.sum_filter, Finset.sum_filter, hinc, hinc] at hLRv
    have hA3L : ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), amt' e (φ e) (Sum.inr v)
        = ∑ e, if G.w e < β then (if φ e = none ∧ v ∈ G.ends e then G.w e else 0) else 0 := by
      rw [hsm]
      apply Finset.sum_congr rfl; intro e _; rfl
    have hA3R : ∑ e ∈ Finset.univ.filter (fun e => G.w e < β), ∑ o, pr e o * amt' e o (Sum.inr v)
        = ∑ e, if G.w e < β then (if v ∈ G.ends e then G.w e * (1 - ∑ c, XS e c) else 0) else 0 := by
      rw [hsm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Fintype.sum_option]
      by_cases h2 : v ∈ G.ends e <;> simp [amt', pr, h2, mul_comm]
    rw [hA3L, hA3R] at hA3v
    have hcw : G.coloredWeight φ v
        = ∑ e, if v ∈ G.ends e then (if (φ e).isSome then G.w e else 0) else 0 := by
      unfold WGraph.coloredWeight; rw [Finset.sum_filter, hinc]
    rw [hcw, hinc]
    have hsL : ∀ e, ¬ G.w e < β → ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) = ∑ c, ∑ i, ∑ j, XL e c i j := by
      intro e he; simp [hXSlarge e he]
    have hsS : ∀ e, G.w e < β → ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) = ∑ c, XS e c := by
      intro e he; simp [hXLsmall e he]
    let A : E → ℝ := fun e => if v ∈ G.ends e then G.w e * ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) else 0
    let B : E → ℝ := fun e =>
      if v ∈ G.ends e then (if β ≤ G.w e then G.w e * (1 - ∑ c, ∑ i, ∑ j, XL e c i j) else 0) else 0
    let C : E → ℝ := fun e =>
      if G.w e < β then (if v ∈ G.ends e then G.w e * (1 - ∑ c, XS e c) else 0) else 0
    let D : E → ℝ := fun e => if v ∈ G.ends e then (if (φ e).isSome then G.w e else 0) else 0
    let F : E → ℝ := fun e => if v ∈ G.ends e then (if β ≤ G.w e ∧ ψ e = none then G.w e else 0) else 0
    let H : E → ℝ := fun e => if G.w e < β then (if φ e = none ∧ v ∈ G.ends e then G.w e else 0) else 0
    have hpt : ∀ e, A e + B e + C e = D e + F e + H e := by
      intro e
      simp only [A, B, C, D, F, H]
      by_cases hv : v ∈ G.ends e
      · by_cases hs : G.w e < β
        · have hnl : ¬ β ≤ G.w e := not_le.mpr hs
          rw [hsS e hs]
          cases hφe : φ e with
          | none => simp [hv, hs, hnl]; ring
          | some c => simp [hv, hs, hnl]; ring
        · have hl : β ≤ G.w e := not_lt.mp hs
          rw [hsL e hs]
          have hφe := hφl e hs
          cases hψe : ψ e with
          | none =>
            rw [hψe] at hφe
            simp [hv, hs, hl, hφe]; ring
          | some t =>
            rw [hψe] at hφe
            simp [hv, hs, hl, hφe]; ring
      · simp [hv]
    have hsumpt : ∑ e, A e + ∑ e, B e + ∑ e, C e = ∑ e, D e + ∑ e, F e + ∑ e, H e := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun e _ => hpt e)
    change ∑ e, F e ≤ ∑ e, B e + ε * n + K * n ^ (2 / 3 : ℝ) at hLRv
    change ∑ e, H e ≤ ∑ e, C e + 2 * τ at hA3v
    show ∑ e, A e - ε * n - (K + 2 * τ) * n ^ (2 / 3 : ℝ) ≤ ∑ e, D e
    have hpow : 1 ≤ n ^ (2 / 3 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
    have hτn : 2 * τ ≤ 2 * τ * n ^ (2 / 3 : ℝ) := by nlinarith
    have hexp : (K + 2 * τ) * n ^ (2 / 3 : ℝ) = K * n ^ (2 / 3 : ℝ) + 2 * τ * n ^ (2 / 3 : ℝ) := by
      ring
    rw [hexp]
    linarith
