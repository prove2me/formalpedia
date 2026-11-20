-- Prove2me | solution 1 for SpreadMatchCircuit.Matching.Supplement.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:44:24.61504+00:00
-- url     : https://prove2.me/submissions/8d143308-d38f-4439-8d40-a915d460138e

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_SetSpread
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_Cliques

section
/-!
# The Spread Set Lemma (Lemma 3), by Rao's encoding argument

Product-measure version with staged sampling: `N` independent `δ`-random sets
`W_1, …, W_N` (whose union is `γ`-random for `δ = 1 - (1-γ)^{1/N}`), scales
`s = q, q-1, …, 0` with `J_s` repetitions each, residual maps `ρ_ℓ`, a one-stage encoding
bound `2^{2^{s+1}} y^{2^s}` (`y = (1-δ)/(δ r)`), Markov with thresholds `2^{-(s+1)}` and the
sequential (chain) bound over the repetitions of a scale.
-/

namespace SpreadMatchCircuit.Matching.Dev.SpreadSet

open Finset

open scoped Classical

noncomputable section

section Weights
variable {β : Type} [Fintype β] [DecidableEq β]

/-- Weight of `G` under the product measure of density `d`. -/
def wt (d : ℝ) (G : Finset β) : ℝ := d ^ G.card * (1 - d) ^ (Fintype.card β - G.card)

lemma wt_nonneg {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (G : Finset β) : 0 ≤ wt d G :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

lemma sum_pow_sub (a b : ℝ) (s : Finset β) :
    ∑ t ∈ s.powerset, a ^ t.card * b ^ (s.card - t.card) = (a + b) ^ s.card :=
  Finset.sum_pow_mul_eq_add_pow a b s

lemma sum_wt (d : ℝ) : ∑ G : Finset β, wt d G = 1 := by
  unfold wt
  rw [← powerset_univ, ← card_univ, sum_pow_sub]
  simp

lemma wt_sdiff {d : ℝ} (hd : 0 < d) {U A : Finset β} (hA : A ⊆ U) :
    wt d (U \ A) = wt d U * ((1 - d) / d) ^ A.card := by
  unfold wt
  have hU := card_le_univ U
  have hAU := card_le_card hA
  rw [card_sdiff_of_subset hA]
  have e : Fintype.card β - (U.card - A.card) = (Fintype.card β - U.card) + A.card := by omega
  rw [e, pow_add, div_pow]
  have hdA : d ^ A.card ≠ 0 := pow_ne_zero _ hd.ne'
  have : d ^ (U.card - A.card) = d ^ U.card / d ^ A.card := by
    rw [eq_div_iff hdA, pow_sub_mul_pow _ hAU]
  rw [this]
  field_simp

/-- Fibre decomposition: `V ↔ (G ∪ V, V ∩ G)`. -/
lemma sum_fibre (G : Finset β) (φ : Finset β → ℝ) :
    ∑ V : Finset β, φ V =
      ∑ W ∈ univ.filter (fun W => G ⊆ W), ∑ V' ∈ G.powerset, φ ((W \ G) ∪ V') := by
  rw [← sum_product']
  apply Finset.sum_nbij' (fun V => (G ∪ V, V ∩ G)) (fun p => (p.1 \ G) ∪ p.2)
  · intro V _
    simp only [mem_product, mem_filter, mem_univ, true_and, mem_powerset]
    exact ⟨subset_union_left, inter_subset_right⟩
  · intro p _; exact mem_univ _
  · intro V _
    ext x; simp only [mem_union, mem_sdiff, mem_inter]; tauto
  · intro p hp
    simp only [mem_product, mem_filter, mem_univ, true_and, mem_powerset] at hp
    obtain ⟨h1, h2⟩ := hp
    ext x
    · simp only [mem_union, mem_sdiff]
      constructor
      · rintro (h | (h | h))
        · exact h1 h
        · exact h.1
        · exact h1 (h2 h)
      · intro h; by_cases hG : x ∈ G
        · exact Or.inl hG
        · exact Or.inr (Or.inl ⟨h, hG⟩)
    · simp only [mem_inter, mem_union, mem_sdiff]
      constructor
      · rintro ⟨(h | h), hG⟩
        · exact absurd hG h.2
        · exact h
      · intro h; exact ⟨Or.inr h, h2 h⟩
  · intro V _
    congr 1
    ext x; simp only [mem_union, mem_sdiff, mem_inter]; tauto

lemma sum_wt_fibre (c : ℝ) {G W : Finset β} (hGW : G ⊆ W) :
    ∑ V' ∈ G.powerset, wt c ((W \ G) ∪ V') =
      c ^ (W.card - G.card) * (1 - c) ^ (Fintype.card β - W.card) := by
  have hW := card_le_univ W
  have hG := card_le_card hGW
  have key : ∀ V' ∈ G.powerset, wt c ((W \ G) ∪ V') =
      c ^ (W.card - G.card) * (1 - c) ^ (Fintype.card β - W.card) *
        (c ^ V'.card * (1 - c) ^ (G.card - V'.card)) := by
    intro V' hV'
    rw [mem_powerset] at hV'
    have hd : Disjoint (W \ G) V' := by
      rw [disjoint_left]; intro x h1 h2; exact (mem_sdiff.1 h1).2 (hV' h2)
    have hV := card_le_card hV'
    unfold wt
    rw [card_union_of_disjoint hd, card_sdiff_of_subset hGW]
    have e : Fintype.card β - (W.card - G.card + V'.card) =
        (Fintype.card β - W.card) + (G.card - V'.card) := by omega
    rw [e, pow_add, pow_add]; ring
  rw [sum_congr rfl key, ← mul_sum, sum_pow_sub]
  simp

/-- The union of independent `a`- and `c`-random sets is `(1-(1-a)(1-c))`-random. -/
lemma sum_union (a c : ℝ) (h : Finset β → ℝ) :
    ∑ G : Finset β, wt a G * ∑ V : Finset β, wt c V * h (G ∪ V) =
      ∑ W : Finset β, wt (1 - (1 - a) * (1 - c)) W * h W := by
  have step1 : ∀ G : Finset β, ∑ V : Finset β, wt c V * h (G ∪ V) =
      ∑ W ∈ univ.filter (fun W => G ⊆ W),
        c ^ (W.card - G.card) * (1 - c) ^ (Fintype.card β - W.card) * h W := by
    intro G
    rw [sum_fibre G]
    apply sum_congr rfl; intro W hW
    rw [mem_filter] at hW
    have hU : ∀ V' ∈ G.powerset, G ∪ ((W \ G) ∪ V') = W := by
      intro V' hV'
      rw [mem_powerset] at hV'
      ext x; simp only [mem_union, mem_sdiff]
      constructor
      · rintro (h | (h | h))
        · exact hW.2 h
        · exact h.1
        · exact hW.2 (hV' h)
      · intro hx; by_cases hG : x ∈ G
        · exact Or.inl hG
        · exact Or.inr (Or.inl ⟨hx, hG⟩)
    rw [sum_congr rfl (fun V' hV' => by rw [hU V' hV']), ← sum_mul, sum_wt_fibre c hW.2]
  simp_rw [step1, mul_sum]
  rw [sum_comm' (t' := univ) (s' := fun W => W.powerset)]
  · apply sum_congr rfl; intro W _
    have hW := card_le_univ W
    have key : ∀ G ∈ W.powerset, wt a G *
        (c ^ (W.card - G.card) * (1 - c) ^ (Fintype.card β - W.card) * h W) =
        ((1 - a) ^ (Fintype.card β - W.card) * (1 - c) ^ (Fintype.card β - W.card) * h W) *
          (a ^ G.card * ((1 - a) * c) ^ (W.card - G.card)) := by
      intro G hG
      rw [mem_powerset] at hG
      have hGc := card_le_card hG
      unfold wt
      have e : Fintype.card β - G.card = (Fintype.card β - W.card) + (W.card - G.card) := by omega
      rw [e, pow_add, mul_pow]; ring
    rw [sum_congr rfl key, ← mul_sum, sum_pow_sub]
    unfold wt
    have : 1 - (1 - (1 - a) * (1 - c)) = (1 - a) * (1 - c) := by ring
    rw [this, mul_pow]
    have : a + (1 - a) * c = 1 - (1 - a) * (1 - c) := by ring
    rw [this]; ring
  · intro G W
    simp [mem_filter, mem_powerset]

end Weights

section Ex
variable {β : Type} [Fintype β] [DecidableEq β]

/-- Expectation over `L` further independent `d`-random stages appended (newest first). -/
def Ex (d : ℝ) (F : List (Finset β) → ℝ) : List (Finset β) → ℕ → ℝ
  | p, 0 => F p
  | p, L + 1 => ∑ G : Finset β, wt d G * Ex d F (G :: p) L

/-- Union of the stages. -/
def Ul : List (Finset β) → Finset β
  | [] => ∅
  | G :: p => G ∪ Ul p

lemma Ex_union (d : ℝ) (g : Finset β → ℝ) : ∀ (L : ℕ) (p : List (Finset β)),
    Ex d (fun l => g (Ul l)) p L = ∑ V : Finset β, wt (1 - (1 - d) ^ L) V * g (Ul p ∪ V)
  | 0, p => by
    simp only [Ex, pow_zero, sub_self]
    rw [sum_eq_single (∅ : Finset β)]
    · simp [wt]
    · intro V _ hV
      have : 0 < V.card := card_pos.2 (nonempty_iff_ne_empty.2 hV)
      simp [wt, zero_pow this.ne']
    · intro h; exact absurd (mem_univ _) h
  | L + 1, p => by
    simp only [Ex]
    simp_rw [Ex_union d g L]
    have : ∀ G V : Finset β, g (Ul (G :: p) ∪ V) = g (Ul p ∪ (G ∪ V)) := by
      intro G V; congr 1; simp only [Ul]
      ext x; simp only [mem_union]; tauto
    simp_rw [this]
    rw [sum_union d (1 - (1 - d) ^ L) (fun W => g (Ul p ∪ W))]
    have : 1 - (1 - d) * (1 - (1 - (1 - d) ^ L)) = 1 - (1 - d) ^ (L + 1) := by ring
    rw [this]

lemma Ex_mono {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) {F F' : List (Finset β) → ℝ} :
    ∀ (L : ℕ) (p : List (Finset β)), (∀ l : List (Finset β), l.length = p.length + L → F l ≤ F' l) →
      Ex d F p L ≤ Ex d F' p L
  | 0, p, h => h p (by simp)
  | L + 1, p, h => by
    simp only [Ex]
    apply sum_le_sum; intro G _
    apply mul_le_mul_of_nonneg_left _ (wt_nonneg h0 h1 G)
    apply Ex_mono h0 h1 L (G :: p)
    intro l hl; apply h; simp only [List.length_cons] at hl; omega

lemma Ex_sum (d : ℝ) {ι : Type} (S : Finset ι) (F : ι → List (Finset β) → ℝ) :
    ∀ (L : ℕ) (p : List (Finset β)),
      Ex d (fun l => ∑ i ∈ S, F i l) p L = ∑ i ∈ S, Ex d (F i) p L
  | 0, p => rfl
  | L + 1, p => by
    simp only [Ex]
    simp_rw [Ex_sum d S F L, mul_sum]
    exact sum_comm

/-- All stages in `K` satisfy `A` (stage `j` sees the prefix of the first `j` sets). -/
def AllA (K : Finset ℕ) (A : List (Finset β) → Finset β → Prop) : List (Finset β) → Prop
  | [] => True
  | G :: p => AllA K A p ∧ (p.length ∈ K → A p G)

/-- Exponent bookkeeping. -/
def ex (K : Finset ℕ) (m L : ℕ) : ℕ := ∑ k ∈ range L, if m + k ∈ K then 1 else 0

lemma ex_succ (K : Finset ℕ) (m L : ℕ) :
    ex K m (L + 1) = ex K (m + 1) L + if m ∈ K then 1 else 0 := by
  unfold ex
  rw [sum_range_succ']
  simp only [add_zero]
  congr 1
  apply sum_congr rfl; intro k _
  rw [show m + (k + 1) = m + 1 + k by omega]

/-- The chain (sequential Markov) bound. -/
theorem chain {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (K : Finset ℕ)
    (A : List (Finset β) → Finset β → Prop) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ p : List (Finset β), p.length ∈ K →
      ∑ G : Finset β, wt d G * (if A p G then 1 else 0) ≤ c) :
    ∀ (L : ℕ) (p : List (Finset β)),
      Ex d (fun l => if AllA K A l then 1 else 0) p L ≤
        (if AllA K A p then 1 else 0) * c ^ ex K p.length L
  | 0, p => by simp [Ex, ex]
  | L + 1, p => by
    simp only [Ex]
    have ih : ∀ G : Finset β, wt d G * Ex d (fun l => if AllA K A l then 1 else 0) (G :: p) L ≤
        wt d G * ((if AllA K A p then 1 else 0) * (if p.length ∈ K → A p G then 1 else 0)) *
          c ^ ex K (p.length + 1) L := by
      intro G
      have := chain h0 h1 K A c hc hA L (G :: p)
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (wt_nonneg h0 h1 G)
      refine this.trans (le_of_eq ?_)
      rw [List.length_cons]
      have hiff : AllA K A (G :: p) ↔ AllA K A p ∧ (p.length ∈ K → A p G) := Iff.rfl
      by_cases ha : AllA K A p <;> by_cases hb : (p.length ∈ K → A p G)
      · rw [if_pos (hiff.2 ⟨ha, hb⟩), if_pos ha, if_pos hb]; ring
      · rw [if_neg (fun h => hb (hiff.1 h).2), if_neg hb]; ring
      · rw [if_neg (fun h => ha (hiff.1 h).1), if_neg ha]; ring
      · rw [if_neg (fun h => ha (hiff.1 h).1), if_neg ha]; ring
    refine (sum_le_sum fun G _ => ih G).trans ?_
    rw [← sum_mul, ex_succ, pow_add]
    have hcp : 0 ≤ c ^ ex K (p.length + 1) L := pow_nonneg hc _
    by_cases hAp : AllA K A p
    · by_cases hK : p.length ∈ K
      · have hs : ∑ G : Finset β, wt d G * ((if AllA K A p then 1 else 0) *
            (if p.length ∈ K → A p G then 1 else 0)) =
            ∑ G : Finset β, wt d G * (if A p G then 1 else 0) := by
          apply sum_congr rfl; intro G _; simp [hAp, hK]
        rw [hs, if_pos hAp, if_pos hK, pow_one, one_mul]
        calc (∑ G : Finset β, wt d G * (if A p G then 1 else 0)) * c ^ ex K (p.length + 1) L
            ≤ c * c ^ ex K (p.length + 1) L := mul_le_mul_of_nonneg_right (hA p hK) hcp
          _ = _ := by ring
      · have hs : ∑ G : Finset β, wt d G * ((if AllA K A p then 1 else 0) *
            (if p.length ∈ K → A p G then 1 else 0)) = 1 := by
          refine (sum_congr rfl (fun G _ => ?_)).trans (sum_wt d)
          rw [if_pos hAp, if_pos (fun h => absurd h hK)]; ring
        rw [hs, if_pos hAp, if_neg hK]; simp
    · have hs : ∑ G : Finset β, wt d G * ((if AllA K A p then 1 else 0) *
          (if p.length ∈ K → A p G then 1 else 0)) = 0 := by
        apply sum_eq_zero; intro G _; simp [hAp]
      rw [hs, if_neg hAp]; simp

/-- Transfer: if a mass `≥ θ` of `z` have all stages in `K` satisfying `E · · z`, then every
stage in `K` has mass `≥ θ` of such `z`. -/
lemma allA_mass (K : Finset ℕ) (E : List (Finset β) → Finset β → Finset β → Prop)
    (m : Finset β → ℝ) (hm : ∀ z, 0 ≤ m z) (Z : Finset (Finset β)) (θ : ℝ) :
    ∀ l : List (Finset β),
      θ ≤ ∑ z ∈ Z.filter (fun z => AllA K (fun p G => E p G z) l), m z →
        AllA K (fun p G => θ ≤ ∑ z ∈ Z.filter (fun z => E p G z), m z) l
  | [], _ => trivial
  | G :: p, h => by
    have hiff : ∀ (A : List (Finset β) → Finset β → Prop),
        AllA K A (G :: p) ↔ AllA K A p ∧ (p.length ∈ K → A p G) := fun A => Iff.rfl
    refine (hiff _).2 ⟨allA_mass K E m hm Z θ p (h.trans ?_), fun hK => h.trans ?_⟩
    · apply sum_le_sum_of_subset_of_nonneg
      · intro z hz; obtain ⟨h1, h2⟩ := mem_filter.1 hz
        exact mem_filter.2 ⟨h1, ((hiff _).1 h2).1⟩
      · intro z _ _; exact hm z
    · apply sum_le_sum_of_subset_of_nonneg
      · intro z hz; obtain ⟨h1, h2⟩ := mem_filter.1 hz
        exact mem_filter.2 ⟨h1, ((hiff _).1 h2).2 hK⟩
      · intro z _ _; exact hm z

/-- Index form of `AllA` (sufficient direction). -/
lemma allA_of_forall (K : Finset ℕ) (A : List (Finset β) → Finset β → Prop) :
    ∀ l : List (Finset β),
      (∀ j < l.length, j ∈ K → A (l.drop (l.length - j)) (l.getD (l.length - j - 1) ∅)) →
        AllA K A l
  | [], _ => trivial
  | G :: p, h => by
    simp only [AllA]
    refine ⟨allA_of_forall K A p (fun j hj hK => ?_), fun hK => ?_⟩
    · have := h j (by simp; omega) hK
      simp only [List.length_cons] at this
      obtain ⟨k, hk⟩ : ∃ k, p.length - j = k + 1 := ⟨p.length - j - 1, by omega⟩
      have e1 : p.length + 1 - j = k + 1 + 1 := by omega
      rw [e1, List.drop_succ_cons, Nat.add_sub_cancel, List.getD_cons_succ] at this
      rw [hk, Nat.add_sub_cancel]; exact this
    · have := h p.length (by simp) hK
      simpa using this

end Ex

section Residual
variable {β : Type} [Fintype β] [DecidableEq β] (𝒵 : Finset (Finset β))

/-- Candidates for `χ(z)`. -/
def cand (prev : Finset β → Finset β) (G : Finset β) (b : ℕ) (z : Finset β) :
    Finset (Finset β) :=
  𝒵.filter (fun u => prev u ⊆ G ∪ prev z ∧ (prev u).card ≤ b)

/-- `χ(z)`: a candidate minimizing `|prev u \ G|`, or `z` if there is none. -/
def chi (prev : Finset β → Finset β) (G : Finset β) (b : ℕ) (z : Finset β) : Finset β :=
  if h : (cand 𝒵 prev G b z).Nonempty then
    Classical.choose ((cand 𝒵 prev G b z).exists_min_image (fun u => (prev u \ G).card) h)
  else z

lemma chi_spec (prev : Finset β → Finset β) (G : Finset β) (b : ℕ) (z : Finset β)
    (h : (cand 𝒵 prev G b z).Nonempty) :
    chi 𝒵 prev G b z ∈ cand 𝒵 prev G b z ∧
      ∀ u ∈ cand 𝒵 prev G b z, (prev (chi 𝒵 prev G b z) \ G).card ≤ (prev u \ G).card := by
  unfold chi; rw [dif_pos h]
  exact Classical.choose_spec ((cand 𝒵 prev G b z).exists_min_image (fun u => (prev u \ G).card) h)

lemma chi_mem (prev : Finset β → Finset β) (G : Finset β) (b : ℕ) {z : Finset β} (hz : z ∈ 𝒵) :
    chi 𝒵 prev G b z ∈ 𝒵 := by
  by_cases h : (cand 𝒵 prev G b z).Nonempty
  · exact (mem_filter.1 (chi_spec 𝒵 prev G b z h).1).1
  · unfold chi; rw [dif_neg h]; exact hz

lemma chi_sub (prev : Finset β → Finset β) (G : Finset β) (b : ℕ) (z : Finset β) :
    prev (chi 𝒵 prev G b z) ⊆ G ∪ prev z := by
  by_cases h : (cand 𝒵 prev G b z).Nonempty
  · exact (mem_filter.1 (chi_spec 𝒵 prev G b z h).1).2.1
  · unfold chi; rw [dif_neg h]; exact subset_union_right

/-- One residual step `π_ℓ(z) = π_{ℓ-1}(χ(z)) \ W_ℓ`. -/
def step (prev : Finset β → Finset β) (G : Finset β) (b : ℕ) (z : Finset β) : Finset β :=
  prev (chi 𝒵 prev G b z) \ G

lemma step_sub (prev : Finset β → Finset β) (G : Finset β) (b : ℕ) (z : Finset β) :
    step 𝒵 prev G b z ⊆ prev z := by
  intro x hx
  unfold step at hx
  rw [mem_sdiff] at hx
  rcases mem_union.1 (chi_sub 𝒵 prev G b z hx.1) with h | h
  · exact absurd h hx.2
  · exact h

/-- The decoder: a fixed candidate inside `U`. -/
def dec (prev : Finset β → Finset β) (U : Finset β) (b : ℕ) : Finset β :=
  if h : (𝒵.filter (fun u => prev u ⊆ U ∧ (prev u).card ≤ b)).Nonempty then Classical.choose h
  else ∅

lemma dec_card (prev : Finset β → Finset β) (hprev : ∀ z, prev z ⊆ z) (U : Finset β) (b : ℕ) :
    (prev (dec 𝒵 prev U b)).card ≤ b := by
  unfold dec
  split_ifs with h
  · exact (mem_filter.1 (Classical.choose_spec h)).2.2
  · have := hprev ∅; rw [subset_empty.1 this]; simp

/-- The encoding facts. -/
lemma bad_facts (prev : Finset β → Finset β) (hprev : ∀ z, prev z ⊆ z) (G : Finset β) (b : ℕ)
    {z : Finset β} (hz : z ∈ 𝒵) (hb : (prev z).card ≤ b) :
    step 𝒵 prev G b z ⊆ prev (dec 𝒵 prev (G ∪ step 𝒵 prev G b z) b) ∧
      step 𝒵 prev G b z ⊆ G ∪ step 𝒵 prev G b z ∧ step 𝒵 prev G b z ⊆ z ∧
      (G ∪ step 𝒵 prev G b z) \ step 𝒵 prev G b z = G := by
  set A := step 𝒵 prev G b z with hA
  set U := G ∪ A with hU
  have hzc : z ∈ cand 𝒵 prev G b z := mem_filter.2 ⟨hz, subset_union_right, hb⟩
  obtain ⟨hχ, hmin⟩ := chi_spec 𝒵 prev G b z ⟨z, hzc⟩
  set χ := chi 𝒵 prev G b z
  have hAG : Disjoint A G := by
    rw [disjoint_left]; intro x hx; exact (mem_sdiff.1 hx).2
  have hAz : A ⊆ prev z := step_sub 𝒵 prev G b z
  -- the decoder finds something
  have hF : (𝒵.filter (fun u => prev u ⊆ U ∧ (prev u).card ≤ b)).Nonempty := by
    refine ⟨χ, mem_filter.2 ⟨(mem_filter.1 hχ).1, ?_, (mem_filter.1 hχ).2.2⟩⟩
    intro x hx
    by_cases hG : x ∈ G
    · exact mem_union_left _ hG
    · exact mem_union_right _ (mem_sdiff.2 ⟨hx, hG⟩)
  have hT : dec 𝒵 prev U b ∈ 𝒵.filter (fun u => prev u ⊆ U ∧ (prev u).card ≤ b) := by
    unfold dec; rw [dif_pos hF]; exact Classical.choose_spec hF
  set T := dec 𝒵 prev U b
  obtain ⟨hT𝒵, hTU, hTb⟩ := mem_filter.1 hT
  have hTc : T ∈ cand 𝒵 prev G b z := by
    refine mem_filter.2 ⟨hT𝒵, hTU.trans (union_subset_union subset_rfl hAz), hTb⟩
  have h1 : prev T \ G ⊆ A := by
    intro x hx
    rw [mem_sdiff] at hx
    rcases mem_union.1 (hTU hx.1) with h | h
    · exact absurd h hx.2
    · exact h
  have h2 : A.card ≤ (prev T \ G).card := hmin T hTc
  have heq : prev T \ G = A := eq_of_subset_of_card_le h1 h2
  refine ⟨?_, subset_union_right, hAz.trans (hprev z), ?_⟩
  · rw [← heq]; exact sdiff_subset
  · rw [union_sdiff_right]; exact sdiff_eq_self_of_disjoint hAG.symm

/-- The one-stage encoding bound. -/
theorem stage_bound (prev : Finset β → Finset β) (hprev : ∀ z, prev z ⊆ z) (b f : ℕ)
    {d r : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) (hr : 0 < r) (hy : (1 - d) / (d * r) ≤ 1)
    (m : Finset β → ℝ) (hm : ∀ z, 0 ≤ m z)
    (hsp : ∀ A : Finset β, ∑ z ∈ 𝒵.filter (fun z => A ⊆ z), m z ≤ (r ^ A.card)⁻¹) :
    ∑ G : Finset β, wt d G *
        ∑ z ∈ 𝒵.filter (fun z => (prev z).card ≤ b ∧ f ≤ (step 𝒵 prev G b z).card), m z ≤
      2 ^ b * ((1 - d) / (d * r)) ^ f := by
  set y := (1 - d) / (d * r) with hydef
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (mul_nonneg hd0.le hr.le)
  set S : Finset β → Finset (Finset β) := fun U =>
    (prev (dec 𝒵 prev U b)).powerset.filter (fun A => f ≤ A.card ∧ A ⊆ U) with hS
  set Bad : Finset β → Finset β → Prop :=
    fun G z => (prev z).card ≤ b ∧ f ≤ (step 𝒵 prev G b z).card with hBad
  set P : Finset β → Finset β × Finset β → Prop := fun z x => x.2 ∈ S x.1 ∧ x.2 ⊆ z with hP
  -- Step B: for fixed `z ∈ 𝒵`
  have hB : ∀ z ∈ 𝒵, ∑ G : Finset β, wt d G * (if Bad G z then 1 else 0) ≤
      ∑ x ∈ (univ ×ˢ univ : Finset (Finset β × Finset β)).filter (P z), wt d (x.1 \ x.2) := by
    intro z hz
    have e1 : ∑ G : Finset β, wt d G * (if Bad G z then 1 else 0) =
        ∑ G ∈ univ.filter (fun G => Bad G z), wt d G := by
      rw [sum_filter]; apply sum_congr rfl; intro G _; split_ifs <;> simp
    rw [e1]
    set φ : Finset β → Finset β × Finset β := fun G => (G ∪ step 𝒵 prev G b z, step 𝒵 prev G b z)
    have hinj : Set.InjOn φ (univ.filter (fun G => Bad G z) : Finset (Finset β)) := by
      intro G1 hG1 G2 hG2 heq
      have hb1 := (mem_filter.1 (mem_coe.1 hG1)).2.1
      have hb2 := (mem_filter.1 (mem_coe.1 hG2)).2.1
      have f1 := (bad_facts 𝒵 prev hprev G1 b hz hb1).2.2.2
      have f2 := (bad_facts 𝒵 prev hprev G2 b hz hb2).2.2.2
      have := congrArg (fun x : Finset β × Finset β => x.1 \ x.2) heq
      simp only [φ] at this
      rw [f1, f2] at this; exact this
    have e2 : ∑ G ∈ univ.filter (fun G => Bad G z), wt d G =
        ∑ x ∈ (univ.filter (fun G => Bad G z)).image φ, wt d (x.1 \ x.2) := by
      rw [sum_image hinj]
      apply sum_congr rfl; intro G hG
      have hb1 := (mem_filter.1 hG).2.1
      simp only [φ]; rw [(bad_facts 𝒵 prev hprev G b hz hb1).2.2.2]
    rw [e2]
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      obtain ⟨G, hG, rfl⟩ := mem_image.1 hx
      obtain ⟨_, hb1, hf1⟩ := mem_filter.1 hG
      obtain ⟨k1, k2, k3, _⟩ := bad_facts 𝒵 prev hprev G b hz hb1
      refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_univ _⟩, ?_, k3⟩
      exact mem_filter.2 ⟨mem_powerset.2 k1, hf1, k2⟩
    · intro x _ _; exact wt_nonneg hd0.le hd1 _
  -- main computation
  have e0 : ∑ G : Finset β, wt d G * ∑ z ∈ 𝒵.filter (fun z => Bad G z), m z =
      ∑ z ∈ 𝒵, m z * ∑ G : Finset β, wt d G * (if Bad G z then 1 else 0) := by
    simp_rw [sum_filter, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro z _; apply sum_congr rfl; intro G _
    split_ifs <;> ring
  show ∑ G : Finset β, wt d G * ∑ z ∈ 𝒵.filter (fun z => Bad G z), m z ≤ _
  rw [e0]
  calc ∑ z ∈ 𝒵, m z * ∑ G : Finset β, wt d G * (if Bad G z then 1 else 0)
      ≤ ∑ z ∈ 𝒵, m z * ∑ x ∈ (univ ×ˢ univ : Finset (Finset β × Finset β)).filter (P z),
          wt d (x.1 \ x.2) :=
        sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hB z hz) (hm z)
    _ = ∑ x ∈ (univ ×ˢ univ : Finset (Finset β × Finset β)).filter (fun x => x.2 ∈ S x.1),
          wt d (x.1 \ x.2) * ∑ z ∈ 𝒵.filter (fun z => x.2 ⊆ z), m z := by
        simp_rw [sum_filter, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro x _
        split_ifs with h1
        · apply sum_congr rfl; intro z _
          split_ifs with h2 h3 h3 <;>
            first | (exfalso; exact h3 h2.2) | (exfalso; exact h2 ⟨h1, h3⟩) | ring
        · apply sum_eq_zero; intro z _
          split_ifs with h2 <;> first | (exfalso; exact h1 h2.1) | ring
    _ ≤ ∑ x ∈ (univ ×ˢ univ : Finset (Finset β × Finset β)).filter (fun x => x.2 ∈ S x.1),
          wt d x.1 * y ^ x.2.card := by
        apply sum_le_sum; intro x hx
        have hxS := (mem_filter.1 hx).2
        have hsub : x.2 ⊆ x.1 := (mem_filter.1 hxS).2.2
        rw [wt_sdiff hd0 hsub]
        have hw := wt_nonneg hd0.le hd1 x.1
        have hq : 0 ≤ ((1 - d) / d) ^ x.2.card := pow_nonneg (div_nonneg (by linarith) hd0.le) _
        calc wt d x.1 * ((1 - d) / d) ^ x.2.card * ∑ z ∈ 𝒵.filter (fun z => x.2 ⊆ z), m z
            ≤ wt d x.1 * ((1 - d) / d) ^ x.2.card * (r ^ x.2.card)⁻¹ :=
              mul_le_mul_of_nonneg_left (hsp x.2) (mul_nonneg hw hq)
          _ = wt d x.1 * y ^ x.2.card := by
              rw [hydef, mul_assoc, ← inv_pow, ← mul_pow]
              congr 2
              field_simp
    _ = ∑ U : Finset β, wt d U * ∑ A ∈ S U, y ^ A.card := by
        rw [sum_filter, sum_product]
        apply sum_congr rfl; intro U _
        simp only
        rw [sum_ite_mem, univ_inter, mul_sum]
    _ ≤ ∑ U : Finset β, wt d U * (2 ^ b * y ^ f) := by
        apply sum_le_sum; intro U _
        apply mul_le_mul_of_nonneg_left _ (wt_nonneg hd0.le hd1 U)
        calc ∑ A ∈ S U, y ^ A.card ≤ ∑ A ∈ S U, y ^ f := by
              apply sum_le_sum; intro A hA
              exact pow_le_pow_of_le_one hy0 hy (mem_filter.1 hA).2.1
          _ = (S U).card * y ^ f := by rw [sum_const, nsmul_eq_mul]
          _ ≤ 2 ^ b * y ^ f := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg hy0 _)
              have h1 : (S U).card ≤ 2 ^ b := by
                refine (card_filter_le _ _).trans ?_
                rw [card_powerset]
                exact Nat.pow_le_pow_right (by norm_num) (dec_card 𝒵 prev hprev U b)
              exact_mod_cast h1
    _ = 2 ^ b * y ^ f := by rw [← sum_mul, sum_wt, one_mul]

end Residual

section Schedule

/-- End (exclusive) of scale `s`: scales `q, q-1, …, s` occupy stages `[0, nxt s)`. -/
def nxt (q : ℕ) (J : ℕ → ℕ) (s : ℕ) : ℕ := ∑ s' ∈ Icc s q, J s'

lemma nxt_anti (q : ℕ) (J : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : nxt q J b ≤ nxt q J a :=
  sum_le_sum_of_subset (Icc_subset_Icc_left h)

lemma nxt_top (q : ℕ) (J : ℕ → ℕ) : nxt q J (q + 1) = 0 := by
  unfold nxt; rw [Icc_eq_empty (by omega)]; simp

lemma nxt_succ (q : ℕ) (J : ℕ → ℕ) {s : ℕ} (hs : s ≤ q) : nxt q J s = J s + nxt q J (s + 1) := by
  unfold nxt
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hs, sum_insert (by simp)]

lemma sc_ne (q : ℕ) (J : ℕ → ℕ) (j : ℕ) :
    ((range (q + 1)).filter (fun s => nxt q J (s + 1) ≤ j)).Nonempty := by
  refine ⟨q, mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_self q), ?_⟩⟩
  rw [nxt_top]; exact Nat.zero_le j

/-- The scale of stage `j`. -/
def sc (q : ℕ) (J : ℕ → ℕ) (j : ℕ) : ℕ :=
  ((range (q + 1)).filter (fun s => nxt q J (s + 1) ≤ j)).min' (sc_ne q J j)

lemma sc_eq (q : ℕ) (J : ℕ → ℕ) {s j : ℕ} (hs : s ≤ q) (h1 : nxt q J (s + 1) ≤ j)
    (h2 : j < nxt q J s) : sc q J j = s := by
  have hm : s ∈ (range (q + 1)).filter (fun s => nxt q J (s + 1) ≤ j) :=
    mem_filter.2 ⟨mem_range.2 (by omega), h1⟩
  unfold sc
  apply le_antisymm
  · exact min'_le _ s hm
  · apply le_min'
    intro s' hs'
    obtain ⟨_, h3⟩ := mem_filter.1 hs'
    by_contra hlt
    push Not at hlt
    have := nxt_anti q J (show s' + 1 ≤ s by omega)
    omega

lemma descend (q : ℕ) (J : ℕ → ℕ) (R : ℕ → ℕ) (hR : ∀ j, j < nxt q J 0 → R (j + 1) ≤ R j)
    (h0 : R 0 ≤ 2 ^ (q + 1))
    (h : ∀ s ≤ q, ∃ j, nxt q J (s + 1) ≤ j ∧ j < nxt q J s ∧
      ¬ (R j ≤ 2 ^ (s + 1) ∧ 2 ^ s ≤ R (j + 1))) :
    R (nxt q J 0) = 0 := by
  have anti : ∀ j k, j ≤ k → k ≤ nxt q J 0 → R k ≤ R j := by
    intro j k hjk hk
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hjk ih => exact (hR k (by omega)).trans (ih (by omega))
  have stepL : ∀ s ≤ q, R (nxt q J (s + 1)) ≤ 2 ^ (s + 1) → R (nxt q J s) < 2 ^ s := by
    intro s hs hin
    obtain ⟨j, hj1, hj2, hj3⟩ := h s hs
    have hnx : nxt q J s ≤ nxt q J 0 := nxt_anti q J (Nat.zero_le s)
    have hRj : R j ≤ 2 ^ (s + 1) := (anti _ j hj1 (by omega)).trans hin
    have hR1 : R (j + 1) < 2 ^ s := by
      by_contra hc; push Not at hc; exact hj3 ⟨hRj, hc⟩
    exact lt_of_le_of_lt (anti (j + 1) (nxt q J s) (by omega) hnx) hR1
  have claim : ∀ d ≤ q, R (nxt q J (q - d)) < 2 ^ (q - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      exact stepL q le_rfl (by rw [nxt_top]; exact h0)
    | succ d ih =>
      intro hd
      have := ih (by omega)
      have e : q - d = q - (d + 1) + 1 := by omega
      rw [e] at this
      exact stepL _ (by omega) this.le
  have := claim q le_rfl
  rw [Nat.sub_self, pow_zero] at this
  omega

end Schedule

section Rho
variable {β : Type} [Fintype β] [DecidableEq β] (𝒵 : Finset (Finset β)) (bud : ℕ → ℕ)

/-- The residual `π_ℓ` for the stage list `p` (newest first). -/
def rho : List (Finset β) → Finset β → Finset β
  | [] => fun z => z
  | G :: p => fun z => step 𝒵 (rho p) G (bud p.length) z

lemma rho_sub : ∀ (p : List (Finset β)) (z : Finset β), rho 𝒵 bud p z ⊆ z
  | [], _ => subset_rfl
  | G :: p, z => (step_sub 𝒵 _ G _ z).trans (rho_sub p z)

lemma rho_cons_sub (G : Finset β) (p : List (Finset β)) (z : Finset β) :
    rho 𝒵 bud (G :: p) z ⊆ rho 𝒵 bud p z := step_sub 𝒵 _ G _ z

lemma rho_succ : ∀ (p : List (Finset β)), ∀ z ∈ 𝒵, ∃ w ∈ 𝒵, w ⊆ Ul p ∪ rho 𝒵 bud p z
  | [], z, hz => ⟨z, hz, subset_union_right⟩
  | G :: p, z, hz => by
    obtain ⟨w, hw, hsub⟩ := rho_succ p (chi 𝒵 (rho 𝒵 bud p) G (bud p.length) z)
      (chi_mem 𝒵 _ G _ hz)
    refine ⟨w, hw, hsub.trans ?_⟩
    intro x hx
    simp only [Ul, rho, step, mem_union, mem_sdiff] at hx ⊢
    by_cases hG : x ∈ G
    · exact Or.inl (Or.inl hG)
    · rcases hx with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨h, hG⟩

lemma drop_getD (l : List (Finset β)) (k : ℕ) (hk : k < l.length) :
    l.drop k = l.getD k ∅ :: l.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem _ _ hk]

/-- Failure of the run forces some scale to fail at every repetition. -/
lemma decomp (q : ℕ) (J : ℕ → ℕ) (l : List (Finset β)) (hl : l.length = nxt q J 0)
    (z : Finset β) (hz : z.card ≤ 2 ^ (q + 1)) (hne : rho 𝒵 (fun j => 2 ^ (sc q J j + 1)) l z ≠ ∅) :
    ∃ s ≤ q, AllA (Ico (nxt q J (s + 1)) (nxt q J s))
      (fun p G => (rho 𝒵 (fun j => 2 ^ (sc q J j + 1)) p z).card ≤ 2 ^ (sc q J p.length + 1) ∧
        2 ^ (sc q J p.length) ≤
          (rho 𝒵 (fun j => 2 ^ (sc q J j + 1)) (G :: p) z).card) l := by
  set bud := fun j => 2 ^ (sc q J j + 1)
  set R : ℕ → ℕ := fun j => (rho 𝒵 bud (l.drop (l.length - j)) z).card with hRdef
  have hcons : ∀ j < l.length, l.drop (l.length - (j + 1)) =
      l.getD (l.length - j - 1) ∅ :: l.drop (l.length - j) := by
    intro j hj
    have e1 : l.length - (j + 1) = l.length - j - 1 := by omega
    have e2 : l.length - j - 1 + 1 = l.length - j := by omega
    rw [e1, drop_getD l _ (by omega), e2]
  have hlen : ∀ j ≤ l.length, (l.drop (l.length - j)).length = j := by
    intro j hj; rw [List.length_drop]; omega
  by_contra hcon
  push Not at hcon
  have hR : ∀ j, j < nxt q J 0 → R (j + 1) ≤ R j := by
    intro j hj
    simp only [hRdef]
    rw [hcons j (by omega)]
    exact card_le_card (rho_cons_sub 𝒵 bud _ _ z)
  have h0 : R 0 ≤ 2 ^ (q + 1) := by
    simp only [hRdef, Nat.sub_zero, List.drop_length]; exact hz
  have h : ∀ s ≤ q, ∃ j, nxt q J (s + 1) ≤ j ∧ j < nxt q J s ∧
      ¬ (R j ≤ 2 ^ (s + 1) ∧ 2 ^ s ≤ R (j + 1)) := by
    intro s hs
    have hna := hcon s hs
    by_contra hall
    push Not at hall
    apply hna
    apply allA_of_forall
    intro j hj hK
    obtain ⟨hK1, hK2⟩ := mem_Ico.1 hK
    have hsc : sc q J j = s := sc_eq q J hs hK1 hK2
    have hj' := hall j hK1 hK2
    have hl1 := hlen j hj.le
    rw [hl1, hsc]
    refine ⟨hj'.1, ?_⟩
    have := hj'.2
    simp only [hRdef] at this
    rw [hcons j hj] at this
    exact this
  have := descend q J R hR h0 h
  simp only [hRdef, ← hl, Nat.sub_self, List.drop_zero] at this
  exact hne (card_eq_zero.1 this)

end Rho

section Core
variable {β : Type} [Fintype β] [DecidableEq β]

lemma geom_half (n : ℕ) : ∑ s ∈ range n, (1 / 2 : ℝ) ^ (s + 1) = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

lemma ex_eq (q : ℕ) (J : ℕ → ℕ) {s : ℕ} (hs : s ≤ q) :
    ex (Ico (nxt q J (s + 1)) (nxt q J s)) 0 (nxt q J 0) = J s := by
  unfold ex
  simp only [zero_add]
  rw [sum_boole]
  have hsub : (range (nxt q J 0)).filter (fun k => k ∈ Ico (nxt q J (s + 1)) (nxt q J s)) =
      Ico (nxt q J (s + 1)) (nxt q J s) := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    have := nxt_anti q J (Nat.zero_le s)
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by omega, h⟩
  rw [hsub, Nat.card_Ico, nxt_succ q J hs]
  simp

/-- The combinatorial core: failure probability of the staged run. -/
theorem core (𝒵 : Finset (Finset β)) (m : Finset β → ℝ) (hm : ∀ z, 0 ≤ m z)
    (hm1 : ∑ z ∈ 𝒵, m z = 1) {r : ℝ} (hr : 0 < r)
    (hsp : ∀ A : Finset β, ∑ z ∈ 𝒵.filter (fun z => A ⊆ z), m z ≤ (r ^ A.card)⁻¹)
    (q : ℕ) (hz : ∀ z ∈ 𝒵, z.card ≤ 2 ^ (q + 1)) (J : ℕ → ℕ) {d : ℝ} (hd0 : 0 < d)
    (hd1 : d ≤ 1) (hy : 8 * ((1 - d) / (d * r)) ≤ 1 / 16) :
    ∑ V : Finset β, wt (1 - (1 - d) ^ (nxt q J 0)) V *
        (if ∃ z ∈ 𝒵, z ⊆ V then 0 else 1) ≤
      ∑ s ∈ range (q + 1), ((1 : ℝ) / 16) ^ (2 ^ s * J s) := by
  set N := nxt q J 0 with hN
  set bud : ℕ → ℕ := fun j => 2 ^ (sc q J j + 1) with hbud
  set y := (1 - d) / (d * r) with hydef
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (mul_nonneg hd0.le hr.le)
  set g : Finset β → ℝ := fun V => if ∃ z ∈ 𝒵, z ⊆ V then 0 else 1 with hg
  set E : List (Finset β) → Finset β → Finset β → Prop := fun p G z =>
    (rho 𝒵 bud p z).card ≤ 2 ^ (sc q J p.length + 1) ∧
      2 ^ (sc q J p.length) ≤ (rho 𝒵 bud (G :: p) z).card with hE
  set θ : ℕ → ℝ := fun s => (1 / 2) ^ (s + 1) with hθ
  set K : ℕ → Finset ℕ := fun s => Ico (nxt q J (s + 1)) (nxt q J s) with hK
  set A : ℕ → List (Finset β) → Finset β → Prop := fun s p G =>
    θ s ≤ ∑ z ∈ 𝒵.filter (fun z => E p G z), m z with hA
  set c : ℕ → ℝ := fun s => 2 ^ (s + 1) * (2 ^ (2 ^ (s + 1)) * y ^ (2 ^ s)) with hc
  have e0 : ∑ V : Finset β, wt (1 - (1 - d) ^ N) V * g V = Ex d (fun l => g (Ul l)) [] N := by
    rw [Ex_union]; simp [Ul]
  show ∑ V : Finset β, wt (1 - (1 - d) ^ N) V * g V ≤ _
  rw [e0]
  -- pointwise decomposition
  have hpt : ∀ l : List (Finset β), l.length = ([] : List (Finset β)).length + N →
      g (Ul l) ≤ ∑ s ∈ range (q + 1), (if AllA (K s) (A s) l then 1 else 0) := by
    intro l hl
    simp only [List.length_nil, zero_add] at hl
    have hnn : 0 ≤ ∑ s ∈ range (q + 1), (if AllA (K s) (A s) l then (1 : ℝ) else 0) :=
      sum_nonneg fun s _ => by split_ifs <;> norm_num
    by_cases hsucc : ∃ z ∈ 𝒵, z ⊆ Ul l
    · simp only [hg, if_pos hsucc]; exact hnn
    simp only [hg, if_neg hsucc]
    have hall : ∀ z ∈ 𝒵, ∃ s ∈ range (q + 1), AllA (K s) (fun p G => E p G z) l := by
      intro z hz𝒵
      have hne : rho 𝒵 bud l z ≠ ∅ := by
        intro h0
        obtain ⟨w, hw, hsub⟩ := rho_succ 𝒵 bud l z hz𝒵
        rw [h0, union_empty] at hsub
        exact hsucc ⟨w, hw, hsub⟩
      obtain ⟨s, hs, hAll⟩ := decomp 𝒵 q J l hl z (hz z hz𝒵) hne
      exact ⟨s, mem_range.2 (by omega), hAll⟩
    -- some scale carries mass ≥ θ s
    have hex : ∃ s ∈ range (q + 1),
        θ s ≤ ∑ z ∈ 𝒵.filter (fun z => AllA (K s) (fun p G => E p G z) l), m z := by
      by_contra hcon
      push Not at hcon
      have h1 : (1 : ℝ) ≤ ∑ s ∈ range (q + 1),
          ∑ z ∈ 𝒵.filter (fun z => AllA (K s) (fun p G => E p G z) l), m z := by
        rw [← hm1]
        simp_rw [sum_filter]
        rw [sum_comm]
        apply sum_le_sum; intro z hz𝒵
        obtain ⟨s, hs, hAll⟩ := hall z hz𝒵
        calc m z = if AllA (K s) (fun p G => E p G z) l then m z else 0 := by rw [if_pos hAll]
          _ ≤ ∑ s ∈ range (q + 1), if AllA (K s) (fun p G => E p G z) l then m z else 0 :=
            single_le_sum (f := fun s => if AllA (K s) (fun p G => E p G z) l then m z else 0)
              (fun s _ => by split_ifs <;> simp [hm z]) hs
      have h2 : ∑ s ∈ range (q + 1),
          ∑ z ∈ 𝒵.filter (fun z => AllA (K s) (fun p G => E p G z) l), m z <
          ∑ s ∈ range (q + 1), θ s :=
        sum_lt_sum_of_nonempty ⟨0, by simp⟩ hcon
      have h3 : ∑ s ∈ range (q + 1), θ s ≤ 1 := by
        simp only [hθ]; rw [geom_half]
        have : (0 : ℝ) ≤ (1 / 2) ^ (q + 1) := by positivity
        linarith
      linarith
    obtain ⟨s, hs, hθs⟩ := hex
    have := allA_mass (K s) E m hm 𝒵 (θ s) l hθs
    calc (1 : ℝ) = if AllA (K s) (A s) l then 1 else 0 := by
          rw [if_pos (show AllA (K s) (A s) l by convert this)]
      _ ≤ _ := single_le_sum (f := fun s => if AllA (K s) (A s) l then (1 : ℝ) else 0)
          (fun s _ => by split_ifs <;> norm_num) hs
  refine (Ex_mono hd0.le hd1 N [] hpt).trans ?_
  rw [Ex_sum]
  apply sum_le_sum
  intro s hs
  have hsq : s ≤ q := by rw [mem_range] at hs; omega
  -- per-stage Markov bound
  have hcs0 : 0 ≤ c s := by simp only [hc]; positivity
  have hAs : ∀ p : List (Finset β), p.length ∈ K s →
      ∑ G : Finset β, wt d G * (if A s p G then 1 else 0) ≤ c s := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_Ico.1 hp
    have hsc : sc q J p.length = s := sc_eq q J hsq hp1 hp2
    have hθ0 : 0 < θ s := by simp only [hθ]; positivity
    have hsb := stage_bound 𝒵 (rho 𝒵 bud p) (rho_sub 𝒵 bud p) (bud p.length)
      (2 ^ (sc q J p.length)) hd0 hd1 hr (by linarith) m hm hsp
    have hmk : ∀ G : Finset β, wt d G * (if A s p G then 1 else 0) ≤
        (θ s)⁻¹ * (wt d G * ∑ z ∈ 𝒵.filter (fun z => (rho 𝒵 bud p z).card ≤ bud p.length ∧
          2 ^ (sc q J p.length) ≤ (step 𝒵 (rho 𝒵 bud p) G (bud p.length) z).card), m z) := by
      intro G
      have hw := wt_nonneg hd0.le hd1 G
      split_ifs with hAG
      · have hAG' : θ s ≤ ∑ z ∈ 𝒵.filter (fun z => (rho 𝒵 bud p z).card ≤ bud p.length ∧
            2 ^ (sc q J p.length) ≤ (step 𝒵 (rho 𝒵 bud p) G (bud p.length) z).card), m z := by
          simp only [hA, hE] at hAG
          exact hAG
        rw [mul_one, ← mul_assoc, mul_comm (θ s)⁻¹, mul_assoc]
        apply le_mul_of_one_le_right hw
        rw [inv_mul_eq_div, le_div_iff₀ hθ0, one_mul]; exact hAG'
      · rw [mul_zero]
        exact mul_nonneg (inv_nonneg.2 hθ0.le)
          (mul_nonneg hw (sum_nonneg fun z _ => hm z))
    refine (sum_le_sum fun G _ => hmk G).trans ?_
    rw [← mul_sum]
    calc (θ s)⁻¹ * _ ≤ (θ s)⁻¹ * (2 ^ bud p.length * y ^ (2 ^ (sc q J p.length))) :=
          mul_le_mul_of_nonneg_left hsb (inv_nonneg.2 hθ0.le)
      _ = c s := by
          simp only [hθ, hc, hbud, hsc]
          rw [one_div, inv_pow, inv_inv]
  have hch := chain hd0.le hd1 (K s) (A s) (c s) hcs0 hAs N []
  simp only [AllA, List.length_nil, ↓reduceIte, one_mul] at hch
  rw [ex_eq q J hsq] at hch
  refine hch.trans ?_
  -- `c s ≤ (1/16)^(2^s)`
  have hcs : c s ≤ ((1 : ℝ) / 16) ^ (2 ^ s) := by
    simp only [hc]
    have h4 : 4 * y ≤ 1 / 32 := by linarith
    have hs2 : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
    calc (2 : ℝ) ^ (s + 1) * (2 ^ (2 ^ (s + 1)) * y ^ (2 ^ s))
        = 2 ^ (s + 1) * (4 * y) ^ (2 ^ s) := by
          have h44 : (2 : ℝ) ^ (2 ^ (s + 1)) = 4 ^ (2 ^ s) := by
            rw [pow_succ 2 s, pow_mul']; norm_num
          rw [h44, mul_pow]
      _ ≤ 2 ^ (2 ^ s) * (1 / 32) ^ (2 ^ s) := by
          apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hs2)
            (pow_le_pow_left₀ (by positivity) h4 _) (by positivity) (by positivity)
      _ = (1 / 16) ^ (2 ^ s) := by rw [← mul_pow]; norm_num
  rw [pow_mul]
  exact pow_le_pow_left₀ hcs0 hcs _

end Core

section Final

open SpreadMatchCircuit.Matching SpreadMatchCircuit.Matching.Supplement

/-- Arithmetic of the schedule: `N ≤ 2M + q + 1`. -/
lemma N_le (q M : ℕ) :
    (nxt q (fun s => M / 2 ^ s + 1) 0 : ℝ) ≤ 2 * M + q + 1 := by
  unfold nxt
  have hI : Icc 0 q = range (q + 1) := by ext x; simp [Nat.lt_succ_iff]
  rw [hI]; push_cast
  have h1 : ∀ s ∈ range (q + 1), ((M / 2 ^ s : ℕ) : ℝ) + 1 ≤ 2 * M * (1 / 2) ^ (s + 1) + 1 := by
    intro s _
    have := Nat.cast_div_le (α := ℝ) (m := M) (n := 2 ^ s)
    have e : 2 * (M : ℝ) * (1 / 2) ^ (s + 1) = M / 2 ^ s := by
      rw [pow_succ, one_div_pow]; field_simp
    push_cast at this
    linarith
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, ← mul_sum, geom_half]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  push_cast
  have : (0 : ℝ) ≤ (1 / 2) ^ (q + 1) := by positivity
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

/-- **The Spread Set Lemma** (Lemma 3), in the form of `Dev.Lemma4.SpreadSetStatement`. -/
theorem spread_set :
    ∃ α : ℝ, 0 < α ∧
      ∀ (n : ℕ) (μ : PMF (Finset (Fin n))) (ε t γ r : ℝ),
        0 < ε → ε ≤ 1 / 2 → 0 < t → 0 < γ → γ ≤ 1 →
        r = α * Real.log (t / ε) / γ →
        IsSetSpread μ r → IsBoundedSetLaw μ t →
        1 - ε < ∑ W ∈ univ.filter (fun W : Finset (Fin n) => ∃ z ∈ lawSupport μ, z ⊆ W),
          γ ^ W.card * (1 - γ) ^ (n - W.card) := by
  refine ⟨2560, by norm_num, ?_⟩
  intro n μ ε t γ r hε0 hε ht hγ0 hγ1 hr hsp hbd
  set 𝒵 := lawSupport μ with h𝒵
  set m : Finset (Fin n) → ℝ := fun z => (μ z).toReal with hmdef
  have hm : ∀ z, 0 ≤ m z := fun z => ENNReal.toReal_nonneg
  have hsum1 : ∑ z, m z = 1 := by
    simp only [hmdef]
    rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top μ x)]
    have := μ.tsum_coe
    rw [tsum_fintype] at this
    rw [this]; simp
  have hm1 : ∑ z ∈ 𝒵, m z = 1 := by
    rw [← hsum1]
    apply sum_subset (subset_univ _)
    intro z _ hz
    simp only [h𝒵, lawSupport, mem_filter, mem_univ, true_and, PMF.mem_support_iff, not_not] at hz
    simp [hmdef, hz]
  -- the target as `1 - failure`
  set P : Finset (Fin n) → Prop := fun W => ∃ z ∈ 𝒵, z ⊆ W with hP
  have hkey : (∑ W ∈ univ.filter (fun W : Finset (Fin n) => ∃ z ∈ lawSupport μ, z ⊆ W),
      γ ^ W.card * (1 - γ) ^ (n - W.card)) +
      ∑ V : Finset (Fin n), wt γ V * (if ∃ z ∈ 𝒵, z ⊆ V then 0 else 1) = 1 := by
    rw [sum_filter, ← sum_add_distrib]
    refine (sum_congr rfl (fun W _ => ?_)).trans (sum_wt (β := Fin n) γ)
    unfold wt; rw [Fintype.card_fin]
    split_ifs with h1 h2 h2 <;> first | ring | (exfalso; tauto)
  -- trivial case `t < 1`
  by_cases ht1 : t < 1
  · have hemp : ∅ ∈ 𝒵 := by
      obtain ⟨z, hz⟩ := μ.support_nonempty
      have hz𝒵 : z ∈ 𝒵 := by
        rw [h𝒵, lawSupport]; simp only [mem_filter, mem_univ, true_and]; exact hz
      have hc := hbd z hz𝒵
      have : z.card = 0 := by
        have : (z.card : ℝ) < 1 := lt_of_le_of_lt hc ht1
        exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
      rw [card_eq_zero] at this; rw [← this]; exact hz𝒵
    have h0 : ∑ V : Finset (Fin n), wt γ V * (if ∃ z ∈ 𝒵, z ⊆ V then 0 else 1) = 0 := by
      apply sum_eq_zero; intro V _
      rw [if_pos ⟨∅, hemp, empty_subset _⟩, mul_zero]
    linarith
  push Not at ht1
  -- parameters
  have hL2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlogε : Real.log ε ≤ -Real.log 2 := by
    have := Real.log_le_log hε0 hε
    rw [one_div, Real.log_inv] at this; exact this
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  set L := Real.log (t / ε) with hL
  have hLeq : L = Real.log t - Real.log ε := Real.log_div ht.ne' hε0.ne'
  have hLpos : 0 < L := by rw [hLeq]; linarith
  have hrpos : 0 < r := by rw [hr]; positivity
  set q := ⌈Real.logb 2 t⌉₊ with hqdef
  have hlogbt : 0 ≤ Real.logb 2 t := Real.logb_nonneg one_lt_two ht1
  have hq : (q : ℝ) ≤ Real.logb 2 t + 1 := (Nat.ceil_lt_add_one hlogbt).le
  have ht2 : t ≤ 2 ^ q := by
    have h1 : Real.logb 2 t ≤ q := Nat.le_ceil _
    have := (Real.logb_le_iff_le_rpow one_lt_two (by linarith)).1 h1
    rwa [Real.rpow_natCast] at this
  have hz : ∀ z ∈ 𝒵, z.card ≤ 2 ^ (q + 1) := by
    intro z hz
    have h1 : (z.card : ℝ) ≤ 2 ^ q := (hbd z hz).trans ht2
    have h2 : z.card ≤ 2 ^ q := by exact_mod_cast h1
    exact h2.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ q))
  set M := ⌈Real.logb 2 ((q + 1) / ε)⌉₊ with hMdef
  have hqε : 1 ≤ ((q : ℝ) + 1) / ε := by
    rw [le_div_iff₀ hε0]; have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith
  have hlogbqε : 0 ≤ Real.logb 2 ((q + 1) / ε) := Real.logb_nonneg one_lt_two hqε
  have hM : (M : ℝ) ≤ Real.logb 2 ((q + 1) / ε) + 1 := (Nat.ceil_lt_add_one hlogbqε).le
  have h2M : ((q : ℝ) + 1) / ε ≤ 2 ^ M := by
    have h1 : Real.logb 2 ((q + 1) / ε) ≤ M := Nat.le_ceil _
    have := (Real.logb_le_iff_le_rpow one_lt_two (by linarith)).1 h1
    rwa [Real.rpow_natCast] at this
  set J : ℕ → ℕ := fun s => M / 2 ^ s + 1 with hJ
  set N := nxt q J 0 with hNdef
  have hN1 : 1 ≤ N := by
    have := nxt_succ q J (Nat.zero_le q)
    rw [hNdef, this]
    exact le_add_right (Nat.le_add_left 1 _)
  have hNle : (N : ℝ) ≤ 20 * L := by
    have h1 := N_le q M
    -- logs
    have hq1 : Real.logb 2 ((q : ℝ) + 1) ≤ q := by
      rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity), Real.rpow_natCast]
      have : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
      exact_mod_cast this
    have hdiv : Real.logb 2 (((q : ℝ) + 1) / ε) = Real.logb 2 ((q : ℝ) + 1) - Real.logb 2 ε :=
      Real.logb_div (by positivity) hε0.ne'
    have hb1 : Real.logb 2 t * Real.log 2 = Real.log t := by
      rw [Real.logb]; field_simp
    have hb2 : Real.logb 2 ε * Real.log 2 = Real.log ε := by
      rw [Real.logb]; field_simp
    have hN' : (N : ℝ) ≤ 3 * Real.logb 2 t + 6 - 2 * Real.logb 2 ε := by
      have : (M : ℝ) ≤ q - Real.logb 2 ε + 1 := by linarith
      linarith
    have hb2' : Real.logb 2 ε ≤ 0 := by
      have : Real.log ε < 0 := by linarith
      rw [Real.logb]; exact div_nonpos_of_nonpos_of_nonneg this.le (by linarith)
    have hNL : (N : ℝ) * Real.log 2 ≤ 3 * Real.log t + 6 * Real.log 2 - 2 * Real.log ε := by
      have := mul_le_mul_of_nonneg_right hN' (by linarith : (0 : ℝ) ≤ Real.log 2)
      nlinarith
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [hLeq]
    nlinarith
  -- the stage density
  have hNne : N ≠ 0 := by omega
  set δ := 1 - (1 - γ) ^ ((N : ℝ)⁻¹) with hδ
  have hγ' : 0 ≤ 1 - γ := by linarith
  have hδN : 1 - (1 - δ) ^ N = γ := by
    rw [hδ, sub_sub_cancel, Real.rpow_inv_natCast_pow hγ' hNne]; ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hNne
  have hγN : γ / N ≤ 1 := by
    rw [div_le_one hNpos]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith
  have hδge : γ / N ≤ δ := by
    have hb : 1 - γ ≤ (1 - γ / N) ^ N := by
      have := one_add_mul_le_pow (a := -(γ / N)) (by linarith) N
      have e : (1 : ℝ) + N * -(γ / N) = 1 - γ := by field_simp; ring
      rw [e, ← sub_eq_add_neg] at this; exact this
    have hb0 : 0 ≤ 1 - γ / N := by linarith
    have := Real.rpow_le_rpow hγ' hb (inv_nonneg.2 hNpos.le)
    rw [Real.pow_rpow_inv_natCast hb0 hNne] at this
    rw [hδ]; linarith
  have hδ0 : 0 < δ := lt_of_lt_of_le (div_pos hγ0 hNpos) hδge
  have hδ1 : δ ≤ 1 := by
    rw [hδ]; have := Real.rpow_nonneg hγ' ((N : ℝ)⁻¹); linarith
  have hy : 8 * ((1 - δ) / (δ * r)) ≤ 1 / 16 := by
    have hγr : γ * r = 2560 * L := by rw [hr]; field_simp
    have h1 : (1 - δ) / (δ * r) ≤ 1 / (δ * r) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : 1 / (δ * r) ≤ N / (γ * r) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have := mul_le_mul_of_nonneg_right hδge hrpos.le
      rw [div_mul_eq_mul_div, div_le_iff₀ hNpos] at this
      linarith
    have h3 : (N : ℝ) / (γ * r) ≤ 1 / 128 := by
      rw [hγr, div_le_iff₀ (by positivity)]; linarith
    linarith
  have hsp' : ∀ A : Finset (Fin n), ∑ z ∈ 𝒵.filter (fun z => A ⊆ z), m z ≤ (r ^ A.card)⁻¹ := by
    intro A
    refine le_trans ?_ (hsp A)
    unfold lawProb
    apply sum_le_sum_of_subset_of_nonneg
    · intro z hz
      have := (mem_filter.1 hz).2
      simp only [mem_filter, mem_univ, true_and]; exact this
    · intro z _ _; exact hm z
  have hcore := core 𝒵 m hm hm1 hrpos hsp' q hz J hδ0 hδ1 hy
  rw [← hNdef, hδN] at hcore
  -- each scale contributes `≤ ε / (2 (q+1))`
  have hterm : ∀ s ∈ range (q + 1), ((1 : ℝ) / 16) ^ (2 ^ s * J s) ≤ ε / (2 * (q + 1)) := by
    intro s _
    have hk : M + 1 ≤ 2 ^ s * J s := by
      have := Nat.lt_div_mul_add (a := M) (show 0 < 2 ^ s by positivity)
      simp only [hJ]; rw [mul_add, mul_one, mul_comm]; omega
    calc ((1 : ℝ) / 16) ^ (2 ^ s * J s) ≤ (1 / 2) ^ (2 ^ s * J s) :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ (1 / 2) ^ (M + 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = (1 / 2) * ((2 : ℝ) ^ M)⁻¹ := by rw [pow_succ, one_div_pow, one_div]; ring
      _ ≤ (1 / 2) * (((q : ℝ) + 1) / ε)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact inv_anti₀ (by positivity) h2M
      _ = ε / (2 * (q + 1)) := by field_simp
  have hfail : ∑ V : Finset (Fin n), wt γ V * (if ∃ z ∈ 𝒵, z ⊆ V then 0 else 1) ≤ ε / 2 := by
    refine hcore.trans ((sum_le_sum hterm).trans (le_of_eq ?_))
    rw [sum_const, card_range, nsmul_eq_mul]; push_cast; field_simp
  linarith

end Final

end

end SpreadMatchCircuit.Matching.Dev.SpreadSet
end

section
/-!
# Lemma 4 (Spread Clique Lemma) from the Spread Set Lemma (Lemma 3)

The paper's hybrid inequality (9) is false as literally stated (edges from vertex `i+1` back to
`[i] \ W_i` are present in `X'_{i+1}` but never in `X'_i`), so we use a corrected hybrid:
for a set `D` of processed vertices (disjoint from `S`), the event is
`∃ z ∈ 𝒵, z ∩ D ⊆ W ∧ R_D(z) ⊆ X`, where `R_D(z)` are the edges of `C_{z ∪ S}` outside `C_S`
avoiding `D`. Processing one more vertex `v` can only decrease the probability.
-/

namespace SpreadMatchCircuit.Matching.Dev.Lemma4

open Finset SpreadMatchCircuit.Matching SpreadMatchCircuit.Matching.Supplement

section Wt
variable {β : Type} [DecidableEq β]

/-- Binomial weight of `y ⊆ s` when each element of `s` is kept with probability `q`. -/
def wt (q : ℝ) (s y : Finset β) : ℝ := q ^ y.card * (1 - q) ^ (s.card - y.card)

lemma sum_wt (q : ℝ) (s : Finset β) : ∑ y ∈ s.powerset, wt q s y = 1 := by
  unfold wt; rw [Finset.sum_pow_mul_eq_add_pow]; simp

lemma wt_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s y : Finset β) : 0 ≤ wt q s y :=
  mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (by linarith) _)

lemma split (q : ℝ) (s B : Finset β) (f : Finset β → ℝ) :
    ∑ x ∈ s.powerset, wt q s x * f x =
      ∑ a ∈ (s \ B).powerset, ∑ y ∈ (s ∩ B).powerset,
        wt q (s \ B) a * wt q (s ∩ B) y * f (a ∪ y) := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun x => (x \ B, x ∩ B))
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    simp only [mem_powerset]
    exact union_subset (hp.1.trans sdiff_subset) (hp.2.trans inter_subset_left)
  · intro x hx
    simp only [mem_powerset] at hx
    simp only [mem_product, mem_powerset]
    exact ⟨sdiff_subset_sdiff hx le_rfl, inter_subset_inter hx le_rfl⟩
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    have h1 : ∀ v ∈ p.1, v ∉ B := fun v hv => (mem_sdiff.1 (hp.1 hv)).2
    have h2 : ∀ v ∈ p.2, v ∈ B := fun v hv => (mem_inter.1 (hp.2 hv)).2
    ext v
    · simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h | h, hB⟩
        · exact h
        · exact absurd (h2 v h) hB
      · intro h; exact ⟨Or.inl h, h1 v h⟩
    · simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨h | h, hB⟩
        · exact absurd hB (h1 v h)
        · exact h
      · intro h; exact ⟨Or.inr h, h2 v h⟩
  · intro x _
    exact sdiff_union_inter x B
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    have hd : Disjoint p.1 p.2 := by
      rw [disjoint_left]
      intro v h1 h2
      exact (mem_sdiff.1 (hp.1 h1)).2 (mem_inter.1 (hp.2 h2)).2
    have hc1 := card_le_card hp.1
    have hc2 := card_le_card hp.2
    have hs := card_sdiff_add_card_inter s B
    unfold wt
    rw [card_union_of_disjoint hd]
    have : s.card - (p.1.card + p.2.card) =
        ((s \ B).card - p.1.card) + ((s ∩ B).card - p.2.card) := by omega
    rw [this, pow_add, pow_add]
    ring

lemma sum_sup (q : ℝ) (B y0 : Finset β) (h : y0 ⊆ B) :
    ∑ y ∈ B.powerset, wt q B y * (if y0 ⊆ y then (1 : ℝ) else 0) = q ^ y0.card := by
  rw [split q B y0]
  rw [inter_eq_right.2 h]
  have : ∀ a ∈ (B \ y0).powerset,
      ∑ y ∈ y0.powerset, wt q (B \ y0) a * wt q y0 y * (if y0 ⊆ a ∪ y then (1 : ℝ) else 0) =
        wt q (B \ y0) a * q ^ y0.card := by
    intro a ha
    rw [mem_powerset] at ha
    rw [sum_eq_single y0]
    · simp [wt]
    · intro y hy hne
      rw [mem_powerset] at hy
      have : ¬ y0 ⊆ a ∪ y := by
        intro hs
        apply hne
        apply Subset.antisymm hy
        intro w hw
        rcases mem_union.1 (hs hw) with h' | h'
        · exact absurd hw (mem_sdiff.1 (ha h')).2
        · exact h'
      simp [this]
    · intro h'; exact absurd (mem_powerset.2 (Subset.refl _)) h'
  rw [sum_congr rfl this, ← sum_mul, sum_wt, one_mul]

end Wt

section Main

variable {n : ℕ}

open scoped Classical

/-- Indicator. -/
noncomputable def ind (P : Prop) : ℝ := if P then 1 else 0

lemma ind_nonneg (P : Prop) : 0 ≤ ind P := by unfold ind; split_ifs <;> norm_num

lemma ind_le_one (P : Prop) : ind P ≤ 1 := by unfold ind; split_ifs <;> norm_num

lemma ind_of {P : Prop} (h : P) : ind P = 1 := if_pos h

lemma ind_of_not {P : Prop} (h : ¬ P) : ind P = 0 := if_neg h

lemma ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  unfold ind
  by_cases hP : P
  · rw [if_pos hP, if_pos (h hP)]
  · rw [if_neg hP]; split_ifs <;> norm_num

/-- Edges of `C_{z ∪ S}` outside `C_S` and avoiding `D`. -/
noncomputable def R (S D z : Finset (Fin n)) : Finset (Edge n) :=
  (cliqueEdges (z ∪ S)).filter fun e => ¬ endpoints e ⊆ S ∧ Disjoint (endpoints e) D

/-- The hybrid event. -/
def F (Z : Finset (Finset (Fin n))) (S D W : Finset (Fin n)) (X : Finset (Edge n)) : Prop :=
  ∃ z ∈ Z, z ∩ D ⊆ W ∧ R S D z ⊆ X

/-- Joint expectation over `W` (vertices kept w.p. `γ`) and `X` (edges kept w.p. `p`). -/
noncomputable def PD (γ p : ℝ) (G : Finset (Fin n) → Finset (Edge n) → Prop) : ℝ :=
  ∑ W : Finset (Fin n), wt γ univ W * ∑ X : Finset (Edge n), wt p univ X * ind (G W X)

lemma mem_cliqueEdges {T : Finset (Fin n)} {e : Edge n} : e ∈ cliqueEdges T ↔ endpoints e ⊆ T := by
  simp [cliqueEdges]

lemma mem_R {S D z : Finset (Fin n)} {e : Edge n} :
    e ∈ R S D z ↔ endpoints e ⊆ z ∪ S ∧ ¬ endpoints e ⊆ S ∧ Disjoint (endpoints e) D := by
  simp [R, mem_cliqueEdges]

lemma split_univ {β : Type} [Fintype β] [DecidableEq β] (q : ℝ) (B : Finset β)
    (f : Finset β → ℝ) :
    ∑ x : Finset β, wt q univ x * f x =
      ∑ a ∈ (univ \ B).powerset, ∑ y ∈ B.powerset, wt q (univ \ B) a * wt q B y * f (a ∪ y) := by
  have := split q (univ : Finset β) B f
  rw [powerset_univ, univ_inter] at this
  exact this

lemma sum_wt_univ {β : Type} [Fintype β] [DecidableEq β] (q : ℝ) :
    ∑ x : Finset β, wt q univ x = 1 := by
  have := sum_wt q (univ : Finset β); rwa [powerset_univ] at this

lemma PD_mono {γ p : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {G G' : Finset (Fin n) → Finset (Edge n) → Prop} (h : ∀ W X, G W X → G' W X) :
    PD γ p G ≤ PD γ p G' := by
  unfold PD
  apply sum_le_sum; intro W _
  apply mul_le_mul_of_nonneg_left _ (wt_nonneg hγ0 hγ1 _ _)
  apply sum_le_sum; intro X _
  exact mul_le_mul_of_nonneg_left (ind_mono (h W X)) (wt_nonneg hp0 hp1 _ _)

/-- The edges at `v` avoiding `D`. -/
noncomputable def Bv (D : Finset (Fin n)) (v : Fin n) : Finset (Edge n) :=
  univ.filter fun e => v ∈ endpoints e ∧ Disjoint (endpoints e) D

/-- The `Q` functional: expectation over `X = a ∪ y`. -/
noncomputable def Qf (p : ℝ) (B : Finset (Edge n)) (H : Finset (Edge n) → Prop) : ℝ :=
  ∑ a ∈ (univ \ B).powerset, ∑ y ∈ B.powerset, wt p (univ \ B) a * wt p B y * ind (H (a ∪ y))

lemma PD_split (γ p : ℝ) (v : Fin n) (B : Finset (Edge n))
    (G : Finset (Fin n) → Finset (Edge n) → Prop) :
    PD γ p G = ∑ c ∈ (univ \ {v}).powerset, wt γ (univ \ {v}) c *
      ((1 - γ) * Qf p B (G c) + γ * Qf p B (G (c ∪ {v}))) := by
  unfold PD
  have hX : ∀ W, ∑ X : Finset (Edge n), wt p univ X * ind (G W X) = Qf p B (G W) := by
    intro W; unfold Qf; exact split_univ p B _
  simp_rw [hX]
  rw [split_univ γ {v} (fun W => Qf p B (G W))]
  apply sum_congr rfl
  intro c _
  have hps : ({v} : Finset (Fin n)).powerset = {∅, {v}} := by
    ext x; simp [subset_singleton_iff]
  rw [hps, sum_pair (by simp)]
  simp only [wt, card_empty, card_singleton, pow_zero, union_empty]
  ring

lemma Qf_const (p : ℝ) (B : Finset (Edge n)) (H : Finset (Edge n) → Prop)
    (hH : ∀ a ∈ (univ \ B).powerset, ∀ y ∈ B.powerset, H (a ∪ y) ↔ H a) :
    Qf p B H = ∑ a ∈ (univ \ B).powerset, wt p (univ \ B) a * ind (H a) := by
  unfold Qf
  apply sum_congr rfl; intro a ha
  rw [show ∑ y ∈ B.powerset, wt p (univ \ B) a * wt p B y * ind (H (a ∪ y)) =
      ∑ y ∈ B.powerset, wt p B y * (wt p (univ \ B) a * ind (H a)) from
    sum_congr rfl fun y hy => by rw [hH a ha y hy]; ring]
  rw [← sum_mul, sum_wt, one_mul]

lemma Qf_eq (p : ℝ) (B : Finset (Edge n)) (H : Finset (Edge n) → Prop) :
    Qf p B H = ∑ a ∈ (univ \ B).powerset, wt p (univ \ B) a *
      ∑ y ∈ B.powerset, wt p B y * ind (H (a ∪ y)) := by
  unfold Qf
  apply sum_congr rfl; intro a _
  rw [mul_sum]; apply sum_congr rfl; intro y _; ring

lemma card_edges_at_le (v : Fin n) (T : Finset (Fin n)) (y0 : Finset (Edge n))
    (h : ∀ e ∈ y0, v ∈ endpoints e ∧ endpoints e ⊆ T) : y0.card ≤ T.card := by
  have h1 : y0.map (Function.Embedding.subtype _) ⊆ T.image (fun u => s(v, u)) := by
    intro x hx
    rw [mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨hv, hT⟩ := h e he
    have hv' : v ∈ e.1 := by simpa [endpoints, Sym2.mem_toFinset] using hv
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 hv'
    rw [mem_image]
    refine ⟨b, hT ?_, ?_⟩
    · simp [endpoints, Sym2.mem_toFinset, hb]
    · simp [hb]
  have := card_le_card h1
  rw [card_map] at this
  exact this.trans card_image_le

/-- The pointwise comparison for one vertex step. -/
lemma pointwise {Z : Finset (Finset (Fin n))} {S D : Finset (Fin n)} {v : Fin n} {t p γ : ℝ}
    (hZ : ∀ z ∈ Z, (z.card : ℝ) ≤ t) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hγ : γ = p ^ (t + (S.card : ℝ))) (hvD : v ∉ D) (hvS : v ∉ S)
    (c : Finset (Fin n)) (hc : v ∉ c) (a : Finset (Edge n)) (ha : a ⊆ univ \ Bv D v) :
    (1 - γ) * ind (F Z S (insert v D) c a) + γ * ind (F Z S (insert v D) (c ∪ {v}) a) ≤
      ∑ y ∈ (Bv D v).powerset, wt p (Bv D v) y * ind (F Z S D c (a ∪ y)) := by
  have hγ0 : 0 < γ := by rw [hγ]; exact Real.rpow_pos_of_pos hp0 _
  have hγ1 : γ ≤ 1 := by
    rw [hγ]; exact Real.rpow_le_one hp0.le hp1 (add_nonneg ht.le (Nat.cast_nonneg _))
  have hwt : ∀ y, 0 ≤ wt p (Bv D v) y := fun y => wt_nonneg hp0.le hp1 _ y
  have hRHS0 : 0 ≤ ∑ y ∈ (Bv D v).powerset, wt p (Bv D v) y * ind (F Z S D c (a ∪ y)) :=
    sum_nonneg fun y _ => mul_nonneg (hwt y) (ind_nonneg _)
  by_cases h1 : F Z S (insert v D) c a
  · -- every `y` works
    have hall : ∀ y, F Z S D c (a ∪ y) := by
      obtain ⟨z, hz, hzc, hR⟩ := h1
      have hvz : v ∉ z := fun hv => hc (hzc (mem_inter.2 ⟨hv, mem_insert_self _ _⟩))
      intro y
      refine ⟨z, hz, fun w hw => hzc ?_, fun e he => ?_⟩
      · rw [mem_inter] at hw ⊢; exact ⟨hw.1, mem_insert_of_mem hw.2⟩
      · rw [mem_R] at he
        apply mem_union_left
        apply hR
        rw [mem_R]
        refine ⟨he.1, he.2.1, ?_⟩
        rw [disjoint_insert_right]
        refine ⟨fun hve => ?_, he.2.2⟩
        rcases mem_union.1 (he.1 hve) with h | h
        · exact hvz h
        · exact hvS h
    have : ∑ y ∈ (Bv D v).powerset, wt p (Bv D v) y * ind (F Z S D c (a ∪ y)) = 1 := by
      rw [← sum_wt p (Bv D v)]
      apply sum_congr rfl; intro y _; rw [ind_of (hall y), mul_one]
    rw [this]
    have := ind_le_one (F Z S (insert v D) c a)
    have := ind_le_one (F Z S (insert v D) (c ∪ {v}) a)
    nlinarith
  · rw [ind_of_not h1, mul_zero, zero_add]
    by_cases h2 : F Z S (insert v D) (c ∪ {v}) a
    · rw [ind_of h2, mul_one]
      obtain ⟨z, hz, hzc, hR⟩ := h2
      set y0 := (R S D z).filter (fun e => e ∈ Bv D v) with hy0
      have hy0B : y0 ⊆ Bv D v := fun e he => (mem_filter.1 he).2
      have hgood : ∀ y, y0 ⊆ y → F Z S D c (a ∪ y) := by
        intro y hy
        refine ⟨z, hz, fun w hw => ?_, fun e he => ?_⟩
        · rw [mem_inter] at hw
          have := hzc (mem_inter.2 ⟨hw.1, mem_insert_of_mem hw.2⟩)
          rcases mem_union.1 this with h | h
          · exact h
          · rw [mem_singleton] at h; subst h; exact absurd hw.2 hvD
        · by_cases heB : e ∈ Bv D v
          · exact mem_union_right _ (hy (mem_filter.2 ⟨he, heB⟩))
          · apply mem_union_left
            apply hR
            rw [mem_R] at he ⊢
            refine ⟨he.1, he.2.1, ?_⟩
            rw [disjoint_insert_right]
            refine ⟨fun hve => heB ?_, he.2.2⟩
            simp only [Bv, mem_filter, mem_univ, true_and]
            exact ⟨hve, he.2.2⟩
      have hcard : (y0.card : ℝ) ≤ t + (S.card : ℝ) := by
        have h3 : y0.card ≤ (z ∪ S).card := by
          apply card_edges_at_le v
          intro e he
          rw [hy0, mem_filter, mem_R] at he
          exact ⟨(by simpa [Bv] using he.2 : v ∈ endpoints e ∧ _).1, he.1.1⟩
        have h4 := card_union_le z S
        have h5 := hZ z hz
        have : ((z ∪ S).card : ℝ) ≤ (z.card : ℝ) + (S.card : ℝ) := by exact_mod_cast h4
        have : (y0.card : ℝ) ≤ ((z ∪ S).card : ℝ) := by exact_mod_cast h3
        linarith
      calc γ ≤ p ^ y0.card := by
            rw [hγ, ← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_ge hp0 hp1 hcard
        _ = ∑ y ∈ (Bv D v).powerset, wt p (Bv D v) y * (if y0 ⊆ y then (1 : ℝ) else 0) :=
            (sum_sup p _ y0 hy0B).symm
        _ ≤ _ := by
            apply sum_le_sum; intro y _
            apply mul_le_mul_of_nonneg_left _ (hwt y)
            split_ifs with h
            · rw [ind_of (hgood y h)]
            · exact ind_nonneg _
    · rw [ind_of_not h2, mul_zero]; exact hRHS0

lemma step {Z : Finset (Finset (Fin n))} {S D : Finset (Fin n)} {v : Fin n} {t p γ : ℝ}
    (hZ : ∀ z ∈ Z, (z.card : ℝ) ≤ t) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hγ : γ = p ^ (t + (S.card : ℝ))) (hvD : v ∉ D) (hvS : v ∉ S) :
    PD γ p (F Z S (insert v D)) ≤ PD γ p (F Z S D) := by
  have hγ0 : 0 < γ := by rw [hγ]; exact Real.rpow_pos_of_pos hp0 _
  have hγ1 : γ ≤ 1 := by
    rw [hγ]; exact Real.rpow_le_one hp0.le hp1 (add_nonneg ht.le (Nat.cast_nonneg _))
  set B := Bv D v
  rw [PD_split γ p v B, PD_split γ p v B]
  apply sum_le_sum; intro c hc
  have hvc : v ∉ c := fun h => by
    have := mem_powerset.1 hc h
    simp at this
  apply mul_le_mul_of_nonneg_left _ (wt_nonneg hγ0.le hγ1 _ _)
  -- left side: `F (insert v D)` does not see `B`
  have hconst : ∀ W, ∀ a ∈ (univ \ B).powerset, ∀ y ∈ B.powerset,
      F Z S (insert v D) W (a ∪ y) ↔ F Z S (insert v D) W a := by
    intro W a _ y hy
    rw [mem_powerset] at hy
    unfold F
    constructor
    · rintro ⟨z, hz, h1, h2⟩
      refine ⟨z, hz, h1, fun e he => ?_⟩
      rcases mem_union.1 (h2 he) with h | h
      · exact h
      · exfalso
        have heB := hy h
        simp only [B, Bv, mem_filter, mem_univ, true_and] at heB
        rw [mem_R] at he
        exact (disjoint_left.1 he.2.2 heB.1) (mem_insert_self _ _)
    · rintro ⟨z, hz, h1, h2⟩
      exact ⟨z, hz, h1, h2.trans subset_union_left⟩
  rw [Qf_const p B _ (hconst c), Qf_const p B _ (hconst (c ∪ {v}))]
  -- right side: `F D` does not see `v ∈ W`
  have hD : ∀ X, F Z S D (c ∪ {v}) X ↔ F Z S D c X := by
    intro X
    unfold F
    constructor
    · rintro ⟨z, hz, h1, h2⟩
      refine ⟨z, hz, fun w hw => ?_, h2⟩
      rcases mem_union.1 (h1 hw) with h | h
      · exact h
      · rw [mem_singleton] at h; subst h; exact absurd (mem_inter.1 hw).2 hvD
    · rintro ⟨z, hz, h1, h2⟩
      exact ⟨z, hz, h1.trans subset_union_left, h2⟩
  rw [show F Z S D (c ∪ {v}) = F Z S D c from funext fun X => propext (hD X)]
  rw [show (1 - γ) * Qf p B (F Z S D c) + γ * Qf p B (F Z S D c) = Qf p B (F Z S D c) by ring]
  rw [Qf_eq, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum; intro a ha
  have hwa := wt_nonneg hp0.le hp1 (univ \ B) a
  have := pointwise hZ ht hp0 hp1 hγ hvD hvS c hvc a (mem_powerset.1 ha)
  calc (1 - γ) * (wt p (univ \ B) a * ind (F Z S (insert v D) c a)) +
        γ * (wt p (univ \ B) a * ind (F Z S (insert v D) (c ∪ {v}) a))
      = wt p (univ \ B) a * ((1 - γ) * ind (F Z S (insert v D) c a) +
          γ * ind (F Z S (insert v D) (c ∪ {v}) a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hwa

lemma chain {Z : Finset (Finset (Fin n))} {S : Finset (Fin n)} {t p γ : ℝ}
    (hZ : ∀ z ∈ Z, (z.card : ℝ) ≤ t) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hγ : γ = p ^ (t + (S.card : ℝ))) :
    ∀ D : Finset (Fin n), Disjoint D S → PD γ p (F Z S D) ≤ PD γ p (F Z S ∅) := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; exact le_rfl
  | insert v D hv ih =>
    intro hd
    rw [disjoint_insert_left] at hd
    exact (step hZ ht hp0 hp1 hγ hv hd.1).trans (ih hd.2)

end Main

open scoped Classical in
/-- The Spread Set Lemma (Lemma 3 of the paper, cited there from [2,16,11,4,17]): if `Z` is an
`r`-spread random subset of `[n]` of size at most `t`, with `r = α log(t/ε)/γ`, then the
`γ`-random subset `W` of `[n]` contains some `z ∈ 𝒵` with probability `> 1 - ε`. -/
def SpreadSetStatement : Prop :=
  ∃ α : ℝ, 0 < α ∧
    ∀ (n : ℕ) (μ : PMF (Finset (Fin n))) (ε t γ r : ℝ),
      0 < ε → ε ≤ 1 / 2 → 0 < t → 0 < γ → γ ≤ 1 →
      r = α * Real.log (t / ε) / γ →
      IsSetSpread μ r → IsBoundedSetLaw μ t →
      1 - ε < ∑ W ∈ univ.filter (fun W : Finset (Fin n) => ∃ z ∈ lawSupport μ, z ⊆ W),
        γ ^ W.card * (1 - γ) ^ (n - W.card)

end SpreadMatchCircuit.Matching.Dev.Lemma4

namespace SpreadMatchCircuit.Matching.Supplement

open Finset SpreadMatchCircuit.Matching.Dev.Lemma4

open scoped Classical in
theorem chk_lemma_4_of_spread_set (hss : SpreadSetStatement) :
    ∃ α : ℝ, 0 < α ∧
      ∀ (n : ℕ) (μ : PMF (Finset (Fin n))) (ε t p r : ℝ) (S : Finset (Fin n)),
        0 < ε → ε ≤ 1 / 2 → 0 < t → 0 < p → p ≤ 1 →
        r = α * Real.log (t / ε) / p ^ (t + (S.card : ℝ)) →
        IsSetSpread μ r → IsBoundedSetLaw μ t →
        1 - ε < randomGraphProb n p
          (fun X => ∃ z ∈ lawSupport μ, cliqueEdges (z ∪ S) ⊆ X ∪ cliqueEdges S) := by
  obtain ⟨α, hα, hss⟩ := hss
  refine ⟨α, hα, ?_⟩
  intro n μ ε t p r S hε0 hε ht hp0 hp1 hr hsp hbd
  set γ := p ^ (t + (S.card : ℝ)) with hγ
  have hγ0 : 0 < γ := Real.rpow_pos_of_pos hp0 _
  have hγ1 : γ ≤ 1 := Real.rpow_le_one hp0.le hp1 (add_nonneg ht.le (Nat.cast_nonneg _))
  have key := hss n μ ε t γ r hε0 hε ht hγ0 hγ1 hr hsp hbd
  set Z := lawSupport μ
  have hZ : ∀ z ∈ Z, (z.card : ℝ) ≤ t := hbd
  -- the vertex probability is a `PD`
  have h1 : ∑ W ∈ univ.filter (fun W : Finset (Fin n) => ∃ z ∈ Z, z ⊆ W),
      γ ^ W.card * (1 - γ) ^ (n - W.card) ≤ PD γ p (F Z S (univ \ S)) := by
    have : ∑ W ∈ univ.filter (fun W : Finset (Fin n) => ∃ z ∈ Z, z ⊆ W),
        γ ^ W.card * (1 - γ) ^ (n - W.card) =
        PD γ p (fun W _ => ∃ z ∈ Z, z ⊆ W) := by
      unfold PD
      rw [sum_filter]
      apply sum_congr rfl; intro W _
      rw [← sum_mul, sum_wt_univ, one_mul]
      unfold ind wt
      rw [card_univ, Fintype.card_fin]
      split_ifs <;> simp
    rw [this]
    apply PD_mono hγ0.le hγ1 hp0.le hp1
    rintro W X ⟨z, hz, hzW⟩
    refine ⟨z, hz, inter_subset_left.trans hzW, fun e he => ?_⟩
    exfalso
    rw [mem_R] at he
    apply he.2.1
    intro w hw
    by_contra hwS
    exact disjoint_left.1 he.2.2 hw (by simp [hwS])
  have h2 := chain hZ ht hp0 hp1 hγ (univ \ S) disjoint_sdiff_self_left
  have h3 : PD γ p (F Z S ∅) = randomGraphProb n p
      (fun X => ∃ z ∈ Z, cliqueEdges (z ∪ S) ⊆ X ∪ cliqueEdges S) := by
    have hiff : ∀ (W : Finset (Fin n)) X, F Z S ∅ W X ↔
        ∃ z ∈ Z, cliqueEdges (z ∪ S) ⊆ X ∪ cliqueEdges S := by
      intro W X
      unfold F
      apply exists_congr; intro z
      apply and_congr_right; intro _
      simp only [inter_empty, empty_subset, true_and]
      constructor
      · intro h e he
        by_cases hS : endpoints e ⊆ S
        · exact mem_union_right _ (mem_cliqueEdges.2 hS)
        · exact mem_union_left _ (h (mem_R.2 ⟨mem_cliqueEdges.1 he, hS, disjoint_empty_right _⟩))
      · intro h e he
        rw [mem_R] at he
        rcases mem_union.1 (h (mem_cliqueEdges.2 he.1)) with h' | h'
        · exact h'
        · exact absurd (mem_cliqueEdges.1 h') he.2.1
    unfold PD
    simp_rw [hiff]
    rw [← sum_mul, sum_wt_univ, one_mul]
    unfold randomGraphProb
    rw [sum_filter]
    apply sum_congr rfl; intro X _
    unfold ind wt
    rw [card_univ]
    split_ifs <;> simp
  linarith
end SpreadMatchCircuit.Matching.Supplement
end

section
/-!
# Lemma 4 (Spread Clique Lemma), complete

`chk_lemma_4_of_spread_set` (Lemma4.lean) reduces Lemma 4 to the Spread Set Lemma, which is
proved in SpreadSet.lean (`Dev.SpreadSet.spread_set`).
-/

namespace SpreadMatchCircuit.Matching.Supplement

/-- Lemma 4 (Spread Clique Lemma), p. 4, statement verbatim. -/
theorem chk_lemma_4 :
    ∃ α : ℝ, 0 < α ∧
      ∀ (n : ℕ) (μ : PMF (Finset (Fin n))) (ε t p r : ℝ) (S : Finset (Fin n)),
        0 < ε → ε ≤ 1 / 2 → 0 < t → 0 < p → p ≤ 1 →
        r = α * Real.log (t / ε) / p ^ (t + (S.card : ℝ)) →
        IsSetSpread μ r → IsBoundedSetLaw μ t →
        1 - ε < randomGraphProb n p
          (fun X => ∃ z ∈ lawSupport μ, cliqueEdges (z ∪ S) ⊆ X ∪ cliqueEdges S) :=
  chk_lemma_4_of_spread_set Dev.SpreadSet.spread_set

end SpreadMatchCircuit.Matching.Supplement
end

theorem solution : type_of% @SpreadMatchCircuit.Matching.Supplement.chk_lemma_4 := @SpreadMatchCircuit.Matching.Supplement.chk_lemma_4
