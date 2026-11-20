-- Prove2me | solution 1 for SpreadMatchCircuit.Matching.Supplement.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:58:39.449984+00:00
-- url     : https://prove2.me/submissions/dd19625f-1197-4e26-bc28-66bf6cc697b8

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_SetSpread
import Definitions.Def_SpreadMatchCircuit_Matching_MonotoneCircuit
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_PolyImage

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
namespace SpreadMatchCircuit.Matching.Dev.Thm9

open Finset Polynomial SpreadMatchCircuit.Matching.Supplement

/-! ## Random subsets -/

/-- The indicator assignment of a set. -/
def ind {U : Type} [DecidableEq U] (X : Finset U) : U → Bool := fun u => decide (u ∈ X)

open scoped Classical in
/-- Probability of an event for the random set containing each element independently with
probability `γ`. -/
noncomputable def randProb (U : Type) [Fintype U] (γ : ℝ) (P : Finset U → Prop) : ℝ :=
  ∑ X ∈ univ.filter P, γ ^ X.card * (1 - γ) ^ (Fintype.card U - X.card)

lemma randProb_eq (U : Type) [Fintype U] (γ : ℝ) (P : Finset U → Prop) [DecidablePred P] :
    randProb U γ P = ∑ X : Finset U,
      if P X then γ ^ X.card * (1 - γ) ^ (Fintype.card U - X.card) else 0 := by
  classical
  unfold randProb
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun X _ => by split_ifs <;> rfl)

lemma w_nonneg {U : Type} [Fintype U] {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (X : Finset U) :
    0 ≤ γ ^ X.card * (1 - γ) ^ (Fintype.card U - X.card) :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

lemma randProb_mono {U : Type} [Fintype U] {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    {P Q : Finset U → Prop} (hPQ : ∀ X, P X → Q X) : randProb U γ P ≤ randProb U γ Q := by
  classical
  rw [randProb_eq, randProb_eq]
  apply Finset.sum_le_sum
  intro X _
  have := w_nonneg h0 h1 X
  split_ifs with h1 h2 <;> first | exact le_rfl | exact this | exact absurd (hPQ X h1) h2

lemma randProb_union {U : Type} [Fintype U] {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    {ι : Type} (s : Finset ι) (P : ι → Finset U → Prop) :
    randProb U γ (fun X => ∃ i ∈ s, P i X) ≤ ∑ i ∈ s, randProb U γ (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [randProb]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsplit : randProb U γ (fun X => ∃ i ∈ insert a s, P i X) ≤
        randProb U γ (P a) + randProb U γ (fun X => ∃ i ∈ s, P i X) := by
      rw [randProb_eq, randProb_eq, randProb_eq, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro X _
      have := w_nonneg h0 h1 X
      by_cases hA : ∃ i ∈ insert a s, P i X
      · rw [if_pos hA]
        obtain ⟨i, hi, hPi⟩ := hA
        rcases mem_insert.mp hi with rfl | hi
        · rw [if_pos hPi]; split_ifs <;> linarith
        · rw [if_pos (show ∃ j ∈ s, P j X from ⟨i, hi, hPi⟩)]; split_ifs <;> linarith
      · rw [if_neg hA]; split_ifs <;> linarith
    linarith

lemma randProb_subset {U : Type} [Fintype U] [DecidableEq U] (γ : ℝ) (T : Finset U) :
    randProb U γ (fun X => T ⊆ X) = γ ^ T.card := by
  rw [randProb_eq, ← Finset.sum_filter]
  have himg : univ.filter (fun X : Finset U => T ⊆ X) = (Tᶜ).powerset.image (fun Y => T ∪ Y) := by
    ext X
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_powerset]
    constructor
    · intro hX
      refine ⟨X \ T, ?_, ?_⟩
      · intro x hx; simp only [mem_compl]; exact (mem_sdiff.mp hx).2
      · exact Finset.union_sdiff_of_subset hX
    · rintro ⟨Y, _, rfl⟩; exact subset_union_left
  rw [himg, Finset.sum_image]
  · have hcard : ∀ Y ∈ (Tᶜ).powerset, (T ∪ Y).card = T.card + Y.card := by
      intro Y hY
      rw [mem_powerset] at hY
      apply Finset.card_union_of_disjoint
      rw [Finset.disjoint_left]
      intro x hxT hxY
      exact (mem_compl.mp (hY hxY)) hxT
    rw [Finset.sum_congr rfl (fun Y hY => by
      rw [hcard Y hY, pow_add, mul_assoc,
        show Fintype.card U - (T.card + Y.card) = Tᶜ.card - Y.card by
          rw [Finset.card_compl]; omega])]
    rw [← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]
    simp
  · intro Y₁ h₁ Y₂ h₂ heq0
    have heq : T ∪ Y₁ = T ∪ Y₂ := heq0
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at h₁ h₂
    ext x
    constructor
    · intro hx
      have : x ∈ T ∪ Y₂ := heq ▸ mem_union_right T hx
      rcases mem_union.mp this with h | h
      · exact absurd h (mem_compl.mp (h₁ hx))
      · exact h
    · intro hx
      have : x ∈ T ∪ Y₁ := heq.symm ▸ mem_union_right T hx
      rcases mem_union.mp this with h | h
      · exact absurd h (mem_compl.mp (h₂ hx))
      · exact h

/-! ## Small `d`: a single input gate cannot compute `F_{k,d}` -/

lemma three_lt_k {n k d : ℕ} (hn : n.Prime) (hd : 1 ≤ d)
    (hlog : 3 * (d : ℝ) * Real.log n ≤ k) : 2 < k := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2
  have hl2 := Real.log_two_gt_d9
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlpos : 0 ≤ Real.log n := by linarith
  have : (2 : ℝ) < k := by nlinarith
  exact_mod_cast this

lemma size_ge_two {n k d : ℕ} (hn : n.Prime) (hd : 1 ≤ d)
    (hlog : 3 * (d : ℝ) * Real.log n ≤ k) (C : MonotoneCircuit (ZMod n))
    (hC : ∀ x : ZMod n → Bool, C.eval x = true ↔ PolyImageFun n k d x) : 2 ≤ C.size := by
  have hk := three_lt_k hn hd hlog
  by_contra hlt
  obtain ⟨size, gate, output⟩ := C
  have hpos : 0 < size := Nat.lt_of_le_of_lt (Nat.zero_le _) output.isLt
  simp only at hlt
  have h1 : size = 1 := by omega
  subst h1
  have hout : output = 0 := Subsingleton.elim _ _
  subst hout
  have key : ∃ i : ZMod n, ∀ x, (MonotoneCircuit.mk 1 gate 0).eval x = x i := by
    cases hg : gate 0 with
    | input i =>
      refine ⟨i, fun x => ?_⟩
      unfold MonotoneCircuit.eval
      rw [MonotoneCircuit.nodeValue]
      simp only [hg]
    | and a b => exact a.elim0
    | or a b => exact a.elim0
  obtain ⟨i, hi⟩ := key
  have hF := (hC (ind {i})).mp (by rw [hi]; simp [ind])
  obtain ⟨w, _, hkw, hsub⟩ := hF
  have hsub' : polyImage n k w ⊆ {i} := by
    intro j hj
    have := hsub j hj
    simpa [ind] using this
  have := Finset.card_le_card hsub'
  simp at this
  omega

/-! ## Polynomials of degree at most `d` by coefficient vectors -/

section Poly

variable {n d : ℕ}

/-- The polynomial with coefficient vector `c`. -/
noncomputable def poly (c : Fin (d + 1) → ZMod n) : (ZMod n)[X] :=
  ∑ i : Fin (d + 1), monomial (i : ℕ) (c i)

lemma coeff_poly (c : Fin (d + 1) → ZMod n) (j : ℕ) :
    (poly c).coeff j = if h : j < d + 1 then c ⟨j, h⟩ else 0 := by
  unfold poly
  rw [Polynomial.finsetSum_coeff]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbj; apply hb; ext; exact hbj
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hbj; apply h; rw [← hbj]; exact b.isLt

lemma degree_poly_le (c : Fin (d + 1) → ZMod n) : (poly c).degree ≤ d := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  rw [coeff_poly, dif_neg]
  intro h
  have : (m : WithBot ℕ) ≤ d := by exact_mod_cast Nat.lt_succ_iff.mp h
  exact absurd hm (not_lt.mpr this)

lemma degree_poly (c : Fin (d + 1) → ZMod n) (h : c (Fin.last d) ≠ 0) :
    (poly c).degree = d := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero (degree_poly_le c)
  rw [coeff_poly, dif_pos (Nat.lt_succ_self d)]
  exact h

lemma poly_injective : Function.Injective (poly (n := n) (d := d)) := by
  intro c c' h
  funext i
  have := congrArg (fun p => Polynomial.coeff p (i : ℕ)) h
  simp only [coeff_poly, dif_pos i.isLt] at this
  exact this

lemma exists_poly (w : (ZMod n)[X]) (hw : w.degree = d) :
    ∃ c : Fin (d + 1) → ZMod n, poly c = w := by
  refine ⟨fun i => w.coeff i, ?_⟩
  ext j
  rw [coeff_poly]
  split_ifs with h
  · rfl
  · symm
    apply Polynomial.coeff_eq_zero_of_degree_lt
    rw [hw]
    exact_mod_cast (by omega : d < j)

variable [Fact n.Prime]

lemma eq_of_eval_eq (T : Finset (ZMod n)) (hT : d + 1 ≤ T.card)
    (c c' : Fin (d + 1) → ZMod n)
    (h : ∀ x ∈ T, (poly c).eval x = (poly c').eval x) : c = c' := by
  apply poly_injective
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq T _ h
  calc (poly c - poly c').degree ≤ max (poly c).degree (poly c').degree := degree_sub_le _ _
    _ ≤ d := max_le (degree_poly_le c) (degree_poly_le c')
    _ < T.card := by exact_mod_cast (by omega : d < T.card)

variable [NeZero n]

lemma card_le_of_agree (A : Finset (Fin (d + 1) → ZMod n)) (P T : Finset (ZMod n))
    (hT : d + 1 ≤ T.card)
    (hagree : ∀ c ∈ A, ∀ c' ∈ A, (∀ x ∈ P, (poly c).eval x = (poly c').eval x) →
      ∀ x ∈ T, (poly c).eval x = (poly c').eval x) :
    A.card ≤ n ^ P.card := by
  have h1 : A.card ≤ (univ : Finset (P → ZMod n)).card := by
    apply Finset.card_le_card_of_injOn (fun c => fun x : P => (poly c).eval (x : ZMod n))
    · intro c _; exact mem_univ _
    · intro c hc c' hc' hcc
      apply eq_of_eval_eq T hT c c'
      apply hagree c hc c' hc'
      intro x hx
      exact congrFun hcc ⟨x, hx⟩
  simpa [Fintype.card_fun, ZMod.card] using h1

omit [NeZero n] in
lemma natCast_inj_of_lt {i j : ℕ} (hi : i < n) (hj : j < n) (h : (i : ZMod n) = (j : ZMod n)) :
    i = j := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  exact h

/-- Spread count: `S ⊆ w([k])` for at most `k^|S| n^{d+1-|S|}` coefficient vectors. -/
lemma card_subset_img_le {k : ℕ} (hnd : d + 1 ≤ n) (S : Finset (ZMod n)) (hS : S.card ≤ d + 1) :
    (univ.filter (fun c : Fin (d + 1) → ZMod n => S ⊆ polyImage n k (poly c))).card ≤
      k ^ S.card * n ^ (d + 1 - S.card) := by
  classical
  set Φ : Finset (S → ℕ) := Fintype.piFinset (fun _ : S => Icc 1 k) with hΦ
  let A : (S → ℕ) → Finset (Fin (d + 1) → ZMod n) := fun φ =>
    univ.filter (fun c => ∀ s : S, (poly c).eval (φ s : ZMod n) = s)
  have hsub : univ.filter (fun c : Fin (d + 1) → ZMod n => S ⊆ polyImage n k (poly c)) ⊆
      Φ.biUnion A := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    have hex : ∀ s : S, ∃ j ∈ Icc 1 k, (poly c).eval (j : ZMod n) = s := by
      intro s
      have := hc s.2
      simp only [polyImage, mem_image] at this
      exact this
    choose φ hφ using hex
    rw [mem_biUnion]
    refine ⟨φ, ?_, ?_⟩
    · rw [hΦ, Fintype.mem_piFinset]; intro s; exact (hφ s).1
    · simp only [A, mem_filter, mem_univ, true_and]; intro s; exact (hφ s).2
  have hA : ∀ φ ∈ Φ, (A φ).card ≤ n ^ (d + 1 - S.card) := by
    intro φ _
    rcases (A φ).eq_empty_or_nonempty with he | ⟨c0, hc0⟩
    · rw [he]; simp
    have hc0' : ∀ s : S, (poly c0).eval (φ s : ZMod n) = s := by
      simpa [A] using hc0
    set T0 : Finset (ZMod n) := univ.image (fun s : S => (φ s : ZMod n)) with hT0
    have hT0card : T0.card = S.card := by
      rw [hT0, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_coe]
      intro s s' hss
      apply Subtype.ext
      have h1 := hc0' s
      have h2 := hc0' s'
      simp only at hss
      rw [← h1, ← h2, hss]
    have hcompl : d + 1 - S.card ≤ T0ᶜ.card := by
      rw [Finset.card_compl, ZMod.card, hT0card]; omega
    obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hcompl
    rw [← hPcard]
    apply card_le_of_agree (A φ) P (T0 ∪ P)
    · rw [Finset.card_union_of_disjoint]
      · omega
      · rw [Finset.disjoint_left]; intro x hx hxP; exact (mem_compl.mp (hPsub hxP)) hx
    · intro c hc c' hc' hagr x hx
      rcases mem_union.mp hx with hx | hx
      · rw [hT0, mem_image] at hx
        obtain ⟨s, _, rfl⟩ := hx
        have e1 : (poly c).eval (φ s : ZMod n) = s := by simp [A] at hc; exact hc s s.2
        have e2 : (poly c').eval (φ s : ZMod n) = s := by simp [A] at hc'; exact hc' s s.2
        rw [e1, e2]
      · exact hagr x hx
  calc _ ≤ (Φ.biUnion A).card := Finset.card_le_card hsub
    _ ≤ ∑ φ ∈ Φ, (A φ).card := Finset.card_biUnion_le
    _ ≤ ∑ φ ∈ Φ, n ^ (d + 1 - S.card) := Finset.sum_le_sum hA
    _ = k ^ S.card * n ^ (d + 1 - S.card) := by
      rw [Finset.sum_const, smul_eq_mul, hΦ, Fintype.card_piFinset]
      simp

/-- `j` repeats an earlier value of `w = poly c` on `[k]`. -/
def coll (k : ℕ) (c : Fin (d + 1) → ZMod n) (j : ℕ) : Prop :=
  ∃ i ∈ Icc 1 k, i < j ∧ (poly c).eval (i : ZMod n) = (poly c).eval (j : ZMod n)

omit [NeZero n] in
open scoped Classical in
lemma k_le_img_add_coll (k : ℕ) (c : Fin (d + 1) → ZMod n) :
    k ≤ (polyImage n k (poly c)).card + ((Icc 1 k).filter (coll k c)).card := by
  have hF : ((Icc 1 k).filter (fun j => ¬ coll k c j)).card ≤ (polyImage n k (poly c)).card := by
    apply Finset.card_le_card_of_injOn (fun j : ℕ => (poly c).eval (j : ZMod n))
    · intro j hj
      simp only [coe_filter, Set.mem_ofPred_eq] at hj
      simp only [polyImage, coe_image, Set.mem_image, mem_coe]
      exact ⟨j, hj.1, rfl⟩
    · intro j₁ h₁ j₂ h₂ heq
      simp only [coe_filter, Set.mem_ofPred_eq] at h₁ h₂
      simp only at heq
      rcases lt_trichotomy j₁ j₂ with h | h | h
      · exact absurd ⟨j₁, h₁.1, h, heq⟩ h₂.2
      · exact h
      · exact absurd ⟨j₂, h₂.1, h, heq.symm⟩ h₁.2
  have := Finset.card_filter_add_card_filter_not (s := Icc 1 k) (coll k c)
  rw [Nat.card_Icc] at this
  omega

lemma card_eval_eq_le (hd : 1 ≤ d) (hnd : d + 1 ≤ n) {i j : ZMod n} (hij : i ≠ j) :
    (univ.filter (fun c : Fin (d + 1) → ZMod n => (poly c).eval i = (poly c).eval j)).card ≤
      n ^ d := by
  classical
  have hc : d - 1 ≤ ({i, j} : Finset (ZMod n))ᶜ.card := by
    rw [Finset.card_compl, ZMod.card, Finset.card_pair hij]; omega
  obtain ⟨P0, hP0sub, hP0card⟩ := Finset.exists_subset_card_eq hc
  have hjP0 : j ∉ P0 := fun h => by simpa using hP0sub h
  have hiP0 : i ∉ P0 := fun h => by simpa using hP0sub h
  have hiP : i ∉ insert j P0 := by
    rw [mem_insert]; rintro (h | h); exact hij h; exact hiP0 h
  have hPcard : (insert j P0).card = d := by rw [card_insert_of_notMem hjP0]; omega
  refine le_trans ?_ (le_of_eq (congrArg (n ^ ·) hPcard))
  apply card_le_of_agree _ (insert j P0) (insert i (insert j P0))
  · rw [card_insert_of_notMem hiP]; omega
  · intro c hc c' hc' hagr x hx
    simp only [mem_filter, mem_univ, true_and] at hc hc'
    rcases mem_insert.mp hx with rfl | hx
    · exact hc.trans ((hagr j (mem_insert_self _ _)).trans hc'.symm)
    · exact hagr x hx

/-- Few coefficient vectors have a small image on `[k]`. -/
lemma card_bad_le {k : ℕ} (hd : 1 ≤ d) (hnd : d + 1 ≤ n) (hkn : k < n) :
    (univ.filter (fun c : Fin (d + 1) → ZMod n =>
      2 * (polyImage n k (poly c)).card < k)).card ≤ 2 * k * n ^ d := by
  classical
  set B := univ.filter (fun c : Fin (d + 1) → ZMod n => 2 * (polyImage n k (poly c)).card < k)
  have hcollj : ∀ j ∈ Icc 1 k, (univ.filter (fun c : Fin (d + 1) → ZMod n => coll k c j)).card ≤ k * n ^ d := by
    intro j hj
    have hsub : univ.filter (fun c : Fin (d + 1) → ZMod n => coll k c j) ⊆ ((Icc 1 k).filter (· < j)).biUnion
        (fun i => univ.filter (fun c : Fin (d + 1) → ZMod n =>
          (poly c).eval (i : ZMod n) = (poly c).eval (j : ZMod n))) := by
      intro c hc
      rw [mem_filter] at hc
      obtain ⟨_, i, hi, hij, he⟩ := hc
      rw [mem_biUnion]
      exact ⟨i, mem_filter.mpr ⟨hi, hij⟩, by simp [he]⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ (Icc 1 k).filter (· < j), (univ.filter (fun c : Fin (d + 1) → ZMod n =>
          (poly c).eval (i : ZMod n) = (poly c).eval (j : ZMod n))).card := card_biUnion_le
      _ ≤ ∑ i ∈ (Icc 1 k).filter (· < j), n ^ d := by
          apply Finset.sum_le_sum
          intro i hi
          simp only [mem_filter, mem_Icc] at hi hj
          apply card_eval_eq_le hd hnd
          intro h
          have := natCast_inj_of_lt (n := n) (by omega) (by omega) h
          omega
      _ ≤ k * n ^ d := by
          rw [Finset.sum_const, smul_eq_mul]
          apply Nat.mul_le_mul_right
          calc _ ≤ (Icc 1 k).card := Finset.card_filter_le _ _
            _ = k := by simp
  have hsum : ∑ c ∈ B, k ≤ ∑ c : Fin (d + 1) → ZMod n, 2 * ((Icc 1 k).filter (coll k c)).card := by
    calc ∑ c ∈ B, k ≤ ∑ c ∈ B, 2 * ((Icc 1 k).filter (coll k c)).card := by
          apply Finset.sum_le_sum
          intro c hc
          simp only [B, mem_filter, mem_univ, true_and] at hc
          have := k_le_img_add_coll k c
          omega
      _ ≤ _ := Finset.sum_le_sum_of_subset (subset_univ _)
  have hswap : ∑ c : Fin (d + 1) → ZMod n, ((Icc 1 k).filter (coll k c)).card =
      ∑ j ∈ Icc 1 k, (univ.filter (fun c : Fin (d + 1) → ZMod n => coll k c j)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : ∑ j ∈ Icc 1 k, (univ.filter (fun c : Fin (d + 1) → ZMod n => coll k c j)).card ≤ k * (k * n ^ d) := by
    calc _ ≤ ∑ j ∈ Icc 1 k, k * n ^ d := Finset.sum_le_sum hcollj
      _ = k * (k * n ^ d) := by simp
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, hswap] at hsum
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : B = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro c hc; simp [B] at hc
    rw [this]; simp
  · have : k * B.card ≤ k * (2 * k * n ^ d) := by
      rw [mul_comm k B.card]; nlinarith
    exact Nat.le_of_mul_le_mul_left this hk

lemma card_last_zero_le :
    (univ.filter (fun c : Fin (d + 1) → ZMod n => c (Fin.last d) = 0)).card ≤ n ^ d := by
  have h1 : (univ.filter (fun c : Fin (d + 1) → ZMod n => c (Fin.last d) = 0)).card ≤
      (univ : Finset (Fin d → ZMod n)).card := by
    apply Finset.card_le_card_of_injOn (fun c => fun i : Fin d => c i.castSucc)
    · intro c _; exact mem_univ _
    · intro c hc c' hc' hcc
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc hc'
      funext i
      cases i using Fin.lastCases with
      | last => rw [hc, hc']
      | cast i => exact congrFun hcc i
  simpa [Fintype.card_fun, ZMod.card] using h1

end Poly

/-! ## The two stubs: the Spread Set Lemma (Lemma 3) and the approximation method -/

/-- Conclusion of the Spread Set Lemma: every `r`-spread random set (uniform over a finite
index set `Ω`) of size at most `m` is contained in a `γ`-random set with probability `> 1 - ε`. -/
def SpreadConclusion (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) (r γ ε : ℝ) : Prop :=
  ∀ (β : Type) (Ω : Finset β) (Z : β → Finset U), Ω.Nonempty → (∀ b ∈ Ω, (Z b).card ≤ m) →
    (∀ S : Finset U, ((Ω.filter fun b => S ⊆ Z b).card : ℝ) ≤ Ω.card * (r ^ S.card)⁻¹) →
    1 - ε < randProb U γ (fun X => ∃ b ∈ Ω, Z b ⊆ X)

/-- Lemma 3 (Spread Set Lemma, Alweiss–Lovett–Wu–Zhang / Rao / Bell–Chueluecha–Warnke). -/
def SpreadSetLemma : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ (U : Type) [Fintype U] [DecidableEq U] (t : ℕ) (r γ ε : ℝ),
    1 ≤ t → 0 < γ → γ ≤ 1 → 0 < ε → ε ≤ 1 / 2 → α * Real.log (t / ε) / γ ≤ r →
    SpreadConclusion U t r γ ε

/-- The approximation method of Section 5.1 (Algorithm 3, Lemmas 15 and 16 and the final
argument), abstracted from the polynomial distribution: a monotone circuit accepting every
`X1 b` (with `X1` `(2r)`-spread on sets of size `≤ 2t`) and accepting a uniformly random set with
probability `≤ 1/3` has more than `min{2^t, 2^{-t}/ε}/2` gates, provided the Spread Set Lemma
conclusion holds with `γ = 1/3, 1/2` for sets of size `≤ 2t`. -/
def ApproxMethod : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U] (β : Type) (Ω : Finset β) (X1 : β → Finset U)
    (t : ℕ) (r ε : ℝ) (C : MonotoneCircuit U),
    Ω.Nonempty → 1 ≤ t → 0 < r → 0 < ε → ε < 1 / 6 →
    (∀ S : Finset U, S.card ≤ 2 * t →
      ((Ω.filter fun b => S ⊆ X1 b).card : ℝ) ≤ Ω.card * ((2 * r) ^ S.card)⁻¹) →
    SpreadConclusion U (2 * t) r (1 / 3) ε → SpreadConclusion U (2 * t) r (1 / 2) ε →
    (∀ b ∈ Ω, C.eval (ind (X1 b)) = true) →
    randProb U (1 / 2) (fun X => C.eval (ind X) = true) ≤ 1 / 3 →
    min ((2 : ℝ) ^ t) (((2 : ℝ) ^ t)⁻¹ / ε) < 2 * C.size

/-! ## Arithmetic -/

lemma two_pow_eq (t : ℕ) : (2 : ℝ) ^ t = Real.exp (t * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

lemma exp_two_log_two : Real.exp (2 * Real.log 2) = 4 := by
  rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
  exact Real.exp_log (by norm_num)

lemma arith_neg {n k d : ℕ} (hn2 : 2 ≤ n) (hd : 100 ≤ d)
    (hlog : 3 * (d : ℝ) * Real.log n ≤ k) :
    (n : ℝ) ^ (d + 1) * Real.exp (-((k : ℝ) / 2) * Real.log 2) ≤ 1 / 3 := by
  have hnpos : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
                                 linarith
  rw [← Real.exp_log hnpos, ← Real.exp_nat_mul, ← Real.exp_add]
  have l2 := Real.log_two_gt_d9
  have hL : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd
  set L := Real.log (n : ℝ)
  have hL0 : 0 ≤ L := by linarith
  have h1 : 3 * (d : ℝ) * L * Real.log 2 ≤ k * Real.log 2 :=
    mul_le_mul_of_nonneg_right hlog (by linarith)
  have h2 : 3 * (d : ℝ) * L * 0.6931471803 ≤ 3 * (d : ℝ) * L * Real.log 2 :=
    mul_le_mul_of_nonneg_left l2.le (by positivity)
  have h3 : ((d + 1 : ℕ) : ℝ) * L + -((k : ℝ) / 2) * Real.log 2 ≤ -(2 * Real.log 2) := by
    push_cast
    nlinarith
  calc Real.exp (((d + 1 : ℕ) : ℝ) * L + -((k : ℝ) / 2) * Real.log 2)
      ≤ Real.exp (-(2 * Real.log 2)) := Real.exp_le_exp.mpr h3
    _ = 1 / 4 := by rw [Real.exp_neg, exp_two_log_two]; norm_num
    _ ≤ 1 / 3 := by norm_num

lemma half_pow_le {m k : ℕ} (hm : k ≤ 2 * m) :
    (1 / 2 : ℝ) ^ m ≤ Real.exp (-((k : ℝ) / 2) * Real.log 2) := by
  rw [one_div, inv_pow, two_pow_eq, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have : (k : ℝ) ≤ 2 * m := by exact_mod_cast hm
  have l2 := Real.log_two_gt_d9
  nlinarith

lemma four_pow_eps {t d : ℕ} (ht : 4 * t ≤ d) :
    (2 : ℝ) ^ t * (2 : ℝ) ^ t * Real.exp (-(d : ℝ)) ≤ 1 := by
  rw [two_pow_eq, ← Real.exp_add, ← Real.exp_add]
  rw [show (1 : ℝ) = Real.exp 0 by simp]
  apply Real.exp_le_exp.mpr
  have : (4 * t : ℝ) ≤ d := by exact_mod_cast ht
  have l2 := Real.log_two_lt_d9
  have l0 := Real.log_two_gt_d9
  have ht0 : (0 : ℝ) ≤ t := by positivity
  nlinarith

lemma exp_le_two_pow {t d : ℕ} (hd : 100 ≤ d) (ht : d < 4 * t + 4) :
    Real.exp ((d : ℝ) / 200) ≤ (2 : ℝ) ^ t / 2 := by
  have h1 : (1 : ℕ) ≤ t := by omega
  rw [show (2 : ℝ) ^ t / 2 = (2 : ℝ) ^ (t - 1) by
    rw [show t = (t - 1) + 1 by omega, pow_succ]; field_simp; simp]
  rw [two_pow_eq]
  apply Real.exp_le_exp.mpr
  have : (d : ℝ) < 4 * t + 4 := by exact_mod_cast ht
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd
  have l0 := Real.log_two_gt_d9
  rw [Nat.cast_sub h1]
  push_cast
  nlinarith

/-! ## Assembly: Theorem 9 from the two stubs -/

theorem main_case (α A : ℝ) (hαA : α ≤ A) (hA1 : 1 ≤ A)
    (h3 : ∀ (U : Type) [Fintype U] [DecidableEq U] (t : ℕ) (r γ ε : ℝ),
      1 ≤ t → 0 < γ → γ ≤ 1 → 0 < ε → ε ≤ 1 / 2 → α * Real.log (t / ε) / γ ≤ r →
      SpreadConclusion U t r γ ε)
    (hG : ApproxMethod) {n k d : ℕ} (hn : n.Prime) (hk : 1 ≤ k) (hd : 100 ≤ d)
    (hkd : 24 * A * k * d ≤ n) (hlog : 3 * (d : ℝ) * Real.log n ≤ k)
    (C : MonotoneCircuit (ZMod n))
    (hC : ∀ x : ZMod n → Bool, C.eval x = true ↔ PolyImageFun n k d x) :
    Real.exp ((d : ℝ) / 200) < C.size := by
  have : Fact n.Prime := ⟨hn⟩
  have : NeZero n := ⟨hn.ne_zero⟩
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd
  have hkdR : (k : ℝ) * d * 24 ≤ n := by
    have : (0 : ℝ) ≤ k * d := by positivity
    nlinarith
  have hkdN : k * d * 24 ≤ n := by exact_mod_cast hkdR
  have hkd1 : d ≤ k * d := Nat.le_mul_of_pos_left d hk
  have hkd2 : 100 * k ≤ k * d := by rw [mul_comm k d]; exact Nat.mul_le_mul_right k hd
  have hnd : d + 1 ≤ n := by omega
  have hkn : k < n := by omega
  have h2k : 2 + 4 * k ≤ n := by omega
  have hn2 : 2 ≤ n := hn.two_le
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  set t := d / 4 with ht
  have ht4 : 4 * t ≤ d := by omega
  have ht4' : d < 4 * t + 4 := by omega
  have ht1 : 1 ≤ t := by omega
  set r : ℝ := 6 * A * d with hr
  set ε : ℝ := Real.exp (-(d : ℝ)) with hε
  clear_value r ε
  have hrpos : 0 < r := by rw [hr]; positivity
  have hεpos : 0 < ε := by rw [hε]; exact Real.exp_pos _
  have hε6 : ε < 1 / 6 := by
    have : (7 : ℝ) ≤ Real.exp d := by
      have := Real.add_one_le_exp (d : ℝ); linarith
    rw [hε, Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  set Ω := univ.filter (fun c : Fin (d + 1) → ZMod n =>
    c (Fin.last d) ≠ 0 ∧ k ≤ 2 * (polyImage n k (poly c)).card) with hΩ
  set X1 := fun c : Fin (d + 1) → ZMod n => polyImage n k (poly c) with hX1
  -- size of Ω
  have hΩN : n ^ (d + 1) ≤ Ω.card + n ^ d + 2 * k * n ^ d := by
    have hsub : (univ : Finset (Fin (d + 1) → ZMod n)) ⊆ Ω ∪
        (univ.filter (fun c : Fin (d + 1) → ZMod n => c (Fin.last d) = 0) ∪
          univ.filter (fun c : Fin (d + 1) → ZMod n => 2 * (polyImage n k (poly c)).card < k)) := by
      intro c _
      by_cases h1 : c (Fin.last d) = 0
      · simp [h1]
      · by_cases h2 : 2 * (polyImage n k (poly c)).card < k
        · simp [h2]
        · simp only [hΩ, mem_union, mem_filter, mem_univ, true_and]
          left; exact ⟨h1, by omega⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hc
    have h1 := card_union_le Ω (univ.filter (fun c : Fin (d + 1) → ZMod n => c (Fin.last d) = 0) ∪
          univ.filter (fun c : Fin (d + 1) → ZMod n => 2 * (polyImage n k (poly c)).card < k))
    have h2 := card_union_le (univ.filter (fun c : Fin (d + 1) → ZMod n => c (Fin.last d) = 0))
          (univ.filter (fun c : Fin (d + 1) → ZMod n => 2 * (polyImage n k (poly c)).card < k))
    have h3' := card_last_zero_le (n := n) (d := d)
    have h4 := card_bad_le (n := n) (d := d) (k := k) (by omega) hnd hkn
    omega
  have hΩR : (n : ℝ) ^ (d + 1) / 2 ≤ Ω.card := by
    have : ((n ^ (d + 1) : ℕ) : ℝ) ≤ Ω.card + n ^ d + 2 * k * n ^ d := by exact_mod_cast hΩN
    push_cast at this
    have h2kR : (2 : ℝ) + 4 * k ≤ n := by exact_mod_cast h2k
    have hnd0 : (0 : ℝ) ≤ (n : ℝ) ^ d := by positivity
    rw [pow_succ] at this ⊢
    nlinarith
  have hΩne : Ω.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Ω.card := lt_of_lt_of_le (by positivity) hΩR
    exact_mod_cast this
  -- spread
  have hspread : ∀ S : Finset (ZMod n), S.card ≤ 2 * t →
      ((Ω.filter fun b => S ⊆ X1 b).card : ℝ) ≤ Ω.card * ((2 * r) ^ S.card)⁻¹ := by
    intro S hS
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0, pow_zero, inv_one, mul_one]
      exact_mod_cast Finset.card_filter_le _ _
    have hsub : Ω.filter (fun b => S ⊆ X1 b) ⊆
        univ.filter (fun c : Fin (d + 1) → ZMod n => S ⊆ polyImage n k (poly c)) := by
      intro c hc; simp only [mem_filter, mem_univ, true_and] at hc ⊢; exact hc.2
    have hcnt := (Finset.card_le_card hsub).trans
      (card_subset_img_le (k := k) hnd S (by omega))
    have hcntR : ((Ω.filter fun b => S ⊆ X1 b).card : ℝ) ≤
        (k : ℝ) ^ S.card * (n : ℝ) ^ (d + 1 - S.card) := by exact_mod_cast hcnt
    set m := S.card with hm
    have hm1 : m ≤ d + 1 := by omega
    have h2r : 0 < 2 * r := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have hrk : 2 * r * k ≤ (n : ℝ) / 2 := by
      rw [hr]; nlinarith
    have hpow : (2 * r * k) ^ m ≤ ((n : ℝ) / 2) ^ m :=
      pow_le_pow_left₀ (by positivity) hrk m
    have hsplit : (n : ℝ) ^ (d + 1) = (n : ℝ) ^ m * (n : ℝ) ^ (d + 1 - m) := by
      rw [← pow_add]; congr 1; omega
    have h2m : (2 : ℝ) ≤ 2 ^ m := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hpos
    calc ((Ω.filter fun b => S ⊆ X1 b).card : ℝ) * (2 * r) ^ m
        ≤ (k : ℝ) ^ m * (n : ℝ) ^ (d + 1 - m) * (2 * r) ^ m :=
          mul_le_mul_of_nonneg_right hcntR (by positivity)
      _ = (2 * r * k) ^ m * (n : ℝ) ^ (d + 1 - m) := by rw [mul_pow, mul_pow]; ring
      _ ≤ ((n : ℝ) / 2) ^ m * (n : ℝ) ^ (d + 1 - m) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (n : ℝ) ^ (d + 1) / 2 ^ m := by rw [hsplit, div_pow]; ring
      _ ≤ (n : ℝ) ^ (d + 1) / 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) h2m
      _ ≤ Ω.card := hΩR
  -- spread set lemma instances
  have hlogle : Real.log (((2 * t : ℕ) : ℝ) / ε) ≤ 2 * d := by
    rw [Real.log_div (by positivity) hεpos.ne', hε, Real.log_exp]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((2 * t : ℕ) : ℝ) by positivity)
    have h4 : ((2 * t : ℕ) : ℝ) ≤ d := by exact_mod_cast (by omega : 2 * t ≤ d)
    linarith
  have hlog0 : 0 ≤ Real.log (((2 * t : ℕ) : ℝ) / ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hεpos, one_mul]
    have : ε < 1 := by linarith
    have h2 : (1 : ℝ) ≤ ((2 * t : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * t)
    linarith
  have hαlog : α * Real.log (((2 * t : ℕ) : ℝ) / ε) ≤ A * (2 * d) := by
    calc α * Real.log (((2 * t : ℕ) : ℝ) / ε) ≤ A * Real.log (((2 * t : ℕ) : ℝ) / ε) :=
          mul_le_mul_of_nonneg_right hαA hlog0
      _ ≤ A * (2 * d) := mul_le_mul_of_nonneg_left hlogle (by linarith)
  have hc3 : SpreadConclusion (ZMod n) (2 * t) r (1 / 3) ε :=
    h3 (ZMod n) (2 * t) r (1 / 3) ε (by omega) (by norm_num) (by norm_num) hεpos (by linarith)
      (by rw [hr]; nlinarith)
  have hc2 : SpreadConclusion (ZMod n) (2 * t) r (1 / 2) ε :=
    h3 (ZMod n) (2 * t) r (1 / 2) ε (by omega) (by norm_num) (by norm_num) hεpos (by linarith)
      (by rw [hr]; nlinarith)
  -- positives
  have hpos : ∀ b ∈ Ω, C.eval (ind (X1 b)) = true := by
    intro b hb
    simp only [hΩ, mem_filter, mem_univ, true_and] at hb
    rw [hC]
    exact ⟨poly b, degree_poly b hb.1, hb.2, fun i hi => by simp [hX1, ind, hi]⟩
  -- negatives
  have hneg : randProb (ZMod n) (1 / 2) (fun X => C.eval (ind X) = true) ≤ 1 / 3 := by
    set G := univ.filter (fun c : Fin (d + 1) → ZMod n => k ≤ 2 * (polyImage n k (poly c)).card)
    calc randProb (ZMod n) (1 / 2) (fun X => C.eval (ind X) = true)
        ≤ randProb (ZMod n) (1 / 2) (fun X => ∃ c ∈ G, polyImage n k (poly c) ⊆ X) := by
          apply randProb_mono (by norm_num) (by norm_num)
          intro X hX
          rw [hC] at hX
          obtain ⟨w, hw, hkw, hsub⟩ := hX
          obtain ⟨c, rfl⟩ := exists_poly w hw
          refine ⟨c, by simp [G, hkw], fun i hi => ?_⟩
          have := hsub i hi
          simpa [ind] using this
      _ ≤ ∑ c ∈ G, randProb (ZMod n) (1 / 2) (fun X => polyImage n k (poly c) ⊆ X) :=
          randProb_union (by norm_num) (by norm_num) G _
      _ = ∑ c ∈ G, (1 / 2 : ℝ) ^ (polyImage n k (poly c)).card := by
          apply Finset.sum_congr rfl; intro c _; exact randProb_subset _ _
      _ ≤ ∑ c ∈ G, Real.exp (-((k : ℝ) / 2) * Real.log 2) := by
          apply Finset.sum_le_sum; intro c hc
          simp only [G, mem_filter, mem_univ, true_and] at hc
          exact half_pow_le hc
      _ ≤ (n : ℝ) ^ (d + 1) * Real.exp (-((k : ℝ) / 2) * Real.log 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have : G.card ≤ n ^ (d + 1) := by
            calc G.card ≤ (univ : Finset (Fin (d + 1) → ZMod n)).card := card_le_univ _
              _ = n ^ (d + 1) := by simp [ZMod.card]
          exact_mod_cast this
      _ ≤ 1 / 3 := arith_neg hn2 hd hlog
  have key := hG (ZMod n) (Fin (d + 1) → ZMod n) Ω X1 t r ε C hΩne ht1 hrpos hεpos hε6 hspread
    hc3 hc2 hpos hneg
  have hmin : min ((2 : ℝ) ^ t) (((2 : ℝ) ^ t)⁻¹ / ε) = (2 : ℝ) ^ t := by
    apply min_eq_left
    rw [le_div_iff₀ hεpos, ← one_div, le_div_iff₀ (by positivity)]
    have := four_pow_eps (t := t) (d := d) ht4
    rw [← hε] at this
    linarith [this]
  rw [hmin] at key
  have := exp_le_two_pow hd ht4'
  linarith

/-! ## Reducing `ApproxMethod` to a single AND-gate step -/

/-- `f_A(X) = 1`: some set of the family `A` is contained in `X`. -/
def fam {U : Type} (A : Finset (Finset U)) (X : Finset U) : Prop := ∃ S ∈ A, S ⊆ X

instance fam_decidable {U : Type} [DecidableEq U] (A : Finset (Finset U)) (X : Finset U) :
    Decidable (fam A X) := by
  unfold fam; infer_instance

/-- The AND-gate step (Algorithm 3 with Lemmas 15 and 16): from approximators `A1, A2` (sets of
size `≤ t`) one builds `A` (sets of size `≤ t`) whose new errors are small on both sides. -/
def AndStep : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U] (β : Type) (Ω : Finset β) (X1 : β → Finset U)
    (t : ℕ) (r ε : ℝ),
    1 ≤ t → 0 < r → 0 < ε →
    (∀ S : Finset U, S.card ≤ 2 * t →
      ((Ω.filter fun b => S ⊆ X1 b).card : ℝ) ≤ Ω.card * ((2 * r) ^ S.card)⁻¹) →
    SpreadConclusion U (2 * t) r (1 / 3) ε →
    ∀ A1 A2 : Finset (Finset U), (∀ S ∈ A1, S.card ≤ t) → (∀ S ∈ A2, S.card ≤ t) →
    ∃ A : Finset (Finset U), (∀ S ∈ A, S.card ≤ t) ∧
      ((Ω.filter fun b => fam A1 (X1 b) ∧ fam A2 (X1 b) ∧ ¬ fam A (X1 b)).card : ℝ) ≤
        Ω.card * ((2 : ℝ) ^ t)⁻¹ ∧
      randProb U (1 / 2) (fun X => fam A X ∧ ¬ (fam A1 X ∧ fam A2 X)) ≤ (2 : ℝ) ^ t * ε

section Approx

variable {U : Type} [DecidableEq U]

/-- The approximator of each gate, given the AND-step choice function `step`. -/
noncomputable def approx (C : MonotoneCircuit U)
    (step : Finset (Finset U) → Finset (Finset U) → Finset (Finset U)) (g : Fin C.size) :
    Finset (Finset U) :=
  match C.gate g with
  | .input i => {{i}}
  | .and a b => step (approx C step ⟨a.val, a.isLt.trans g.isLt⟩)
      (approx C step ⟨b.val, b.isLt.trans g.isLt⟩)
  | .or a b => approx C step ⟨a.val, a.isLt.trans g.isLt⟩ ∪
      approx C step ⟨b.val, b.isLt.trans g.isLt⟩
termination_by g.val
decreasing_by
  all_goals first | exact a.isLt | exact b.isLt

/-- New positive-side errors at an AND gate. -/
def New1 (C : MonotoneCircuit U) (step : Finset (Finset U) → Finset (Finset U) → Finset (Finset U))
    (g : Fin C.size) (X : Finset U) : Prop :=
  ∃ a b : Fin g.val, C.gate g = .and a b ∧
    fam (approx C step ⟨a.val, a.isLt.trans g.isLt⟩) X ∧
    fam (approx C step ⟨b.val, b.isLt.trans g.isLt⟩) X ∧ ¬ fam (approx C step g) X

/-- New negative-side errors at an AND gate. -/
def New0 (C : MonotoneCircuit U) (step : Finset (Finset U) → Finset (Finset U) → Finset (Finset U))
    (g : Fin C.size) (X : Finset U) : Prop :=
  ∃ a b : Fin g.val, C.gate g = .and a b ∧ fam (approx C step g) X ∧
    ¬ (fam (approx C step ⟨a.val, a.isLt.trans g.isLt⟩) X ∧
      fam (approx C step ⟨b.val, b.isLt.trans g.isLt⟩) X)

lemma fam_union (A B : Finset (Finset U)) (X : Finset U) :
    fam (A ∪ B) X ↔ fam A X ∨ fam B X := by
  unfold fam
  constructor
  · rintro ⟨S, hS, hSX⟩
    rcases mem_union.mp hS with h | h
    · exact Or.inl ⟨S, h, hSX⟩
    · exact Or.inr ⟨S, h, hSX⟩
  · rintro (⟨S, hS, hSX⟩ | ⟨S, hS, hSX⟩)
    · exact ⟨S, mem_union_left _ hS, hSX⟩
    · exact ⟨S, mem_union_right _ hS, hSX⟩

lemma approx_spec (C : MonotoneCircuit U) (t : ℕ) (ht : 1 ≤ t)
    (step : Finset (Finset U) → Finset (Finset U) → Finset (Finset U))
    (hstep : ∀ A1 A2 : Finset (Finset U), (∀ S ∈ A1, S.card ≤ t) → (∀ S ∈ A2, S.card ≤ t) →
      ∀ S ∈ step A1 A2, S.card ≤ t) :
    ∀ (m : ℕ) (g : Fin C.size), g.val = m →
      (∀ S ∈ approx C step g, S.card ≤ t) ∧
      (∀ X, C.nodeValue (ind X) g = true → ¬ fam (approx C step g) X →
        ∃ g' : Fin C.size, g'.val ≤ g.val ∧ New1 C step g' X) ∧
      (∀ X, C.nodeValue (ind X) g = false → fam (approx C step g) X →
        ∃ g' : Fin C.size, g'.val ≤ g.val ∧ New0 C step g' X) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro g hgm
  cases hg : C.gate g with
  | input i =>
    have hA : approx C step g = {{i}} := by rw [approx]; simp only [hg]
    have hV : ∀ X, C.nodeValue (ind X) g = decide (i ∈ X) := by
      intro X; rw [MonotoneCircuit.nodeValue]; simp only [hg]; rfl
    have hfam : ∀ X, fam (approx C step g) X ↔ i ∈ X := by
      intro X; rw [hA]; simp [fam]
    refine ⟨?_, ?_, ?_⟩
    · rw [hA]; intro S hS; rw [mem_singleton] at hS; subst hS; simpa using ht
    · intro X hX hf; rw [hV] at hX; exact absurd ((hfam X).mpr (by simpa using hX)) hf
    · intro X hX hf; rw [hV] at hX; have := (hfam X).mp hf; simp [this] at hX
  | and a b =>
    set ga : Fin C.size := ⟨a.val, a.isLt.trans g.isLt⟩ with hga
    set gb : Fin C.size := ⟨b.val, b.isLt.trans g.isLt⟩ with hgb
    have iha := ih a.val (by omega) ga rfl
    have ihb := ih b.val (by omega) gb rfl
    have hA : approx C step g = step (approx C step ga) (approx C step gb) := by
      rw [approx]; simp only [hg]; rfl
    have hV : ∀ X, C.nodeValue (ind X) g =
        (C.nodeValue (ind X) ga && C.nodeValue (ind X) gb) := by
      intro X; rw [MonotoneCircuit.nodeValue]; simp only [hg]; rfl
    have hle_a : ga.val ≤ g.val := Nat.le_of_lt a.isLt
    have hle_b : gb.val ≤ g.val := Nat.le_of_lt b.isLt
    refine ⟨?_, ?_, ?_⟩
    · rw [hA]; exact hstep _ _ iha.1 ihb.1
    · intro X hX hf
      rw [hV, Bool.and_eq_true] at hX
      by_cases h1 : fam (approx C step ga) X
      · by_cases h2 : fam (approx C step gb) X
        · exact ⟨g, le_rfl, a, b, hg, h1, h2, hf⟩
        · obtain ⟨g', hg', hN⟩ := ihb.2.1 X hX.2 h2
          exact ⟨g', hg'.trans hle_b, hN⟩
      · obtain ⟨g', hg', hN⟩ := iha.2.1 X hX.1 h1
        exact ⟨g', hg'.trans hle_a, hN⟩
    · intro X hX hf
      rw [hV, Bool.and_eq_false_iff] at hX
      by_cases h12 : fam (approx C step ga) X ∧ fam (approx C step gb) X
      · rcases hX with hX | hX
        · obtain ⟨g', hg', hN⟩ := iha.2.2 X hX h12.1
          exact ⟨g', hg'.trans hle_a, hN⟩
        · obtain ⟨g', hg', hN⟩ := ihb.2.2 X hX h12.2
          exact ⟨g', hg'.trans hle_b, hN⟩
      · exact ⟨g, le_rfl, a, b, hg, hf, h12⟩
  | or a b =>
    set ga : Fin C.size := ⟨a.val, a.isLt.trans g.isLt⟩ with hga
    set gb : Fin C.size := ⟨b.val, b.isLt.trans g.isLt⟩ with hgb
    have iha := ih a.val (by omega) ga rfl
    have ihb := ih b.val (by omega) gb rfl
    have hA : approx C step g = approx C step ga ∪ approx C step gb := by
      rw [approx]; simp only [hg]; rfl
    have hV : ∀ X, C.nodeValue (ind X) g =
        (C.nodeValue (ind X) ga || C.nodeValue (ind X) gb) := by
      intro X; rw [MonotoneCircuit.nodeValue]; simp only [hg]; rfl
    have hle_a : ga.val ≤ g.val := Nat.le_of_lt a.isLt
    have hle_b : gb.val ≤ g.val := Nat.le_of_lt b.isLt
    refine ⟨?_, ?_, ?_⟩
    · rw [hA]; intro S hS
      rcases mem_union.mp hS with h | h
      · exact iha.1 S h
      · exact ihb.1 S h
    · intro X hX hf
      rw [hA, fam_union, not_or] at hf
      rw [hV, Bool.or_eq_true] at hX
      rcases hX with hX | hX
      · obtain ⟨g', hg', hN⟩ := iha.2.1 X hX hf.1
        exact ⟨g', hg'.trans hle_a, hN⟩
      · obtain ⟨g', hg', hN⟩ := ihb.2.1 X hX hf.2
        exact ⟨g', hg'.trans hle_b, hN⟩
    · intro X hX hf
      rw [hA, fam_union] at hf
      rw [hV, Bool.or_eq_false_iff] at hX
      rcases hf with hf | hf
      · obtain ⟨g', hg', hN⟩ := iha.2.2 X hX.1 hf
        exact ⟨g', hg'.trans hle_a, hN⟩
      · obtain ⟨g', hg', hN⟩ := ihb.2.2 X hX.2 hf
        exact ⟨g', hg'.trans hle_b, hN⟩

end Approx

lemma randProb_or {U : Type} [Fintype U] {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (P Q : Finset U → Prop) :
    randProb U γ (fun X => P X ∨ Q X) ≤ randProb U γ P + randProb U γ Q := by
  classical
  rw [randProb_eq, randProb_eq, randProb_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro X _
  have := w_nonneg h0 h1 X
  by_cases hP : P X
  · rw [if_pos (Or.inl hP), if_pos hP]; split_ifs <;> linarith
  · by_cases hQ : Q X
    · rw [if_pos (Or.inr hQ), if_pos hQ]; split_ifs <;> linarith
    · rw [if_neg (by tauto)]; split_ifs <;> linarith

theorem approxMethod_of_andStep (hA : AndStep) : ApproxMethod := by
  intro U _ _ β Ω X1 t r ε C hΩ ht hr hε hε6 hspread hc3 hc2 hpos hneg
  classical
  by_contra hcon
  rw [not_lt, le_min_iff] at hcon
  obtain ⟨hN1, hN0⟩ := hcon
  have hex : ∀ A1 A2 : Finset (Finset U), ∃ A : Finset (Finset U),
      (∀ S ∈ A1, S.card ≤ t) → (∀ S ∈ A2, S.card ≤ t) →
      (∀ S ∈ A, S.card ≤ t) ∧
      ((Ω.filter fun b => fam A1 (X1 b) ∧ fam A2 (X1 b) ∧ ¬ fam A (X1 b)).card : ℝ) ≤
        Ω.card * ((2 : ℝ) ^ t)⁻¹ ∧
      randProb U (1 / 2) (fun X => fam A X ∧ ¬ (fam A1 X ∧ fam A2 X)) ≤ (2 : ℝ) ^ t * ε := by
    intro A1 A2
    by_cases h : (∀ S ∈ A1, S.card ≤ t) ∧ (∀ S ∈ A2, S.card ≤ t)
    · obtain ⟨A, hA'⟩ := hA U β Ω X1 t r ε ht hr hε hspread hc3 A1 A2 h.1 h.2
      exact ⟨A, fun _ _ => hA'⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose step hstep using hex
  have spec := approx_spec C t ht step (fun A1 A2 h1 h2 => (hstep A1 A2 h1 h2).1)
  set N := C.size
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  -- new errors, positive side
  have hNew1 : ∀ g : Fin C.size,
      ((Ω.filter fun b => New1 C step g (X1 b)).card : ℝ) ≤ Ω.card * ((2 : ℝ) ^ t)⁻¹ := by
    intro g
    by_cases hg : ∃ a b : Fin g.val, C.gate g = .and a b
    · obtain ⟨a, b, hab⟩ := hg
      set ga : Fin C.size := ⟨a.val, a.isLt.trans g.isLt⟩
      set gb : Fin C.size := ⟨b.val, b.isLt.trans g.isLt⟩
      have hAg : approx C step g = step (approx C step ga) (approx C step gb) := by
        rw [approx]; simp only [hab]; rfl
      have hsz := fun g' => (spec g'.val g' rfl).1
      have hb := (hstep (approx C step ga) (approx C step gb) (hsz ga) (hsz gb)).2.1
      rw [← hAg] at hb
      refine le_trans ?_ hb
      exact_mod_cast Finset.card_le_card (fun x hx => by
        simp only [mem_filter] at hx ⊢
        obtain ⟨hxΩ, a', b', hab', h1, h2, h3⟩ := hx
        rw [hab] at hab'
        injection hab' with e1 e2
        subst e1; subst e2
        exact ⟨hxΩ, h1, h2, h3⟩)
    · have : Ω.filter (fun b => New1 C step g (X1 b)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        simp only [mem_filter] at hx
        obtain ⟨_, a', b', hab', _⟩ := hx
        exact hg ⟨a', b', hab'⟩
      rw [this]; simp only [card_empty, Nat.cast_zero]; positivity
  have hNew0 : ∀ g : Fin C.size,
      randProb U (1 / 2) (fun X => New0 C step g X) ≤ (2 : ℝ) ^ t * ε := by
    intro g
    by_cases hg : ∃ a b : Fin g.val, C.gate g = .and a b
    · obtain ⟨a, b, hab⟩ := hg
      set ga : Fin C.size := ⟨a.val, a.isLt.trans g.isLt⟩
      set gb : Fin C.size := ⟨b.val, b.isLt.trans g.isLt⟩
      have hAg : approx C step g = step (approx C step ga) (approx C step gb) := by
        rw [approx]; simp only [hab]; rfl
      have hsz := fun g' => (spec g'.val g' rfl).1
      have hb := (hstep (approx C step ga) (approx C step gb) (hsz ga) (hsz gb)).2.2
      rw [← hAg] at hb
      refine le_trans (randProb_mono (by norm_num) (by norm_num) ?_) hb
      intro X hX
      obtain ⟨a', b', hab', h1, h2⟩ := hX
      rw [hab] at hab'
      injection hab' with e1 e2
      subst e1; subst e2
      exact ⟨h1, h2⟩
    · calc randProb U (1 / 2) (fun X => New0 C step g X) ≤ randProb U (1 / 2) (fun _ => False) :=
            randProb_mono (by norm_num) (by norm_num) (fun X hX => by
              obtain ⟨a', b', hab', _⟩ := hX; exact hg ⟨a', b', hab'⟩)
        _ = 0 := by simp [randProb]
        _ ≤ _ := by positivity
  -- union bounds
  set B1 := Ω.filter (fun b => ∃ g : Fin C.size, New1 C step g (X1 b)) with hB1
  have hB1card : (B1.card : ℝ) ≤ Ω.card / 2 := by
    have hsub : B1 ⊆ (univ : Finset (Fin C.size)).biUnion
        (fun g => Ω.filter fun b => New1 C step g (X1 b)) := by
      intro x hx
      simp only [hB1, mem_filter] at hx
      obtain ⟨hxΩ, g, hg⟩ := hx
      exact mem_biUnion.mpr ⟨g, mem_univ _, mem_filter.mpr ⟨hxΩ, hg⟩⟩
    have h1 : (B1.card : ℝ) ≤ ∑ g : Fin C.size,
        ((Ω.filter fun b => New1 C step g (X1 b)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∑ g : Fin C.size, ((Ω.filter fun b => New1 C step g (X1 b)).card : ℝ) ≤
        N * (Ω.card * ((2 : ℝ) ^ t)⁻¹) := by
      calc _ ≤ ∑ _g : Fin C.size, (Ω.card * ((2 : ℝ) ^ t)⁻¹) := Finset.sum_le_sum (fun g _ => hNew1 g)
        _ = _ := by simp [N]
    have h3 : (N : ℝ) * (Ω.card * ((2 : ℝ) ^ t)⁻¹) ≤ Ω.card / 2 := by
      rw [← mul_assoc, mul_comm (N : ℝ), mul_assoc, ← div_eq_mul_inv]
      rw [show (Ω.card : ℝ) / 2 = Ω.card * (1 / 2) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_iff₀ h2t]; linarith
    linarith
  have hB0 : randProb U (1 / 2) (fun X => ∃ g ∈ (univ : Finset (Fin C.size)), New0 C step g X)
      ≤ 1 / 2 := by
    calc _ ≤ ∑ g : Fin C.size, randProb U (1 / 2) (fun X => New0 C step g X) :=
          randProb_union (by norm_num) (by norm_num) _ _
      _ ≤ ∑ _g : Fin C.size, (2 : ℝ) ^ t * ε := Finset.sum_le_sum (fun g _ => hNew0 g)
      _ = N * ((2 : ℝ) ^ t * ε) := by simp [N]
      _ ≤ 1 / 2 := by
          rw [le_div_iff₀ hε] at hN0
          have := mul_le_mul_of_nonneg_left hN0 h2t.le
          rw [mul_inv_cancel₀ h2t.ne'] at this
          nlinarith
  -- the good positive inputs
  set Ω' := Ω.filter (fun b => ¬ ∃ g : Fin C.size, New1 C step g (X1 b)) with hΩ'
  have hΩ'card : (Ω.card : ℝ) / 2 ≤ Ω'.card := by
    have := Finset.card_filter_add_card_filter_not (s := Ω)
      (fun b => ∃ g : Fin C.size, New1 C step g (X1 b))
    have : (B1.card : ℝ) + Ω'.card = Ω.card := by exact_mod_cast this
    linarith
  have hΩpos : (0 : ℝ) < Ω.card := by exact_mod_cast Finset.card_pos.mpr hΩ
  have hΩ'ne : Ω'.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Ω'.card := by linarith
    exact_mod_cast this
  set out := C.output
  have hfam_out : ∀ b ∈ Ω', fam (approx C step out) (X1 b) := by
    intro b hb
    simp only [hΩ', mem_filter] at hb
    by_contra hf
    obtain ⟨g', _, hN⟩ := (spec out.val out rfl).2.1 (X1 b) (hpos b hb.1) hf
    exact hb.2 ⟨g', hN⟩
  let Z : β → Finset U := fun b =>
    if h : fam (approx C step out) (X1 b) then Classical.choose h else ∅
  have hZ : ∀ b ∈ Ω', Z b ∈ approx C step out ∧ Z b ⊆ X1 b := by
    intro b hb
    have h := hfam_out b hb
    simp only [Z, dif_pos h]
    exact Classical.choose_spec h
  have hsz_out := (spec out.val out rfl).1
  have hZspread : ∀ S : Finset U,
      ((Ω'.filter fun b => S ⊆ Z b).card : ℝ) ≤ Ω'.card * (r ^ S.card)⁻¹ := by
    intro S
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos'
    · rw [h0, pow_zero, inv_one, mul_one]
      exact_mod_cast Finset.card_filter_le _ _
    by_cases hSt : S.card ≤ t
    · have hsub : Ω'.filter (fun b => S ⊆ Z b) ⊆ Ω.filter (fun b => S ⊆ X1 b) := by
        intro b hb
        simp only [mem_filter] at hb ⊢
        exact ⟨(mem_filter.mp hb.1).1, hb.2.trans (hZ b hb.1).2⟩
      have h1 : ((Ω'.filter fun b => S ⊆ Z b).card : ℝ) ≤ Ω.card * ((2 * r) ^ S.card)⁻¹ :=
        le_trans (by exact_mod_cast Finset.card_le_card hsub) (hspread S (by omega))
      have h2m : (2 : ℝ) ≤ 2 ^ S.card := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ S.card := pow_le_pow_right₀ (by norm_num) hpos'
      have hrS : 0 < r ^ S.card := by positivity
      refine le_trans h1 ?_
      rw [mul_pow, mul_inv]
      have : (Ω.card : ℝ) * ((2 : ℝ) ^ S.card)⁻¹ ≤ Ω'.card := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        nlinarith
      calc (Ω.card : ℝ) * (((2 : ℝ) ^ S.card)⁻¹ * (r ^ S.card)⁻¹)
          = (Ω.card : ℝ) * ((2 : ℝ) ^ S.card)⁻¹ * (r ^ S.card)⁻¹ := by ring
        _ ≤ Ω'.card * (r ^ S.card)⁻¹ :=
          mul_le_mul_of_nonneg_right this (by positivity)
    · have : Ω'.filter (fun b => S ⊆ Z b) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro b hb
        simp only [mem_filter] at hb
        have := Finset.card_le_card hb.2
        have := hsz_out _ (hZ b hb.1).1
        omega
      rw [this]; simp only [card_empty, Nat.cast_zero]; positivity
  have hcover := hc2 β Ω' Z hΩ'ne
    (fun b hb => (hsz_out _ (hZ b hb).1).trans (by omega)) hZspread
  have hcov2 : randProb U (1 / 2) (fun X => ∃ b ∈ Ω', Z b ⊆ X) ≤
      randProb U (1 / 2) (fun X => C.eval (ind X) = true ∨
        ∃ g ∈ (univ : Finset (Fin C.size)), New0 C step g X) := by
    apply randProb_mono (by norm_num) (by norm_num)
    rintro X ⟨b, hb, hZX⟩
    have hf : fam (approx C step out) X := ⟨Z b, (hZ b hb).1, hZX⟩
    by_cases hev : C.eval (ind X) = true
    · exact Or.inl hev
    · right
      have hv : C.nodeValue (ind X) out = false := by
        simpa [MonotoneCircuit.eval, out] using hev
      obtain ⟨g', _, hN⟩ := (spec out.val out rfl).2.2 X hv hf
      exact ⟨g', mem_univ _, hN⟩
  have hor := randProb_or (U := U) (γ := 1 / 2) (by norm_num) (by norm_num)
    (fun X => C.eval (ind X) = true)
    (fun X => ∃ g ∈ (univ : Finset (Fin C.size)), New0 C step g X)
  linarith

lemma exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

end SpreadMatchCircuit.Matching.Dev.Thm9

namespace SpreadMatchCircuit.Matching.Supplement

open SpreadMatchCircuit.Matching.Dev.Thm9

/-- Theorem 9, conditional on the two stubs `SpreadSetLemma` (Lemma 3) and `ApproxMethod`
(the approximation method of Section 5.1). -/
theorem chk_theorem_9_of_stubs (h3 : SpreadSetLemma) (hG : ApproxMethod) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ (n k d : ℕ), n.Prime → 1 ≤ k →
        (k : ℝ) * (d : ℝ) ≤ η * (n : ℝ) → 3 * (d : ℝ) * Real.log (n : ℝ) ≤ (k : ℝ) →
        ∀ C : MonotoneCircuit (ZMod n), (∀ x : ZMod n → Bool, C.eval x = true ↔ PolyImageFun n k d x) →
          Real.exp (c * min (d : ℝ) ((n : ℝ) / (k : ℝ))) ≤ (C.size : ℝ) := by
  obtain ⟨α, _, h3⟩ := h3
  set A := max α 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  have hαA : α ≤ A := le_max_left _ _
  refine ⟨1 / (24 * A), 1 / 200, by positivity, by norm_num, ?_⟩
  intro n k d hn hk hkd hlog C hC
  have hsize1 : (1 : ℝ) ≤ C.size := by
    have : 1 ≤ C.size := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) C.output.isLt)
    exact_mod_cast this
  have hnk : (0 : ℝ) ≤ (n : ℝ) / k := by positivity
  have hle : Real.exp (1 / 200 * min (d : ℝ) ((n : ℝ) / k)) ≤ Real.exp ((d : ℝ) / 200) := by
    apply Real.exp_le_exp.mpr
    have := min_le_left (d : ℝ) ((n : ℝ) / k)
    linarith
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · subst hd0
    have : min ((0 : ℕ) : ℝ) ((n : ℝ) / k) = 0 := by simp [hnk]
    rw [this]; simpa using hsize1
  by_cases hd : d < 100
  · have h2 := size_ge_two hn hd1 hlog C hC
    have h2R : (2 : ℝ) ≤ C.size := by exact_mod_cast h2
    have : Real.exp ((d : ℝ) / 200) ≤ Real.exp (1 / 2) := by
      apply Real.exp_le_exp.mpr
      have : (d : ℝ) ≤ 100 := by exact_mod_cast hd.le
      linarith
    linarith [exp_half_lt_two]
  · push Not at hd
    have hkd' : 24 * A * k * d ≤ n := by
      have h24 : 0 < 24 * A := by positivity
      have := mul_le_mul_of_nonneg_left hkd h24.le
      have e : 24 * A * (1 / (24 * A) * n) = n := by field_simp
      linarith
    have := main_case α A hαA hA1 h3 hG hn hk hd hkd' hlog C hC
    linarith

/-- Theorem 9, conditional on the Spread Set Lemma (Lemma 3) and the AND-gate step `AndStep`
(Algorithm 3 with Lemmas 15 and 16). -/
theorem chk_theorem_9_of_andStep (h3 : SpreadSetLemma) (hA : AndStep) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ (n k d : ℕ), n.Prime → 1 ≤ k →
        (k : ℝ) * (d : ℝ) ≤ η * (n : ℝ) → 3 * (d : ℝ) * Real.log (n : ℝ) ≤ (k : ℝ) →
        ∀ C : MonotoneCircuit (ZMod n), (∀ x : ZMod n → Bool, C.eval x = true ↔ PolyImageFun n k d x) →
          Real.exp (c * min (d : ℝ) ((n : ℝ) / (k : ℝ))) ≤ (C.size : ℝ) :=
  chk_theorem_9_of_stubs h3 (approxMethod_of_andStep hA)

end SpreadMatchCircuit.Matching.Supplement
end

section
/-!
# Theorem 9 (exponential lower bound for `F_{k,d}`), unconditionally

`Thm9.lean` proves Theorem 9 from two stubs, `SpreadSetLemma` and `AndStep`. Here:

* `spreadSetLemma_holds` derives `SpreadSetLemma` from `Dev.SpreadSet.spread_set` (Lemma 3,
  law version), by transporting the uniform law on `Ω` pushed by `Z` to `Fin (card U)`;
* `andStep_holds` proves `AndStep` (Algorithm 3 with Lemmas 15 and 16).
-/

namespace SpreadMatchCircuit.Matching.Dev.Thm9Full

open Finset SpreadMatchCircuit.Matching SpreadMatchCircuit.Matching.Supplement
open SpreadMatchCircuit.Matching.Dev.Thm9

/-! ## Part 1: the Spread Set Lemma in the `Ω`-indexed form -/

section Bridge

variable {U : Type} [Fintype U] [DecidableEq U] {β : Type}

/-- The pushed set `Z b`, transported to `Fin (card U)`. -/
noncomputable def img (Z : β → Finset U) (b : β) : Finset (Fin (Fintype.card U)) :=
  (Z b).map (Fintype.equivFin U).toEmbedding

lemma sum_fibres (Ω : Finset β) (Z : β → Finset U) :
    ∑ z : Finset (Fin (Fintype.card U)), (Ω.filter fun b => img Z b = z).card = Ω.card :=
  (Finset.card_eq_sum_card_fiberwise (fun b _ => mem_univ (img Z b))).symm

/-- The uniform law on `Ω`, pushed by `img Z`. -/
noncomputable def lawOf (Ω : Finset β) (hΩ : Ω.Nonempty) (Z : β → Finset U) :
    PMF (Finset (Fin (Fintype.card U))) :=
  PMF.ofFintype (fun z => ((Ω.filter fun b => img Z b = z).card : ENNReal) / Ω.card) (by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    have : ∑ z : Finset (Fin (Fintype.card U)), (((Ω.filter fun b => img Z b = z).card : ℕ) :
        ENNReal) = ((Ω.card : ℕ) : ENNReal) := by
      rw [← Nat.cast_sum, sum_fibres]
    rw [this]
    exact ENNReal.mul_inv_cancel (by simpa using hΩ.ne_empty) (ENNReal.natCast_ne_top _))

lemma lawOf_toReal (Ω : Finset β) (hΩ : Ω.Nonempty) (Z : β → Finset U) (z) :
    (lawOf Ω hΩ Z z).toReal = ((Ω.filter fun b => img Z b = z).card : ℝ) / Ω.card := by
  rw [lawOf, PMF.ofFintype_apply, ENNReal.toReal_div]
  simp

open scoped Classical in
lemma lawProb_lawOf (Ω : Finset β) (hΩ : Ω.Nonempty) (Z : β → Finset U)
    (A : Finset (Fin (Fintype.card U)) → Prop) :
    lawProb (lawOf Ω hΩ Z) A = ((Ω.filter fun b => A (img Z b)).card : ℝ) / Ω.card := by
  classical
  unfold lawProb
  rw [Finset.sum_congr rfl (fun z _ => lawOf_toReal Ω hΩ Z z), ← Finset.sum_div]
  congr 1
  have h := Finset.card_eq_sum_card_fiberwise (s := Ω.filter fun b => A (img Z b))
    (t := univ.filter A) (f := img Z) (fun b hb => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hb).2⟩)
  rw [h]
  push_cast
  apply Finset.sum_congr (by ext; simp)
  intro z hz
  simp only [mem_filter, mem_univ, true_and] at hz
  congr 2
  ext b
  simp only [mem_filter]
  constructor
  · intro h; exact ⟨⟨h.1, h.2 ▸ hz⟩, h.2⟩
  · intro h; exact ⟨h.1.1, h.2⟩

lemma lawSupport_lawOf (Ω : Finset β) (hΩ : Ω.Nonempty) (Z : β → Finset U) :
    ∀ z, z ∈ lawSupport (lawOf Ω hΩ Z) ↔ ∃ b ∈ Ω, img Z b = z := by
  intro z
  classical
  unfold lawSupport
  simp only [Finset.mem_filter, mem_univ, true_and, PMF.mem_support_iff]
  rw [lawOf, PMF.ofFintype_apply]
  simp only [ne_eq, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero, card_eq_zero,
    ENNReal.natCast_ne_top, or_false]
  rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨b, hb⟩; simp only [mem_filter] at hb; exact ⟨b, hb.1, hb.2⟩
  · rintro ⟨b, hb, he⟩; exact ⟨b, mem_filter.mpr ⟨hb, he⟩⟩

lemma subset_img_iff (Z : β → Finset U) (b : β) (S : Finset (Fin (Fintype.card U))) :
    S ⊆ img Z b ↔ S.map (Fintype.equivFin U).symm.toEmbedding ⊆ Z b := by
  unfold img
  constructor
  · intro h x hx
    simp only [mem_map_equiv, Equiv.symm_symm] at hx
    have := h hx
    simpa using this
  · intro h x hx
    have : (Fintype.equivFin U).symm x ∈ Z b := h (by simpa using hx)
    simpa using this

end Bridge

theorem spreadSetLemma_holds : SpreadSetLemma := by
  obtain ⟨α, hα, H⟩ := SpreadSet.spread_set
  refine ⟨α, hα, ?_⟩
  intro U _ _ t r γ ε ht hγ0 hγ1 hε0 hε hr β Ω Z hΩ hsz hsp
  classical
  set n := Fintype.card U
  set e := Fintype.equivFin U
  set μ := lawOf Ω hΩ Z
  set r0 := α * Real.log (t / ε) / γ with hr0
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog : 0 < Real.log (t / ε) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hε0]; linarith
  have hr0pos : 0 < r0 := by positivity
  have hΩpos : (0 : ℝ) < Ω.card := by exact_mod_cast hΩ.card_pos
  have hspμ : IsSetSpread μ r0 := by
    intro A
    rw [lawProb_lawOf, div_le_iff₀ hΩpos]
    have h1 := hsp (A.map e.symm.toEmbedding)
    rw [card_map] at h1
    calc _ = ((Ω.filter fun b => A.map e.symm.toEmbedding ⊆ Z b).card : ℝ) := by
          congr 2; ext b; simp only [mem_filter, subset_img_iff]; rfl
      _ ≤ _ := h1
      _ ≤ _ := ?_
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hΩpos.le
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hr0pos.le hr _)
  have hbd : IsBoundedSetLaw μ (t : ℝ) := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := (lawSupport_lawOf Ω hΩ Z z).mp hz
    rw [img, card_map]; exact_mod_cast hsz b hb
  have key := H n μ ε t γ r0 hε0 hε (by linarith) hγ0 hγ1 rfl hspμ hbd
  refine key.trans_le (le_of_eq ?_)
  unfold randProb
  apply Finset.sum_nbij' (fun W => W.map e.symm.toEmbedding) (fun X => X.map e.toEmbedding)
  · intro W hW
    simp only [mem_filter, mem_univ, true_and] at hW ⊢
    obtain ⟨z, hz, hzW⟩ := hW
    obtain ⟨b, hb, rfl⟩ := (lawSupport_lawOf Ω hΩ Z z).mp hz
    refine ⟨b, hb, ?_⟩
    intro x hx
    have : e x ∈ img Z b := by simp [img, e, hx]
    have := hzW this
    simpa [e] using this
  · intro X hX
    simp only [mem_filter, mem_univ, true_and] at hX ⊢
    obtain ⟨b, hb, hbX⟩ := hX
    exact ⟨img Z b, (lawSupport_lawOf Ω hΩ Z _).mpr ⟨b, hb, rfl⟩, by
      unfold img; exact Finset.map_subset_map.mpr hbX⟩
  · intro W _; ext x; simp [e]
  · intro X _; ext x; simp [e]
  · intro W _; simp [n]

/-! ## Part 2: the AND-gate step (Algorithm 3, Lemmas 15 and 16) -/

section Weights

variable {U : Type} [Fintype U] [DecidableEq U]

open SpreadMatchCircuit.Matching.Dev.SpreadSet in
lemma randProb_eq_wt (γ : ℝ) (Q : Finset U → Prop) [DecidablePred Q] :
    randProb U γ Q = ∑ X : Finset U, wt γ X * (if Q X then 1 else 0) := by
  rw [randProb_eq]
  apply sum_congr rfl
  intro X _
  split_ifs <;> simp [wt]

open SpreadMatchCircuit.Matching.Dev.SpreadSet in
lemma sum_wt_compl (γ : ℝ) (Q : Finset U → Prop) [DecidablePred Q] :
    randProb U γ Q + ∑ X : Finset U, wt γ X * (if Q X then 0 else 1) = 1 := by
  rw [randProb_eq_wt, ← sum_add_distrib]
  refine (sum_congr rfl (fun X _ => ?_)).trans (sum_wt (β := U) γ)
  split_ifs <;> ring

open SpreadMatchCircuit.Matching.Dev.SpreadSet in
lemma wt_half (X : Finset U) : wt (1 / 2) X = (1 / 2 : ℝ) ^ Fintype.card U := by
  unfold wt
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← pow_add]
  congr 1
  have := card_le_univ X
  omega

open SpreadMatchCircuit.Matching.Dev.SpreadSet in
/-- A `1/4`-random set `G` and an independent `1/3`-random set `V`: `G ∪ V` is `1/2`-random and,
given `G ∪ V = W`, the set `G` is a uniformly random subset of `W`. -/
lemma sum_union2 (h : Finset U → Finset U → ℝ) :
    ∑ G : Finset U, wt (1 / 4) G * ∑ V : Finset U, wt (1 / 3) V * h G (G ∪ V) =
      ∑ W : Finset U, ∑ G ∈ W.powerset,
        (1 / 2 : ℝ) ^ Fintype.card U * (1 / 2 : ℝ) ^ W.card * h G W := by
  have step1 : ∀ G : Finset U, ∑ V : Finset U, wt (1 / 3) V * h G (G ∪ V) =
      ∑ W ∈ univ.filter (fun W => G ⊆ W),
        (1 / 3 : ℝ) ^ (W.card - G.card) * (1 - 1 / 3) ^ (Fintype.card U - W.card) * h G W := by
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
    rw [sum_congr rfl (fun V' hV' => by rw [hU V' hV']), ← sum_mul, sum_wt_fibre _ hW.2]
  simp_rw [step1, mul_sum]
  rw [sum_comm' (t' := univ) (s' := fun W => W.powerset)]
  · apply sum_congr rfl; intro W _
    apply sum_congr rfl; intro G hG
    rw [mem_powerset] at hG
    have hGc := card_le_card hG
    have hW := card_le_univ W
    obtain ⟨q, hq⟩ : ∃ q, W.card = G.card + q := ⟨W.card - G.card, by omega⟩
    obtain ⟨p, hp⟩ : ∃ p, Fintype.card U = W.card + p := ⟨Fintype.card U - W.card, by omega⟩
    unfold wt
    rw [hp, hq, show G.card + q + p - G.card = q + p by omega,
      show G.card + q - G.card = q by omega, show G.card + q + p - (G.card + q) = p by omega,
      show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num]
    have k1 : ∀ x : ℕ, (1 / 4 : ℝ) ^ x = (1 / 2) ^ x * (1 / 2) ^ x := fun x => by
      rw [← mul_pow]; norm_num
    have k2 : ∀ x : ℕ, (3 / 4 : ℝ) ^ x * (1 / 3) ^ x = (1 / 2) ^ x * (1 / 2) ^ x := fun x => by
      rw [← mul_pow, ← mul_pow]; norm_num
    have k3 : ∀ x : ℕ, (3 / 4 : ℝ) ^ x * (2 / 3) ^ x = (1 / 2) ^ x := fun x => by
      rw [← mul_pow]; norm_num
    calc (1 / 4 : ℝ) ^ G.card * (3 / 4) ^ (q + p) * ((1 / 3) ^ q * (2 / 3) ^ p * h G W)
        = (1 / 4 : ℝ) ^ G.card * ((3 / 4) ^ q * (1 / 3) ^ q) * ((3 / 4) ^ p * (2 / 3) ^ p) *
            h G W := by ring
      _ = _ := by rw [k1, k2, k3]; ring
  · intro G W
    simp [mem_filter, mem_powerset]

end Weights

section Step

variable {U : Type} [Fintype U] [DecidableEq U] {β : Type}

/-- The new positive-side errors for the current family `A`. -/
def Nset (Ω : Finset β) (X1 : β → Finset U) (A1 A2 A : Finset (Finset U)) : Finset β :=
  Ω.filter fun b => fam A1 (X1 b) ∧ fam A2 (X1 b) ∧ ¬ fam A (X1 b)

/-- `S` was chosen by Algorithm 3: conditioned on `S ⊆ Z` (and on the new errors at that time),
`Z \ S` is `r`-spread. -/
def GoodSet (A1 A2 : Finset (Finset U)) (Z0 : β → Finset U) (t : ℕ) (r : ℝ) (S : Finset U) :
    Prop :=
  ∃ Ω' : Finset β, Ω'.Nonempty ∧
    (∀ b ∈ Ω', S ⊆ Z0 b ∧ (Z0 b).card ≤ 2 * t ∧ ∀ Y, Z0 b ⊆ Y → fam A1 Y ∧ fam A2 Y) ∧
    ∀ S' : Finset U, ((Ω'.filter fun b => S' ⊆ Z0 b \ S).card : ℝ) ≤ Ω'.card * (r ^ S'.card)⁻¹

lemma mem_Nset {Ω : Finset β} {X1 : β → Finset U} {A1 A2 A : Finset (Finset U)} {b : β} :
    b ∈ Nset Ω X1 A1 A2 A ↔ b ∈ Ω ∧ fam A1 (X1 b) ∧ fam A2 (X1 b) ∧ ¬ fam A (X1 b) := by
  unfold Nset; rw [mem_filter]

/-- Algorithm 3 (the while loop), with Lemma 15 at termination. -/
lemma loop (Ω : Finset β) (X1 : β → Finset U) (A1 A2 : Finset (Finset U)) (Z0 : β → Finset U)
    (t : ℕ) (r : ℝ) (hr : 0 < r)
    (hspread : ∀ S : Finset U, S.card ≤ 2 * t →
      ((Ω.filter fun b => S ⊆ X1 b).card : ℝ) ≤ Ω.card * ((2 * r) ^ S.card)⁻¹)
    (hZ0 : ∀ b, fam A1 (X1 b) ∧ fam A2 (X1 b) → Z0 b ⊆ X1 b ∧ (Z0 b).card ≤ 2 * t ∧
      ∀ Y, Z0 b ⊆ Y → fam A1 Y ∧ fam A2 Y) :
    ∀ (m : ℕ) (A0 : Finset (Finset U)), (Nset Ω X1 A1 A2 A0).card = m →
      (∀ S ∈ A0, S.card ≤ t) → (∀ S ∈ A0, GoodSet A1 A2 Z0 t r S) →
      ∃ A : Finset (Finset U), (∀ S ∈ A, S.card ≤ t) ∧ (∀ S ∈ A, GoodSet A1 A2 Z0 t r S) ∧
        ((Nset Ω X1 A1 A2 A).card : ℝ) ≤ Ω.card * ((2 : ℝ) ^ t)⁻¹ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro A0 hm hsz hgood
  set N := Nset Ω X1 A1 A2 A0 with hN
  rcases N.eq_empty_or_nonempty with hN0 | hNne
  · refine ⟨A0, hsz, hgood, ?_⟩
    have hN0' : Nset Ω X1 A1 A2 A0 = ∅ := hN0
    rw [hN0']; simp only [card_empty, Nat.cast_zero]; positivity
  have hNpos : (0 : ℝ) < N.card := by exact_mod_cast hNne.card_pos
  set V := (univ : Finset (Finset U)).filter (fun S =>
    (N.card : ℝ) * (r ^ S.card)⁻¹ ≤ ((N.filter fun b => S ⊆ Z0 b).card : ℝ)) with hV
  have hVne : V.Nonempty := ⟨∅, by simp [hV]⟩
  obtain ⟨S, hSV, hmax⟩ := V.exists_max_image Finset.card hVne
  have hSval : (N.card : ℝ) * (r ^ S.card)⁻¹ ≤ ((N.filter fun b => S ⊆ Z0 b).card : ℝ) := by
    rw [hV, mem_filter] at hSV; exact hSV.2
  have hcpos : 0 < ((N.filter fun b => S ⊆ Z0 b).card : ℝ) :=
    lt_of_lt_of_le (by positivity) hSval
  obtain ⟨b0, hb0⟩ : (N.filter fun b => S ⊆ Z0 b).Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hcpos
  rw [mem_filter] at hb0
  have hb0N := hb0.1
  have hb0' := mem_Nset.mp hb0N
  obtain ⟨hZsub, hZcard, _⟩ := hZ0 b0 ⟨hb0'.2.1, hb0'.2.2.1⟩
  have hS2t : S.card ≤ 2 * t := (card_le_card hb0.2).trans hZcard
  by_cases hSt : t < S.card
  · refine ⟨A0, hsz, hgood, ?_⟩
    have h1 : ((N.filter fun b => S ⊆ Z0 b).card : ℝ) ≤
        ((Ω.filter fun b => S ⊆ X1 b).card : ℝ) := by
      exact_mod_cast card_le_card (fun b hb => by
        rw [mem_filter] at hb ⊢
        have := mem_Nset.mp hb.1
        exact ⟨this.1, hb.2.trans (hZ0 b ⟨this.2.1, this.2.2.1⟩).1⟩)
    have h2 := hspread S hS2t
    have h3 : (N.card : ℝ) * (r ^ S.card)⁻¹ ≤ Ω.card * ((2 * r) ^ S.card)⁻¹ :=
      hSval.trans (h1.trans h2)
    rw [mul_pow, mul_inv, ← mul_assoc] at h3
    have hrs : 0 < (r ^ S.card)⁻¹ := by positivity
    have h4 : (N.card : ℝ) ≤ Ω.card * ((2 : ℝ) ^ S.card)⁻¹ := le_of_mul_le_mul_right h3 hrs
    refine h4.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ (by norm_num) hSt.le
  · push Not at hSt
    have hgS : GoodSet A1 A2 Z0 t r S := by
      refine ⟨N.filter fun b => S ⊆ Z0 b, ⟨b0, mem_filter.mpr hb0⟩, ?_, ?_⟩
      · intro b hb
        rw [mem_filter] at hb
        have := mem_Nset.mp hb.1
        obtain ⟨_, h2, h3⟩ := hZ0 b ⟨this.2.1, this.2.2.1⟩
        exact ⟨hb.2, h2, h3⟩
      · intro S'
        rcases Nat.eq_zero_or_pos S'.card with h0 | hpos
        · rw [h0, pow_zero, inv_one, mul_one]; exact_mod_cast card_filter_le _ _
        by_cases hdis : Disjoint S' S
        · have hnot : S ∪ S' ∉ V := by
            intro hmem
            have := hmax _ hmem
            rw [card_union_of_disjoint hdis.symm] at this
            omega
          have hlt : ((N.filter fun b => S ∪ S' ⊆ Z0 b).card : ℝ) <
              N.card * (r ^ (S ∪ S').card)⁻¹ := by
            rw [hV, mem_filter] at hnot
            push Not at hnot
            exact hnot (mem_univ _)
          rw [card_union_of_disjoint hdis.symm, pow_add, mul_inv, ← mul_assoc] at hlt
          have hsub : ((N.filter fun b => S ⊆ Z0 b).filter fun b => S' ⊆ Z0 b \ S) ⊆
              N.filter fun b => S ∪ S' ⊆ Z0 b := by
            intro b hb
            simp only [mem_filter] at hb ⊢
            exact ⟨hb.1.1, union_subset hb.1.2 (hb.2.trans sdiff_subset)⟩
          have hc : ((((N.filter fun b => S ⊆ Z0 b).filter fun b => S' ⊆ Z0 b \ S)).card : ℝ) ≤
              ((N.filter fun b => S ∪ S' ⊆ Z0 b).card : ℝ) := by
            exact_mod_cast card_le_card hsub
          calc _ ≤ _ := hc
            _ ≤ N.card * (r ^ S.card)⁻¹ * (r ^ S'.card)⁻¹ := hlt.le
            _ ≤ _ := mul_le_mul_of_nonneg_right hSval (by positivity)
        · have : ((N.filter fun b => S ⊆ Z0 b).filter fun b => S' ⊆ Z0 b \ S) = ∅ := by
            apply eq_empty_of_forall_notMem
            intro b hb
            simp only [mem_filter] at hb
            apply hdis
            rw [disjoint_left]
            intro x hx hxS
            exact (mem_sdiff.mp (hb.2 hx)).2 hxS
          rw [this]; simp only [card_empty, Nat.cast_zero]; positivity
    have hlt : (Nset Ω X1 A1 A2 (insert S A0)).card < m := by
      rw [← hm]
      apply card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨b0, hb0N, ?_⟩
        intro hb
        have := mem_Nset.mp hb
        exact this.2.2.2 ⟨S, mem_insert_self _ _, hb0.2.trans hZsub⟩
      · intro b hb
        rw [mem_Nset] at hb ⊢
        refine ⟨hb.1, hb.2.1, hb.2.2.1, fun h => hb.2.2.2 ?_⟩
        obtain ⟨T, hT, hTX⟩ := h
        exact ⟨T, mem_insert_of_mem hT, hTX⟩
    exact ih _ hlt (insert S A0) rfl
      (fun T hT => by
        rcases mem_insert.mp hT with rfl | hT
        · exact hSt
        · exact hsz T hT)
      (fun T hT => by
        rcases mem_insert.mp hT with rfl | hT
        · exact hgS
        · exact hgood T hT)

open SpreadMatchCircuit.Matching.Dev.SpreadSet in
/-- Lemma 16 from the conditional bound: `p(X0 ∈ N⁰) ≤ 2^t ε`. -/
lemma newErr0 (A A1 A2 : Finset (Finset U)) (t : ℕ) (ε : ℝ) (hA : ∀ S ∈ A, S.card ≤ t)
    (hε : 0 ≤ ε)
    (hinner : ∀ G, fam A G → ∑ V : Finset U, wt (1 / 3) V *
      (if fam A (G ∪ V) ∧ ¬ (fam A1 (G ∪ V) ∧ fam A2 (G ∪ V)) then 1 else 0) ≤ ε) :
    randProb U (1 / 2) (fun X => fam A X ∧ ¬ (fam A1 X ∧ fam A2 X)) ≤ (2 : ℝ) ^ t * ε := by
  set n := Fintype.card U
  rw [randProb_eq_wt]
  have hid := sum_union2 (U := U) (fun G W => (if fam A G then (1 : ℝ) else 0) *
    (if fam A W ∧ ¬ (fam A1 W ∧ fam A2 W) then 1 else 0))
  have hLHS : ∑ G : Finset U, wt (1 / 4) G * ∑ V : Finset U, wt (1 / 3) V *
      ((if fam A G then (1 : ℝ) else 0) *
        (if fam A (G ∪ V) ∧ ¬ (fam A1 (G ∪ V) ∧ fam A2 (G ∪ V)) then 1 else 0)) ≤ ε := by
    calc _ ≤ ∑ G : Finset U, wt (1 / 4) G * ε := by
          apply sum_le_sum; intro G _
          apply mul_le_mul_of_nonneg_left _ (wt_nonneg (by norm_num) (by norm_num) G)
          by_cases hG : fam A G
          · simp only [if_pos hG, one_mul]; exact hinner G hG
          · simp only [if_neg hG, zero_mul, mul_zero, sum_const_zero]; exact hε
      _ = ε := by rw [← sum_mul, sum_wt, one_mul]
  have hpt : ∀ X : Finset U, wt (1 / 2) X *
      (if fam A X ∧ ¬ (fam A1 X ∧ fam A2 X) then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ t * ∑ G ∈ X.powerset, (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ X.card *
        ((if fam A G then (1 : ℝ) else 0) *
          (if fam A X ∧ ¬ (fam A1 X ∧ fam A2 X) then 1 else 0)) := by
    intro X
    by_cases hP : fam A X ∧ ¬ (fam A1 X ∧ fam A2 X)
    · simp only [if_pos hP, mul_one]
      rw [← mul_sum, Finset.sum_boole, wt_half]
      obtain ⟨S, hSA, hSX⟩ := hP.1
      have hcard : 2 ^ (X.card - S.card) ≤ (X.powerset.filter fun G => fam A G).card := by
        calc 2 ^ (X.card - S.card) = (X \ S).powerset.card := by
              rw [card_powerset, card_sdiff_of_subset hSX]
          _ ≤ _ := by
            apply Finset.card_le_card_of_injOn (fun Y => S ∪ Y)
            · intro Y hY
              have hY' := mem_powerset.mp (mem_coe.mp hY)
              refine mem_coe.mpr (mem_filter.mpr ⟨mem_powerset.mpr
                (union_subset hSX (hY'.trans sdiff_subset)), S, hSA, subset_union_left⟩)
            · intro Y₁ h₁ Y₂ h₂ heq0
              have heq : S ∪ Y₁ = S ∪ Y₂ := heq0
              have h₁' := mem_powerset.mp (mem_coe.mp h₁)
              have h₂' := mem_powerset.mp (mem_coe.mp h₂)
              ext x
              constructor
              · intro hx
                have : x ∈ S ∪ Y₂ := heq ▸ mem_union_right S hx
                rcases mem_union.mp this with h | h
                · exact absurd h (mem_sdiff.mp (h₁' hx)).2
                · exact h
              · intro hx
                have : x ∈ S ∪ Y₁ := heq.symm ▸ mem_union_right S hx
                rcases mem_union.mp this with h | h
                · exact absurd h (mem_sdiff.mp (h₂' hx)).2
                · exact h
      have hcardR : (2 : ℝ) ^ (X.card - S.card) ≤
          ((X.powerset.filter fun G => fam A G).card : ℝ) := by exact_mod_cast hcard
      have hSXc := card_le_card hSX
      have hSt := hA S hSA
      obtain ⟨k, hk⟩ : ∃ k, X.card = S.card + k := ⟨X.card - S.card, by omega⟩
      rw [hk, Nat.add_sub_cancel_left] at hcardR
      rw [hk]
      have e1 : (1 / 2 : ℝ) ^ (S.card + k) * 2 ^ k = (1 / 2) ^ S.card := by
        rw [pow_add, mul_assoc, ← mul_pow]; norm_num
      have e2 : (1 : ℝ) ≤ 2 ^ t * (1 / 2) ^ S.card := by
        have : (2 : ℝ) ^ S.card ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) hSt
        have e3 : (2 : ℝ) ^ S.card * (1 / 2) ^ S.card = 1 := by rw [← mul_pow]; norm_num
        nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) S.card]
      have hn : (0 : ℝ) < (1 / 2) ^ n := by positivity
      have hX : (0 : ℝ) ≤ (1 / 2) ^ (S.card + k) := by positivity
      calc (1 / 2 : ℝ) ^ n = (1 / 2) ^ n * 1 := by ring
        _ ≤ (1 / 2) ^ n * (2 ^ t * (1 / 2) ^ S.card) := mul_le_mul_of_nonneg_left e2 hn.le
        _ = 2 ^ t * ((1 / 2) ^ n * ((1 / 2) ^ (S.card + k) * 2 ^ k)) := by rw [e1]; ring
        _ ≤ 2 ^ t * ((1 / 2) ^ n * ((1 / 2) ^ (S.card + k) *
              ((X.powerset.filter fun G => fam A G).card : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hn.le
          exact mul_le_mul_of_nonneg_left hcardR hX
        _ = _ := by ring
    · simp only [if_neg hP, mul_zero, sum_const_zero]; rfl
  calc ∑ X : Finset U, wt (1 / 2) X *
        (if fam A X ∧ ¬ (fam A1 X ∧ fam A2 X) then (1 : ℝ) else 0)
      ≤ ∑ X : Finset U, (2 : ℝ) ^ t * ∑ G ∈ X.powerset, (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ X.card *
        ((if fam A G then (1 : ℝ) else 0) *
          (if fam A X ∧ ¬ (fam A1 X ∧ fam A2 X) then 1 else 0)) := sum_le_sum (fun X _ => hpt X)
    _ = (2 : ℝ) ^ t * ∑ G : Finset U, wt (1 / 4) G * ∑ V : Finset U, wt (1 / 3) V *
      ((if fam A G then (1 : ℝ) else 0) *
        (if fam A (G ∪ V) ∧ ¬ (fam A1 (G ∪ V) ∧ fam A2 (G ∪ V)) then 1 else 0)) := by
          rw [← mul_sum, hid]
    _ ≤ (2 : ℝ) ^ t * ε := mul_le_mul_of_nonneg_left hLHS (by positivity)

end Step

open SpreadMatchCircuit.Matching.Dev.SpreadSet in
theorem andStep_holds : AndStep := by
  intro U _ _ β Ω X1 t r ε ht hr hε hspread hc3 A1 A2 hA1 hA2
  have hex : ∀ b, ∃ Z : Finset U, fam A1 (X1 b) ∧ fam A2 (X1 b) →
      Z ⊆ X1 b ∧ Z.card ≤ 2 * t ∧ ∀ Y, Z ⊆ Y → fam A1 Y ∧ fam A2 Y := by
    intro b
    by_cases h : fam A1 (X1 b) ∧ fam A2 (X1 b)
    · obtain ⟨⟨S1, h1, h1X⟩, ⟨S2, h2, h2X⟩⟩ := h
      have c1 := hA1 S1 h1
      have c2 := hA2 S2 h2
      exact ⟨S1 ∪ S2, fun _ => ⟨union_subset h1X h2X,
        (card_union_le _ _).trans (by omega),
        fun Y hY => ⟨⟨S1, h1, subset_union_left.trans hY⟩, ⟨S2, h2, subset_union_right.trans hY⟩⟩⟩⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose Z0 hZ0 using hex
  obtain ⟨A, hAsz, hAgood, hAN⟩ := loop Ω X1 A1 A2 Z0 t r hr hspread hZ0 _ ∅ rfl
    (by simp) (by simp)
  refine ⟨A, hAsz, hAN, ?_⟩
  apply newErr0 A A1 A2 t ε hAsz hε.le
  intro G hG
  obtain ⟨S, hSA, hSG⟩ := hG
  obtain ⟨Ω', hne, hprop, hsp⟩ := hAgood S hSA
  have hc := hc3 β Ω' (fun b => Z0 b \ S) hne
    (fun b hb => (card_le_card sdiff_subset).trans (hprop b hb).2.1) hsp
  have hcomp := sum_wt_compl (U := U) (1 / 3) (fun V => ∃ b ∈ Ω', Z0 b \ S ⊆ V)
  have hle : ∑ V : Finset U, wt (1 / 3) V *
      (if fam A (G ∪ V) ∧ ¬ (fam A1 (G ∪ V) ∧ fam A2 (G ∪ V)) then (1 : ℝ) else 0) ≤
      ∑ V : Finset U, wt (1 / 3) V * (if ∃ b ∈ Ω', Z0 b \ S ⊆ V then 0 else 1) := by
    apply sum_le_sum; intro V _
    apply mul_le_mul_of_nonneg_left _ (wt_nonneg (by norm_num) (by norm_num) V)
    by_cases hQ : ∃ b ∈ Ω', Z0 b \ S ⊆ V
    · rw [if_pos hQ, if_neg]
      rintro ⟨_, hP⟩
      obtain ⟨b, hb, hbV⟩ := hQ
      apply hP
      apply (hprop b hb).2.2 (G ∪ V)
      intro x hx
      by_cases hxS : x ∈ S
      · exact mem_union_left _ (hSG hxS)
      · exact mem_union_right _ (hbV (mem_sdiff.mpr ⟨hx, hxS⟩))
    · rw [if_neg hQ]; split_ifs <;> norm_num
  linarith

end SpreadMatchCircuit.Matching.Dev.Thm9Full

namespace SpreadMatchCircuit.Matching.Supplement

/-- **Theorem 9**, p. 5. -/
theorem chk_theorem_9 :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ (n k d : ℕ), n.Prime → 1 ≤ k →
        (k : ℝ) * (d : ℝ) ≤ η * (n : ℝ) → 3 * (d : ℝ) * Real.log (n : ℝ) ≤ (k : ℝ) →
        ∀ C : MonotoneCircuit (ZMod n), (∀ x : ZMod n → Bool, C.eval x = true ↔ PolyImageFun n k d x) →
          Real.exp (c * min (d : ℝ) ((n : ℝ) / (k : ℝ))) ≤ (C.size : ℝ) :=
  chk_theorem_9_of_andStep Dev.Thm9Full.spreadSetLemma_holds Dev.Thm9Full.andStep_holds

end SpreadMatchCircuit.Matching.Supplement
end

theorem solution : type_of% @SpreadMatchCircuit.Matching.Supplement.chk_theorem_9 := @SpreadMatchCircuit.Matching.Supplement.chk_theorem_9
