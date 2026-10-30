-- Prove2me | solution 1 for RobustPCA.Recovery.sec_7_1_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T08:38:46.616467+00:00
-- url     : https://prove2.me/submissions/ba98df30-3fe6-4cd6-bcd7-7491550ede8e

import Mathlib
import Definitions.Def_RobustPCA_Recovery_Setup

set_option autoImplicit false

open MatrixCompletion

namespace RPCAe4173a1a

open RobustPCA.Recovery
open scoped Classical BigOperators
open Finset

/-! ## Elimination (monotonicity of the success event) -/

lemma l1_add_le {n : ℕ} (A B : RealMatrix n n) : l1Norm (A + B) ≤ l1Norm A + l1Norm B := by
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun j _ => ?_)
  simpa only [Matrix.add_apply] using abs_add_le (A i j) (B i j)

lemma l1_split {n : ℕ} (Ω' Ω : Finset (Fin n × Fin n)) (h : Ω' ⊆ Ω) (S : RealMatrix n n) :
    l1Norm (samplingProjection Ω S) = l1Norm (samplingProjection Ω' S) +
      l1Norm (samplingProjection Ω S - samplingProjection Ω' S) := by
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [samplingProjection, Matrix.sub_apply]
  by_cases h1 : (i, j) ∈ Ω'
  · have h2 : (i, j) ∈ Ω := h h1
    simp [h1, h2]
  · by_cases h2 : (i, j) ∈ Ω
    · simp [h1, h2]
    · simp [h1, h2]

lemma elim {n : ℕ} (lam : ℝ) (hlam : 0 ≤ lam) (L0 S : RealMatrix n n)
    (Ω' Ω : Finset (Fin n × Fin n)) (h : Ω' ⊆ Ω)
    (hE : IsPCPExact lam L0 (samplingProjection Ω S)) :
    IsPCPExact lam L0 (samplingProjection Ω' S) := by
  intro L S' hfeas hne
  set D := samplingProjection Ω S - samplingProjection Ω' S with hD
  have hf : L + (S' + D) = L0 + samplingProjection Ω S := by
    rw [← add_assoc, hfeas, hD]; abel
  have hn : (L, S' + D) ≠ (L0, samplingProjection Ω S) := by
    intro heq
    apply hne
    simp only [Prod.mk.injEq] at heq ⊢
    refine ⟨heq.1, ?_⟩
    have := heq.2
    rw [hD] at this
    calc S' = (S' + (samplingProjection Ω S - samplingProjection Ω' S)) -
          (samplingProjection Ω S - samplingProjection Ω' S) := by abel
      _ = samplingProjection Ω' S := by rw [this]; abel
  have h1 := hE L (S' + D) hf hn
  have h2 := l1_add_le S' D
  have h3 := l1_split Ω' Ω h S
  have h4 : lam * l1Norm (S' + D) ≤ lam * (l1Norm S' + l1Norm D) :=
    mul_le_mul_of_nonneg_left h2 hlam
  rw [h3] at h1
  nlinarith

/-! ## Counting: the uniform success probability is nonincreasing in the cardinality -/

lemma count_mono {α : Type} [Fintype α] [DecidableEq α] (E : Finset α → Prop) [DecidablePred E]
    (hE : ∀ s t : Finset α, s ⊆ t → E t → E s) {m k : ℕ} (hmk : m ≤ k)
    (hk : k ≤ Fintype.card α) :
    ((powersetCard k (univ : Finset α)).filter E).card * (Fintype.card α).choose m ≤
      ((powersetCard m (univ : Finset α)).filter E).card * (Fintype.card α).choose k := by
  set N := Fintype.card α with hN
  set s := (powersetCard k (univ : Finset α)).filter E with hs
  set t := (powersetCard m (univ : Finset α)).filter E with ht
  have key : s.card * k.choose m ≤ t.card * (N - m).choose (k - m) := by
    refine Finset.card_mul_le_card_mul (fun a b => b ⊆ a) ?_ ?_
    · intro a ha
      rw [hs, mem_filter, mem_powersetCard] at ha
      have hsub : powersetCard m a ⊆ t.bipartiteAbove (fun a b => b ⊆ a) a := by
        intro x hx
        rw [mem_powersetCard] at hx
        simp only [Finset.bipartiteAbove, mem_filter, ht, mem_powersetCard]
        exact ⟨⟨⟨subset_univ _, hx.2⟩, hE x a hx.1 ha.2⟩, hx.1⟩
      have := card_le_card hsub
      rw [card_powersetCard, ha.1.2] at this
      exact this
    · intro b hb
      rw [ht, mem_filter, mem_powersetCard] at hb
      have hcard : (powersetCard (k - m) ((univ : Finset α) \ b)).card =
          (N - m).choose (k - m) := by
        rw [card_powersetCard, card_sdiff_of_subset (subset_univ _), card_univ, hb.1.2]
      rw [← hcard]
      refine card_le_card_of_injOn (fun a => a \ b) ?_ ?_
      · intro a ha
        rw [Finset.mem_coe] at ha ⊢
        simp only [Finset.bipartiteBelow, hs, mem_filter, mem_powersetCard] at ha
        rw [mem_powersetCard]
        refine ⟨sdiff_subset_sdiff (subset_univ _) le_rfl, ?_⟩
        rw [card_sdiff_of_subset ha.2, ha.1.1.2, hb.1.2]
      · intro a1 ha1 a2 ha2 heq
        rw [Finset.mem_coe] at ha1 ha2
        simp only [Finset.bipartiteBelow, hs, mem_filter, mem_powersetCard] at ha1 ha2
        have e1 : a1 \ b ∪ b = a1 := sdiff_union_of_subset ha1.2
        have e2 : a2 \ b ∪ b = a2 := sdiff_union_of_subset ha2.2
        simp only at heq
        rw [← e1, ← e2, heq]
  have hcm : N.choose k * k.choose m = N.choose m * (N - m).choose (k - m) := Nat.choose_mul hmk
  have hpos : 0 < k.choose m := Nat.choose_pos hmk
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc s.card * N.choose m * k.choose m = N.choose m * (s.card * k.choose m) := by ring
    _ ≤ N.choose m * (t.card * (N - m).choose (k - m)) := Nat.mul_le_mul_left _ key
    _ = t.card * (N.choose m * (N - m).choose (k - m)) := by ring
    _ = t.card * (N.choose k * k.choose m) := by rw [hcm]
    _ = t.card * N.choose k * k.choose m := by ring

/-! ## Bernoulli law as a mixture over cardinalities -/

lemma sum_by_card {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ) :
    ∑ Ω : Finset α, f Ω = ∑ k ∈ range (Fintype.card α + 1),
      ∑ Ω ∈ powersetCard k (univ : Finset α), f Ω := by
  have h := Finset.sum_disjiUnion (range (#(univ : Finset α) + 1)) (fun i => powersetCard i univ)
    ((univ : Finset α).pairwise_disjoint_powersetCard.set_pairwise _) (f := f)
  rw [← powerset_card_disjiUnion, powerset_univ, card_univ] at h
  exact h

lemma ber_decomp {n : ℕ} (p : ℝ) (E : Finset (Fin n × Fin n) → Prop) :
    bernoulliEventProb p E =
      ∑ k ∈ range (Fintype.card (Fin n × Fin n) + 1),
        (((powersetCard k (univ : Finset (Fin n × Fin n))).filter E).card : ℝ) *
          (p ^ k * (1 - p) ^ (Fintype.card (Fin n × Fin n) - k)) := by
  unfold bernoulliEventProb bernoulliObservationWeight
  rw [sum_by_card]
  refine sum_congr rfl (fun k _ => ?_)
  rw [← sum_filter]
  rw [sum_congr rfl (g := fun _ => p ^ k * (1 - p) ^ (Fintype.card (Fin n × Fin n) - k))]
  · rw [sum_const, nsmul_eq_mul]
  · intro x hx
    rw [mem_filter, mem_powersetCard] at hx
    rw [hx.1.2]

end RPCAe4173a1a

open MatrixCompletion RobustPCA.Recovery Finset in
theorem solution {n : ℕ} (lam : ℝ) (L0 S : RealMatrix n n) (m : ℕ) (p : ℝ)
    (hlam : 0 ≤ lam) (hm : m ≤ n * n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fixedCardinalityEventProb m (fun Ω => IsPCPExact lam L0 (samplingProjection Ω S)) ≥
      bernoulliEventProb p (fun Ω => IsPCPExact lam L0 (samplingProjection Ω S)) -
        bernoulliEventProb p (fun Ω : Finset (Fin n × Fin n) => Ω.card < m) := by
  classical
  set N := Fintype.card (Fin n × Fin n) with hN
  have hNn : N = n * n := by simp [hN]
  have hmN : m ≤ N := hNn ▸ hm
  set E : Finset (Fin n × Fin n) → Prop := fun Ω => IsPCPExact lam L0 (samplingProjection Ω S)
    with hEdef
  have hEmono : ∀ s t : Finset (Fin n × Fin n), s ⊆ t → E t → E s :=
    fun s t hst ht => RPCAe4173a1a.elim lam hlam L0 S s t hst ht
  set A : ℕ → ℕ := fun k => ((powersetCard k (univ : Finset (Fin n × Fin n))).filter E).card
    with hA
  have hCm : (0 : ℝ) < (N.choose m : ℝ) := by exact_mod_cast Nat.choose_pos hmN
  set Pm : ℝ := (A m : ℝ) / (N.choose m : ℝ) with hPm
  have hfix : fixedCardinalityEventProb m E = Pm := by
    unfold fixedCardinalityEventProb
    simp only [hPm, hA, card_powersetCard, card_univ, hN]
  have hPm0 : 0 ≤ Pm := div_nonneg (Nat.cast_nonneg _) hCm.le
  have hbE := RPCAe4173a1a.ber_decomp p E
  have hbF := RPCAe4173a1a.ber_decomp p (fun Ω : Finset (Fin n × Fin n) => Ω.card < m)
  have hFk : ∀ (k : ℕ) (inst : DecidablePred (fun Ω : Finset (Fin n × Fin n) => Ω.card < m)),
      (@Finset.filter _ (fun Ω : Finset (Fin n × Fin n) => Ω.card < m) inst
        (powersetCard k (univ : Finset (Fin n × Fin n)))).card =
      if k < m then N.choose k else 0 := by
    intro k inst
    split_ifs with hk
    · rw [filter_true_of_mem, card_powersetCard, card_univ]
      intro x hx
      rw [mem_powersetCard] at hx
      rw [hx.2]; exact hk
    · rw [filter_false_of_mem, card_empty]
      intro x hx
      rw [mem_powersetCard] at hx
      rw [hx.2]; exact hk
  have hsum1 : ∑ k ∈ range (N + 1), (N.choose k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) = 1 := by
    have := add_pow p (1 - p) N
    rw [show p + (1 - p) = 1 by ring, one_pow] at this
    refine Eq.trans ?_ this.symm
    refine sum_congr rfl (fun k _ => ?_)
    ring
  have hterm : ∀ k ∈ range (N + 1),
      (A k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) ≤
        ((if k < m then N.choose k else 0 : ℕ) : ℝ) * (p ^ k * (1 - p) ^ (N - k)) +
          Pm * ((N.choose k : ℝ) * (p ^ k * (1 - p) ^ (N - k))) := by
    intro k hk
    rw [mem_range] at hk
    have hq : 0 ≤ p ^ k * (1 - p) ^ (N - k) :=
      mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    have hAk : (A k : ℝ) ≤ (N.choose k : ℝ) := by
      have : A k ≤ N.choose k := by
        have h1 := card_filter_le (powersetCard k (univ : Finset (Fin n × Fin n))) E
        rw [card_powersetCard, card_univ] at h1
        exact h1
      exact_mod_cast this
    split_ifs with hkm
    · have : 0 ≤ Pm * ((N.choose k : ℝ) * (p ^ k * (1 - p) ^ (N - k))) :=
        mul_nonneg hPm0 (mul_nonneg (Nat.cast_nonneg _) hq)
      nlinarith
    · replace hkm := not_lt.mp hkm
      have hc := RPCAe4173a1a.count_mono E hEmono hkm (by omega)
      have hc' : (A k : ℝ) * (N.choose m : ℝ) ≤ (A m : ℝ) * (N.choose k : ℝ) := by
        exact_mod_cast hc
      have hAk' : (A k : ℝ) ≤ Pm * (N.choose k : ℝ) := by
        rw [hPm, div_mul_eq_mul_div, le_div_iff₀ hCm]
        exact hc'
      push_cast
      nlinarith
  have hmain : bernoulliEventProb p E ≤
      bernoulliEventProb p (fun Ω : Finset (Fin n × Fin n) => Ω.card < m) + Pm := by
    rw [hbE, hbF]
    simp_rw [hFk]
    calc ∑ k ∈ range (N + 1), (A k : ℝ) * (p ^ k * (1 - p) ^ (N - k))
        ≤ ∑ k ∈ range (N + 1),
            (((if k < m then N.choose k else 0 : ℕ) : ℝ) * (p ^ k * (1 - p) ^ (N - k)) +
              Pm * ((N.choose k : ℝ) * (p ^ k * (1 - p) ^ (N - k)))) := sum_le_sum hterm
      _ = ∑ k ∈ range (N + 1),
            ((if k < m then N.choose k else 0 : ℕ) : ℝ) * (p ^ k * (1 - p) ^ (N - k)) + Pm := by
        rw [sum_add_distrib, ← mul_sum, hsum1, mul_one]
  show fixedCardinalityEventProb m E ≥ bernoulliEventProb p E -
    bernoulliEventProb p (fun Ω : Finset (Fin n × Fin n) => Ω.card < m)
  rw [hfix]
  linarith
