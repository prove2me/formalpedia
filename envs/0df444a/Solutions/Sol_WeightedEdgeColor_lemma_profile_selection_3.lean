-- Prove2me | solution 3 for WeightedEdgeColor.lemma_profile_selection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T08:13:34.362884+00:00
-- url     : https://prove2.me/submissions/527d12c1-e4b7-4d1e-baae-fa7b5d61965f

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets
import Theorems.Thm_WeightedEdgeColor_lemma_C_1
import Theorems.Thm_WeightedEdgeColor_lemma_profile_choice_pos

set_option autoImplicit false
set_option maxHeartbeats 0

open WeightedEdgeColor WeightedEdgeColor.WGraph

theorem solution (C₀ C₁ ε : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hε : 0 < ε)
    (r : ℕ) :
    ∃ (σ r₀ β Cm : ℝ) (Ks : ℕ), 0 < σ ∧ σ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < β ∧ β ≤ r₀ ∧
      2 * β ≤ σ * r₀ ∧ 0 < Cm ∧
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ g : V → Fin r,
      (∀ (e : E) (u v : V), G.ends e = s(u, v) → g u ≠ g v) →
      ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ x : E → 𝒞 → ℝ, (∀ e c, 0 ≤ x e c ∧ x e c ≤ C₀ / n) → (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, G.InK v (fun e => x e c)) →
      ∃ (b : V → 𝒞 → Fin Ks → ℝ) (R : V → 𝒞 → ℝ) (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ)
        (XS : E → 𝒞 → ℝ),
      -- valid profiles: slots `b v c i ≥ 0`, reserve `R v c ≥ 0`, total size at most one,
      -- every positive reserve at least `r₀`
      (∀ v c, (∀ i, 0 ≤ b v c i) ∧ 0 ≤ R v c ∧ ∑ i, b v c i + R v c ≤ 1 ∧ (R v c = 0 ∨ r₀ ≤ R v c)) ∧
      -- nonnegative option fractions
      (∀ e c i j, 0 ≤ XL e c i j) ∧
      (∀ e c, 0 ≤ XS e c) ∧
      -- large options use slots that can hold the edge, at both ends
      (∀ e c i j, XL e c i j ≠ 0 → β ≤ G.w e ∧ G.w e ≤ b (src e) c i ∧ G.w e ≤ b (tgt e) c j) ∧
      -- small options use positive reserves at both ends
      (∀ e c, XS e c ≠ 0 → G.w e < β ∧ 0 < R (src e) c ∧ 0 < R (tgt e) c) ∧
      -- each edge has total fraction at most one, and at most `Cm / n` in each color
      (∀ e, ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) ≤ 1) ∧
      (∀ e c, ∑ i, ∑ j, XL e c i j + XS e c ≤ Cm / n) ∧
      -- slack in every slot and every reserve
      (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
         + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ) ∧
      (∀ v c, ∑ e ∈ G.inc v, G.w e * XS e c ≤ (1 - σ) * R v c) ∧
      -- options only where the proposal is positive
      (∀ e c, ∑ i, ∑ j, XL e c i j + XS e c ≠ 0 → 0 < x e c) ∧
      -- almost all proposed weight survives at every vertex
      ∀ v, (∑ e ∈ G.inc v, G.w e * ∑ c, x e c) - ε * n - K * n ^ (3 / 4 : ℝ) ≤
        ∑ e ∈ G.inc v, G.w e * ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min ε 1 / 8 := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht8 : t ≤ 1 / 8 := by rw [ht]; have := min_le_right ε 1; linarith
  have htε : t ≤ ε / 8 := by rw [ht]; have := min_le_left ε 1; linarith
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℝ, r₀ = t / 4 := ⟨_, rfl⟩
  have hr₀0 : 0 < r₀ := by rw [hr₀]; positivity
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = t * r₀ / 4 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hβr : β ≤ r₀ := by rw [hβ]; nlinarith only [hr₀0, ht8]
  have hβδ : β ≤ t / 4 := by rw [← hr₀]; exact hβr
  obtain ⟨M, hC1⟩ := lemma_C_1 t β ht0 (by linarith) hβ0 hβδ
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = C₀ * ((M : ℝ) / t) ^ 2 + 1 := ⟨_, rfl⟩
  have hCm0 : 0 < Cm := by rw [hCm]; positivity
  refine ⟨t / 2, r₀, β, Cm, ⌊1 / β⌋₊, by positivity, by linarith, hr₀0, by rw [hr₀]; linarith,
    hβ0, hβr, by rw [hβ]; linarith, hCm0, ?_⟩
  obtain ⟨n₀, K, hPC⟩ := lemma_profile_choice_pos C₀ C₁ t t r₀ β M ⌊1 / β⌋₊ r hC₀ hC₁ ht0 ht0
    (by linarith) hr₀0 hβ0
  refine ⟨max n₀ 1, K, ?_⟩
  intro V E _ _ _ _ G hG g hg src tgt hst n hn hW 𝒞 _ _ hcard x hx hxs hxK
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : 0 < n := by linarith
  -- Lemma C.1 at every vertex and color
  have hloc := fun (v : V) (c : 𝒞) => hC1 (G.inc v) (fun e => G.w e) (fun e => x e c)
    (fun e => G.w_pos e) (fun e => G.w_le_one e) (hxK v c)
  choose lamC bC RC aLC aSC hval hlam0 hlam1 haL0 haS0 hmarg hcapL hcapS htypL htypS hRr hLle hSle
    using hloc
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 - t) * (1 - t) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; nlinarith only [ht8]
  have hρ1 : ρ ≤ 1 - t := by rw [hρ]; nlinarith only [ht0, ht8]
  let aL' : V → 𝒞 → E → Fin M → Fin ⌊1 / β⌋₊ → ℝ := fun v c e P i =>
    if h : e ∈ G.inc v then ρ * aLC v c ⟨e, h⟩ P i else 0
  let aS' : V → 𝒞 → E → Fin M → ℝ := fun v c e P =>
    if h : e ∈ G.inc v then ρ * aSC v c ⟨e, h⟩ P else 0
  let y : E → 𝒞 → ℝ := fun e c => ρ * ((1 - t) * x e c)
  let lam' : V → 𝒞 → Fin M → ℝ := fun v c P => (1 - t) * lamC v c P + t / M
  have hMpos : ∀ (v : V) (c : 𝒞), (0 : ℝ) < M := by
    intro v c
    have := hlam1 v c
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0; simp at this
    · exact_mod_cast h0
  -- sums over `G.inc v` of the extended fractions
  have hsum_inc : ∀ (v : V) (F : G.inc v → ℝ),
      ∑ e ∈ G.inc v, (if h : e ∈ G.inc v then F ⟨e, h⟩ else 0) = ∑ e' : G.inc v, F e' := by
    intro v F
    rw [← Finset.sum_coe_sort (G.inc v)]
    apply Finset.sum_congr rfl
    intro e _
    rw [dif_pos e.2]
  have hy : ∀ e c, 0 ≤ y e c ∧ y e c ≤ C₀ / n := by
    intro e c
    have hx0 := (hx e c).1
    have hx1 := (hx e c).2
    have h1 : ρ * (1 - t) ≤ 1 := by
      have h2 := mul_le_mul_of_nonneg_right hρ1 (by linarith : (0 : ℝ) ≤ 1 - t)
      nlinarith only [h2, ht8, ht0]
    constructor
    · simp only [y]; have : 0 ≤ 1 - t := by linarith
      positivity
    · simp only [y]
      have : ρ * ((1 - t) * x e c) = (ρ * (1 - t)) * x e c := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_right h1 hx0
      linarith
  have hlam'lo : ∀ v c P, t / M ≤ lam' v c P := by
    intro v c P
    simp only [lam']
    have := hlam0 v c P
    have : 0 ≤ (1 - t) * lamC v c P := mul_nonneg (by linarith) this
    linarith
  have hlam'1 : ∀ v c, ∑ P, lam' v c P = 1 := by
    intro v c
    simp only [lam']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hlam1 v c, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have := hMpos v c
    field_simp
    ring
  have hRr' : ∀ v c P, RC v c P = 0 ∨ r₀ ≤ RC v c P := by
    intro v c P; rw [hr₀]; exact hRr v c P
  have haL'0 : ∀ v c e P i, 0 ≤ aL' v c e P i := by
    intro v c e P i; simp only [aL']; split_ifs
    · exact mul_nonneg hρ0.le (haL0 v c _ P i)
    · exact le_refl _
  have haS'0 : ∀ v c e P, 0 ≤ aS' v c e P := by
    intro v c e P; simp only [aS']; split_ifs
    · exact mul_nonneg hρ0.le (haS0 v c _ P)
    · exact le_refl _
  have haS'R : ∀ v c e P, aS' v c e P ≠ 0 → 0 < RC v c P := by
    intro v c e P h
    simp only [aS'] at h
    split_ifs at h with he
    · exact (htypS v c ⟨e, he⟩ P (fun h0 => h (by rw [h0, mul_zero]))).2
    · exact absurd rfl h
  have hmarg' : ∀ v c e, v ∈ G.ends e → ∑ P, (∑ i, aL' v c e P i + aS' v c e P) = y e c := by
    intro v c e hv
    have he : e ∈ G.inc v := by simp [WGraph.inc, hv]
    simp only [aL', aS', dif_pos he, y]
    rw [← hmarg v c ⟨e, he⟩, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro P _
    rw [← Finset.mul_sum]; ring
  have hcapL' : ∀ v c P i, ∑ e ∈ G.inc v, aL' v c e P i ≤ (1 - t) * lam' v c P := by
    intro v c P i
    simp only [aL']
    rw [hsum_inc v (fun e' => ρ * aLC v c e' P i), ← Finset.mul_sum]
    have h1 := hcapL v c P i
    have h2 : ρ * lamC v c P ≤ (1 - t) * ((1 - t) * lamC v c P) := by
      rw [hρ, mul_assoc]
    have h3 : (1 - t) * ((1 - t) * lamC v c P) ≤ (1 - t) * lam' v c P := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      simp only [lam']
      have := hMpos v c
      have : 0 ≤ t / M := by positivity
      linarith
    have h4 := mul_le_mul_of_nonneg_left h1 hρ0.le
    linarith
  have hcapS' : ∀ v c P, ∑ e ∈ G.inc v, G.w e * aS' v c e P ≤ (1 - t) * lam' v c P * RC v c P := by
    intro v c P
    simp only [aS']
    have hconv : ∑ e ∈ G.inc v, G.w e * (if h : e ∈ G.inc v then ρ * aSC v c ⟨e, h⟩ P else 0)
        = ∑ e ∈ G.inc v, (if h : e ∈ G.inc v then G.w e * (ρ * aSC v c ⟨e, h⟩ P) else 0) := by
      apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp
    rw [hconv, hsum_inc v (fun e' => G.w e' * (ρ * aSC v c e' P))]
    have hsmall : ∑ e' : G.inc v, G.w e' * (ρ * aSC v c e' P)
        = ρ * ∑ e' ∈ Finset.univ.filter (fun e' : G.inc v => G.w e' < β), G.w e' * aSC v c e' P := by
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro e' _
      split_ifs with h
      · ring
      · have : aSC v c e' P = 0 := by
          by_contra hne
          exact h (htypS v c e' P hne).1
        rw [this]; ring
    rw [hsmall]
    have h1 := hcapS v c P
    have hR0 := (hval v c P).2.1
    have h4 := mul_le_mul_of_nonneg_left h1 hρ0.le
    have h2 : ρ * (lamC v c P * RC v c P) ≤ (1 - t) * lam' v c P * RC v c P := by
      have : ρ * lamC v c P ≤ (1 - t) * lam' v c P := by
        have : ρ * lamC v c P ≤ (1 - t) * ((1 - t) * lamC v c P) := by rw [hρ, mul_assoc]
        have h3 : (1 - t) * ((1 - t) * lamC v c P) ≤ (1 - t) * lam' v c P := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          simp only [lam']
          have := hMpos v c
          have : 0 ≤ t / M := by positivity
          linarith
        linarith
      have := mul_le_mul_of_nonneg_right this hR0
      linarith
    linarith
  have htypL' : ∀ v c e P i, aL' v c e P i ≠ 0 → β ≤ G.w e := by
    intro v c e P i h
    simp only [aL'] at h
    split_ifs at h with he
    · exact (htypL v c ⟨e, he⟩ P i (fun h0 => h (by rw [h0, mul_zero]))).1
    · exact absurd rfl h
  have htypS' : ∀ v c e P, aS' v c e P ≠ 0 → G.w e < β := by
    intro v c e P h
    simp only [aS'] at h
    split_ifs at h with he
    · exact (htypS v c ⟨e, he⟩ P (fun h0 => h (by rw [h0, mul_zero]))).1
    · exact absurd rfl h
  obtain ⟨Pc, hPc⟩ := hPC V E G hG g hg src tgt hst n hn0 hW 𝒞 hcard y lam' RC aL' aS' hy hlam'lo
    hlam'1 hRr' haL'0 haS'0 haS'R htypL' htypS' hmarg' hcapL' hcapS'
  -- the options before clipping
  obtain ⟨XL0, hXL0⟩ : ∃ F : E → 𝒞 → Fin ⌊1 / β⌋₊ → Fin ⌊1 / β⌋₊ → ℝ, ∀ e c i j, F e c i j =
      aL' (src e) c e (Pc (src e) c) i * aL' (tgt e) c e (Pc (tgt e) c) j /
        (y e c * lam' (src e) c (Pc (src e) c) * lam' (tgt e) c (Pc (tgt e) c)) :=
    ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨XS0, hXS0⟩ : ∃ F : E → 𝒞 → ℝ, ∀ e c, F e c =
      aS' (src e) c e (Pc (src e) c) * aS' (tgt e) c e (Pc (tgt e) c) /
        (y e c * lam' (src e) c (Pc (src e) c) * lam' (tgt e) c (Pc (tgt e) c)) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨hload, hres, hdisc⟩ := hPc XL0 XS0 hXL0 hXS0
  have hlam'pos : ∀ v c P, 0 < lam' v c P := fun v c P =>
    lt_of_lt_of_le (div_pos ht0 (hMpos v c)) (hlam'lo v c P)
  have hden0 : ∀ e c, 0 ≤ y e c * lam' (src e) c (Pc (src e) c) * lam' (tgt e) c (Pc (tgt e) c) :=
    fun e c => mul_nonneg (mul_nonneg (hy e c).1 (hlam'pos _ _ _).le) (hlam'pos _ _ _).le
  have hXL00 : ∀ e c i j, 0 ≤ XL0 e c i j := fun e c i j => by
    rw [hXL0]; exact div_nonneg (mul_nonneg (haL'0 _ _ _ _ _) (haL'0 _ _ _ _ _)) (hden0 e c)
  have hXS00 : ∀ e c, 0 ≤ XS0 e c := fun e c => by
    rw [hXS0]; exact div_nonneg (mul_nonneg (haS'0 _ _ _ _) (haS'0 _ _ _ _)) (hden0 e c)
  obtain ⟨Sm, hSm⟩ : ∃ F : E → ℝ, ∀ e, F e = ∑ c, (∑ i, ∑ j, XL0 e c i j + XS0 e c) :=
    ⟨_, fun _ => rfl⟩
  have hSm0 : ∀ e, 0 ≤ Sm e := fun e => by
    rw [hSm]; exact Finset.sum_nonneg (fun c _ => add_nonneg (Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => hXL00 e c i j))) (hXS00 e c))
  have hf1 : ∀ e, 1 ≤ max 1 (Sm e) := fun e => le_max_left _ _
  have hfpos : ∀ e, 0 < max 1 (Sm e) := fun e => lt_of_lt_of_le one_pos (hf1 e)
  have hdivle : ∀ e (a : ℝ), 0 ≤ a → a / max 1 (Sm e) ≤ a := fun e a ha =>
    div_le_self ha (hf1 e)
  -- the endpoints
  have hsrc_inc : ∀ e, e ∈ G.inc (src e) := fun e => by
    simp [WGraph.inc, hst e]
  have htgt_inc : ∀ e, e ∈ G.inc (tgt e) := fun e => by
    simp [WGraph.inc, hst e]
  have haL'ne : ∀ v c e P i, aL' v c e P i ≠ 0 → ∃ h : e ∈ G.inc v, aLC v c ⟨e, h⟩ P i ≠ 0 := by
    intro v c e P i h
    simp only [aL'] at h
    split_ifs at h with he
    · exact ⟨he, fun h0 => h (by rw [h0, mul_zero])⟩
    · exact absurd rfl h
  have haS'ne : ∀ v c e P, aS' v c e P ≠ 0 → ∃ h : e ∈ G.inc v, aSC v c ⟨e, h⟩ P ≠ 0 := by
    intro v c e P h
    simp only [aS'] at h
    split_ifs at h with he
    · exact ⟨he, fun h0 => h (by rw [h0, mul_zero])⟩
    · exact absurd rfl h
  -- the fraction at the chosen label is at most `y`
  have hAle : ∀ v c e, v ∈ G.ends e → ∀ P, ∑ i, aL' v c e P i + aS' v c e P ≤ y e c := by
    intro v c e hv P
    rw [← hmarg' v c e hv]
    exact Finset.single_le_sum (f := fun P => ∑ i, aL' v c e P i + aS' v c e P)
      (fun P _ => add_nonneg (Finset.sum_nonneg (fun i _ => haL'0 v c e P i)) (haS'0 v c e P))
      (Finset.mem_univ P)
  have hsrc_mem : ∀ e, src e ∈ G.ends e := fun e => by rw [hst e]; exact Sym2.mem_mk_left _ _
  have htgt_mem : ∀ e, tgt e ∈ G.ends e := fun e => by rw [hst e]; exact Sym2.mem_mk_right _ _
  refine ⟨fun v c i => bC v c (Pc v c) i, fun v c => RC v c (Pc v c),
    fun e c i j => XL0 e c i j / max 1 (Sm e), fun e c => XS0 e c / max 1 (Sm e),
    fun v c => ⟨(hval v c (Pc v c)).1, (hval v c (Pc v c)).2.1, (hval v c (Pc v c)).2.2,
      hRr' v c (Pc v c)⟩,
    fun e c i j => div_nonneg (hXL00 e c i j) (hfpos e).le,
    fun e c => div_nonneg (hXS00 e c) (hfpos e).le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- compatibility of large options
    intro e c i j h
    have h' : XL0 e c i j ≠ 0 := fun h0 => h (by show XL0 e c i j / max 1 (Sm e) = 0; rw [h0, zero_div])
    rw [hXL0] at h'
    have hn := (div_ne_zero_iff.mp h').1
    obtain ⟨hs, h1⟩ := haL'ne _ _ _ _ _ (left_ne_zero_of_mul hn)
    obtain ⟨ht', h2⟩ := haL'ne _ _ _ _ _ (right_ne_zero_of_mul hn)
    have c1 := htypL (src e) c ⟨e, hs⟩ (Pc (src e) c) i h1
    have c2 := htypL (tgt e) c ⟨e, ht'⟩ (Pc (tgt e) c) j h2
    exact ⟨c1.1, c1.2, c2.2⟩
  · -- compatibility of small options
    intro e c h
    have h' : XS0 e c ≠ 0 := fun h0 => h (by show XS0 e c / max 1 (Sm e) = 0; rw [h0, zero_div])
    rw [hXS0] at h'
    have hn := (div_ne_zero_iff.mp h').1
    obtain ⟨hs, h1⟩ := haS'ne _ _ _ _ (left_ne_zero_of_mul hn)
    obtain ⟨ht', h2⟩ := haS'ne _ _ _ _ (right_ne_zero_of_mul hn)
    have c1 := htypS (src e) c ⟨e, hs⟩ (Pc (src e) c) h1
    have c2 := htypS (tgt e) c ⟨e, ht'⟩ (Pc (tgt e) c) h2
    exact ⟨c1.1, c1.2, c2.2⟩
  · -- total at most one
    intro e
    have : ∑ c, (∑ i, ∑ j, XL0 e c i j / max 1 (Sm e) + XS0 e c / max 1 (Sm e))
        = Sm e / max 1 (Sm e) := by
      rw [hSm, Finset.sum_div]
      apply Finset.sum_congr rfl; intro c _
      rw [add_div, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_div]
    rw [this, div_le_one (hfpos e)]
    exact le_max_right _ _
  · -- small fractions per color
    intro e c
    have h1 : ∑ i, ∑ j, XL0 e c i j / max 1 (Sm e) + XS0 e c / max 1 (Sm e)
        ≤ ∑ i, ∑ j, XL0 e c i j + XS0 e c := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hdivle e _ (hXL00 e c i j)))
      · exact hdivle e _ (hXS00 e c)
    refine le_trans h1 ?_
    set u := src e
    set v := tgt e
    set Pu := Pc u c
    set Pv := Pc v c
    have hu := hAle u c e (hsrc_mem e) Pu
    have hv := hAle v c e (htgt_mem e) Pv
    have hsum : ∑ i, ∑ j, XL0 e c i j + XS0 e c =
        ((∑ i, aL' u c e Pu i) * (∑ j, aL' v c e Pv j) + aS' u c e Pu * aS' v c e Pv) /
          (y e c * lam' u c Pu * lam' v c Pv) := by
      simp only [hXL0, hXS0]
      rw [add_div, Finset.sum_mul_sum, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_div]
    rw [hsum]
    have hA0 : 0 ≤ ∑ i, aL' u c e Pu i := Finset.sum_nonneg (fun i _ => haL'0 _ _ _ _ _)
    have hB0 : 0 ≤ ∑ j, aL' v c e Pv j := Finset.sum_nonneg (fun j _ => haL'0 _ _ _ _ _)
    have hS1 := haS'0 u c e Pu
    have hS2 := haS'0 v c e Pv
    have hnum : (∑ i, aL' u c e Pu i) * (∑ j, aL' v c e Pv j) + aS' u c e Pu * aS' v c e Pv
        ≤ y e c * y e c := by
      have := mul_le_mul hu hv (add_nonneg hB0 hS2) (hy e c).1
      nlinarith only [this, hA0, hB0, hS1, hS2]
    rcases (hy e c).1.lt_or_eq with hy0 | hy0
    · have hlu := hlam'lo u c Pu
      have hlv := hlam'lo v c Pv
      have hM0 := hMpos u c
      have htM : 0 < t / M := div_pos ht0 hM0
      calc ((∑ i, aL' u c e Pu i) * (∑ j, aL' v c e Pv j) + aS' u c e Pu * aS' v c e Pv) /
            (y e c * lam' u c Pu * lam' v c Pv)
          ≤ (y e c * y e c) / (y e c * (t / M) * (t / M)) := by
            apply div_le_div₀ (by positivity) hnum (by positivity)
            have := mul_le_mul hlu hlv htM.le (hlam'pos u c Pu).le
            have h2 := mul_le_mul_of_nonneg_left this hy0.le
            linarith [h2]
        _ = y e c * ((M : ℝ) / t) ^ 2 := by field_simp
        _ ≤ C₀ / n * ((M : ℝ) / t) ^ 2 := mul_le_mul_of_nonneg_right (hy e c).2 (by positivity)
        _ ≤ Cm / n := by
            rw [hCm, add_div]
            have : C₀ / n * ((M : ℝ) / t) ^ 2 = C₀ * ((M : ℝ) / t) ^ 2 / n := by ring
            rw [this]
            have : (0 : ℝ) ≤ 1 / n := by positivity
            linarith
    · rw [← hy0]; simp only [zero_mul, div_zero]; positivity
  · -- slot slack
    intro v c i
    refine le_trans ?_ (hload v c i)
    apply add_le_add
    · exact Finset.sum_le_sum (fun e _ => Finset.sum_le_sum (fun j _ => hdivle e _ (hXL00 e c i j)))
    · exact Finset.sum_le_sum (fun e _ => Finset.sum_le_sum (fun j _ => hdivle e _ (hXL00 e c j i)))
  · -- reserve slack
    intro v c
    refine le_trans ?_ (hres v c)
    apply Finset.sum_le_sum; intro e _
    exact mul_le_mul_of_nonneg_left (hdivle e _ (hXS00 e c)) (G.w_pos e).le
  · -- support
    intro e c h
    by_contra hx0
    have hxz : x e c = 0 := le_antisymm (not_lt.mp hx0) (hx e c).1
    have hyz : y e c = 0 := by simp only [y, hxz, mul_zero]
    apply h
    have h1 : ∀ i j, XL0 e c i j = 0 := fun i j => by rw [hXL0, hyz]; simp
    have h2 : XS0 e c = 0 := by rw [hXS0, hyz]; simp
    simp [h1, h2]
  · -- almost no weight is lost
    intro v
    have hs : ∀ e, ∑ c, (∑ i, ∑ j, XL0 e c i j / max 1 (Sm e) + XS0 e c / max 1 (Sm e))
        = Sm e / max 1 (Sm e) := by
      intro e
      rw [hSm, Finset.sum_div]
      apply Finset.sum_congr rfl; intro c _
      rw [add_div, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_div]
    simp_rw [hs]
    have hd := hdisc v
    simp_rw [← hSm] at hd
    have hμ : ∀ e, ∑ c, y e c = ρ * (1 - t) * ∑ c, x e c := by
      intro e; simp only [y]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring
    have hμ1 : ∀ e, ∑ c, y e c ≤ 1 := by
      intro e
      rw [hμ e]
      have h1 : ρ * (1 - t) ≤ 1 := by
        have h2 := mul_le_mul_of_nonneg_right hρ1 (by linarith : (0 : ℝ) ≤ 1 - t)
        nlinarith only [h2, ht8, ht0]
      have h3 := hxs e
      have h4 : 0 ≤ ∑ c, x e c := Finset.sum_nonneg (fun c _ => (hx e c).1)
      have h5 : 0 ≤ ρ * (1 - t) := mul_nonneg hρ0.le (by linarith)
      nlinarith only [h1, h3, h4, h5]
    have hpt : ∀ e, ∑ c, y e c - |Sm e - ∑ c, y e c| ≤ Sm e / max 1 (Sm e) := by
      intro e
      rcases le_total (Sm e) 1 with h | h
      · rw [max_eq_left h, div_one]
        have := neg_abs_le (Sm e - ∑ c, y e c)
        linarith
      · rw [max_eq_right h, div_self (by linarith)]
        have := abs_nonneg (Sm e - ∑ c, y e c)
        linarith [hμ1 e]
    have hsum1 : ∑ e ∈ G.inc v, G.w e * (∑ c, y e c) - K * n ^ (3 / 4 : ℝ)
        ≤ ∑ e ∈ G.inc v, G.w e * (Sm e / max 1 (Sm e)) := by
      have : ∑ e ∈ G.inc v, G.w e * (∑ c, y e c - |Sm e - ∑ c, y e c|)
          ≤ ∑ e ∈ G.inc v, G.w e * (Sm e / max 1 (Sm e)) :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hpt e) (G.w_pos e).le)
      have h2 : ∑ e ∈ G.inc v, G.w e * (∑ c, y e c - |Sm e - ∑ c, y e c|)
          = ∑ e ∈ G.inc v, G.w e * (∑ c, y e c) - ∑ e ∈ G.inc v, G.w e * |Sm e - ∑ c, y e c| := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro e _; ring
      linarith
    have hT : ∑ e ∈ G.inc v, G.w e * (∑ c, y e c)
        = ρ * (1 - t) * ∑ e ∈ G.inc v, G.w e * ∑ c, x e c := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; rw [hμ e]; ring
    have hT0 : 0 ≤ ∑ e ∈ G.inc v, G.w e * ∑ c, x e c :=
      Finset.sum_nonneg (fun e _ => mul_nonneg (G.w_pos e).le
        (Finset.sum_nonneg (fun c _ => (hx e c).1)))
    have hTn : ∑ e ∈ G.inc v, G.w e * ∑ c, x e c ≤ n := by
      refine le_trans ?_ (hW v)
      unfold WGraph.W
      apply Finset.sum_le_sum; intro e _
      exact mul_le_of_le_one_right (G.w_pos e).le (hxs e)
    have hloss : (1 - ρ * (1 - t)) ≤ ε := by
      rw [hρ]
      have : 1 - (1 - t) * (1 - t) * (1 - t) ≤ 3 * t := by
        have h1 : t * t * (t - 3) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        have e : 1 - (1 - t) * (1 - t) * (1 - t) - 3 * t = t * t * (t - 3) := by ring
        linarith
      linarith
    have hloss' : (1 - ρ * (1 - t)) * ∑ e ∈ G.inc v, G.w e * ∑ c, x e c ≤ ε * n := by
      have h0 : 0 ≤ 1 - ρ * (1 - t) := by
        have h2 := mul_le_mul_of_nonneg_right hρ1 (by linarith : (0 : ℝ) ≤ 1 - t)
        nlinarith only [h2, ht8, ht0]
      calc (1 - ρ * (1 - t)) * ∑ e ∈ G.inc v, G.w e * ∑ c, x e c ≤ ε * ∑ e ∈ G.inc v, G.w e * ∑ c, x e c :=
            mul_le_mul_of_nonneg_right hloss hT0
        _ ≤ ε * n := mul_le_mul_of_nonneg_left hTn hε.le
    rw [hT] at hsum1
    nlinarith only [hsum1, hloss']
