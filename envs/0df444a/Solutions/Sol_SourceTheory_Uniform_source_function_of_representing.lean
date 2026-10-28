-- Prove2me | solution 1 for SourceTheory.Uniform.source_function_of_representing
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:25:52.196984+00:00
-- url     : https://prove2.me/submissions/a91eb43d-baa3-430d-a4b3-aa566e301e33

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.Uniform.SFRAux

open MeasureTheory

section bets

variable {S Γ : Type*}

lemma bet_act {𝒜 : Set (Set S)} (h𝒜 : IsSetAlgebra 𝒜) {α β : Γ} (hab : α ≠ β) {E : Set S}
    (hE : E ∈ 𝒜) : IsActFrom 𝒜 (bet α E β) := by
  refine ⟨Set.Finite.subset (Set.toFinite {α, β}) ?_, fun γ => ?_⟩
  · rintro _ ⟨s, rfl⟩
    unfold bet; split_ifs <;> simp
  · by_cases hγα : γ = α
    · subst hγα
      have : bet γ E β ⁻¹' {γ} = E := by
        ext s; simp only [mem_preimage, mem_singleton_iff, bet]
        split_ifs with hs
        · simp [hs]
        · simp [hs, Ne.symm hab]
      rw [this]; exact hE
    · by_cases hγβ : γ = β
      · subst hγβ
        have : bet α E γ ⁻¹' {γ} = Eᶜ := by
          ext s; simp only [mem_preimage, mem_singleton_iff, bet, mem_compl_iff]
          split_ifs with hs
          · simp [hs, hab]
          · simp [hs]
        rw [this]; exact h𝒜.compl_mem hE
      · have : bet α E β ⁻¹' {γ} = ∅ := by
          ext s; simp only [mem_preimage, mem_singleton_iff, bet, mem_empty_iff_false, iff_false]
          split_ifs
          · exact fun h => hγα h.symm
          · exact fun h => hγβ h.symm
        rw [this]; exact h𝒜.empty_mem

end bets

section main

variable {S Γ : Type*} {𝓔 : Set (Set S)} {pref : (S → Γ) → (S → Γ) → Prop} {U : Γ → ℝ}
  {W : Set S → ℝ} (h1 : Assumption1 𝓔 pref U W) {𝒮 : Set (Set S)} (h𝒮 : IsSource 𝓔 W 𝒮)
  {P : Set S → ℝ} (hP : IsProbOn 𝒮 P ∧ ∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A) {α β : Γ} (hUab : U β < U α)

include h1 hUab in
lemma bet_pref_iff {E F : Set S} (hE : E ∈ 𝓔) (hF : F ∈ 𝓔) :
    pref (bet α E β) (bet α F β) ↔ W F ≤ W E := by
  rw [h1.biseparable α β α β E hE F hF hUab.le hUab.le]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hUab)]
  · intro h
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_pos.2 hUab).le]

include hUab in
lemma ne_ab : α ≠ β := fun h => by rw [h] at hUab; exact lt_irrefl _ hUab

include h𝒮 hP in
lemma P_empty : P ∅ = 0 := by
  have := hP.1.2.2 ∅ h𝒮.algebra.empty_mem ∅ h𝒮.algebra.empty_mem (disjoint_empty _)
  rw [empty_union] at this; linarith

include h𝒮 hP in
lemma P_diff {F K : Set S} (hF : F ∈ 𝒮) (hK : K ∈ 𝒮) (hKF : K ⊆ F) : P (F \ K) = P F - P K := by
  have hd : F \ K ∈ 𝒮 := h𝒮.algebra.sdiff_mem hF hK
  have := hP.1.2.2 (F \ K) hd K hK disjoint_sdiff_left
  rw [diff_union_of_subset hKF] at this; linarith

include h𝒮 hP in
lemma P_mono {F K : Set S} (hF : F ∈ 𝒮) (hK : K ∈ 𝒮) (hKF : K ⊆ F) : P K ≤ P F := by
  have := P_diff h𝒮 hP hF hK hKF
  have := hP.1.2.1 (F \ K) (h𝒮.algebra.sdiff_mem hF hK)
  linarith

include h1 h𝒮 hP hUab in
/-- Stochastic dominance on bets: `P E ≤ P F ⇒ W E ≤ W F`. -/
lemma W_mono_P {E F : Set S} (hE : E ∈ 𝒮) (hF : F ∈ 𝒮) (h : P E ≤ P F) : W E ≤ W F :=
  (hP.2 F hF E hE).2 h

include h1 in
lemma W_nonneg {E : Set S} (hE : E ∈ 𝓔) : 0 ≤ W E := by
  have := h1.W_mono E hE ∅ h1.events.empty_mem (empty_subset _)
  rwa [h1.W_empty] at this

include h1 in
lemma W_le_one {E : Set S} (hE : E ∈ 𝓔) : W E ≤ 1 := by
  have := h1.W_mono univ h1.events.univ_mem E hE (subset_univ _)
  rwa [h1.W_univ] at this

include h1 h𝒮 in
lemma exists_sub {F : Set S} (hF : F ∈ 𝒮) {μ : ℝ} (h0 : 0 ≤ μ) (hμ : μ ≤ W F) :
    ∃ K ∈ 𝒮, K ⊆ F ∧ W K = μ := by
  obtain ⟨K, hK, -, hKF, hW⟩ := h𝒮.convexRanged ∅ h𝒮.algebra.empty_mem F hF (empty_subset _) μ
    (by rw [h1.W_empty]; exact h0) hμ
  exact ⟨K, hK, hKF, hW⟩

include h1 h𝒮 hP hUab in
/-- Events with positive weight can have arbitrarily small probability (via the Archimedean
axiom). -/
lemma small_pos (d : ℝ) (hd : 0 < d) : ∃ G ∈ 𝒮, 0 < W G ∧ P G < d := by
  by_contra hcon
  push_neg at hcon
  set T : Set ℝ := {x | ∃ G ∈ 𝒮, 0 < W G ∧ P G = x} with hT
  have hTne : T.Nonempty := ⟨P univ, univ, h𝒮.algebra.univ_mem, by rw [h1.W_univ]; norm_num, rfl⟩
  have hTbdd : BddBelow T := ⟨d, by rintro _ ⟨G, hG, hW, rfl⟩; exact hcon G hG hW⟩
  set m := sInf T
  have hm : d ≤ m := le_csInf hTne (by rintro _ ⟨G, hG, hW, rfl⟩; exact hcon G hG hW)
  have hmT : ∀ G ∈ 𝒮, 0 < W G → m ≤ P G := fun G hG hW => csInf_le hTbdd ⟨G, hG, hW, rfl⟩
  obtain ⟨_, ⟨H1, hH1, hWH1, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hTne (show m < 2 * m by linarith)
  -- the halving chain
  let C := {H : Set S // H ∈ 𝒮 ∧ 0 < W H}
  have step : ∀ H : C, ∃ H' : C, H'.1 ⊆ H.1 ∧ W H'.1 = W H.1 / 2 := by
    intro H
    obtain ⟨K, hK, hKF, hW⟩ := exists_sub h1 h𝒮 H.2.1 (μ := W H.1 / 2) (by linarith [H.2.2])
      (by linarith [H.2.2])
    exact ⟨⟨K, hK, by rw [hW]; linarith [H.2.2]⟩, hKF, hW⟩
  choose next hnext using step
  let seq : ℕ → C := fun n => next^[n] ⟨H1, hH1, hWH1⟩
  have hseq_succ : ∀ n, seq (n + 1) = next (seq n) := fun n =>
    Function.iterate_succ_apply' next n _
  have hanti : Antitone (fun n => (seq n).1) := by
    refine antitone_nat_of_succ_le fun n => ?_
    show (seq (n+1)).1 ⊆ (seq n).1
    rw [hseq_succ]; exact (hnext _).1
  have hsub0 : ∀ n, (seq n).1 ⊆ H1 := fun n => hanti (Nat.zero_le n)
  let K : ℕ → Set S := fun n => (seq n).1 \ (seq (n + 1)).1
  have hKS : ∀ n, K n ∈ 𝒮 := fun n => h𝒮.algebra.sdiff_mem (seq n).2.1 (seq (n+1)).2.1
  have hWdrop : ∀ n, W (seq (n + 1)).1 < W (seq n).1 := by
    intro n; rw [hseq_succ, (hnext _).2]; linarith [(seq n).2.2]
  apply h1.archimedean
  refine ⟨K, fun n => h𝒮.subset (hKS n), ?_, ?_, ?_⟩
  · -- pairwise disjoint
    have key : ∀ i j, i < j → Disjoint (K i) (K j) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro s ⟨-, hs⟩ ⟨hsj, -⟩
      exact hs (hanti (Nat.succ_le_of_lt hij) hsj)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  · -- non-null
    intro n hN
    have hsub : (seq (n + 1)).1 ⊆ (seq n).1 := hanti (Nat.le_succ n)
    have hab := ne_ab hUab
    have := (hN (bet α (seq (n + 1)).1 β) (bet α (seq n).1 β)
      (bet_act h1.events hab (h𝒮.subset (seq (n+1)).2.1))
      (bet_act h1.events hab (h𝒮.subset (seq n).2.1)) (by
        intro s hs
        simp only [K, mem_diff, not_and, not_not] at hs
        unfold bet
        by_cases h' : s ∈ (seq n).1
        · simp [h', hs h']
        · have : s ∉ (seq (n + 1)).1 := fun h'' => h' (hsub h'')
          simp [h', this])).1
    rw [bet_pref_iff h1 hUab (h𝒮.subset (seq (n+1)).2.1) (h𝒮.subset (seq n).2.1)] at this
    linarith [hWdrop n]
  · -- all weights zero
    have hzero : ∀ n, W (K n) = 0 := by
      intro n
      rcases (W_nonneg h1 (h𝒮.subset (hKS n))).lt_or_eq with h | h
      · exfalso
        have h2 := hmT _ (hKS n) h
        have hPK : P (K n) = P (seq n).1 - P (seq (n+1)).1 :=
          P_diff h𝒮 hP (seq n).2.1 (seq (n+1)).2.1 (hanti (Nat.le_succ n))
        have h3 := hmT _ (seq (n+1)).2.1 (seq (n+1)).2.2
        have h4 := P_mono h𝒮 hP hH1 (seq n).2.1 (hsub0 n)
        linarith
      · exact h.symm
    intro i j; rw [hzero i, hzero j]

include h1 h𝒮 hP hUab in
lemma slice {F : Set S} (hF : F ∈ 𝒮) (hWF : 0 < W F) {d : ℝ} (hd : 0 < d) :
    ∃ K ∈ 𝒮, K ⊆ F ∧ 0 < W K ∧ P K < d := by
  obtain ⟨G, hG, hWG, hPG⟩ := small_pos h1 h𝒮 hP hUab d hd
  set μ := min (W G) (W F) / 2
  have hμ0 : 0 < μ := by simp only [μ]; positivity
  have hμG : μ < W G := by
    have := min_le_left (W G) (W F); simp only [μ]; linarith
  have hμF : μ ≤ W F := by
    have := min_le_right (W G) (W F); simp only [μ]; linarith
  obtain ⟨K, hK, hKF, hWK⟩ := exists_sub h1 h𝒮 hF hμ0.le hμF
  refine ⟨K, hK, hKF, hWK ▸ hμ0, ?_⟩
  by_contra hc
  push_neg at hc
  have := W_mono_P h1 h𝒮 hP hUab hG hK (by linarith)
  linarith

include h1 h𝒮 hP hUab in
/-- Strictness: `P E < P F ⇒ W E < W F` (strong monotonicity). -/
lemma W_strict {E F : Set S} (hE : E ∈ 𝒮) (hF : F ∈ 𝒮) (h : P E < P F) : W E < W F :=
  lt_of_not_ge fun hc => absurd ((hP.2 E hE F hF).1 hc) (not_le.2 h)

include h1 h𝒮 hP hUab in
lemma P_range {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : ∃ B ∈ 𝒮, P B = q := by
  have hPe := P_empty h𝒮 hP
  set T : Set ℝ := {x | ∃ E ∈ 𝒮, P E ≤ q ∧ W E = x}
  have hTne : T.Nonempty := ⟨W ∅, ∅, h𝒮.algebra.empty_mem, by rw [hPe]; exact hq.1, rfl⟩
  have hTbdd : BddAbove T := ⟨1, by
    rintro _ ⟨E, hE, -, rfl⟩; exact W_le_one h1 (h𝒮.subset hE)⟩
  set c := sSup T
  have hc0 : 0 ≤ c := by
    have := le_csSup hTbdd ⟨∅, h𝒮.algebra.empty_mem, by rw [hPe]; exact hq.1, rfl⟩
    rw [h1.W_empty] at this; exact this
  have hc1 : c ≤ 1 := csSup_le hTne (by
    rintro _ ⟨E, hE, -, rfl⟩; exact W_le_one h1 (h𝒮.subset hE))
  obtain ⟨B, hB, -, hWBc⟩ := exists_sub h1 h𝒮 h𝒮.algebra.univ_mem hc0 (by rw [h1.W_univ]; exact hc1)
  refine ⟨B, hB, ?_⟩
  rcases lt_trichotomy (P B) q with hlt | heq | hgt
  · exfalso
    have hBc : Bᶜ ∈ 𝒮 := h𝒮.algebra.compl_mem hB
    have hPBc : P Bᶜ = 1 - P B := by
      have := hP.1.2.2 B hB Bᶜ hBc disjoint_compl_right
      rw [union_compl_self, hP.1.1] at this; linarith
    have hWBc0 : 0 < W Bᶜ := by
      have := W_strict h1 h𝒮 hP hUab h𝒮.algebra.empty_mem hBc (by rw [hPe, hPBc]; linarith [hq.2])
      rwa [h1.W_empty] at this
    obtain ⟨K, hK, hKB, hWK, hPK⟩ := slice h1 h𝒮 hP hUab hBc hWBc0 (show 0 < q - P B by linarith)
    have hPK0 : 0 < P K := by
      by_contra hc; push_neg at hc
      have := W_mono_P h1 h𝒮 hP hUab hK h𝒮.algebra.empty_mem (by rw [hPe]; exact hc)
      rw [h1.W_empty] at this; linarith
    have hEU : B ∪ K ∈ 𝒮 := h𝒮.algebra.union_mem hB hK
    have hdisj : Disjoint B K := Set.disjoint_left.mpr fun s hs hs' => hKB hs' hs
    have hPE : P (B ∪ K) = P B + P K := hP.1.2.2 B hB K hK hdisj
    have h1' : W B < W (B ∪ K) := W_strict h1 h𝒮 hP hUab hB hEU (by linarith)
    have h2' : W (B ∪ K) ≤ c := le_csSup hTbdd ⟨B ∪ K, hEU, by linarith, rfl⟩
    linarith
  · exact heq
  · exfalso
    have hWB0 : 0 < W B := by
      have := W_strict h1 h𝒮 hP hUab h𝒮.algebra.empty_mem hB (by rw [hPe]; linarith [hq.1])
      rwa [h1.W_empty] at this
    obtain ⟨K, hK, hKB, hWK, hPK⟩ := slice h1 h𝒮 hP hUab hB hWB0 (show 0 < P B - q by linarith)
    have hPK0 : 0 < P K := by
      by_contra hc; push_neg at hc
      have := W_mono_P h1 h𝒮 hP hUab hK h𝒮.algebra.empty_mem (by rw [hPe]; exact hc)
      rw [h1.W_empty] at this; linarith
    have hE : B \ K ∈ 𝒮 := h𝒮.algebra.sdiff_mem hB hK
    have hPE : P (B \ K) = P B - P K := P_diff h𝒮 hP hB hK hKB
    have hWE : W (B \ K) < c := hWBc ▸ W_strict h1 h𝒮 hP hUab hE hB (by linarith)
    obtain ⟨_, ⟨E', hE', hPE', rfl⟩, hlt'⟩ := exists_lt_of_lt_csSup hTne hWE
    have := W_mono_P h1 h𝒮 hP hUab hE' hE (by linarith)
    linarith

end main

end SourceTheory.Uniform.SFRAux

open SourceTheory.Uniform SourceTheory.Uniform.SFRAux in
theorem solution {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (h1 : Assumption1 𝓔 pref U W) (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮) (P : Set S → ℝ) (hP0 : IsProbOn 𝒮 P) (hrep : ∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A) :
    ∃ w : ℝ → ℝ, IsSourceFunction W 𝒮 P w := by
  classical
  have hP : IsProbOn 𝒮 P ∧ ∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A := ⟨hP0, hrep⟩
  obtain ⟨α, β, -, hUab, -⟩ := h1.three_outcomes
  have hPe := P_empty h𝒮 hP
  have hrange := fun q (hq : q ∈ Icc (0 : ℝ) 1) => P_range h1 h𝒮 hP hUab hq
  let w : ℝ → ℝ := fun p => if h : ∃ E ∈ 𝒮, P E = p then W (Classical.choose h) else p
  have hwE : ∀ E ∈ 𝒮, W E = w (P E) := by
    intro E hE
    have h : ∃ E' ∈ 𝒮, P E' = P E := ⟨E, hE, rfl⟩
    simp only [w, dif_pos h]
    obtain ⟨hE', hPE'⟩ := Classical.choose_spec h
    exact le_antisymm (W_mono_P h1 h𝒮 hP hUab hE hE' hPE'.ge)
      (W_mono_P h1 h𝒮 hP hUab hE' hE hPE'.le)
  have hPI : ∀ E ∈ 𝒮, P E ∈ Icc (0 : ℝ) 1 := by
    intro E hE
    refine ⟨hP.1.2.1 E hE, ?_⟩
    have := hP.1.2.2 E hE Eᶜ (h𝒮.algebra.compl_mem hE) disjoint_compl_right
    rw [union_compl_self, hP.1.1] at this
    linarith [hP.1.2.1 Eᶜ (h𝒮.algebra.compl_mem hE)]
  have hmaps : MapsTo w (Icc 0 1) (Icc 0 1) := by
    intro p hp
    obtain ⟨E, hE, rfl⟩ := hrange p hp
    rw [← hwE E hE]
    exact ⟨W_nonneg h1 (h𝒮.subset hE), W_le_one h1 (h𝒮.subset hE)⟩
  have hmono : StrictMonoOn w (Icc 0 1) := by
    intro p hp q hq hpq
    obtain ⟨E, hE, rfl⟩ := hrange p hp
    obtain ⟨F, hF, rfl⟩ := hrange q hq
    rw [← hwE E hE, ← hwE F hF]
    exact W_strict h1 h𝒮 hP hUab hE hF hpq
  have hw0 : w 0 = 0 := by
    have := hwE ∅ h𝒮.algebra.empty_mem
    rw [hPe, h1.W_empty] at this; exact this.symm
  have hw1 : w 1 = 1 := by
    have := hwE univ h𝒮.algebra.univ_mem
    rw [hP.1.1, h1.W_univ] at this; exact this.symm
  refine ⟨w, ⟨⟨hmaps, hmono, hw0, hw1⟩, ?_⟩, hwE⟩
  -- continuity: a strictly monotone surjection of `[0,1]` onto itself
  let f : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun x => ⟨w x, hmaps x.2⟩
  have hf : StrictMono f := fun x y hxy => hmono x.2 y.2 hxy
  have hsurj : Function.Surjective f := by
    rintro ⟨μ, hμ⟩
    obtain ⟨B, hB, -, -, hWB⟩ := h𝒮.convexRanged ∅ h𝒮.algebra.empty_mem univ
      h𝒮.algebra.univ_mem (empty_subset _) μ (by rw [h1.W_empty]; exact hμ.1)
      (by rw [h1.W_univ]; exact hμ.2)
    exact ⟨⟨P B, hPI B hB⟩, Subtype.ext (by simp only [f]; rw [← hwE B hB, hWB])⟩
  let e := StrictMono.orderIsoOfSurjective f hf hsurj
  rw [continuousOn_iff_continuous_domRestrict]
  have : (Icc (0 : ℝ) 1).domRestrict w = fun x => (e x : ℝ) := by
    funext x; rfl
  rw [this]
  exact continuous_subtype_val.comp e.continuous
