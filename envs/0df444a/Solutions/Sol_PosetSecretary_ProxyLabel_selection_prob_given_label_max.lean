-- Prove2me | solution 1 for PosetSecretary.ProxyLabel.selection_prob_given_label_max
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:28:46.081773+00:00
-- url     : https://prove2.me/submissions/42548554-4547-4afa-b281-998c2840b1bb

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting

namespace PSDisplay3Aux

open Finset

/-- the sample set of the first `m` arrivals -/
def sampleSet {α : Type*} [Fintype α] [DecidableEq α] (pos : α ≃ Fin (Fintype.card α)) (m : ℕ) :
    Finset α := univ.filter (fun x => (pos x : ℕ) < m)

lemma card_sampleSet {α : Type*} [Fintype α] [DecidableEq α] (pos : α ≃ Fin (Fintype.card α))
    (m : ℕ) (hm : m ≤ Fintype.card α) : (sampleSet pos m).card = m := by
  unfold sampleSet
  have : (univ.filter (fun x => (pos x : ℕ) < m)) =
      (univ.filter (fun i : Fin (Fintype.card α) => (i : ℕ) < m)).map pos.symm.toEmbedding := by
    ext x; simp
  rw [this, card_map, Fin.card_filter_val_lt]; omega

lemma exists_perm_of_card_eq {α : Type*} [Fintype α] [DecidableEq α] (F F' : Finset α)
    (h : F.card = F'.card) : ∃ σ : Equiv.Perm α, ∀ x, σ x ∈ F' ↔ x ∈ F := by
  have e : {x // x ∈ F} ≃ {x // x ∈ F'} := Fintype.equivOfCardEq (by simpa using h)
  have f : {x // ¬ x ∈ F} ≃ {x // ¬ x ∈ F'} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp only [Fintype.card_coe]; rw [h])
  refine ⟨Equiv.subtypeCongr e f, fun x => ?_⟩
  by_cases hx : x ∈ F
  · have : Equiv.subtypeCongr e f x = e ⟨x, hx⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]
    rw [this]; simp [hx]
  · have : Equiv.subtypeCongr e f x = f ⟨x, hx⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]
    rw [this]; simp only [hx, iff_false]; exact (f ⟨x, hx⟩).2

lemma fiber_card_eq {α : Type*} [Fintype α] [DecidableEq α] (m : ℕ) (F F' : Finset α)
    (h : F.card = F'.card) :
    (univ.filter (fun pos : α ≃ Fin (Fintype.card α) => sampleSet pos m = F)).card =
      (univ.filter (fun pos : α ≃ Fin (Fintype.card α) => sampleSet pos m = F')).card := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_card_eq F F' h
  refine Finset.card_bij' (fun pos _ => σ.symm.trans pos) (fun pos _ => σ.trans pos) ?_ ?_ ?_ ?_
  · intro pos hpos
    simp only [mem_filter, mem_univ, true_and] at hpos ⊢
    ext x
    have := hσ (σ.symm x)
    simp only [Equiv.apply_symm_apply] at this
    rw [this, ← hpos]; simp only [sampleSet, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  · intro pos hpos
    simp only [mem_filter, mem_univ, true_and] at hpos ⊢
    ext x
    rw [← hσ x, ← hpos]; simp only [sampleSet, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  · intro pos _; ext x; simp
  · intro pos _; ext x; simp

lemma fiber_card_mul {α : Type*} [Fintype α] [DecidableEq α] (m : ℕ)
    (hm : m ≤ Fintype.card α) (F : Finset α) (hF : F.card = m) :
    ((Fintype.card α).choose m) *
      (univ.filter (fun pos : α ≃ Fin (Fintype.card α) => sampleSet pos m = F)).card =
      (Fintype.card α).factorial := by
  have htot := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (α ≃ Fin (Fintype.card α))))
    (t := univ.filter (fun G : Finset α => G.card = m)) (f := fun pos => sampleSet pos m)
    (by intro pos _; simp [card_sampleSet pos m hm])
  rw [Finset.sum_congr rfl (fun G hG => by
    simp only [mem_filter, mem_univ, true_and] at hG
    exact fiber_card_eq m G F (by rw [hG, hF]))] at htot
  rw [sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_equiv (Fintype.equivFin α)] at htot

  have : (univ.filter (fun G : Finset α => G.card = m)).card = (Fintype.card α).choose m := by
    rw [← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, card_powersetCard, card_univ]
  rw [this] at htot
  exact htot.symm

lemma avg_sample {α : Type*} [Fintype α] [DecidableEq α] (E : Finset α → Prop) [DecidablePred E]
    (p : ℝ) :
    ∑ pos : α ≃ Fin (Fintype.card α), ∑ m ∈ Finset.range (Fintype.card α + 1),
        (1 / ((Fintype.card α).factorial : ℝ)) *
          (((Fintype.card α).choose m : ℝ) * p ^ m * (1 - p) ^ (Fintype.card α - m)) *
            (if E (sampleSet pos m) then 1 else 0)
      = ∑ F : Finset α, p ^ F.card * (1 - p) ^ (Fintype.card α - F.card) *
            (if E F then 1 else 0) := by
  set N := Fintype.card α
  set cnt : ℕ → Finset α → ℕ := fun m F =>
    (univ.filter (fun pos : α ≃ Fin N => sampleSet pos m = F)).card with hcnt
  rw [Finset.sum_comm]
  have h1 : ∀ m, ∑ pos : α ≃ Fin N, (1 / (N.factorial : ℝ)) *
          ((N.choose m : ℝ) * p ^ m * (1 - p) ^ (N - m)) *
            (if E (sampleSet pos m) then 1 else 0)
      = ∑ F : Finset α, (cnt m F : ℝ) * ((1 / (N.factorial : ℝ)) *
          ((N.choose m : ℝ) * p ^ m * (1 - p) ^ (N - m)) * (if E F then 1 else 0)) := by
    intro m
    rw [← Finset.sum_fiberwise' (s := (univ : Finset (α ≃ Fin N)))
      (g := fun pos => sampleSet pos m)
      (f := fun F => (1 / (N.factorial : ℝ)) *
          ((N.choose m : ℝ) * p ^ m * (1 - p) ^ (N - m)) * (if E F then 1 else 0))]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun m _ => h1 m)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  have hFN : F.card ≤ N := by
    have := Finset.card_le_card (Finset.subset_univ F); rwa [Finset.card_univ] at this
  rw [Finset.sum_eq_single_of_mem F.card (by simp; omega)]
  · have hmul := fiber_card_mul F.card hFN F rfl
    have hmulR : ((N.choose F.card : ℕ) : ℝ) * (cnt F.card F : ℝ) = (N.factorial : ℝ) := by
      exact_mod_cast hmul
    have hf : (N.factorial : ℝ) ≠ 0 := by positivity
    calc (cnt F.card F : ℝ) * ((1 / (N.factorial : ℝ)) *
          ((N.choose F.card : ℝ) * p ^ F.card * (1 - p) ^ (N - F.card)) * (if E F then 1 else 0))
        = (((N.choose F.card : ℕ) : ℝ) * (cnt F.card F : ℝ)) / (N.factorial : ℝ) *
          (p ^ F.card * (1 - p) ^ (N - F.card) * (if E F then 1 else 0)) := by ring
      _ = _ := by rw [hmulR, div_self hf, one_mul]
  · intro m hmr hm
    have hle : m ≤ N := by simp at hmr; omega
    have : cnt m F = 0 := by
      simp only [hcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
        true_implies]
      intro pos hpos
      exact hm (by rw [← hpos, card_sampleSet pos m hle])
    rw [this]; simp

lemma subset_sum {α : Type*} [Fintype α] [DecidableEq α] (a : α) (M : Finset α) (haM : a ∉ M)
    (p : ℝ) :
    ∑ F : Finset α, p ^ F.card * (1 - p) ^ (Fintype.card α - F.card) *
        (if a ∉ F ∧ M ⊆ F then 1 else 0) = (1 - p) * p ^ M.card := by
  set N := Fintype.card α
  set R := univ \ insert a M with hR
  have hRcard : R.card + M.card + 1 = N := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (insert a M))
    rw [Finset.card_insert_of_notMem haM, Finset.card_univ] at h1
    rw [hR]; omega
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hbij : ∑ F ∈ univ.filter (fun F : Finset α => a ∉ F ∧ M ⊆ F),
      p ^ F.card * (1 - p) ^ (N - F.card) =
      ∑ G ∈ R.powerset, p ^ (G ∪ M).card * (1 - p) ^ (N - (G ∪ M).card) := by
    refine Finset.sum_bij' (fun F _ => F \ M) (fun G _ => G ∪ M) ?_ ?_ ?_ ?_ ?_
    · intro F hF
      simp only [mem_filter, mem_univ, true_and] at hF
      simp only [mem_powerset, hR]
      intro x hx
      simp only [mem_sdiff] at hx
      simp only [mem_sdiff, mem_univ, mem_insert, true_and, not_or]
      exact ⟨fun h => hF.1 (h ▸ hx.1), hx.2⟩
    · intro G hG
      simp only [mem_powerset, hR] at hG
      simp only [mem_filter, mem_univ, true_and, mem_union, not_or]
      refine ⟨⟨fun h => ?_, haM⟩, subset_union_right⟩
      have := hG h; simp at this
    · intro F hF
      simp only [mem_filter, mem_univ, true_and] at hF
      exact Finset.sdiff_union_of_subset hF.2
    · intro G hG
      simp only [mem_powerset, hR] at hG
      ext x; simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact h
        · exact absurd h h'
      · intro h; refine ⟨Or.inl h, fun hm => ?_⟩
        have := hG h; simp [hm] at this
    · intro F hF
      simp only [mem_filter, mem_univ, true_and] at hF
      rw [Finset.sdiff_union_of_subset hF.2]
  rw [hbij]
  have hcard : ∀ G ∈ R.powerset, (G ∪ M).card = G.card + M.card := by
    intro G hG
    simp only [mem_powerset, hR] at hG
    apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_left]
    intro x hx hm
    have := hG hx; simp [hm] at this
  have hterm : ∀ G ∈ R.powerset, p ^ (G ∪ M).card * (1 - p) ^ (N - (G ∪ M).card) =
      ((1 - p) * p ^ M.card) * (p ^ G.card * (1 - p) ^ (R.card - G.card)) := by
    intro G hG
    rw [hcard G hG]
    have hGR : G.card ≤ R.card := Finset.card_le_card (mem_powerset.1 hG)
    have : N - (G.card + M.card) = (R.card - G.card) + 1 := by omega
    rw [this, pow_add, pow_add, pow_one]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]
  simp

end PSDisplay3Aux

open PosetSecretary.ProxyLabel PSDisplay3Aux Finset

theorem solution {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : IsConsistentScoring w) (k : ℕ) (hk : 1 ≤ k) (ω' : ℕ) (a : α)
    (ℓ : α → Fin k) (hmax : ∀ b, w a < w b → ℓ b ≠ ℓ a) :
    (1 / (ω' + 1 : ℝ)) * (1 - 1 / (ω' + 1 : ℝ)) ^ AppliedComb.Posets.width α ≤
      ∑ pos : α ≃ Fin (Fintype.card α), ∑ m ∈ Finset.range (Fintype.card α + 1),
        (1 / ((Fintype.card α).factorial : ℝ)) *
          binomWeight (Fintype.card α) m (sampleProb ω') *
            (if a ∈ selected pos ℓ m then 1 else 0) := by
  classical
  obtain ⟨hw0, hinj, hmono⟩ := hw
  set N := Fintype.card α
  set p := sampleProb ω' with hp
  set X' := univ.filter (fun b => ℓ b = ℓ a ∧ b ≠ a) with hX'
  set M := X'.filter (fun b => ∀ c ∈ X', ¬ b < c) with hM
  have haM : a ∉ M := by simp [hM, hX']
  have hanti : IsAntichain (· ≤ ·) (M : Set α) := by
    intro b hb c hc hbc hle
    simp only [coe_filter, Set.mem_ofPred_eq, hM] at hb hc
    exact hb.2 c hc.1 (lt_of_le_of_ne hle hbc)
  have hMw : M.card ≤ AppliedComb.Posets.width α := by
    unfold AppliedComb.Posets.width
    exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨mem_univ _, hanti⟩)
  have hdom : ∀ b ∈ X', b ∉ M → ∃ c ∈ M, b < c := by
    intro b hb hbM
    have hne : (X'.filter (fun c => b < c)).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
      exact hbM (by simp only [hM, mem_filter]; exact ⟨hb, hcon⟩)
    obtain ⟨c, hc, hcmax⟩ := Finset.exists_max_image _ w hne
    simp only [mem_filter] at hc
    refine ⟨c, ?_, hc.2⟩
    simp only [hM, mem_filter]
    refine ⟨hc.1, fun d hd hcd => ?_⟩
    have := hcmax d (by simp only [mem_filter]; exact ⟨hd, lt_trans hc.2 hcd⟩)
    have := hmono c d hcd
    linarith
  have himp : ∀ (pos : α ≃ Fin N) (m : ℕ), a ∉ sampleSet pos m → M ⊆ sampleSet pos m →
      a ∈ selected pos ℓ m := by
    intro pos m haS hMS
    simp only [sampleSet, mem_filter, mem_univ, true_and, not_lt] at haS
    simp only [selected, mem_filter, mem_univ, true_and]
    refine ⟨haS, ?_, ?_⟩
    · intro b hb _ hab
      exact hmax b (hmono a b hab) hb
    · intro b hb hmb hba hpass
      have hbX : b ∈ X' := by
        simp only [hX', mem_filter, mem_univ, true_and]
        exact ⟨hb, fun h => by subst h; exact lt_irrefl _ hba⟩
      have hbM : b ∉ M := by
        intro h
        have := hMS h
        simp only [sampleSet, mem_filter, mem_univ, true_and] at this
        omega
      obtain ⟨c, hcM, hbc⟩ := hdom b hbX hbM
      have hcS := hMS hcM
      simp only [sampleSet, mem_filter, mem_univ, true_and] at hcS
      have hcX : c ∈ X' := (mem_filter.1 hcM).1
      simp only [hX', mem_filter, mem_univ, true_and] at hcX
      exact hpass c (by rw [hcX.1, hb]) (by
        show (pos c : ℕ) < pos b; omega) hbc
  have hp0 : 0 ≤ p := by rw [hp]; unfold sampleProb; positivity
  have hp1 : p ≤ 1 := by
    rw [hp]; unfold sampleProb; rw [div_le_one (by positivity)]; linarith
  have hq : 1 - p = 1 / (ω' + 1 : ℝ) := by
    rw [hp]; unfold sampleProb; field_simp; ring
  have hB : ∀ m, 0 ≤ binomWeight N m p := by
    intro m; unfold binomWeight
    have : 0 ≤ 1 - p := by linarith
    positivity
  have hlow : ∑ pos : α ≃ Fin N, ∑ m ∈ Finset.range (N + 1),
        (1 / (N.factorial : ℝ)) * binomWeight N m p *
          (if (a ∉ sampleSet pos m ∧ M ⊆ sampleSet pos m) then 1 else 0) ≤
      ∑ pos : α ≃ Fin N, ∑ m ∈ Finset.range (N + 1),
        (1 / (N.factorial : ℝ)) * binomWeight N m p *
          (if a ∈ selected pos ℓ m then 1 else 0) := by
    refine Finset.sum_le_sum fun pos _ => Finset.sum_le_sum fun m _ => ?_
    have hw' : 0 ≤ (1 / (N.factorial : ℝ)) * binomWeight N m p := by
      have := hB m; positivity
    apply mul_le_mul_of_nonneg_left _ hw'
    split_ifs with h1 h2
    · exact le_refl _
    · exact absurd (himp pos m h1.1 h1.2) h2
    · exact zero_le_one
    · exact le_refl _
  have heq := avg_sample (fun F : Finset α => a ∉ F ∧ M ⊆ F) p
  rw [subset_sum a M haM p] at heq
  unfold binomWeight at hlow
  rw [heq] at hlow
  refine le_trans ?_ hlow
  rw [hq.symm, sub_sub_cancel]
  apply mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp0 hp1 hMw)
  linarith
