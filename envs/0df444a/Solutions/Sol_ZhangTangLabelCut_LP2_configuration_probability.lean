-- Prove2me | solution 1 for ZhangTangLabelCut.LP2.configuration_probability
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:28:27.305915+00:00
-- url     : https://prove2.me/submissions/f673e28a-3239-4fb7-88b4-dca498399865
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
import Definitions.Def_ZhangTangLabelCut_LP2_Shutter
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations
import Theorems.Thm_ZhangTangLabelCut_LP2_chain_separation_probability

open ZhangTangLabelCut.LP2

private lemma sum_counts_eq_card {k d : ℕ} (S : Finset (Fin k × Fin d)) :
    ∑ μ : Fin k, counts S μ = S.card := by
  classical
  unfold counts
  exact (Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := S) (t := Finset.univ)
    (fun x _ => Finset.mem_univ x.1)).symm

private lemma three_quarters_le_light_card {k d : ℕ} (hk : 2 ≤ k)
    (S : Finset (Fin k × Fin d)) (hc : 0 < S.card) :
    3 * (k : ℝ) / 4 ≤ ((light S).card : ℝ) := by
  classical
  let a := average k S.card
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have ha_pos : 0 < a := div_pos (by exact_mod_cast hc) hk_pos
  let heavy : Finset (Fin k) := Finset.univ \ light S
  have h_part : (light S).card + heavy.card = k := by
    have h_disj : Disjoint (light S) heavy := by
      rw [Finset.disjoint_left]
      intro μ h1 h2
      exact (Finset.mem_sdiff.mp h2).2 h1
    have h_union : light S ∪ heavy = Finset.univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ (light S))
    have h_card := (Finset.card_union_of_disjoint h_disj).symm
    rw [h_union, Finset.card_univ, Fintype.card_fin] at h_card
    exact h_card
  have h_heavy_le : (heavy.card : ℝ) ≤ (k : ℝ) / 4 := by
    by_contra h_gt
    have h_heavy_pos : 0 < heavy.card := by
      by_contra h_zero
      have h0 : heavy.card = 0 := by omega
      simp [h0] at h_gt
      linarith
    have h_nonempty : heavy.Nonempty := Finset.card_pos.mp h_heavy_pos
    have h_sum_lt :
        ∑ μ ∈ heavy, (4 * a) < ∑ μ ∈ heavy, (counts S μ : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty h_nonempty
      intro μ hμ
      simp only [heavy, light, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter,
        true_and, not_le] at hμ
      exact hμ
    have h_sum_le :
        ∑ μ ∈ heavy, (counts S μ : ℝ) ≤ ∑ μ : Fin k, (counts S μ : ℝ) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.cast_nonneg _)
    have h_sum_all : ∑ μ : Fin k, (counts S μ : ℝ) = (k : ℝ) * a := by
      have h_nat : (∑ μ : Fin k, (counts S μ : ℝ)) = (S.card : ℝ) := by
        exact_mod_cast sum_counts_eq_card S
      rw [h_nat]
      dsimp [a, average]
      rw [mul_div_cancel₀ _ (ne_of_gt hk_pos)]
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum_lt
    have h_comb : (heavy.card : ℝ) * (4 * a) < (k : ℝ) * a :=
      lt_of_lt_of_le h_sum_lt (le_trans h_sum_le (le_of_eq h_sum_all))
    nlinarith
  have h_part_real : ((light S).card : ℝ) + (heavy.card : ℝ) = (k : ℝ) := by
    exact_mod_cast h_part
  linarith

private lemma light_chains_card_ge {k d h : ℕ} (hk : 2 ≤ k)
    (S : Finset (Fin k × Fin d)) (hc : 0 < S.card) :
    (h : ℝ) / 2 * (3 * (k : ℝ) / 4) * (3 * (k : ℝ) / 4 - 1) ≤
      ((Finset.univ.filter
        (fun c : Chain k h => c.1.val.1 ∈ light S ∧ c.1.val.2 ∈ light S)).card : ℝ) := by
  classical
  let L₀ := light S
  let LP : Finset (Pair k) :=
    Finset.univ.filter (fun p : Pair k => p.val.1 ∈ L₀ ∧ p.val.2 ∈ L₀)
  let LC : Finset (Chain k h) :=
    Finset.univ.filter (fun c : Chain k h => c.1.val.1 ∈ L₀ ∧ c.1.val.2 ∈ L₀)
  let inj1 : L₀.offDiag → LP × Bool := fun xy =>
    have h_mem := Finset.mem_offDiag.mp xy.2
    if hlt : xy.1.1 < xy.1.2 then
      (⟨⟨(xy.1.1, xy.1.2), hlt⟩, by simp [LP, h_mem.1, h_mem.2.1]⟩, true)
    else
      (⟨⟨(xy.1.2, xy.1.1), lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h_mem.2.2)⟩,
        by simp [LP, h_mem.2.1, h_mem.1]⟩, false)
  have hinj1 : Function.Injective inj1 := by
    rintro ⟨⟨x₁, y₁⟩, hxy₁⟩ ⟨⟨x₂, y₂⟩, hxy₂⟩ h_eq
    by_cases h₁ : x₁ < y₁ <;> by_cases h₂ : x₂ < y₂
    · simp only [inj1, h₁, h₂, ↓reduceDIte, Prod.mk.injEq, Subtype.mk.injEq, and_true] at h_eq
      rcases h_eq with ⟨rfl, rfl⟩
      rfl
    · simp only [inj1, h₁, h₂, ↓reduceDIte, Prod.mk.injEq, reduceCtorEq, and_false] at h_eq
    · simp only [inj1, h₁, h₂, ↓reduceDIte, Prod.mk.injEq, reduceCtorEq, and_false] at h_eq
    · simp only [inj1, h₁, h₂, ↓reduceDIte, Prod.mk.injEq, Subtype.mk.injEq, and_true] at h_eq
      rcases h_eq with ⟨rfl, rfl⟩
      rfl
  have h_card1 := Fintype.card_le_of_injective inj1 hinj1
  simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool, Finset.offDiag_card] at h_card1
  let inj2 : LP × Fin h → LC := fun ⟨p, i⟩ =>
    ⟨(p.1, i), by
      have hp := p.2
      simp only [LP, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp⟩
  have hinj2 : Function.Injective inj2 := by
    rintro ⟨⟨p₁, hp₁⟩, i₁⟩ ⟨⟨p₂, hp₂⟩, i₂⟩ h_eq
    simp only [inj2, Subtype.mk.injEq, Prod.mk.injEq] at h_eq
    rcases h_eq with ⟨rfl, rfl⟩
    rfl
  have h_card2 := Fintype.card_le_of_injective inj2 hinj2
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at h_card2
  have h_nat_ineq : (L₀.card * L₀.card - L₀.card) * h ≤ 2 * LC.card := by
    nlinarith [h_card1, h_card2]
  have h_L₀_ge : 3 * (k : ℝ) / 4 ≤ (L₀.card : ℝ) :=
    three_quarters_le_light_card hk S hc
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h_L₀_ge_one_nat : 1 ≤ L₀.card := by
    have : (1 : ℝ) < (L₀.card : ℝ) := by linarith
    exact_mod_cast (le_of_lt this)
  have h_L₀_sq_ge : L₀.card ≤ L₀.card * L₀.card := Nat.le_mul_self L₀.card
  have h_real_ineq :
      ((L₀.card : ℝ) * (L₀.card : ℝ) - (L₀.card : ℝ)) * (h : ℝ) ≤ 2 * (LC.card : ℝ) := by
    have h_cast :
        (((L₀.card * L₀.card - L₀.card) * h : ℕ) : ℝ) ≤ ((2 * LC.card : ℕ) : ℝ) := by
      exact_mod_cast h_nat_ineq
    rw [Nat.cast_mul, Nat.cast_sub h_L₀_sq_ge, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat] at h_cast
    exact h_cast
  have h_quad_mono :
      (3 * (k : ℝ) / 4) * (3 * (k : ℝ) / 4 - 1) ≤ (L₀.card : ℝ) * ((L₀.card : ℝ) - 1) := by
    nlinarith [h_L₀_ge, hk_real]
  have hh_nonneg : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have h_mul_h := mul_le_mul_of_nonneg_right h_quad_mono hh_nonneg
  linarith

private lemma chainSeparated_congr {k d h : ℕ} (directed : Bool)
    (S : Finset (Fin k × Fin d)) (c : Chain k h) (σ₁ σ₂ : Sample k d h)
    (hσ : σ₁ c = σ₂ c) :
    chainSeparated directed S c σ₁ ↔ chainSeparated directed S c σ₂ := by
  unfold chainSeparated CutsOn
  constructor <;> intro h_cut p hp <;> rcases h_cut p hp with ⟨j, hj⟩ <;> refine ⟨j, ?_⟩
  · have h_lbl : (shutterInstance k d h directed σ₂).label (p.edge j) =
        (shutterInstance k d h directed σ₁).label (p.edge j) := by
      dsimp [shutterInstance]
      rw [hp j, hσ]
    rwa [h_lbl]
  · have h_lbl : (shutterInstance k d h directed σ₁).label (p.edge j) =
        (shutterInstance k d h directed σ₂).label (p.edge j) := by
      dsimp [shutterInstance]
      rw [hp j, hσ]
    rwa [h_lbl]

theorem solution (k d h : ℕ) (hk : 2 ≤ k) (hh : 0 < h)
    (directed : Bool) (S : Finset (Fin k × Fin d)) (hc : 0 < S.card)
    (hreg : 8 * average k S.card < (d : ℝ)) :
    probability k d h (good directed S) ≤ configurationBound k h (average k S.card) d := by
  classical
  let a := average k S.card
  let L₀ := light S
  let LC : Finset (Chain k h) :=
    Finset.univ.filter (fun c : Chain k h => c.1.val.1 ∈ L₀ ∧ c.1.val.2 ∈ L₀)
  let coordEvent (c : Chain k h) (π : Equiv.Perm (Fin d)) : Prop :=
    chainSeparated directed S c (fun _ => π)
  let B (c : Chain k h) : Finset (Equiv.Perm (Fin d)) :=
    Finset.univ.filter (coordEvent c)
  have h_sample_card :
      (Fintype.card (Sample k d h) : ℝ) =
        ∏ _c : Chain k h, (Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
    have h_nat : Fintype.card (Sample k d h) = ∏ _c : Chain k h, Fintype.card (Equiv.Perm (Fin d)) :=
      Fintype.card_pi
    exact_mod_cast h_nat
  have h_single_prob :
      ∀ c₀ : Chain k h,
        probability k d h (chainSeparated directed S c₀) =
          ((B c₀).card : ℝ) / (Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
    intro c₀
    let A₁ : Chain k h → Finset (Equiv.Perm (Fin d)) :=
      fun c => if c = c₀ then B c₀ else Finset.univ
    have h_filter_eq :
        Finset.univ.filter (chainSeparated directed S c₀) = Fintype.piFinset A₁ := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, A₁]
      constructor
      · intro hσ c
        split_ifs with hc₀
        · subst hc₀
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, coordEvent]
          exact (chainSeparated_congr directed S c σ (fun _ => σ c) rfl).mp hσ
        · exact Finset.mem_univ _
      · intro hσ
        have h_c₀ := hσ c₀
        simp only [↓reduceIte, B, Finset.mem_filter, Finset.mem_univ, true_and, coordEvent] at h_c₀
        exact (chainSeparated_congr directed S c₀ σ (fun _ => σ c₀) rfl).mpr h_c₀
    unfold probability
    rw [h_filter_eq, Fintype.card_piFinset, Nat.cast_prod, h_sample_card, ← Finset.prod_div_distrib]
    rw [Finset.prod_eq_single c₀]
    · simp [A₁]
    · intro c _ hc_ne
      simp [A₁, hc_ne]
    · intro h_abs
      exact False.elim (h_abs (Finset.mem_univ c₀))
  let A : Chain k h → Finset (Equiv.Perm (Fin d)) :=
    fun c => if c ∈ LC then B c else Finset.univ
  have h_good_sub :
      Finset.univ.filter (good directed S) ⊆ Fintype.piFinset A := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    simp only [Fintype.mem_piFinset, A]
    intro c
    split_ifs with hc_mem
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, coordEvent]
      rw [← chainSeparated_congr directed S c σ (fun _ => σ c) rfl]
      simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hc_mem
      intro p hp
      have hp_light :
          ∀ j, (p.edge j).1.1.val.1 ∈ light S ∧ (p.edge j).1.1.val.2 ∈ light S := by
        intro j
        rw [hp j]
        exact hc_mem
      rcases hσ p hp_light with ⟨j, hj⟩
      exact ⟨j, Finset.filter_subset _ _ hj⟩
    · exact Finset.mem_univ _
  have h_prob_le_prod :
      probability k d h (good directed S) ≤
        ∏ c ∈ LC, probability k d h (chainSeparated directed S c) := by
    have h_card_le :
        (((Finset.univ : Finset (Sample k d h)).filter (good directed S)).card : ℝ) ≤
          ((Fintype.piFinset A).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_good_sub
    have h_sample_nonneg : (0 : ℝ) ≤ (Fintype.card (Sample k d h) : ℝ) := Nat.cast_nonneg _
    have h_div_le :
        probability k d h (good directed S) ≤
          ((Fintype.piFinset A).card : ℝ) / (Fintype.card (Sample k d h) : ℝ) := by
      unfold probability
      exact div_le_div_of_nonneg_right h_card_le h_sample_nonneg
    have h_prod_eq :
        ((Fintype.piFinset A).card : ℝ) / (Fintype.card (Sample k d h) : ℝ) =
          ∏ c ∈ LC, probability k d h (chainSeparated directed S c) := by
      rw [Fintype.card_piFinset, Nat.cast_prod, h_sample_card, ← Finset.prod_div_distrib]
      rw [← Finset.prod_subset (Finset.subset_univ LC)]
      · apply Finset.prod_congr rfl
        intro c hc_mem
        simp only [A, hc_mem, ↓reduceIte, h_single_prob c]
      · intro c _ hc_not_mem
        simp [A, hc_not_mem]
    linarith
  have h_prod_le_pow :
      (∏ c ∈ LC, probability k d h (chainSeparated directed S c)) ≤
        (chainBound a d) ^ LC.card := by
    calc (∏ c ∈ LC, probability k d h (chainSeparated directed S c))
      _ ≤ ∏ _c ∈ LC, chainBound a d := by
        apply Finset.prod_le_prod
        · intro c _
          unfold probability
          positivity
        · intro c hc_mem
          simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hc_mem
          exact chain_separation_probability k d h directed S hc hreg c hc_mem.1 hc_mem.2
      _ = (chainBound a d) ^ LC.card := by
        rw [Finset.prod_const]
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have ha_pos : 0 < a := div_pos (by exact_mod_cast hc) hk_pos
  have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have h_inner_pos : 0 < 1 - 8 * a / (d : ℝ) := by
    rw [sub_pos, div_lt_iff₀ hd_pos]
    linarith
  have h_inner_lt_one : 1 - 8 * a / (d : ℝ) < 1 := by
    have : 0 < 8 * a / (d : ℝ) := div_pos (by linarith) hd_pos
    linarith
  have h_cb_pos : 0 < chainBound a d := by
    unfold chainBound
    rw [sub_pos]
    exact Real.rpow_lt_one (le_of_lt h_inner_pos) h_inner_lt_one (by linarith)
  have h_cb_le_one : chainBound a d ≤ 1 := by
    unfold chainBound
    have : 0 ≤ (1 - 8 * a / (d : ℝ)) ^ (4 * a) := Real.rpow_nonneg (le_of_lt h_inner_pos) _
    linarith
  have h_exp_le :
      (h : ℝ) / 2 * (3 * (k : ℝ) / 4) * (3 * (k : ℝ) / 4 - 1) ≤ (LC.card : ℝ) :=
    light_chains_card_ge hk S hc
  have h_rpow_le :
      (chainBound a d) ^ LC.card ≤ configurationBound k h a d := by
    rw [← Real.rpow_natCast (chainBound a d) LC.card]
    unfold configurationBound
    exact Real.rpow_le_rpow_of_exponent_ge h_cb_pos h_cb_le_one h_exp_le
  exact le_trans h_prob_le_prod (le_trans h_prod_le_pow h_rpow_le)
