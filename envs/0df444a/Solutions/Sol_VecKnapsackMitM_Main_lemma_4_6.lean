-- Prove2me | solution 1 for VecKnapsackMitM.Main.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:56:57.691962+00:00
-- url     : https://prove2.me/submissions/734fccf9-91c3-476a-95d5-b342b1955d8b

import Mathlib
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Algorithm3

namespace Aux46

open VecKnapsackMitM.Main

lemma maxIdx_eq_max' {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) :
    maxIdx S = (((S.max' hS).val : ℝ) : EReal) := by
  unfold maxIdx
  apply le_antisymm
  · refine Finset.sup_le fun i hi => ?_
    exact EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr (Fin.le_def.mp (Finset.le_max' S i hi)))
  · exact Finset.le_sup (f := fun i : Fin n => (((i.val : ℝ)) : EReal)) (Finset.max'_mem S hS)

lemma minIdx_eq_min' {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) :
    minIdx S = (((S.min' hS).val : ℝ) : EReal) := by
  unfold minIdx
  apply le_antisymm
  · exact Finset.inf_le (f := fun i : Fin n => (((i.val : ℝ)) : EReal)) (Finset.min'_mem S hS)
  · refine Finset.le_inf fun i hi => ?_
    exact EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr (Fin.le_def.mp (Finset.min'_le S i hi)))

lemma maxIdx_le_sub_one_iff {n : ℕ} (S₁ S₂ : Finset (Fin n)) :
    maxIdx S₁ ≤ minIdx S₂ - 1 ↔ maxIdx S₁ < minIdx S₂ := by
  rcases S₁.eq_empty_or_nonempty with rfl | hS₁
  · have hm₁ : maxIdx (∅ : Finset (Fin n)) = ⊥ := by simp [maxIdx]
    rw [hm₁]
    simp only [bot_le, true_iff]
    rcases S₂.eq_empty_or_nonempty with rfl | hS₂
    · simp [minIdx]
    · rw [minIdx_eq_min' hS₂]
      exact EReal.bot_lt_coe _
  · rw [maxIdx_eq_max' hS₁]
    rcases S₂.eq_empty_or_nonempty with rfl | hS₂
    · have hm₂ : minIdx (∅ : Finset (Fin n)) = ⊤ := by simp [minIdx]
      rw [hm₂]
      have htop : (⊤ : EReal) - 1 = ⊤ := rfl
      rw [htop]
      simp only [le_top, true_iff]
      exact EReal.coe_lt_top _
    · rw [minIdx_eq_min' hS₂]
      have h1 : (1 : EReal) = ((1 : ℝ) : EReal) := rfl
      rw [h1, ← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_lt_coe_iff]
      constructor
      · intro hle
        have hnat : (S₁.max' hS₁).val + 1 ≤ (S₂.min' hS₂).val := by
          exact_mod_cast (by linarith : ((S₁.max' hS₁).val : ℝ) + 1 ≤ ((S₂.min' hS₂).val : ℝ))
        exact Nat.cast_lt.mpr (Nat.lt_of_succ_le hnat)
      · intro hlt
        have hnat : (S₁.max' hS₁).val < (S₂.min' hS₂).val := Nat.cast_lt.mp hlt
        have hle : (S₁.max' hS₁).val + 1 ≤ (S₂.min' hS₂).val := Nat.succ_le_of_lt hnat
        have hreal : ((S₁.max' hS₁).val : ℝ) + 1 ≤ ((S₂.min' hS₂).val : ℝ) := by exact_mod_cast hle
        linarith

lemma inBox_iff_matched {d n : ℕ} (inst : Instance d n) (hinst : inst.Nonneg)
    (S₁ S₂ : Finset (Fin n)) :
    InBox (rangeLo d) (rangeHi inst S₂) (embed inst.toItems S₁) ↔ Matched inst S₁ S₂ := by
  constructor
  · intro hbox
    refine ⟨fun t => ?_, ?_⟩
    · have hj := hbox ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩
      simp only [rangeLo, rangeHi, embed, t.isLt, ↓reduceDIte] at hj
      have hle : inst.toItems.weight S₁ t ≤ inst.W t - inst.toItems.weight S₂ t :=
        EReal.coe_le_coe_iff.mp hj.2
      linarith
    · have hd_idx := hbox ⟨d, Nat.lt_succ_self d⟩
      simp only [rangeLo, rangeHi, embed, lt_irrefl, ↓reduceDIte, ↓reduceIte] at hd_idx
      exact (maxIdx_le_sub_one_iff S₁ S₂).mp hd_idx.2
  · rintro ⟨hw, hidx⟩ j
    by_cases hj : j.val < d
    · simp only [rangeLo, rangeHi, embed, hj, ↓reduceDIte, ↓reduceIte]
      have h0 : (0 : EReal) = ((0 : ℝ) : EReal) := rfl
      rw [h0, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      exact ⟨Finset.sum_nonneg fun i _ => hinst.1.2 i ⟨j.val, hj⟩, by have := hw ⟨j.val, hj⟩; linarith⟩
    · simp only [rangeLo, rangeHi, embed, hj, ↓reduceDIte, ↓reduceIte]
      exact ⟨bot_le, (maxIdx_le_sub_one_iff S₁ S₂).mpr hidx⟩

lemma maxIdx_lt_minIdx_of_forall_lt {n : ℕ} {A B : Finset (Fin n)}
    (h : ∀ i ∈ A, ∀ j ∈ B, i < j) : maxIdx A < minIdx B := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hmA : maxIdx (∅ : Finset (Fin n)) = ⊥ := by simp [maxIdx]
    rw [hmA]
    rcases B.eq_empty_or_nonempty with rfl | hB
    · simp [minIdx]
    · rw [minIdx_eq_min' hB]; exact EReal.bot_lt_coe _
  · rw [maxIdx_eq_max' hA]
    rcases B.eq_empty_or_nonempty with rfl | hB
    · simp only [minIdx, Finset.inf_empty]
      exact EReal.coe_lt_top _
    · rw [minIdx_eq_min' hB, EReal.coe_lt_coe_iff]
      exact Nat.cast_lt.mpr (Fin.lt_def.mp (h _ (Finset.max'_mem A hA) _ (Finset.min'_mem B hB)))

lemma disjoint_of_maxIdx_lt_minIdx {n : ℕ} {A B : Finset (Fin n)} (h : maxIdx A < minIdx B) :
    Disjoint A B := by
  rw [Finset.disjoint_left]
  intro i hiA hiB
  have h1 : (((i.val : ℝ)) : EReal) ≤ maxIdx A :=
    Finset.le_sup (f := fun j : Fin n => (((j.val : ℝ)) : EReal)) hiA
  have h2 : minIdx B ≤ (((i.val : ℝ)) : EReal) :=
    Finset.inf_le (f := fun j : Fin n => (((j.val : ℝ)) : EReal)) hiB
  exact lt_irrefl _ ((h1.trans_lt h).trans_le h2)

lemma disjoint_of_subset_nextIdx {n : ℕ} {S₂ v : Finset (Fin n)}
    (hv : v ⊆ Items.suffix n (nextIdx S₂).val) : Disjoint S₂ v := by
  rw [Finset.disjoint_left]
  intro i hiS₂ hiv
  have h1 : i.val + 1 ≤ (nextIdx S₂).val :=
    Finset.le_sup (f := fun j : Fin n => j.val + 1) hiS₂
  have h2 : (nextIdx S₂).val ≤ i.val := (Finset.mem_filter.mp (hv hiv)).2
  omega

def slice {n : ℕ} (OPT : Finset (Fin n)) (a b : ℕ) (hb : b ≤ OPT.card) : Finset (Fin n) :=
  (Finset.Ico a b).attach.map
    ⟨fun k => OPT.orderEmbOfFin rfl ⟨k.1, lt_of_lt_of_le (Finset.mem_Ico.mp k.2).2 hb⟩,
     fun k₁ k₂ heq => by
       have hfin := (OPT.orderEmbOfFin rfl).injective heq
       exact Subtype.ext (Fin.mk.inj hfin)⟩

lemma slice_card {n : ℕ} (OPT : Finset (Fin n)) (a b : ℕ) (_hab : a ≤ b) (hb : b ≤ OPT.card) :
    (slice OPT a b hb).card = b - a := by
  simp [slice, Nat.card_Ico]

lemma mem_slice {n : ℕ} (OPT : Finset (Fin n)) (a b : ℕ) (hb : b ≤ OPT.card) (x : Fin n) :
    x ∈ slice OPT a b hb ↔
      ∃ (k : ℕ) (hk : a ≤ k ∧ k < b),
        OPT.orderEmbOfFin rfl ⟨k, lt_of_lt_of_le hk.2 hb⟩ = x := by
  simp only [slice, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_Ico]
  rfl

lemma slice_lt {n : ℕ} (OPT : Finset (Fin n)) (a b c d_hi : ℕ)
    (hbc : b ≤ c) (hb : b ≤ OPT.card) (hd : d_hi ≤ OPT.card)
    {x y : Fin n} (hx : x ∈ slice OPT a b hb) (hy : y ∈ slice OPT c d_hi hd) : x < y := by
  rw [mem_slice] at hx hy
  obtain ⟨k₁, hk₁, rfl⟩ := hx
  obtain ⟨k₂, hk₂, rfl⟩ := hy
  exact (OPT.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega))

lemma slice_disjoint {n : ℕ} (OPT : Finset (Fin n)) (a b c : ℕ)
    (_hbc : b ≤ c) (hb : b ≤ OPT.card) (hc : c ≤ OPT.card) :
    Disjoint (slice OPT a b hb) (slice OPT b c hc) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  exact lt_irrefl x (slice_lt OPT a b b c le_rfl hb hc hx₁ hx₂)

lemma slice_union {n : ℕ} (OPT : Finset (Fin n)) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ OPT.card) :
    slice OPT a b (hbc.trans hc) ∪ slice OPT b c hc = slice OPT a c hc := by
  ext x
  simp only [Finset.mem_union, mem_slice]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact ⟨k, ⟨hk.1, lt_of_lt_of_le hk.2 hbc⟩, rfl⟩
    · exact ⟨k, ⟨hab.trans hk.1, hk.2⟩, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    by_cases hkb : k < b
    · exact Or.inl ⟨k, ⟨hk.1, hkb⟩, rfl⟩
    · exact Or.inr ⟨k, ⟨by omega, hk.2⟩, rfl⟩

lemma slice_full {n : ℕ} (OPT : Finset (Fin n)) :
    slice OPT 0 OPT.card le_rfl = OPT := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [mem_slice] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact Finset.orderEmbOfFin_mem OPT rfl _
  · rw [slice_card OPT 0 OPT.card (Nat.zero_le _) le_rfl, Nat.sub_zero]

lemma alg3_ratio_bound (d : ℕ) (hd : 2 ≤ d) (ρ ε : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε0 : 0 < ε) (hε1 : ε ≤ ((d : ℝ) - 1) / d)
    (pH pL pv : ℝ) (hpH : 0 ≤ pH) (hpL : 0 ≤ pL)
    (hp1 : (1 - alg3delta d ε ρ) * pL - ((d : ℝ) - 1 + alg3delta d ε ρ) * (pH / (alg3q d ε ρ : ℝ)) ≤ pv)
    (hp2 : (1 - alg3delta d ε ρ) / d * pL - alg3delta d ε ρ * (pH / (alg3q d ε ρ : ℝ)) ≤ pv) :
    (1 - ε) * (pH + pL) ≤ pH + pv := by
  let dr : ℝ := (d : ℝ)
  have hdr : 2 ≤ dr := by dsimp [dr]; exact_mod_cast hd
  have hdr_pos : 0 < dr := by linarith
  have hdr1_pos : 0 < dr - 1 := by linarith
  let qz : ℤ := alg3q d ε ρ
  let qr : ℝ := (qz : ℝ)
  have hdiv_ge : dr ≤ (dr - 1) / ε := by
    rw [le_div_iff₀ hε0]
    have := (le_div_iff₀ hdr_pos).mp hε1
    linarith
  have harg_pos : 0 < (dr - 1) / ε - dr + ρ := by linarith
  have hqz_pos : 1 ≤ qz := by
    have : 0 < qz := Int.ceil_pos.mpr harg_pos
    omega
  have hqr_ge1 : 1 ≤ qr := by dsimp [qr]; exact_mod_cast hqz_pos
  have hqr_pos : 0 < qr := by linarith
  have hq_ge : (dr - 1) / ε - dr + ρ ≤ qr := Int.le_ceil _
  let δ : ℝ := alg3delta d ε ρ
  have hδ_pos : 0 < δ := by
    dsimp [δ, alg3delta]
    exact div_pos (mul_pos (pow_pos hε0 2) hρ0) (by linarith)
  -- Multiply hp1 by qr and hp2 by dr
  have hmul1 : qr * (1 - δ) * pL - (dr - 1 + δ) * pH ≤ qr * pv := by
    have h := mul_le_mul_of_nonneg_left hp1 hqr_pos.le
    have hcancel : qr * ((dr - 1 + δ) * (pH / qr)) = (dr - 1 + δ) * pH := by
      field_simp [hqr_pos.ne']
    linarith
  have hmul2 : (1 - δ) * pL - dr * δ * pH ≤ dr * pv := by
    have h := mul_le_mul_of_nonneg_left hp2 hdr_pos.le
    have hcancel : dr * ((1 - δ) / dr * pL) = (1 - δ) * pL := by
      field_simp [hdr_pos.ne']
    have hpH_div : pH / qr ≤ pH := div_le_self hpH hqr_ge1
    have hterm : dr * (δ * (pH / qr)) ≤ dr * δ * pH := by
      have : 0 ≤ dr * δ := mul_nonneg hdr_pos.le hδ_pos.le
      nlinarith
    linarith
  have hqd_pos : 0 < qr + dr := by linarith
  have hcomb : (qr + 1 - δ * (qr + dr)) * (pH + pL) ≤ (qr + dr) * (pH + pv) := by
    have hextra1 : 0 ≤ (qr - 1) * δ * pH :=
      mul_nonneg (mul_nonneg (by linarith) hδ_pos.le) hpH
    have hextra2 : 0 ≤ (dr - 1) * δ * pL :=
      mul_nonneg (mul_nonneg hdr1_pos.le hδ_pos.le) hpL
    have hid : (qr + dr) * pH + (qr * (1 - δ) * pL - (dr - 1 + δ) * pH) +
        ((1 - δ) * pL - dr * δ * pH) =
        (qr + 1 - δ * (qr + dr)) * (pH + pL) + (qr - 1) * δ * pH + (dr - 1) * δ * pL := by ring
    linarith
  -- Show (dr - 1) / (qr + dr) + δ ≤ ε, i.e., (1 - ε) * (qr + dr) ≤ qr + 1 - δ * (qr + dr)
  have hdenom_pos : 0 < dr - 1 + ρ * ε := by nlinarith
  have hqd_lower : (dr - 1 + ρ * ε) / ε ≤ qr + dr := by
    have : (dr - 1 + ρ * ε) / ε = (dr - 1) / ε + ρ := by
      rw [add_div, mul_div_cancel_right₀ _ hε0.ne']
    linarith
  have hterm1 : (dr - 1) / (qr + dr) ≤ ε * (dr - 1) / (dr - 1 + ρ * ε) := by
    rw [div_le_div_iff₀ hqd_pos hdenom_pos]
    have := (div_le_iff₀ hε0).mp hqd_lower
    nlinarith
  have hterm2 : δ ≤ ε * (ρ * ε) / (dr - 1 + ρ * ε) := by
    dsimp [δ, alg3delta]
    rw [div_le_div_iff₀ (by linarith) hdenom_pos]
    have hρε_lt1 : ρ * ε < 1 := by
      have hε_lt1 : ε < 1 := lt_of_le_of_lt hε1 (by rw [div_lt_one hdr_pos]; linarith)
      nlinarith
    have h2d : dr - 1 + ρ * ε ≤ 2 * (dr - 1) := by linarith
    have hnum_nonneg : 0 ≤ ε ^ 2 * ρ := by positivity
    nlinarith
  have hsum_eps : (dr - 1) / (qr + dr) + δ ≤ ε := by
    calc (dr - 1) / (qr + dr) + δ
        ≤ ε * (dr - 1) / (dr - 1 + ρ * ε) + ε * (ρ * ε) / (dr - 1 + ρ * ε) :=
          add_le_add hterm1 hterm2
      _ = ε * (dr - 1 + ρ * ε) / (dr - 1 + ρ * ε) := by ring
      _ = ε := mul_div_cancel_right₀ ε hdenom_pos.ne'
  have hcoef : (1 - ε) * (qr + dr) ≤ qr + 1 - δ * (qr + dr) := by
    have h1 : dr - 1 + δ * (qr + dr) ≤ ε * (qr + dr) := by
      have := mul_le_mul_of_nonneg_right hsum_eps hqd_pos.le
      rw [add_mul, div_mul_cancel₀ _ hqd_pos.ne'] at this
      exact this
    linarith
  have hfinal : (1 - ε) * (qr + dr) * (pH + pL) ≤ (qr + dr) * (pH + pv) :=
    (mul_le_mul_of_nonneg_right hcoef (by linarith)).trans hcomb
  have hfinal' : (qr + dr) * ((1 - ε) * (pH + pL)) ≤ (qr + dr) * (pH + pv) := by linarith
  exact le_of_mul_le_mul_left hfinal' hqd_pos

end Aux46

open VecKnapsackMitM.Main

theorem solution (d n : ℕ) (hd : 2 ≤ d) (ρ ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε0 : 0 < ε)
    (hε1 : ε ≤ ((d : ℝ) - 1) / d) (inst : Instance d n) (hinst : inst.Nonneg)
    (S : Finset (Fin n)) (hS : Alg3Output inst ε ρ S) : inst.IsApprox ε S := by
  obtain ⟨σ, hSort, L, ans, S', hRep, hORS, hRet, rfl⟩ := hS
  let J := inst.reindex σ
  have hJ : J.Nonneg := ⟨⟨fun j => hinst.1.1 (σ j), fun j t => hinst.1.2 (σ j) t⟩, hinst.2⟩
  -- Helper relating J and inst via σ
  have hprof_map : ∀ T : Finset (Fin n), inst.toItems.profit (T.map σ.toEmbedding) = J.toItems.profit T := by
    intro T; simp [Items.profit, J, Instance.reindex]
  have hw_map : ∀ (T : Finset (Fin n)) (t : Fin d),
      inst.toItems.weight (T.map σ.toEmbedding) t = J.toItems.weight T t := by
    intro T t; simp [Items.weight, J, Instance.reindex]
  -- Candidate properties on J
  have hcand_props : ∀ S₁ S₂ v : Finset (Fin n),
      v ∈ L (nextIdx S₂) → ans S₂ v = some S₁ →
      J.Feasible (S₁ ∪ S₂ ∪ v) ∧
        J.toItems.profit (S₁ ∪ S₂ ∪ v) =
          J.toItems.profit S₁ + J.toItems.profit S₂ + J.toItems.profit v := by
    intro S₁ S₂ v hv hans
    have hors := hORS S₂ v
    rw [hans] at hors
    dsimp [ORSAnswer] at hors
    have hmatch := (Aux46.inBox_iff_matched J hJ S₁ (S₂ ∪ v)).mp hors.2.1
    have hdisj2v : Disjoint S₂ v :=
      Aux46.disjoint_of_subset_nextIdx ((hRep (nextIdx S₂)).1 v hv)
    have hdisj1 : Disjoint S₁ (S₂ ∪ v) := Aux46.disjoint_of_maxIdx_lt_minIdx hmatch.2
    have hunion_assoc : S₁ ∪ S₂ ∪ v = S₁ ∪ (S₂ ∪ v) := Finset.union_assoc S₁ S₂ v
    refine ⟨fun t => ?_, ?_⟩
    · rw [hunion_assoc]
      unfold Items.weight at *
      rw [Finset.sum_union hdisj1]
      exact hmatch.1 t
    · rw [hunion_assoc]
      unfold Items.profit
      rw [Finset.sum_union hdisj1, Finset.sum_union hdisj2v, add_assoc]
  -- Feasibility of S' and candidate dominance
  have hS'_feas : J.Feasible S' := by
    rcases hRet with ⟨_, rfl⟩ | ⟨S₁, S₂, v, hcand, _, _, rfl⟩
    · intro t; simp [Items.weight, hJ.2 t]
    · exact (hcand_props S₁ S₂ v hcand.2.2.1 hcand.2.2.2).1
  have hS'_prof_ge_cand : ∀ S₁ S₂ v : Finset (Fin n),
      1 ≤ S₂.card → (S₂.card : ℤ) ≤ alg3l2 d ε ρ →
      v ∈ L (nextIdx S₂) → ans S₂ v = some S₁ →
      J.toItems.profit S₁ + J.toItems.profit S₂ + J.toItems.profit v ≤ J.toItems.profit S' := by
    intro S₁ S₂ v h1 h2 hv hans
    rcases hRet with ⟨hle0, rfl⟩ | ⟨S₁_s, S₂_s, v_s, hcand_s, _, hmax_s, rfl⟩
    · have := hle0 S₁ S₂ v ⟨h1, h2, hv, hans⟩
      simpa [Items.profit] using this
    · have hle := hmax_s S₁ S₂ v ⟨h1, h2, hv, hans⟩
      have heq := (hcand_props S₁_s S₂_s v_s hcand_s.2.2.1 hcand_s.2.2.2).2
      linarith
  have hors_some : ∀ St1 S₂ v : Finset (Fin n),
      (St1.card : ℤ) ≤ alg3l1 d ε ρ → Matched J St1 (S₂ ∪ v) →
      ∃ S₁ : Finset (Fin n), ans S₂ v = some S₁ ∧ J.toItems.profit St1 ≤ J.toItems.profit S₁ := by
    intro St1 S₂ v hcard hmatch
    have hbox := (Aux46.inBox_iff_matched J hJ St1 (S₂ ∪ v)).mpr hmatch
    have hors := hORS S₂ v
    cases hans : ans S₂ v with
    | none =>
      rw [hans] at hors
      exact False.elim (hors St1 hcard hbox)
    | some S₁ =>
      rw [hans] at hors
      exact ⟨S₁, rfl, hors.2.2 St1 hcard hbox⟩
  -- Prove inst.IsApprox ε (S'.map σ.toEmbedding)
  refine ⟨fun t => by rw [hw_map]; exact hS'_feas t, fun S_orig hS_orig => ?_⟩
  rw [hprof_map]
  let OPT : Finset (Fin n) := S_orig.map σ.symm.toEmbedding
  have hOPT_map : OPT.map σ.toEmbedding = S_orig := by
    ext x
    simp [OPT]
  have hOPT_feas : J.Feasible OPT := by
    intro t
    rw [← hw_map OPT t, hOPT_map]
    exact hS_orig t
  have hOPT_prof : inst.toItems.profit S_orig = J.toItems.profit OPT := by
    rw [← hOPT_map, hprof_map]
  rw [hOPT_prof]
  have hS'_nonneg : 0 ≤ J.toItems.profit S' := Finset.sum_nonneg fun i _ => hJ.1.1 i
  -- Establish parameter bounds q ≥ 1, l1 ≥ 1, l2 ≥ 1
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdr_pos : (0 : ℝ) < d := by linarith
  have hdiv_ge : (d : ℝ) ≤ ((d : ℝ) - 1) / ε := by
    rw [le_div_iff₀ hε0]
    have := (le_div_iff₀ hdr_pos).mp hε1
    linarith
  have hqz_pos : 1 ≤ alg3q d ε ρ := by
    have : 0 < alg3q d ε ρ := Int.ceil_pos.mpr (by linarith : 0 < ((d : ℝ) - 1) / ε - d + ρ)
    omega
  have hl1_pos : 1 ≤ alg3l1 d ε ρ := by
    unfold alg3l1
    rw [Int.le_floor]
    have hq1 : (1 : ℝ) ≤ (alg3q d ε ρ : ℝ) := by exact_mod_cast hqz_pos
    linarith
  have hl2_pos : 1 ≤ alg3l2 d ε ρ := le_max_right _ _
  have hl2_le_q : alg3l2 d ε ρ ≤ alg3q d ε ρ := by
    unfold alg3l2
    exact max_le (by omega) hqz_pos
  have hq_sub_l2_le_l1 : alg3q d ε ρ - alg3l2 d ε ρ ≤ alg3l1 d ε ρ := by
    have : alg3q d ε ρ - alg3l1 d ε ρ ≤ alg3l2 d ε ρ := le_max_left _ _
    omega
  -- Three cases on OPT.card
  by_cases hcard0 : OPT.card = 0
  · rw [Finset.card_eq_zero.mp hcard0]
    have hp0 : J.toItems.profit (∅ : Finset (Fin n)) = 0 := by simp [Items.profit]
    rw [hp0, mul_zero]
    exact hS'_nonneg
  · have hOPT_pos : 1 ≤ OPT.card := Nat.pos_of_ne_zero hcard0
    by_cases hcard_le_q : (OPT.card : ℤ) ≤ alg3q d ε ρ
    · -- Case 2: 1 ≤ |OPT| ≤ q
      let r : ℕ := min (alg3l1 d ε ρ).toNat (OPT.card - 1)
      have hr_lt : r < OPT.card := by
        have := min_le_right (alg3l1 d ε ρ).toNat (OPT.card - 1)
        omega
      let St1 := Aux46.slice OPT 0 r hr_lt.le
      let St2 := Aux46.slice OPT r OPT.card le_rfl
      have hdisj12 : Disjoint St1 St2 := Aux46.slice_disjoint OPT 0 r OPT.card hr_lt.le hr_lt.le le_rfl
      have hunion12 : St1 ∪ St2 = OPT :=
        (Aux46.slice_union OPT 0 r OPT.card (Nat.zero_le _) hr_lt.le le_rfl).trans (Aux46.slice_full OPT)
      have hSt1_card : (St1.card : ℤ) ≤ alg3l1 d ε ρ := by
        rw [Aux46.slice_card OPT 0 r (Nat.zero_le _) hr_lt.le, Nat.sub_zero]
        have hr_le : r ≤ (alg3l1 d ε ρ).toNat := min_le_left _ _
        have : (r : ℤ) ≤ ((alg3l1 d ε ρ).toNat : ℤ) := by exact_mod_cast hr_le
        omega
      have hSt2_card_eq : St2.card = OPT.card - r := Aux46.slice_card OPT r OPT.card hr_lt.le le_rfl
      have hSt2_ge1 : 1 ≤ St2.card := by omega
      have hSt2_le_l2 : (St2.card : ℤ) ≤ alg3l2 d ε ρ := by
        rw [hSt2_card_eq]
        by_cases hmin : (alg3l1 d ε ρ).toNat ≤ OPT.card - 1
        · have hr_eq : r = (alg3l1 d ε ρ).toNat := min_eq_left hmin
          rw [hr_eq]
          have h1 : alg3q d ε ρ - alg3l1 d ε ρ ≤ alg3l2 d ε ρ := le_max_left _ _
          omega
        · have hr_eq : r = OPT.card - 1 := min_eq_right (by omega)
          rw [hr_eq]
          omega
      have hmatch : Matched J St1 (St2 ∪ ∅) := by
        rw [Finset.union_empty]
        refine ⟨fun t => ?_, Aux46.maxIdx_lt_minIdx_of_forall_lt fun x hx y hy =>
          Aux46.slice_lt OPT 0 r r OPT.card le_rfl hr_lt.le le_rfl hx hy⟩
        have hsum : J.toItems.weight St1 t + J.toItems.weight St2 t = J.toItems.weight OPT t := by
          rw [← hunion12]; unfold Items.weight; exact (Finset.sum_union hdisj12).symm
        linarith [hOPT_feas t]
      obtain ⟨S₁, hans, hprof1⟩ := hors_some St1 St2 ∅ hSt1_card hmatch
      have hv_empty : (∅ : Finset (Fin n)) ∈ L (nextIdx St2) := (hRep (nextIdx St2)).2.1
      have hcand_le := hS'_prof_ge_cand S₁ St2 ∅ hSt2_ge1 hSt2_le_l2 hv_empty hans
      have hOPT_sum : J.toItems.profit OPT = J.toItems.profit St1 + J.toItems.profit St2 := by
        rw [← hunion12]; unfold Items.profit; exact Finset.sum_union hdisj12
      have hOPT_nonneg : 0 ≤ J.toItems.profit OPT := Finset.sum_nonneg fun i _ => hJ.1.1 i
      have h1_eps : (1 - ε) * J.toItems.profit OPT ≤ J.toItems.profit OPT := by nlinarith
      have hp0 : J.toItems.profit (∅ : Finset (Fin n)) = 0 := by simp [Items.profit]
      linarith
    · -- Case 1: |OPT| > q
      have hq_lt_OPT : alg3q d ε ρ < (OPT.card : ℤ) := by omega
      let qn : ℕ := (alg3q d ε ρ).toNat
      have hqn_lt : qn < OPT.card := by omega
      have hqn_pos : 1 ≤ qn := by omega
      let r : ℕ := (alg3q d ε ρ - alg3l2 d ε ρ).toNat
      have hr_lt_qn : r < qn := by omega
      let St1 := Aux46.slice OPT 0 r (hr_lt_qn.le.trans hqn_lt.le)
      let St2 := Aux46.slice OPT r qn hqn_lt.le
      let H := Aux46.slice OPT 0 qn hqn_lt.le
      let Low := Aux46.slice OPT qn OPT.card le_rfl
      have hdisj12 : Disjoint St1 St2 :=
        Aux46.slice_disjoint OPT 0 r qn hr_lt_qn.le (hr_lt_qn.le.trans hqn_lt.le) hqn_lt.le
      have hunion12 : St1 ∪ St2 = H :=
        Aux46.slice_union OPT 0 r qn (Nat.zero_le _) hr_lt_qn.le hqn_lt.le
      have hdisjHL : Disjoint H Low := Aux46.slice_disjoint OPT 0 qn OPT.card hqn_lt.le hqn_lt.le le_rfl
      have hunionHL : H ∪ Low = OPT :=
        (Aux46.slice_union OPT 0 qn OPT.card (Nat.zero_le _) hqn_lt.le le_rfl).trans (Aux46.slice_full OPT)
      have hSt1_card : (St1.card : ℤ) ≤ alg3l1 d ε ρ := by
        rw [Aux46.slice_card OPT 0 r (Nat.zero_le _) (hr_lt_qn.le.trans hqn_lt.le), Nat.sub_zero]
        omega
      have hSt2_card_eq : St2.card = qn - r := Aux46.slice_card OPT r qn hr_lt_qn.le hqn_lt.le
      have hSt2_ge1 : 1 ≤ St2.card := by omega
      have hSt2_le_l2 : (St2.card : ℤ) ≤ alg3l2 d ε ρ := by rw [hSt2_card_eq]; omega
      -- Compute (nextIdx St2).val = (e ⟨qn - 1, _⟩).val + 1
      let lastH : Fin n := OPT.orderEmbOfFin rfl ⟨qn - 1, by omega⟩
      have hlastH_in_St2 : lastH ∈ St2 := by
        rw [Aux46.mem_slice]
        exact ⟨qn - 1, ⟨by omega, by omega⟩, rfl⟩
      have hnext_eq : (nextIdx St2).val = lastH.val + 1 := by
        dsimp [nextIdx]
        apply le_antisymm
        · refine Finset.sup_le fun x hx => ?_
          rw [Aux46.mem_slice] at hx
          obtain ⟨k, hk, rfl⟩ := hx
          have hle : OPT.orderEmbOfFin rfl ⟨k, lt_of_lt_of_le hk.2 hqn_lt.le⟩ ≤ lastH :=
            (OPT.orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr (by omega))
          exact Nat.succ_le_succ (Fin.le_def.mp hle)
        · exact Finset.le_sup (f := fun j : Fin n => j.val + 1) hlastH_in_St2
      -- Show Low ⊆ Items.suffix n (nextIdx St2).val
      have hLow_sub : Low ⊆ Items.suffix n (nextIdx St2).val := by
        intro y hy
        rw [Aux46.mem_slice] at hy
        obtain ⟨k, hk, rfl⟩ := hy
        have hlt : lastH < OPT.orderEmbOfFin rfl ⟨k, lt_of_lt_of_le hk.2 le_rfl⟩ :=
          (OPT.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega))
        simp only [Items.suffix, Finset.mem_filter, Finset.mem_univ, true_and, hnext_eq]
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hlt)
      -- Apply RepFamily to Low
      obtain ⟨v, hv_in_L, hv_wt, hv_p1, hv_p2⟩ := (hRep (nextIdx St2)).2.2 Low hLow_sub
      have hv_sub : v ⊆ Items.suffix n (nextIdx St2).val := (hRep (nextIdx St2)).1 v hv_in_L
      have hdisj2v : Disjoint St2 v := Aux46.disjoint_of_subset_nextIdx hv_sub
      -- Show Matched J St1 (St2 ∪ v)
      have hmatch : Matched J St1 (St2 ∪ v) := by
        refine ⟨fun t => ?_, Aux46.maxIdx_lt_minIdx_of_forall_lt fun x hx y hy => ?_⟩
        · have hw2v : J.toItems.weight (St2 ∪ v) t = J.toItems.weight St2 t + J.toItems.weight v t := by
            unfold Items.weight; exact Finset.sum_union hdisj2v
          have hwH : J.toItems.weight St1 t + J.toItems.weight St2 t = J.toItems.weight H t := by
            rw [← hunion12]; unfold Items.weight; exact (Finset.sum_union hdisj12).symm
          have hwOPT : J.toItems.weight H t + J.toItems.weight Low t = J.toItems.weight OPT t := by
            rw [← hunionHL]; unfold Items.weight; exact (Finset.sum_union hdisjHL).symm
          linarith [hv_wt t, hOPT_feas t]
        · rcases Finset.mem_union.mp hy with hy2 | hyv
          · exact Aux46.slice_lt OPT 0 r r qn le_rfl (hr_lt_qn.le.trans hqn_lt.le) hqn_lt.le hx hy2
          · have hx_lt_last : x ≤ lastH := by
              rw [Aux46.mem_slice] at hx
              obtain ⟨k, hk, rfl⟩ := hx
              exact (OPT.orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr (by omega))
            have hy_ge : (nextIdx St2).val ≤ y.val := (Finset.mem_filter.mp (hv_sub hyv)).2
            rw [hnext_eq] at hy_ge
            exact Fin.lt_def.mpr (by have := Fin.le_def.mp hx_lt_last; omega)
      obtain ⟨S₁, hans, hprof1⟩ := hors_some St1 St2 v hSt1_card hmatch
      have hcand_le := hS'_prof_ge_cand S₁ St2 v hSt2_ge1 hSt2_le_l2 hv_in_L hans
      have hH_sum : J.toItems.profit H = J.toItems.profit St1 + J.toItems.profit St2 := by
        rw [← hunion12]; unfold Items.profit; exact Finset.sum_union hdisj12
      have hOPT_sum : J.toItems.profit OPT = J.toItems.profit H + J.toItems.profit Low := by
        rw [← hunionHL]; unfold Items.profit; exact Finset.sum_union hdisjHL
      -- Bound pAt J.toItems (nextIdx St2)
      have hpAt_nonneg : 0 ≤ pAt J.toItems (nextIdx St2) := by
        unfold pAt
        split_ifs with hk
        · exact hJ.1.1 _
        · exact le_rfl
      have hpAt_le : pAt J.toItems (nextIdx St2) ≤ J.toItems.profit H / (alg3q d ε ρ : ℝ) := by
        have hqr_pos : (0 : ℝ) < (alg3q d ε ρ : ℝ) := by exact_mod_cast (by omega : 0 < alg3q d ε ρ)
        rw [le_div_iff₀ hqr_pos]
        unfold pAt
        split_ifs with hk
        · have hH_card : H.card = qn := Aux46.slice_card OPT 0 qn (Nat.zero_le _) hqn_lt.le
          have hqn_real : (H.card : ℝ) = (alg3q d ε ρ : ℝ) := by
            rw [hH_card]; exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ alg3q d ε ρ))
          calc J.p ⟨(nextIdx St2).val, hk⟩ * (alg3q d ε ρ : ℝ)
              = ∑ _x ∈ H, J.p ⟨(nextIdx St2).val, hk⟩ := by
                rw [Finset.sum_const, nsmul_eq_mul, hqn_real, mul_comm]
            _ ≤ ∑ x ∈ H, J.p x := by
                refine Finset.sum_le_sum fun x hx => hSort x ⟨(nextIdx St2).val, hk⟩ ?_
                rw [Aux46.mem_slice] at hx
                obtain ⟨k, hk_lt, rfl⟩ := hx
                have hx_le_last : OPT.orderEmbOfFin rfl ⟨k, lt_of_lt_of_le hk_lt.2 hqn_lt.le⟩ ≤ lastH :=
                  (OPT.orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr (by omega))
                exact Fin.le_def.mpr (by
                  simp only []
                  have h1 := Fin.le_def.mp hx_le_last
                  omega)
            _ = J.toItems.profit H := rfl
        · rw [zero_mul]
          exact Finset.sum_nonneg fun i _ => hJ.1.1 i
      -- Show δ / n ≤ δ since 1 ≤ n
      have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : 1 ≤ n := by
          have := OPT.card_le_univ
          rw [Fintype.card_fin] at this
          omega
        exact_mod_cast this
      let δ := alg3delta d ε ρ
      have hδ_pos : 0 < δ := by
        dsimp [δ, alg3delta]
        exact div_pos (mul_pos (pow_pos hε0 2) hρ0) (by linarith)
      have hδ_div_le : δ / n ≤ δ := div_le_self hδ_pos.le hn_ge1
      have hp1_clean : (1 - δ) * J.toItems.profit Low -
          ((d : ℝ) - 1 + δ) * (J.toItems.profit H / (alg3q d ε ρ : ℝ)) ≤ J.toItems.profit v := by
        have h1 : ((d : ℝ) - 1 + δ / n) * pAt J.toItems (nextIdx St2) ≤
            ((d : ℝ) - 1 + δ) * (J.toItems.profit H / (alg3q d ε ρ : ℝ)) :=
          mul_le_mul (by linarith) hpAt_le hpAt_nonneg (by linarith)
        linarith
      have hp2_clean : (1 - δ) / d * J.toItems.profit Low -
          δ * (J.toItems.profit H / (alg3q d ε ρ : ℝ)) ≤ J.toItems.profit v := by
        have h2 : δ / n * pAt J.toItems (nextIdx St2) ≤
            δ * (J.toItems.profit H / (alg3q d ε ρ : ℝ)) :=
          mul_le_mul hδ_div_le hpAt_le hpAt_nonneg hδ_pos.le
        linarith
      have hratio := Aux46.alg3_ratio_bound d hd ρ ε hρ0 hρ1 hε0 hε1
        (J.toItems.profit H) (J.toItems.profit Low) (J.toItems.profit v)
        (Finset.sum_nonneg fun i _ => hJ.1.1 i)
        (Finset.sum_nonneg fun i _ => hJ.1.1 i)
        hp1_clean hp2_clean
      rw [hOPT_sum]
      linarith
