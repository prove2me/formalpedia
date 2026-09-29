-- Prove2me | solution 1 for StochasticProg.ValueOfInfo.evrs_epev_vssref_spev_ws_chain
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T05:08:21.691162+00:00
-- url     : https://prove2.me/submissions/feb8e96c-7d9d-49f6-b538-3b74a1b4b105

import Mathlib
import Definitions.Def_StochasticProg_ValueOfInfo_Instance
import Definitions.Def_StochasticProg_ValueOfInfo_RP

set_option autoImplicit false

theorem voi_bsum_mono_aux {ι : Type*} [Fintype ι] (f g : ι → EReal) (h : ∀ i, f i ≤ g i) :
    StochasticProg.ValueOfInfo.bsum f ≤ StochasticProg.ValueOfInfo.bsum g := by
  unfold StochasticProg.ValueOfInfo.bsum
  by_cases hg : ∃ i, g i = ⊤
  · rw [if_pos hg]; exact le_top
  · have hf : ¬ ∃ i, f i = ⊤ := by
      rintro ⟨i, hi⟩
      apply hg
      refine ⟨i, top_le_iff.mp ?_⟩
      rw [← hi]; exact h i
    rw [if_neg hf, if_neg hg]
    exact Finset.sum_le_sum (fun i _ => h i)

theorem voi_badd_mono {a a' b b' : EReal} (ha : a ≤ a') (hb : b ≤ b') :
    StochasticProg.ValueOfInfo.badd a b ≤ StochasticProg.ValueOfInfo.badd a' b' := by
  unfold StochasticProg.ValueOfInfo.badd
  by_cases h' : a' = ⊤ ∨ b' = ⊤
  · rw [if_pos h']; exact le_top
  · have h : ¬ (a = ⊤ ∨ b = ⊤) := by
      rintro (h | h)
      · exact h' (Or.inl (top_le_iff.mp (h ▸ ha)))
      · exact h' (Or.inr (top_le_iff.mp (h ▸ hb)))
    rw [if_neg h, if_neg h']
    exact add_le_add ha hb

theorem voi_badd_of_ne {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    StochasticProg.ValueOfInfo.badd a b = a + b := by
  unfold StochasticProg.ValueOfInfo.badd
  rw [if_neg]
  rintro (h | h)
  · exact ha h
  · exact hb h

theorem voi_cmul_top {c : ℝ} (hc : 0 ≤ c) (w : EReal) :
    (c : EReal) * w = ⊤ ↔ 0 < c ∧ w = ⊤ := by
  rw [EReal.mul_eq_top]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩)
    · exact absurd h1 (EReal.coe_ne_bot c)
    · exact absurd h1 (not_lt.mpr (EReal.coe_nonneg.mpr hc))
    · exact absurd h1 (EReal.coe_ne_top c)
    · exact ⟨EReal.coe_pos.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact Or.inr (Or.inr (Or.inr ⟨EReal.coe_pos.mpr h1, h2⟩))

theorem voi_cmul_bot {c : ℝ} (hc : 0 ≤ c) (w : EReal) :
    (c : EReal) * w = ⊥ ↔ 0 < c ∧ w = ⊥ := by
  rw [EReal.mul_eq_bot]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩)
    · exact absurd h1 (EReal.coe_ne_bot c)
    · exact ⟨EReal.coe_pos.mp h1, h2⟩
    · exact absurd h1 (EReal.coe_ne_top c)
    · exact absurd h1 (not_lt.mpr (EReal.coe_nonneg.mpr hc))
  · rintro ⟨h1, h2⟩
    exact Or.inr (Or.inl ⟨EReal.coe_pos.mpr h1, h2⟩)

theorem voi_cmul_real {c : ℝ} (hc : 0 ≤ c) (w : EReal)
    (h1 : (c : EReal) * w ≠ ⊤) (h2 : (c : EReal) * w ≠ ⊥) :
    (c : EReal) * w = ((c * w.toReal : ℝ) : EReal) := by
  rcases hc.eq_or_lt with h0 | hpos
  · rw [← h0, EReal.coe_zero, zero_mul, zero_mul, EReal.coe_zero]
  · have hw1 : w ≠ ⊤ := fun h => h1 ((voi_cmul_top hc w).mpr ⟨hpos, h⟩)
    have hw2 : w ≠ ⊥ := fun h => h2 ((voi_cmul_bot hc w).mpr ⟨hpos, h⟩)
    rw [EReal.coe_mul, EReal.coe_toReal hw1 hw2]

theorem voi_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem voi_sum_bot {ι : Type*} [Fintype ι] (f : ι → EReal) (h : ∃ i, f i = ⊥) :
    ∑ i, f i = ⊥ := by
  classical
  obtain ⟨i, hi⟩ := h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi, EReal.bot_add]

theorem voi_key {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (S : ι → Prop) [DecidablePred S]
    (pr : ℝ) (hpr : pr = ∑ i, if S i then p i else 0) (hpr1 : pr < 1)
    (q : ℝ) (hqdef : q = 1 - pr) (v : EReal) (u : ι → EReal) :
    (q : EReal)⁻¹ *
      StochasticProg.ValueOfInfo.bsum (fun k => if S k then 0 else (p k : EReal) *
        StochasticProg.ValueOfInfo.badd ((pr : EReal) * v) ((q : EReal) * u k)) =
    StochasticProg.ValueOfInfo.bsum (fun k => (p k : EReal) * (if S k then v else u k)) := by
  have hq0 : 0 < q := by rw [hqdef]; linarith
  have hpr0 : 0 ≤ pr := by
    rw [hpr]
    exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hp i; exact le_rfl)
  have hT : (∑ i, if S i then 0 else p i) = q := by
    have e : ∀ i, (if S i then 0 else p i) = p i - (if S i then p i else 0) := by
      intro i; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, hsum, ← hpr, hqdef]
  have exT : ∃ j, ¬ S j ∧ 0 < p j := by
    by_contra hcon
    push_neg at hcon
    have : (∑ i, if S i then 0 else p i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hs
      · rfl
      · exact le_antisymm (hcon i hs) (hp i)
    linarith
  have exS : 0 < pr → ∃ j, S j ∧ 0 < p j := by
    intro hpos
    by_contra hcon
    push_neg at hcon
    have : (∑ i, if S i then p i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hs
      · exact le_antisymm (hcon i hs) (hp i)
      · rfl
    linarith
  have hSle : ∀ k, S k → p k ≤ pr := by
    intro k hk
    have := Finset.single_le_sum (f := fun i => if S i then p i else 0)
      (fun i _ => by split_ifs; exact hp i; exact le_rfl) (Finset.mem_univ k)
    simp only [if_pos hk] at this
    rw [hpr]; exact this
  have hqinv : (q : EReal)⁻¹ = ((q⁻¹ : ℝ) : EReal) := (EReal.coe_inv q).symm
  have hqinv0 : 0 < q⁻¹ := inv_pos.mpr hq0
  unfold StochasticProg.ValueOfInfo.bsum
  by_cases hR : ∃ k, (p k : EReal) * (if S k then v else u k) = ⊤
  · rw [if_pos hR]
    have hTtop : ∃ k, (if S k then 0 else (p k : EReal) *
        StochasticProg.ValueOfInfo.badd ((pr : EReal) * v) ((q : EReal) * u k)) = ⊤ := by
      obtain ⟨k, hk⟩ := hR
      rw [voi_cmul_top (hp k)] at hk
      obtain ⟨hpk, hw⟩ := hk
      by_cases hSk : S k
      · rw [if_pos hSk] at hw
        have hprpos : 0 < pr := lt_of_lt_of_le hpk (hSle k hSk)
        obtain ⟨j, hSj, hpj⟩ := exT
        refine ⟨j, ?_⟩
        rw [if_neg hSj, hw, EReal.coe_mul_top_of_pos hprpos]
        unfold StochasticProg.ValueOfInfo.badd
        rw [if_pos (Or.inl rfl), EReal.coe_mul_top_of_pos hpj]
      · rw [if_neg hSk] at hw
        refine ⟨k, ?_⟩
        rw [if_neg hSk, hw, EReal.coe_mul_top_of_pos hq0]
        unfold StochasticProg.ValueOfInfo.badd
        rw [if_pos (Or.inr rfl), EReal.coe_mul_top_of_pos hpk]
    rw [if_pos hTtop, hqinv, EReal.coe_mul_top_of_pos hqinv0]
  · rw [if_neg hR]
    push_neg at hR
    have hv : 0 < pr → v ≠ ⊤ := by
      intro hpos hvt
      obtain ⟨k, hSk, hpk⟩ := exS hpos
      apply hR k
      rw [if_pos hSk, hvt, EReal.coe_mul_top_of_pos hpk]
    have hprv : (pr : EReal) * v ≠ ⊤ := by
      intro h
      rw [voi_cmul_top hpr0] at h
      exact hv h.1 h.2
    have huT : ∀ k, ¬ S k → 0 < p k → u k ≠ ⊤ := by
      intro k hSk hpk h
      apply hR k
      rw [if_neg hSk, h, EReal.coe_mul_top_of_pos hpk]
    have hquT : ∀ k, ¬ S k → 0 < p k → (q : EReal) * u k ≠ ⊤ := by
      intro k hSk hpk h
      rw [voi_cmul_top hq0.le] at h
      exact huT k hSk hpk h.2
    have hTne : ¬ ∃ k, (if S k then 0 else (p k : EReal) *
        StochasticProg.ValueOfInfo.badd ((pr : EReal) * v) ((q : EReal) * u k)) = ⊤ := by
      rintro ⟨k, hk⟩
      by_cases hSk : S k
      · rw [if_pos hSk] at hk; exact EReal.zero_ne_top hk
      · rw [if_neg hSk, voi_cmul_top (hp k)] at hk
        obtain ⟨hpk, hb⟩ := hk
        rw [voi_badd_of_ne hprv (hquT k hSk hpk)] at hb
        exact EReal.add_ne_top hprv (hquT k hSk hpk) hb
    rw [if_neg hTne]
    by_cases hB : ∃ k, (p k : EReal) * (if S k then v else u k) = ⊥
    · rw [voi_sum_bot _ hB]
      have hTbot : ∃ k, (if S k then 0 else (p k : EReal) *
          StochasticProg.ValueOfInfo.badd ((pr : EReal) * v) ((q : EReal) * u k)) = ⊥ := by
        obtain ⟨k, hk⟩ := hB
        rw [voi_cmul_bot (hp k)] at hk
        obtain ⟨hpk, hw⟩ := hk
        by_cases hSk : S k
        · rw [if_pos hSk] at hw
          have hprpos : 0 < pr := lt_of_lt_of_le hpk (hSle k hSk)
          obtain ⟨j, hSj, hpj⟩ := exT
          refine ⟨j, ?_⟩
          rw [if_neg hSj, hw, EReal.coe_mul_bot_of_pos hprpos,
            voi_badd_of_ne bot_ne_top (hquT j hSj hpj), EReal.bot_add, EReal.coe_mul_bot_of_pos hpj]
        · rw [if_neg hSk] at hw
          refine ⟨k, ?_⟩
          rw [if_neg hSk, hw, EReal.coe_mul_bot_of_pos hq0, voi_badd_of_ne hprv bot_ne_top,
            EReal.add_bot, EReal.coe_mul_bot_of_pos hpk]
      rw [voi_sum_bot _ hTbot, hqinv, EReal.coe_mul_bot_of_pos hqinv0]
    · push_neg at hB
      have hprvb : (pr : EReal) * v ≠ ⊥ := by
        intro h
        rw [voi_cmul_bot hpr0] at h
        obtain ⟨k, hSk, hpk⟩ := exS h.1
        apply hB k
        rw [if_pos hSk, h.2, EReal.coe_mul_bot_of_pos hpk]
      have hprv_r : (pr : EReal) * v = ((pr * v.toReal : ℝ) : EReal) :=
        voi_cmul_real hpr0 v hprv hprvb
      have hRr : ∀ k, (p k : EReal) * (if S k then v else u k) =
          ((p k * (if S k then v.toReal else (u k).toReal) : ℝ) : EReal) := by
        intro k
        rw [voi_cmul_real (hp k) _ (hR k) (hB k)]
        split_ifs <;> rfl
      have hTr : ∀ k, (if S k then 0 else (p k : EReal) *
          StochasticProg.ValueOfInfo.badd ((pr : EReal) * v) ((q : EReal) * u k)) =
          ((if S k then 0 else p k * (pr * v.toReal + q * (u k).toReal) : ℝ) : EReal) := by
        intro k
        by_cases hSk : S k
        · rw [if_pos hSk, if_pos hSk, EReal.coe_zero]
        · rw [if_neg hSk, if_neg hSk]
          rcases (hp k).eq_or_lt with h0 | hpk
          · rw [← h0, EReal.coe_zero, zero_mul, zero_mul, EReal.coe_zero]
          · have huk : u k ≠ ⊤ := huT k hSk hpk
            have huk' : u k ≠ ⊥ := by
              intro h
              apply hB k
              rw [if_neg hSk, h, EReal.coe_mul_bot_of_pos hpk]
            have hq_r : (q : EReal) * u k = ((q * (u k).toReal : ℝ) : EReal) := by
              rw [EReal.coe_mul, EReal.coe_toReal huk huk']
            rw [hprv_r, hq_r, voi_badd_of_ne (EReal.coe_ne_top _) (EReal.coe_ne_top _),
              ← EReal.coe_add, ← EReal.coe_mul]
      rw [Finset.sum_congr rfl (fun k _ => hTr k), Finset.sum_congr rfl (fun k _ => hRr k),
        ← voi_coe_sum, ← voi_coe_sum, hqinv, ← EReal.coe_mul, EReal.coe_eq_coe_iff]
      have h1 : ∀ k, (if S k then 0 else p k * (pr * v.toReal + q * (u k).toReal)) =
          pr * v.toReal * (if S k then 0 else p k) + q * (if S k then 0 else p k * (u k).toReal) := by
        intro k; split_ifs <;> ring
      have h2 : ∀ k, p k * (if S k then v.toReal else (u k).toReal) =
          v.toReal * (if S k then p k else 0) + (if S k then 0 else p k * (u k).toReal) := by
        intro k; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_congr rfl (fun k _ => h2 k),
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, hT, ← hpr]
      rw [inv_mul_eq_div, div_eq_iff hq0.ne']
      ring

open StochasticProg.ValueOfInfo in
theorem voi_prop7_aux {n1 d K : ℕ} (I : Instance n1 d K)
    (xir : Fin d → ℝ) (hpr1 : refProb I xir < 1) :
    WS I ≤ SPEV I xir ∧ SPEV I xir ≤ RP I := by
  have hpr0 : 0 ≤ refProb I xir := by
    unfold refProb
    exact Finset.sum_nonneg (fun i _ => by split_ifs; exact I.p_nonneg i; exact le_rfl)
  have hq0 : 0 < 1 - refProb I xir := by linarith
  have hqinv_nn : (0 : EReal) ≤ ((1 - refProb I xir : ℝ) : EReal)⁻¹ := by
    rw [← EReal.coe_inv]
    exact EReal.coe_nonneg.mpr (inv_nonneg.mpr hq0.le)
  constructor
  · calc WS I = bsum (fun k => (I.p k : EReal) *
            (if I.xi k = xir then (⨅ x ∈ I.K1, I.z x xir) else (⨅ x ∈ I.K1, I.z x (I.xi k)))) := by
          unfold WS
          congr 1
          funext k
          split_ifs with h
          · rw [h]
          · rfl
      _ = ((1 - refProb I xir : ℝ) : EReal)⁻¹ *
            bsum (fun k => if I.xi k = xir then 0 else (I.p k : EReal) *
              badd ((refProb I xir : EReal) * (⨅ x ∈ I.K1, I.z x xir))
                (((1 - refProb I xir : ℝ) : EReal) * (⨅ x ∈ I.K1, I.z x (I.xi k)))) :=
          (voi_key I.p I.p_nonneg I.p_sum (fun k => I.xi k = xir) (refProb I xir) rfl hpr1
            (1 - refProb I xir) rfl _ _).symm
      _ ≤ SPEV I xir := by
          unfold SPEV
          apply mul_le_mul_of_nonneg_left _ hqinv_nn
          apply voi_bsum_mono_aux
          intro k
          split_ifs
          · exact le_rfl
          · apply mul_le_mul_of_nonneg_left _ (EReal.coe_nonneg.mpr (I.p_nonneg k))
            unfold pairsValue
            refine le_iInf₂ (fun x hx => ?_)
            apply voi_badd_mono
            · exact mul_le_mul_of_nonneg_left (iInf₂_le x hx) (EReal.coe_nonneg.mpr hpr0)
            · exact mul_le_mul_of_nonneg_left (iInf₂_le x hx) (EReal.coe_nonneg.mpr hq0.le)
  · unfold RP
    refine le_iInf₂ (fun x hx => ?_)
    calc SPEV I xir ≤ ((1 - refProb I xir : ℝ) : EReal)⁻¹ *
            bsum (fun k => if I.xi k = xir then 0 else (I.p k : EReal) *
              badd ((refProb I xir : EReal) * I.z x xir)
                (((1 - refProb I xir : ℝ) : EReal) * I.z x (I.xi k))) := by
          unfold SPEV
          apply mul_le_mul_of_nonneg_left _ hqinv_nn
          apply voi_bsum_mono_aux
          intro k
          split_ifs
          · exact le_rfl
          · apply mul_le_mul_of_nonneg_left _ (EReal.coe_nonneg.mpr (I.p_nonneg k))
            unfold pairsValue
            exact iInf₂_le x hx
      _ = bsum (fun k => (I.p k : EReal) * (if I.xi k = xir then I.z x xir else I.z x (I.xi k))) :=
          voi_key I.p I.p_nonneg I.p_sum (fun k => I.xi k = xir) (refProb I xir) rfl hpr1
            (1 - refProb I xir) rfl _ _
      _ = expect I x := by
          unfold expect
          congr 1
          funext k
          split_ifs with h
          · rw [h]
          · rfl

open StochasticProg.ValueOfInfo in
theorem voi_prop8_aux {n1 d K : ℕ} (I : Instance n1 d K)
    (xBarK : Fin K → (Fin n1 → ℝ)) (hxBarK_mem : ∀ k, xBarK k ∈ I.K1)
    (xBarR : Fin n1 → ℝ) (hxBarR_mem : xBarR ∈ I.K1) :
    RP I ≤ EPEV I xBarK xBarR ∧ EPEV I xBarK xBarR ≤ EVRS I xBarR := by
  constructor
  · unfold EPEV RP
    refine le_min (le_iInf (fun k => ?_)) ?_
    · exact iInf₂_le (xBarK k) (hxBarK_mem k)
    · exact iInf₂_le xBarR hxBarR_mem
  · unfold EPEV EVRS
    exact min_le_right _ _

theorem voi_bsub_nonneg {a b : EReal} (h : b ≤ a) :
    (0 : EReal) ≤ StochasticProg.ValueOfInfo.bsub a b := by
  unfold StochasticProg.ValueOfInfo.bsub StochasticProg.ValueOfInfo.badd
  by_cases hc : a = ⊤ ∨ -b = ⊤
  · rw [if_pos hc]; exact le_top
  · rw [if_neg hc]
    have ha : a ≠ ⊤ := fun e => hc (Or.inl e)
    have hb : b ≠ ⊥ := fun e => hc (Or.inr (EReal.neg_eq_top_iff.mpr e))
    induction a using EReal.rec with
    | bot => exact absurd (le_bot_iff.mp h) hb
    | top => exact absurd rfl ha
    | coe x =>
      induction b using EReal.rec with
      | bot => exact absurd rfl hb
      | top => exact absurd (top_le_iff.mp h) (EReal.coe_ne_top x)
      | coe y =>
        rw [← EReal.coe_neg, ← EReal.coe_add]
        exact EReal.coe_nonneg.mpr (by have := EReal.coe_le_coe_iff.mp h; linarith)

theorem voi_bsub_anti (a : EReal) {b b' : EReal} (h : b ≤ b') :
    StochasticProg.ValueOfInfo.bsub a b' ≤ StochasticProg.ValueOfInfo.bsub a b := by
  unfold StochasticProg.ValueOfInfo.bsub
  exact voi_badd_mono le_rfl (EReal.neg_le_neg_iff.mpr h)

open StochasticProg.ValueOfInfo in
theorem solution {n1 d K : ℕ} (I : Instance n1 d K)
    (xir : Fin d → ℝ) (hpr1 : refProb I xir < 1)
    (xBarK : Fin K → (Fin n1 → ℝ))
    (hxBarK_mem : ∀ k, xBarK k ∈ I.K1)
    (hxBarK_opt : ∀ k, badd ((refProb I xir : EReal) * I.z (xBarK k) xir)
        (((1 - refProb I xir : ℝ) : EReal) * I.z (xBarK k) (I.xi k)) =
        pairsValue I xir k)
    (xBarR : Fin n1 → ℝ) (hxBarR_mem : xBarR ∈ I.K1)
    (hxBarR_opt : I.z xBarR xir = ⨅ x ∈ I.K1, I.z x xir) :
    (0 : EReal) ≤ bsub (EVRS I xBarR) (EPEV I xBarK xBarR) ∧
      bsub (EVRS I xBarR) (EPEV I xBarK xBarR) ≤ VSSRef I xBarR ∧
      VSSRef I xBarR ≤ bsub (EVRS I xBarR) (SPEV I xir) ∧
      bsub (EVRS I xBarR) (SPEV I xir) ≤ bsub (EVRS I xBarR) (WS I) := by
  obtain ⟨h7a, h7b⟩ := voi_prop7_aux I xir hpr1
  obtain ⟨h8a, h8b⟩ := voi_prop8_aux I xBarK hxBarK_mem xBarR hxBarR_mem
  refine ⟨voi_bsub_nonneg h8b, ?_, ?_, voi_bsub_anti _ h7a⟩
  · unfold VSSRef
    exact voi_bsub_anti _ h8a
  · unfold VSSRef
    exact voi_bsub_anti _ h7b
