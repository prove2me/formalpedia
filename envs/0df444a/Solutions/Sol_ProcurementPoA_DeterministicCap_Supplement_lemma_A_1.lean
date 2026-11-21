-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.Supplement.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:06:40.197898+00:00
-- url     : https://prove2.me/submissions/c47fd979-8f55-4f33-a699-b38ffd10f8e1

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Monopoly

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A1

variable {R : ℝ} {S : ℝ → ℝ}

lemma S_nonneg (hS : IsAcceptance R S) (b : ℝ) : 0 ≤ S b := by
  obtain ⟨μ, _, _, h⟩ := hS
  rw [h]; exact ENNReal.toReal_nonneg

lemma S_le_one (hS : IsAcceptance R S) (b : ℝ) : S b ≤ 1 := by
  obtain ⟨μ, hp, _, h⟩ := hS
  rw [h]
  have : μ (Set.Ici b) ≤ 1 := prob_le_one
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

lemma S_zero (hS : IsAcceptance R S) {b : ℝ} (hb : R < b) : S b = 0 := by
  obtain ⟨μ, hp, h0, h⟩ := hS
  rw [h]
  have : μ (Set.Ici b) = 0 :=
    measure_mono_null (fun x hx => lt_of_lt_of_le hb hx) h0
  simp [this]

lemma S_leftcont (hS : IsAcceptance R S) (b ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ b', b - δ < b' → S b' ≤ S b + ε := by
  obtain ⟨μ, hp, h0, h⟩ := hS
  have hS' : IsAcceptance R S := ⟨μ, hp, h0, h⟩
  let A : ℕ → Set ℝ := fun k => Set.Ici (b - 1 / ((k : ℝ) + 1))
  have hA : Antitone A := by
    intro j k hjk
    apply Set.Ici_subset_Ici.2
    have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (j : ℝ) ≤ k := by exact_mod_cast hjk
      linarith
    linarith
  have hI : (⋂ k, A k) = Set.Ici b := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Ici, A]
    constructor
    · intro hx
      by_contra hlt
      push_neg at hlt
      have hpos : 0 < b - x := by linarith
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      have := hx k
      linarith
    · intro hx k
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have ht := tendsto_measure_iInter_atTop (μ := μ) (s := A)
    (fun k => measurableSet_Ici.nullMeasurableSet) hA ⟨0, measure_ne_top _ _⟩
  rw [hI] at ht
  have ht2 : Tendsto (fun k => (μ (A k)).toReal) atTop (𝓝 (μ (Set.Ici b)).toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  have hev := ht2.eventually (gt_mem_nhds (show (μ (Set.Ici b)).toReal < (μ (Set.Ici b)).toReal + ε by linarith))
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun b' hb' => ?_⟩
  rw [h b', h b]
  have hle : (μ (Set.Ici b')).toReal ≤ (μ (A k)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (Set.Ici_subset_Ici.2 (by show b - 1 / ((k : ℝ) + 1) ≤ b'; linarith)))
  show _ ≤ (μ (Set.Ici b)).toReal + ε
  have : (μ (A k)).toReal < (μ (Set.Ici b)).toReal + ε := hk
  linarith

lemma f_le_bound (hS : IsAcceptance R S) (c b : ℝ) : (b - c) * S b ≤ max (R - c) 0 := by
  have h0 := S_nonneg hS b
  have h1 := S_le_one hS b
  by_cases hbc : b ≤ c
  · have : (b - c) * S b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h0
    exact this.trans (le_max_right _ _)
  · push_neg at hbc
    by_cases hbR : b ≤ R
    · have : (b - c) * S b ≤ b - c := by nlinarith
      exact (by linarith : b - c ≤ R - c).trans' this |>.trans (le_max_left _ _)
    · push_neg at hbR
      rw [S_zero hS hbR, mul_zero]; exact le_max_right _ _

lemma bdd (hS : IsAcceptance R S) (c : ℝ) :
    BddAbove (Set.range fun b : ℝ => (b - c) * S b) :=
  ⟨max (R - c) 0, by rintro _ ⟨b, rfl⟩; exact f_le_bound hS c b⟩

lemma f_le_P (hS : IsAcceptance R S) (c b : ℝ) : (b - c) * S b ≤ monopolyProfit S c :=
  le_csSup (bdd hS c) ⟨b, rfl⟩

lemma P_nonneg (hS : IsAcceptance R S) (c : ℝ) : 0 ≤ monopolyProfit S c := by
  have := f_le_P hS c c
  simpa using this

lemma P_anti (hS : IsAcceptance R S) : Antitone (monopolyProfit S) := by
  intro c c' hcc'
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨b, rfl⟩
  refine le_trans ?_ (f_le_P hS c b)
  have := S_nonneg hS b
  nlinarith

lemma usc (hS : IsAcceptance R S) {c : ℝ} {b : ℕ → ℝ} {b0 t : ℝ}
    (hb : Tendsto b atTop (𝓝 b0)) (hcb : ∀ k, c ≤ b k)
    (ht : Tendsto (fun k => (b k - c) * S (b k)) atTop (𝓝 t)) :
    t ≤ (b0 - c) * S b0 := by
  have hc0 : c ≤ b0 := ge_of_tendsto' hb hcb
  have key : ∀ ε > 0, t ≤ (b0 - c) * (S b0 + ε) := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := S_leftcont hS b0 ε hε
    have hev : ∀ᶠ k in atTop, b0 - δ < b k :=
      hb.eventually (lt_mem_nhds (by linarith))
    have hlim : Tendsto (fun k => (b k - c) * (S b0 + ε)) atTop (𝓝 ((b0 - c) * (S b0 + ε))) :=
      ((hb.sub_const c).mul_const _)
    refine le_of_tendsto_of_tendsto ht hlim ?_
    filter_upwards [hev] with k hk
    have := hδ' (b k) hk
    have hk0 : 0 ≤ b k - c := by linarith [hcb k]
    exact mul_le_mul_of_nonneg_left this hk0
  have hg : Tendsto (fun ε : ℝ => (b0 - c) * (S b0 + ε)) (𝓝[>] 0) (𝓝 ((b0 - c) * (S b0 + 0))) :=
    ((continuous_const.mul (continuous_const.add continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have := ge_of_tendsto hg (eventually_nhdsWithin_of_forall (fun ε hε => key ε hε))
  simpa using this

lemma attain (hS : IsAcceptance R S) (c : ℝ) (hP : 0 < monopolyProfit S c) :
    ∃ b, (b - c) * S b = monopolyProfit S c := by
  set P := monopolyProfit S c with hPdef
  have hne : (Set.range fun b : ℝ => (b - c) * S b).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hseq : ∀ k : ℕ, ∃ b : ℝ, P - P / 2 * (1 / ((k : ℝ) + 1)) < (b - c) * S b := by
    intro k
    have hlt : P - P / 2 * (1 / ((k : ℝ) + 1)) < monopolyProfit S c := by
      have : 0 < P / 2 * (1 / ((k : ℝ) + 1)) := by positivity
      linarith
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := exists_lt_of_lt_csSup hne hlt
    exact ⟨b, hb⟩
  choose b hb using hseq
  have hpos : ∀ k, 0 < (b k - c) * S (b k) := by
    intro k
    have h1 : P / 2 * (1 / ((k : ℝ) + 1)) ≤ P / 2 := by
      have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ k := by positivity
        linarith
      nlinarith
    have := hb k
    linarith
  have hmem : ∀ k, b k ∈ Set.Icc c R := by
    intro k
    have hp := hpos k
    have h0 := S_nonneg hS (b k)
    constructor
    · by_contra hlt; push_neg at hlt
      have : (b k - c) * S (b k) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h0
      linarith
    · by_contra hlt; push_neg at hlt
      rw [S_zero hS hlt] at hp; simp at hp
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hf : Tendsto (fun k => (b k - c) * S (b k)) atTop (𝓝 P) := by
    have hlow : Tendsto (fun k : ℕ => P - P / 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 P) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (P / 2)
      simpa using (tendsto_const_nhds (x := P)).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun k => (hb k).le) (fun k => f_le_P hS c (b k))
  have := usc hS (c := c) (b := b ∘ φ) hlim (fun k => (hmem _).1)
    (hf.comp hφ.tendsto_atTop)
  exact ⟨a, le_antisymm (f_le_P hS c a) this⟩

lemma exists_max_bid (hS : IsAcceptance R S) (c : ℝ) (hc : monopolyProfit S c ≠ 0) :
    ∃ b, (b - c) * S b = monopolyProfit S c ∧ sigma R S c = S b := by
  have hP : 0 < monopolyProfit S c := lt_of_le_of_ne (P_nonneg hS c) (Ne.symm hc)
  set P := monopolyProfit S c with hPdef
  set M : Set ℝ := {b | (b - c) * S b = P} with hM
  obtain ⟨b0, hb0⟩ := attain hS c hP
  have hMne : M.Nonempty := ⟨b0, hb0⟩
  have hMgt : ∀ b ∈ M, c < b ∧ b ≤ R := by
    intro b hb
    have hp : 0 < (b - c) * S b := by rw [hb]; exact hP
    have h0 := S_nonneg hS b
    constructor
    · by_contra hlt; push_neg at hlt
      have : (b - c) * S b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h0
      linarith
    · by_contra hlt; push_neg at hlt
      rw [S_zero hS hlt] at hp; simp at hp
  have hMbdd : BddAbove M := ⟨R, fun b hb => (hMgt b hb).2⟩
  obtain ⟨u, -, hu, humem⟩ := exists_seq_tendsto_sSup hMne hMbdd
  have hcu : ∀ k, c ≤ u k := fun k => (hMgt _ (humem k)).1.le
  have hconst : Tendsto (fun k => (u k - c) * S (u k)) atTop (𝓝 P) := by
    have : (fun k => (u k - c) * S (u k)) = fun _ => P := funext fun k => humem k
    rw [this]; exact tendsto_const_nhds
  have h1 := usc hS hu hcu hconst
  have hB : (sSup M - c) * S (sSup M) = P := le_antisymm (f_le_P hS c _) h1
  refine ⟨sSup M, hB, ?_⟩
  unfold sigma monopolyBid
  rw [if_neg hc, if_neg hc]

lemma sigma_nonneg (hS : IsAcceptance R S) (c : ℝ) : 0 ≤ sigma R S c := by
  unfold sigma; split_ifs
  · exact le_rfl
  · exact S_nonneg hS _

lemma sigma_le_one (hS : IsAcceptance R S) (c : ℝ) : sigma R S c ≤ 1 := by
  unfold sigma; split_ifs
  · exact zero_le_one
  · exact S_le_one hS _

lemma sigma_anti (hS : IsAcceptance R S) : Antitone (sigma R S) := by
  intro c c' hcc'
  by_cases hc' : monopolyProfit S c' = 0
  · have : sigma R S c' = 0 := by unfold sigma; rw [if_pos hc']
    rw [this]; exact sigma_nonneg hS c
  · have hPc : monopolyProfit S c ≠ 0 := by
      have h1 := P_anti hS hcc'
      have h2 := P_nonneg hS c'
      have h3 : 0 < monopolyProfit S c' := lt_of_le_of_ne h2 (Ne.symm hc')
      linarith
    obtain ⟨b, hb, hsb⟩ := exists_max_bid hS c hPc
    obtain ⟨b', hb', hsb'⟩ := exists_max_bid hS c' hc'
    rcases hcc'.eq_or_lt with h | h
    · subst h
      exact le_rfl
    rw [hsb, hsb']
    have h1 := f_le_P hS c b'
    have h2 := f_le_P hS c' b
    rw [← hb] at h1
    rw [← hb'] at h2
    have h3 : 0 ≤ (c' - c) * (S b - S b') := by nlinarith
    have := (mul_nonneg_iff_of_pos_left (sub_pos.2 h)).1 h3
    linarith

lemma key (hS : IsAcceptance R S) {c c' : ℝ} (h : c < c') :
    (c' - c) * sigma R S c' ≤ monopolyProfit S c - monopolyProfit S c' := by
  by_cases hc' : monopolyProfit S c' = 0
  · have : sigma R S c' = 0 := by unfold sigma; rw [if_pos hc']
    rw [this, hc']; simpa using P_nonneg hS c
  · obtain ⟨b, hb, hsb⟩ := exists_max_bid hS c' hc'
    have h1 := f_le_P hS c b
    rw [hsb]
    nlinarith

lemma main (hS : IsAcceptance R S) (x : ℝ) (hx : 1 ≤ x) :
    ∫ t in (1 : ℝ)..x, sigma R S t ≤ monopolyProfit S 1 := by
  have hσ := sigma_anti hS
  have hP := P_anti hS
  have iσ : ∀ a b : ℝ, IntervalIntegrable (sigma R S) volume a b := fun a b =>
    hσ.intervalIntegrable
  have iP : ∀ a b : ℝ, IntervalIntegrable (monopolyProfit S) volume a b := fun a b =>
    hP.intervalIntegrable
  refine le_of_forall_pos_le_add fun h hh => ?_
  have hσh : Antitone (fun t => sigma R S (t + h)) :=
    hσ.comp_monotone (fun a b hab => by linarith)
  have hPh : Antitone (fun t => monopolyProfit S (t + h)) :=
    hP.comp_monotone (fun a b hab => by linarith)
  -- h * ∫ σ(t+h) ≤ ∫ (P t - P (t+h))
  have step1 : ∫ t in (1 : ℝ)..x, h * sigma R S (t + h) ≤
      ∫ t in (1 : ℝ)..x, (monopolyProfit S t - monopolyProfit S (t + h)) := by
    apply intervalIntegral.integral_mono_on hx
    · exact (hσh.intervalIntegrable).const_mul h
    · exact (iP _ _).sub hPh.intervalIntegrable
    · intro t ht
      have := key hS (c := t) (c' := t + h) (by linarith)
      simpa using this
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (iP _ _) hPh.intervalIntegrable,
    intervalIntegral.integral_comp_add_right (monopolyProfit S) h,
    intervalIntegral.integral_comp_add_right (sigma R S) h] at step1
  have e1 : (∫ t in (1 : ℝ)..x, monopolyProfit S t) - ∫ t in (1 + h)..(x + h), monopolyProfit S t
      = (∫ t in (1 : ℝ)..(1 + h), monopolyProfit S t) - ∫ t in x..(x + h), monopolyProfit S t := by
    have a1 := intervalIntegral.integral_add_adjacent_intervals (iP 1 x) (iP x (x + h))
    have a2 := intervalIntegral.integral_add_adjacent_intervals (iP 1 (1 + h)) (iP (1 + h) (x + h))
    linarith
  have e2 : ∫ t in (1 : ℝ)..x, sigma R S t
      = (∫ t in (1 + h)..(x + h), sigma R S t) + (∫ t in (1 : ℝ)..(1 + h), sigma R S t)
        - ∫ t in x..(x + h), sigma R S t := by
    have a1 := intervalIntegral.integral_add_adjacent_intervals (iσ 1 x) (iσ x (x + h))
    have a2 := intervalIntegral.integral_add_adjacent_intervals (iσ 1 (1 + h)) (iσ (1 + h) (x + h))
    linarith
  have b1 : ∫ t in (1 : ℝ)..(1 + h), monopolyProfit S t ≤ h * monopolyProfit S 1 := by
    have := intervalIntegral.integral_mono_on (a := 1) (b := 1 + h) (by linarith) (iP _ _)
      (intervalIntegrable_const (c := monopolyProfit S 1))
      (fun t ht => hP ht.1)
    simpa using this
  have b2 : 0 ≤ ∫ t in x..(x + h), monopolyProfit S t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => P_nonneg hS t)
  have b3 : ∫ t in (1 : ℝ)..(1 + h), sigma R S t ≤ h := by
    have := intervalIntegral.integral_mono_on (a := 1) (b := 1 + h) (by linarith) (iσ _ _)
      (intervalIntegrable_const (c := (1 : ℝ)))
      (fun t _ => sigma_le_one hS t)
    simpa using this
  have b4 : 0 ≤ ∫ t in x..(x + h), sigma R S t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => sigma_nonneg hS t)
  have b5 : ∫ t in (1 + h)..(x + h), sigma R S t ≤ monopolyProfit S 1 := by
    have : h * ∫ t in (1 + h)..(x + h), sigma R S t ≤ h * monopolyProfit S 1 := by
      linarith
    exact le_of_mul_le_mul_left this hh
  linarith

end ProcurementPoA.DeterministicCap.Supplement.Dev.A1

namespace ProcurementPoA.DeterministicCap.Supplement

theorem chk_lemma_A_1 (R : ℝ) (hR : 1 ≤ R) (S : ℝ → ℝ) (hS : IsAcceptance R S)
    (x : ℝ) (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, sigma R S t) ≤ monopolyProfit S 1 :=
  Dev.A1.main hS x hx

end ProcurementPoA.DeterministicCap.Supplement
end

theorem solution : type_of% @ProcurementPoA.DeterministicCap.Supplement.chk_lemma_A_1 := @ProcurementPoA.DeterministicCap.Supplement.chk_lemma_A_1
