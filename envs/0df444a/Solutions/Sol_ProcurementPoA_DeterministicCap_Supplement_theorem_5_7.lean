-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.Supplement.theorem_5_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:18:47.757069+00:00
-- url     : https://prove2.me/submissions/7167b5fd-9416-4620-adbe-3462acbe5e22

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Monopoly
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Mechanism
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_RivalInstance
import Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_lemma_5_5
universe uB uC

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

lemma S_anti (hS : IsAcceptance R S) : Antitone S := by
  intro b b' hbb'
  obtain ⟨μ, hp, _, h⟩ := hS
  rw [h, h]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ici_subset_Ici.2 hbb'))

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

lemma sigma_le_one (hS : IsAcceptance R S) (c : ℝ) : sigma R S c ≤ 1 := by
  unfold sigma; split_ifs
  · exact zero_le_one
  · exact S_le_one hS _

lemma key (hS : IsAcceptance R S) {c c' : ℝ} (h : c < c') :
    (c' - c) * sigma R S c' ≤ monopolyProfit S c - monopolyProfit S c' := by
  by_cases hc' : monopolyProfit S c' = 0
  · have : sigma R S c' = 0 := by unfold sigma; rw [if_pos hc']
    rw [this, hc']; simpa using P_nonneg hS c
  · obtain ⟨b, hb, hsb⟩ := exists_max_bid hS c' hc'
    have h1 := f_le_P hS c b
    rw [hsb]
    nlinarith

end ProcurementPoA.DeterministicCap.Supplement.Dev.A1

namespace ProcurementPoA.DeterministicCap.Supplement

end ProcurementPoA.DeterministicCap.Supplement
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical
open ProcurementPoA.DeterministicCap.Supplement.Dev.A1

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.M5A

variable {R : ℝ} {S : ℝ → ℝ}

/-- the monopoly bid is a maximizer, and the largest one -/
lemma bid_spec (hS : IsAcceptance R S) (c : ℝ) (hc : monopolyProfit S c ≠ 0) :
    (monopolyBid R S c - c) * S (monopolyBid R S c) = monopolyProfit S c ∧
      ∀ b, (b - c) * S b = monopolyProfit S c → b ≤ monopolyBid R S c := by
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
  have hmb : monopolyBid R S c = sSup M := by
    unfold monopolyBid; rw [if_neg hc]
  rw [hmb]
  exact ⟨hB, fun b hb => le_csSup hMbdd hb⟩

lemma attain_ge (hS : IsAcceptance R S) (c t v : ℝ) (hv : 0 < v)
    (hle : ∀ b, (b - c) * S b ≤ v)
    (happ : ∀ k : ℕ, ∃ b, t ≤ b ∧ v - v / 2 * (1 / ((k : ℝ) + 1)) < (b - c) * S b) :
    ∃ b, t ≤ b ∧ (b - c) * S b = v := by
  choose b hbt hb using happ
  have hpos : ∀ k, 0 < (b k - c) * S (b k) := by
    intro k
    have h1 : v / 2 * (1 / ((k : ℝ) + 1)) ≤ v / 2 := by
      have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ k := by positivity
        linarith
      nlinarith
    have := hb k
    linarith
  have hmem : ∀ k, b k ∈ Set.Icc (max t c) R := by
    intro k
    have hp := hpos k
    have h0 := S_nonneg hS (b k)
    refine ⟨max_le (hbt k) ?_, ?_⟩
    · by_contra hlt; push_neg at hlt
      have : (b k - c) * S (b k) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h0
      linarith
    · by_contra hlt; push_neg at hlt
      rw [S_zero hS hlt] at hp; simp at hp
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hf : Tendsto (fun k => (b k - c) * S (b k)) atTop (𝓝 v) := by
    have hlow : Tendsto (fun k : ℕ => v - v / 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 v) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (v / 2)
      simpa using (tendsto_const_nhds (x := v)).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun k => (hb k).le) (fun k => hle (b k))
  have := usc hS (c := c) (b := b ∘ φ) hlim (fun k => (le_max_right _ _).trans (hmem _).1)
    (hf.comp hφ.tendsto_atTop)
  exact ⟨a, (le_max_left _ _).trans ha.1, le_antisymm (hle a) this⟩


noncomputable def phi (S : ℝ → ℝ) (c b : ℝ) : ℝ := (b - c) * S b

lemma rat_approx (hS : IsAcceptance R S) (c : ℝ) {a b : ℝ} (hab : a < b) (hca : c ≤ a)
    (ε : ℝ) (hε : 0 < ε) : ∃ q : ℚ, a < q ∧ (q : ℝ) < b ∧ phi S c b - ε < phi S c q := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max a (b - ε) < b from max_lt hab (by linarith))
  have hqa : a < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hqb : b - ε < q := lt_of_le_of_lt (le_max_right _ _) hq1
  refine ⟨q, hqa, hq2, ?_⟩
  unfold phi
  have h1 := S_anti hS hq2.le
  have h2 := S_le_one hS b
  have h3 := S_nonneg hS b
  nlinarith

lemma bdd_rat (hS : IsAcceptance R S) (c : ℝ) {ι : Type} (f : ι → ℝ) :
    BddAbove (Set.range fun i => phi S c (f i)) :=
  ⟨max (R - c) 0, by rintro _ ⟨i, rfl⟩; exact f_le_bound hS c (f i)⟩

lemma P_eq_iSup (hS : IsAcceptance R S) (c : ℝ) :
    monopolyProfit S c = ⨆ q : ℚ, phi S c q := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨b, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hbc : b ≤ c
    · obtain ⟨q, hq⟩ := exists_rat_gt c
      have h1 : phi S c b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (S_nonneg hS b)
      have h2 : 0 ≤ phi S c q := mul_nonneg (by linarith) (S_nonneg hS _)
      have := le_ciSup (bdd_rat hS c (fun q : ℚ => (q : ℝ))) q
      show phi S c b ≤ _
      linarith
    · push_neg at hbc
      obtain ⟨q, -, -, hq⟩ := rat_approx hS c hbc le_rfl ε hε
      have := le_ciSup (bdd_rat hS c (fun q : ℚ => (q : ℝ))) q
      show phi S c b ≤ _
      linarith
  · apply ciSup_le
    intro q
    exact f_le_P hS c q

noncomputable def Gt (S : ℝ → ℝ) (c t : ℝ) : ℝ :=
  max (phi S c t) (⨆ q : {q : ℚ // t < (q : ℝ)}, phi S c (q : ℝ))

lemma phi_le_Gt (hS : IsAcceptance R S) (c t b : ℝ) (hb : t ≤ b) : phi S c b ≤ Gt S c t := by
  have hbdd := bdd_rat hS c (fun q : {q : ℚ // t < (q : ℝ)} => ((q : ℚ) : ℝ))
  rcases hb.eq_or_lt with h | h
  · subst h; exact le_max_left _ _
  refine le_trans ?_ (le_max_right _ _)
  by_cases hbc : b ≤ c
  · obtain ⟨q, hq⟩ := exists_rat_gt (max t c)
    have hq' : t < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq
    have h1 : phi S c b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (S_nonneg hS b)
    have h2 : 0 ≤ phi S c q := mul_nonneg (by have := le_max_right t c; linarith) (S_nonneg hS _)
    have := le_ciSup hbdd ⟨q, hq'⟩
    linarith
  · push_neg at hbc
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq1, -, hq⟩ := rat_approx hS c (a := max t c) (b := b)
      (max_lt h hbc) (le_max_right _ _) ε hε
    have hq' : t < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
    have := le_ciSup hbdd ⟨q, hq'⟩
    linarith

lemma ge_iff (hS : IsAcceptance R S) (c t : ℝ) (hc : monopolyProfit S c ≠ 0) :
    t ≤ monopolyBid R S c ↔ monopolyProfit S c ≤ Gt S c t := by
  obtain ⟨hB, hmax⟩ := bid_spec hS c hc
  have hP : 0 < monopolyProfit S c := lt_of_le_of_ne (P_nonneg hS c) (Ne.symm hc)
  constructor
  · intro h
    have := phi_le_Gt hS c t _ h
    unfold phi at this
    linarith
  · intro h
    by_cases h1 : monopolyProfit S c ≤ phi S c t
    · exact hmax t (le_antisymm (f_le_P hS c t) h1)
    · push_neg at h1
      have h2 : monopolyProfit S c ≤ ⨆ q : {q : ℚ // t < (q : ℝ)}, phi S c (q : ℝ) := by
        unfold Gt at h
        rcases le_max_iff.1 h with h' | h'
        · exact absurd h' (not_le.2 h1)
        · exact h'
      have hbdd := bdd_rat hS c (fun q : {q : ℚ // t < (q : ℝ)} => ((q : ℚ) : ℝ))
      have hne : Nonempty {q : ℚ // t < (q : ℝ)} := by
        obtain ⟨q, hq⟩ := exists_rat_gt t
        exact ⟨⟨q, hq⟩⟩
      have happ : ∀ k : ℕ, ∃ b, t ≤ b ∧ monopolyProfit S c - monopolyProfit S c / 2 * (1 / ((k : ℝ) + 1))
          < (b - c) * S b := by
        intro k
        have hδ : 0 < monopolyProfit S c / 2 * (1 / ((k : ℝ) + 1)) := by positivity
        obtain ⟨q, hq⟩ := exists_lt_of_lt_ciSup
          (show monopolyProfit S c - monopolyProfit S c / 2 * (1 / ((k : ℝ) + 1)) <
            ⨆ q : {q : ℚ // t < (q : ℝ)}, phi S c (q : ℝ) by linarith)
        exact ⟨q, (q.2).le, hq⟩
      obtain ⟨b, hbt, hb⟩ := attain_ge hS c t _ hP (fun b => f_le_P hS c b) happ
      exact hbt.trans (hmax b hb)

end ProcurementPoA.DeterministicCap.Supplement.Dev.M5A
end

section
set_option autoImplicit false

open Filter Topology

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

variable {n : ℕ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

variable {n : ℕ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31A
end

section
set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31B

variable {n : ℕ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31B
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31A
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31B
open ProcurementPoA.DeterministicCap

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31C

variable {n : ℕ}

lemma sel_one (τ : TieRule n) (v : Suppliers n → ℝ) (i : Suppliers n)
    (h : ∀ j, j ≠ i → v i < v j) : τ.select v {i} = 1 := by
  have h1 := τ.lowest_only v
  have h2 : ∀ᵐ k ∂(τ.select v), k = i := by
    filter_upwards [h1] with k hk
    by_contra hki
    have := hk i
    exact absurd (h k hki) (not_lt.2 this)
  have h3 : ({i} : Set (Suppliers n)) =ᵐ[τ.select v] (univ : Set (Suppliers n)) := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [h2] with k hk
    simp [hk]
  rw [measure_congr h3, measure_univ]

lemma sel_zero (τ : TieRule n) (v : Suppliers n → ℝ) (i : Suppliers n)
    (h : ∃ j, v j < v i) : τ.select v {i} = 0 := by
  obtain ⟨j, hj⟩ := h
  have h1 := τ.lowest_only v
  have h2 : ∀ᵐ k ∂(τ.select v), k ≠ i := by
    filter_upwards [h1] with k hk hki
    subst hki
    exact absurd (hk j) (not_le.2 hj)
  exact measure_mono_null (fun k hk => not_not.2 (mem_singleton_iff.1 hk)) (ae_iff.1 h2)

lemma sum_select {n : ℕ} (τ : TieRule n) (b : Suppliers n → ℝ) : ∑ i, τ.select b {i} = 1 := by
  rw [sum_measure_singleton]; simp

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31C
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Classical
open ProcurementPoA.DeterministicCap.Supplement.Dev.A1
open ProcurementPoA.DeterministicCap.Supplement.Dev.M5A

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.M5B


variable {R : ℝ} {Sig : Type uB} [MeasurableSpace Sig]

lemma meas_Sacc (M : PhantomMechanism R Sig) (b : ℝ) :
    Measurable fun s => signalAcceptance M s b :=
  (Kernel.measurable_coe M.phantom measurableSet_Ici).ennreal_toReal

lemma meas_good (M : PhantomMechanism R Sig) :
    MeasurableSet {s | M.phantom s (Ioi R) = 0} :=
  (Kernel.measurable_coe M.phantom measurableSet_Ioi) (measurableSet_singleton 0)

lemma isAcc_of_good (M : PhantomMechanism R Sig) {s : Sig} (hs : M.phantom s (Ioi R) = 0) :
    IsAcceptance R (signalAcceptance M s) :=
  ⟨M.phantom s, inferInstance, hs, fun b => rfl⟩

lemma meas_phi (M : PhantomMechanism R Sig) (c b : ℝ) :
    Measurable fun s => phi (signalAcceptance M s) c b :=
  (meas_Sacc M b).const_mul (b - c)

noncomputable def Bs (M : PhantomMechanism R Sig) (c : ℝ) (s : Sig) : ℝ :=
  if M.phantom s (Ioi R) = 0 then monopolyBid R (signalAcceptance M s) c else R + 1

theorem measurable_Bs (M : PhantomMechanism R Sig) (c : ℝ) : Measurable (Bs M c) := by
  apply measurable_of_Ici
  intro t
  let P' : Sig → ℝ := fun s => ⨆ q : ℚ, phi (signalAcceptance M s) c q
  let G' : Sig → ℝ := fun s => max (phi (signalAcceptance M s) c t)
    (⨆ q : {q : ℚ // t < (q : ℝ)}, phi (signalAcceptance M s) c (q : ℝ))
  have hP' : Measurable P' := Measurable.iSup fun q => meas_phi M c q
  have hG' : Measurable G' :=
    (meas_phi M c t).max (Measurable.iSup fun q => meas_phi M c q)
  have e : Bs M c ⁻¹' Ici t =
      ({s | M.phantom s (Ioi R) = 0} ∩ (({s | P' s = 0} ∩ {_s | t ≤ R + 1}) ∪
        ({s | P' s ≠ 0} ∩ {s | P' s ≤ G' s}))) ∪
      ({s | M.phantom s (Ioi R) = 0}ᶜ ∩ {_s | t ≤ R + 1}) := by
    ext s
    simp only [mem_preimage, mem_Ici, mem_union, mem_inter_iff, mem_setOf_eq, mem_compl_iff, Bs]
    by_cases hs : M.phantom s (Ioi R) = 0
    · have hacc := isAcc_of_good M hs
      have hP : monopolyProfit (signalAcceptance M s) c = P' s := P_eq_iSup hacc c
      simp only [hs, if_true, true_and, not_true, false_and, or_false]
      by_cases h0 : P' s = 0
      · have : monopolyProfit (signalAcceptance M s) c = 0 := by rw [hP, h0]
        simp [monopolyBid, this, h0]
      · have h1 : monopolyProfit (signalAcceptance M s) c ≠ 0 := by rw [hP]; exact h0
        rw [ge_iff hacc c t h1, hP]
        simp [h0, G', Gt]
    · simp [hs]
  rw [e]
  refine MeasurableSet.union (MeasurableSet.inter (meas_good M) ?_) (MeasurableSet.inter (meas_good M).compl (MeasurableSet.const _))
  refine MeasurableSet.union (MeasurableSet.inter (measurableSet_eq_fun hP' measurable_const) (MeasurableSet.const _)) (MeasurableSet.inter ?_ (measurableSet_le hP' hG'))
  exact (measurableSet_eq_fun hP' measurable_const).compl

end ProcurementPoA.DeterministicCap.Supplement.Dev.M5B
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Classical
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement.Dev.A1
open ProcurementPoA.DeterministicCap.Supplement.Dev.M5A
open ProcurementPoA.DeterministicCap.Supplement.Dev.M5B

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.M5C


/-! ### a tie rule -/

noncomputable def firstLow {n : ℕ} (b : Suppliers n → ℝ) : Suppliers n :=
  (Finset.univ.filter (fun i => ∀ j, b i ≤ b j)).min' (by
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ b Finset.univ_nonempty
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩)

lemma firstLow_mem {n : ℕ} (b : Suppliers n → ℝ) : ∀ j, b (firstLow b) ≤ b j := by
  have := Finset.min'_mem (Finset.univ.filter (fun i => ∀ j, b i ≤ b j)) (by
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ b Finset.univ_nonempty
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩)
  exact (Finset.mem_filter.1 this).2

lemma firstLow_eq_iff {n : ℕ} (b : Suppliers n → ℝ) (i : Suppliers n) :
    firstLow b = i ↔ (∀ j, b i ≤ b j) ∧ ∀ k : Suppliers n, k < i → ∃ j, b j < b k := by
  constructor
  · intro h
    refine ⟨fun j => h ▸ firstLow_mem b j, fun k hk => ?_⟩
    by_contra hcon
    push_neg at hcon
    have hmem : k ∈ Finset.univ.filter (fun i => ∀ j, b i ≤ b j) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩
    have := Finset.min'_le _ k hmem
    have h2 : firstLow b ≤ k := this
    rw [h] at h2
    exact absurd hk (not_lt.2 h2)
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Finset.min'_le _ i (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩)
    · by_contra hlt
      push_neg at hlt
      obtain ⟨j, hj⟩ := h2 _ hlt
      exact absurd (firstLow_mem b j) (not_le.2 hj)

lemma measurable_firstLow {n : ℕ} : Measurable (firstLow : (Suppliers n → ℝ) → Suppliers n) := by
  apply measurable_to_countable'
  intro i
  have : firstLow ⁻¹' {i} =
      {b : Suppliers n → ℝ | (∀ j, b i ≤ b j) ∧ ∀ k : Suppliers n, k < i → ∃ j, b j < b k} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact firstLow_eq_iff b i
  rw [this]
  have h1 : MeasurableSet {b : Suppliers n → ℝ | ∀ j, b i ≤ b j} := by
    have : {b : Suppliers n → ℝ | ∀ j, b i ≤ b j} = ⋂ j, {b | b i ≤ b j} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
  have h2 : MeasurableSet {b : Suppliers n → ℝ | ∀ k : Suppliers n, k < i → ∃ j, b j < b k} := by
    have : {b : Suppliers n → ℝ | ∀ k : Suppliers n, k < i → ∃ j, b j < b k} =
        ⋂ k, ⋂ (_ : k < i), ⋃ j, {b | b j < b k} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun j => measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply k)
  exact h1.inter h2

noncomputable def tie (n : ℕ) : TieRule n where
  select := Kernel.deterministic firstLow measurable_firstLow
  markov := inferInstance
  lowest_only b := by
    simp only [Kernel.deterministic_apply]
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 (firstLow_mem b)

/-! ### Dirac helpers -/


/-! ### the two-supplier instance -/

variable {R : ℝ} {Sig : Type uC} [MeasurableSpace Sig]

end ProcurementPoA.DeterministicCap.Supplement.Dev.M5C

namespace ProcurementPoA.DeterministicCap.Supplement


end ProcurementPoA.DeterministicCap.Supplement
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! Blueprint for Lemma A.2 (rival equilibrium). Every `sorry` here is a stub proved in a Part. -/
/-! ## Part C: probability laws from CDFs -/
def IsCDF (F : ℝ → ℝ) : Prop :=
  Monotone F ∧ (∀ x, ContinuousWithinAt F (Ici x) x) ∧
    Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1)

noncomputable def cdfLaw (F : ℝ → ℝ) : Measure ℝ := by
  classical
  exact if h : IsCDF F then (StieltjesFunction.mk F h.1 h.2.1).measure else Measure.dirac 0

instance cdfLaw_isProb (F : ℝ → ℝ) : IsProbabilityMeasure (cdfLaw F) := by
  classical
  by_cases h : IsCDF F
  · have e : cdfLaw F = (StieltjesFunction.mk F h.1 h.2.1).measure := by
      unfold cdfLaw; rw [dif_pos h]
    rw [e]; exact StieltjesFunction.isProbabilityMeasure _ h.2.2.1 h.2.2.2
  · unfold cdfLaw; rw [dif_neg h]; infer_instance

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! ## Part C helpers -/
lemma xlaw_eq {F : ℝ → ℝ} (h : IsCDF F) :
    cdfLaw F = (StieltjesFunction.mk F h.1 h.2.1).measure := by
  unfold cdfLaw; rw [dif_pos h]

lemma xleftLim {F : ℝ → ℝ} (h : IsCDF F) (x L : ℝ) (hL : Tendsto F (𝓝[<] x) (𝓝 L)) :
    Function.leftLim (⇑(StieltjesFunction.mk F h.1 h.2.1)) x = L :=
  leftLim_eq_of_tendsto hL

lemma xlaw_Iic {F : ℝ → ℝ} (h : IsCDF F) (x : ℝ) :
    cdfLaw F (Iic x) = ENNReal.ofReal (F x) := by
  rw [xlaw_eq h, (StieltjesFunction.mk F h.1 h.2.1).measure_Iic h.2.2.1 x, sub_zero]

lemma xlaw_Ioi {F : ℝ → ℝ} (h : IsCDF F) (x : ℝ) :
    cdfLaw F (Ioi x) = ENNReal.ofReal (1 - F x) := by
  rw [xlaw_eq h, (StieltjesFunction.mk F h.1 h.2.1).measure_Ioi h.2.2.2 x]

lemma xlaw_singleton {F : ℝ → ℝ} (h : IsCDF F) (x L : ℝ)
    (hL : Tendsto F (𝓝[<] x) (𝓝 L)) :
    cdfLaw F {x} = ENNReal.ofReal (F x - L) := by
  rw [xlaw_eq h, StieltjesFunction.measure_singleton, xleftLim h x L hL]

lemma xlaw_Iio {F : ℝ → ℝ} (h : IsCDF F) (x L : ℝ)
    (hL : Tendsto F (𝓝[<] x) (𝓝 L)) :
    cdfLaw F (Iio x) = ENNReal.ofReal L := by
  rw [xlaw_eq h, (StieltjesFunction.mk F h.1 h.2.1).measure_Iio h.2.2.1 x, xleftLim h x L hL,
    sub_zero]

lemma xlaw_Ici {F : ℝ → ℝ} (h : IsCDF F) (x L : ℝ)
    (hL : Tendsto F (𝓝[<] x) (𝓝 L)) :
    cdfLaw F (Ici x) = ENNReal.ofReal (1 - L) := by
  rw [xlaw_eq h, (StieltjesFunction.mk F h.1 h.2.1).measure_Ici h.2.2.2 x, xleftLim h x L hL]

lemma xlaw_Ico {F : ℝ → ℝ} (h : IsCDF F) (x y Lx Ly : ℝ)
    (hx : Tendsto F (𝓝[<] x) (𝓝 Lx)) (hy : Tendsto F (𝓝[<] y) (𝓝 Ly)) :
    cdfLaw F (Ico x y) = ENNReal.ofReal (Ly - Lx) := by
  rw [xlaw_eq h, StieltjesFunction.measure_Ico, xleftLim h x Lx hx, xleftLim h y Ly hy]

/-! ## A generic CDF shape: `K` below `c`, `1` from `c` -/
noncomputable def pw (K : ℝ → ℝ) (c x : ℝ) : ℝ := if x < c then K x else 1

structure GoodK (K : ℝ → ℝ) (a : ℝ) : Prop where
  cont : Continuous K
  mono : Monotone K
  le1 : ∀ x, K x ≤ 1
  zero : ∀ x, x ≤ a → K x = 0

lemma pw_lt {K : ℝ → ℝ} {c x : ℝ} (hx : x < c) : pw K c x = K x := by
  simp only [pw]; rw [if_pos hx]

lemma pw_ge {K : ℝ → ℝ} {c x : ℝ} (hx : c ≤ x) : pw K c x = 1 := by
  simp only [pw]; rw [if_neg (not_lt.2 hx)]

lemma pw_mono {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c : ℝ) : Monotone (pw K c) := by
  intro x y hxy
  by_cases hy : y < c
  · rw [pw_lt hy, pw_lt (lt_of_le_of_lt hxy hy)]; exact hK.mono hxy
  · rw [pw_ge (not_lt.1 hy)]
    by_cases hx : x < c
    · rw [pw_lt hx]; exact hK.le1 x
    · rw [pw_ge (not_lt.1 hx)]

lemma pw_rc {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c x : ℝ) :
    ContinuousWithinAt (pw K c) (Ici x) x := by
  by_cases hx : x < c
  · have : K =ᶠ[𝓝 x] pw K c := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      rw [pw_lt hy]
    exact ((hK.cont.continuousAt).congr this).continuousWithinAt
  · have : ∀ y ∈ Ici x, pw K c y = 1 := fun y hy => pw_ge ((not_lt.1 hx).trans hy)
    exact continuousWithinAt_const.congr this (this x self_mem_Ici)

lemma pw_isCDF {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c : ℝ) : IsCDF (pw K c) := by
  refine ⟨pw_mono hK c, pw_rc hK c, ?_, ?_⟩
  · have : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atBot] pw K c := by
      filter_upwards [eventually_le_atBot (min a c - 1)] with y hy
      rw [pw_lt (by linarith [min_le_right a c]), hK.zero y (by linarith [min_le_left a c])]
    exact tendsto_const_nhds.congr' this
  · have : (fun _ : ℝ => (1 : ℝ)) =ᶠ[atTop] pw K c := by
      filter_upwards [eventually_ge_atTop c] with y hy
      rw [pw_ge hy]
    exact tendsto_const_nhds.congr' this

lemma pw_left {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c x : ℝ) (hx : x ≤ c) :
    Tendsto (pw K c) (𝓝[<] x) (𝓝 (K x)) := by
  have : K =ᶠ[𝓝[<] x] pw K c := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [pw_lt (lt_of_lt_of_le hy hx)]
  exact ((hK.cont.tendsto x).mono_left nhdsWithin_le_nhds).congr' this

lemma pw_left_gt {K : ℝ → ℝ} (c x : ℝ) (hx : c < x) :
    Tendsto (pw K c) (𝓝[<] x) (𝓝 1) := by
  have : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝[<] x] pw K c := by
    filter_upwards [Ioo_mem_nhdsLT hx] with y hy
    rw [pw_ge hy.1.le]
  exact tendsto_const_nhds.congr' this

lemma pwl_Ioi {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c x : ℝ) :
    cdfLaw (pw K c) (Ioi x) = ENNReal.ofReal (1 - pw K c x) :=
  xlaw_Ioi (pw_isCDF hK c) x

lemma pwl_Ici {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c x : ℝ) (hx : x ≤ c) :
    cdfLaw (pw K c) (Ici x) = ENNReal.ofReal (1 - K x) :=
  xlaw_Ici (pw_isCDF hK c) x _ (pw_left hK c x hx)

lemma pwl_Iio {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c x : ℝ) (hx : x ≤ c) :
    cdfLaw (pw K c) (Iio x) = ENNReal.ofReal (K x) :=
  xlaw_Iio (pw_isCDF hK c) x _ (pw_left hK c x hx)

lemma pwl_single {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c x : ℝ) (hx : x ≤ c) :
    cdfLaw (pw K c) {x} = ENNReal.ofReal (pw K c x - K x) :=
  xlaw_singleton (pw_isCDF hK c) x _ (pw_left hK c x hx)

lemma pwl_single_gt {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c x : ℝ) (hx : c < x) :
    cdfLaw (pw K c) {x} = 0 := by
  rw [xlaw_singleton (pw_isCDF hK c) x _ (pw_left_gt c x hx), pw_ge hx.le]; simp

lemma pwl_Ico {K : ℝ → ℝ} {a : ℝ} (hK : GoodK K a) (c x y : ℝ) (hx : x ≤ c) (hy : y ≤ c) :
    cdfLaw (pw K c) (Ico x y) = ENNReal.ofReal (K y - K x) :=
  xlaw_Ico (pw_isCDF hK c) x y _ _ (pw_left hK c x hx) (pw_left hK c y hy)

/-! ## Clamping -/
lemma cl_mem {a b : ℝ} (hab : a ≤ b) (y : ℝ) : max a (min y b) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma cl_of_mem {a b y : ℝ} (hy : y ∈ Icc a b) : max a (min y b) = y := by
  rw [min_eq_left hy.2, max_eq_right hy.1]

lemma cl_ge {a b y : ℝ} (hab : a ≤ b) (hy : b ≤ y) : max a (min y b) = b := by
  rw [min_eq_right hy, max_eq_right hab]

lemma cl_le {a b y : ℝ} (hy : y ≤ a) : max a (min y b) = a :=
  max_eq_left ((min_le_left _ _).trans hy)

lemma mkK_good {a b : ℝ} (hab : a ≤ b) (H : ℝ → ℝ) (hc : ContinuousOn H (Icc a b))
    (hanti : AntitoneOn H (Icc a b)) (h1 : H a = 1) (h0 : ∀ w ∈ Icc a b, 0 ≤ H w) :
    GoodK (fun x => 1 - H (max a (min (x - 1) b))) (1 + a) where
  cont := by
    refine continuous_const.sub (hc.comp_continuous ?_ (fun x => cl_mem hab _))
    fun_prop
  mono := by
    intro x y hxy
    have : H (max a (min (y - 1) b)) ≤ H (max a (min (x - 1) b)) :=
      hanti (cl_mem hab _) (cl_mem hab _)
        (max_le_max le_rfl (min_le_min (by linarith) le_rfl))
    linarith
  le1 := fun x => by
    have := h0 _ (cl_mem hab (x - 1)); linarith
  zero := fun x hx => by
    show 1 - H (max a (min (x - 1) b)) = 0
    rw [cl_le (by linarith), h1]; ring

lemma one_add_sub (w : ℝ) : 1 + w - 1 = w := by ring

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! ## Part F: the monopoly profit of the cost-1 supplier, and the construction's functions -/
/-- profit of M at margin `w` -/
noncomputable def g (S : ℝ → ℝ) (w : ℝ) : ℝ := w * S (1 + w)

noncomputable def piS (S : ℝ → ℝ) : ℝ := monopolyProfit S 1

/-- the monopoly margin τ = T₁ − 1 -/
noncomputable def tau (R : ℝ) (S : ℝ → ℝ) : ℝ := monopolyBid R S 1 - 1

/-- the probability `θ^(1/n)` that one rival has cost `R` -/
noncomputable def p (θ : ℝ) (n : ℕ) : ℝ := θ ^ (1 / (n : ℝ))

structure Hyp (R m θ : ℝ) (n : ℕ) (S : ℝ → ℝ) : Prop where
  hm : 0 < m
  hmR : m < R - 1
  hθ : 0 < θ
  hθ1 : θ < 1
  hn : 1 ≤ n
  hS : IsAcceptance R S

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-! ## Part F -/
lemma xn_pos (h : Hyp R m θ n S) : (0 : ℝ) < n := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
  linarith

lemma xp_pos (h : Hyp R m θ n S) : 0 < p θ n := Real.rpow_pos_of_pos h.hθ _

lemma xp_lt_one (h : Hyp R m θ n S) : p θ n < 1 :=
  Real.rpow_lt_one h.hθ.le h.hθ1 (by have := xn_pos h; positivity)

lemma xp_pow (h : Hyp R m θ n S) : p θ n ^ n = θ := by
  unfold p; rw [one_div]
  exact Real.rpow_inv_natCast_pow h.hθ.le (by have := h.hn; omega)

lemma xg_le_pi (h : Hyp R m θ n S) (w : ℝ) : g S w ≤ piS S := by
  have := Dev.A1.f_le_P h.hS 1 (1 + w)
  unfold g piS; rwa [one_add_sub] at this

lemma xpi_nonneg (h : Hyp R m θ n S) : 0 ≤ piS S := Dev.A1.P_nonneg h.hS 1

lemma xpi_eq_zero_of_zero (h : Hyp R m θ n S) (hz : ∀ b : ℝ, 1 < b → S b = 0) :
    piS S = 0 := by
  apply le_antisymm _ (xpi_nonneg h)
  unfold piS monopolyProfit
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨b, rfl⟩
  show (b - 1) * S b ≤ 0
  by_cases hb : 1 < b
  · rw [hz b hb, mul_zero]
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Dev.A1.S_nonneg h.hS b)

lemma xpi_pos (h : Hyp R m θ n S) (hr : IsRegular R S) : 0 < piS S := by
  obtain ⟨b, hb1, hb⟩ := hr.1
  have h1 := Dev.A1.f_le_P h.hS 1 b
  have h2 : 0 < (b - 1) * S b := mul_pos (by linarith) hb
  unfold piS; linarith

lemma xg_tau (h : Hyp R m θ n S) (hr : IsRegular R S) : g S (tau R S) = piS S := by
  have := (Dev.M5A.bid_spec h.hS 1 (xpi_pos h hr).ne').1
  unfold g tau piS
  have e : 1 + (monopolyBid R S 1 - 1) = monopolyBid R S 1 := by ring
  rw [e]; exact this

lemma xtau_pos (h : Hyp R m θ n S) (hr : IsRegular R S) : 0 < tau R S := by
  have h1 := xg_tau h hr
  have h2 := xpi_pos h hr
  by_contra hc; push Not at hc
  have : g S (tau R S) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc (Dev.A1.S_nonneg h.hS _)
  linarith

lemma xtau_le (h : Hyp R m θ n S) (hr : IsRegular R S) : tau R S ≤ R - 1 := by
  have h1 := xg_tau h hr
  have h2 := xpi_pos h hr
  by_contra hc; push Not at hc
  have : g S (tau R S) = 0 := by
    unfold g; rw [Dev.A1.S_zero h.hS (by linarith), mul_zero]
  linarith

lemma xpi_le_tau (h : Hyp R m θ n S) (hr : IsRegular R S) : piS S ≤ tau R S := by
  rw [← xg_tau h hr]
  exact mul_le_of_le_one_right (xtau_pos h hr).le (Dev.A1.S_le_one h.hS _)

lemma xg_mono (h : Hyp R m θ n S) (hr : IsRegular R S) :
    MonotoneOn (g S) (Icc 0 (tau R S)) := by
  intro x hx y hy hxy
  have ht : tau R S = monopolyBid R S 1 - 1 := rfl
  have := hr.2 (show 1 + x ∈ Icc 1 (monopolyBid R S 1) from
      ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (show 1 + y ∈ Icc 1 (monopolyBid R S 1) from ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    (by linarith)
  simp only [one_add_sub] at this
  exact this

lemma xg_cont (h : Hyp R m θ n S) (hr : IsRegular R S) :
    ContinuousOn (g S) (Icc 0 (tau R S)) := by
  have key : ∀ x ∈ Icc 0 (tau R S), ∀ y ∈ Icc 0 (tau R S), x ≤ y →
      |g S y - g S x| ≤ y - x := by
    intro x hx y hy hxy
    have h1 := xg_mono h hr hx hy hxy
    have h2 : S (1 + y) ≤ S (1 + x) := Dev.A1.S_anti h.hS (by linarith)
    have h3 := Dev.A1.S_le_one h.hS (1 + x)
    have e : g S y - g S x ≤ y - x := by
      unfold g
      nlinarith [mul_nonneg hy.1 (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 h3)]
    rw [abs_of_nonneg (sub_nonneg.2 h1)]; exact e
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε, hε, fun {y} hy hd => ?_⟩
  rw [Real.dist_eq] at hd ⊢
  rcases le_total x y with hxy | hxy
  · exact (key x hx y hy hxy).trans_lt (lt_of_le_of_lt (le_abs_self _) hd)
  · rw [abs_sub_comm]
    exact (key y hy x hx hxy).trans_lt (lt_of_le_of_lt (le_abs_self _) (by rwa [abs_sub_comm]))

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- `u := max (g m) (θ π)` -/
noncomputable def u (m θ : ℝ) (S : ℝ → ℝ) : ℝ := max (g S m) (θ * piS S)

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma xu_pos (h : Hyp R m θ n S) (hr : IsRegular R S) : 0 < u m θ S :=
  lt_of_lt_of_le (mul_pos h.hθ (xpi_pos h hr)) (le_max_right _ _)

lemma xu_le_pi (h : Hyp R m θ n S) : u m θ S ≤ piS S :=
  max_le (xg_le_pi h m) (mul_le_of_le_one_left (xpi_nonneg h) h.hθ1.le)

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- `w0 := min {w ∈ [m, τ] | g w = u}` -/
noncomputable def w0 (R m θ : ℝ) (S : ℝ → ℝ) : ℝ :=
  sInf {w | w ∈ Icc m (tau R S) ∧ g S w = u m θ S}

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma xw0_mem (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    w0 R m θ S ∈ Icc m (tau R S) ∧ g S (w0 R m θ S) = u m θ S := by
  have hcont : ContinuousOn (g S) (Icc m (tau R S)) :=
    (xg_cont h hr).mono (Icc_subset_Icc_left h.hm.le)
  have hne : {w | w ∈ Icc m (tau R S) ∧ g S w = u m θ S}.Nonempty := by
    have hu : u m θ S ∈ Icc (g S m) (g S (tau R S)) :=
      ⟨le_max_left _ _, by rw [xg_tau h hr]; exact xu_le_pi h⟩
    obtain ⟨w, hw, hgw⟩ := intermediate_value_Icc hτ.le hcont hu
    exact ⟨w, hw, hgw⟩
  have hcl : IsClosed {w | w ∈ Icc m (tau R S) ∧ g S w = u m θ S} :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hbdd : BddBelow {w | w ∈ Icc m (tau R S) ∧ g S w = u m θ S} :=
    ⟨m, fun w hw => hw.1.1⟩
  exact hcl.csInf_mem hne hbdd

lemma xg_le_u (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ≤ w0 R m θ S) : g S w ≤ u m θ S := by
  obtain ⟨hmem, hg⟩ := xw0_mem h hr hτ
  rcases lt_or_ge w 0 with hw0 | hw0
  · have : g S w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hw0.le (Dev.A1.S_nonneg h.hS _)
    linarith [xu_pos h hr]
  · rw [← hg]
    exact xg_mono h hr ⟨hw0, hw.trans hmem.2⟩ ⟨h.hm.le.trans hmem.1, hmem.2⟩ hw

lemma xu_eq_of_w0 (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) : u m θ S = θ * piS S := by
  rcases le_total (g S m) (θ * piS S) with h1 | h1
  · exact max_eq_right h1
  · exfalso
    have hu : u m θ S = g S m := max_eq_left h1
    have : w0 R m θ S ≤ m := csInf_le ⟨m, fun w hw => hw.1.1⟩ ⟨⟨le_rfl, hτ.le⟩, hu.symm⟩
    linarith

lemma xw0_gt_of (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hπ : m < θ * piS S) : m < w0 R m θ S := by
  have hgm : g S m ≤ m := mul_le_of_le_one_right h.hm.le (Dev.A1.S_le_one h.hS _)
  obtain ⟨hmem, hg⟩ := xw0_mem h hr hτ
  rcases hmem.1.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    rw [← heq] at hg
    have : θ * piS S ≤ u m θ S := le_max_right _ _
    linarith

lemma xu_le_w0 (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    u m θ S ≤ w0 R m θ S := by
  obtain ⟨hmem, hg⟩ := xw0_mem h hr hτ
  rw [← hg]
  exact mul_le_of_le_one_right (h.hm.le.trans hmem.1) (Dev.A1.S_le_one h.hS _)

/-! ### Γ and G -/
lemma xg_ge_u (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : u m θ S ≤ g S w := by
  obtain ⟨hmem, hg⟩ := xw0_mem h hr hτ
  rw [← hg]
  exact xg_mono h hr ⟨h.hm.le.trans hmem.1, hmem.2⟩
    ⟨h.hm.le.trans (hmem.1.trans hw.1), hw.2⟩ hw.1

lemma xg_pos (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : 0 < g S w :=
  lt_of_lt_of_le (xu_pos h hr) (xg_ge_u h hr hτ w hw)

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- `Γ(w) = u / g(w)` -/
noncomputable def Gam (m θ : ℝ) (S : ℝ → ℝ) (w : ℝ) : ℝ := u m θ S / g S w

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma xGam_nonneg (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : 0 ≤ Gam m θ S w :=
  div_nonneg (xu_pos h hr).le (xg_pos h hr hτ w hw).le

lemma xGam_le_one (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : Gam m θ S w ≤ 1 :=
  div_le_one_of_le₀ (xg_ge_u h hr hτ w hw) (xg_pos h hr hτ w hw).le

lemma xGam_ge (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : θ ≤ Gam m θ S w := by
  have hπ := xpi_pos h hr
  have h1 : θ ≤ u m θ S / piS S := by
    rw [le_div_iff₀ hπ]; exact le_max_right _ _
  exact h1.trans (div_le_div_of_nonneg_left (xu_pos h hr).le (xg_pos h hr hτ w hw)
    (xg_le_pi h w))

lemma xX_ge (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : p θ n ≤ Gam m θ S w ^ (1 / (n : ℝ)) :=
  Real.rpow_le_rpow h.hθ.le (xGam_ge h hr hτ w hw) (by have := xn_pos h; positivity)

lemma xX_le (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : Gam m θ S w ^ (1 / (n : ℝ)) ≤ 1 :=
  Real.rpow_le_one (xGam_nonneg h hr hτ w hw) (xGam_le_one h hr hτ w hw)
    (by have := xn_pos h; positivity)

lemma xX_nonneg (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : 0 ≤ Gam m θ S w ^ (1 / (n : ℝ)) :=
  Real.rpow_nonneg (xGam_nonneg h hr hτ w hw) _

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- one present rival's probability of bidding margin ≥ w on [w0, τ] -/
noncomputable def G (m θ : ℝ) (n : ℕ) (S : ℝ → ℝ) (w : ℝ) : ℝ :=
  (Gam m θ S w ^ (1 / (n : ℝ)) - p θ n) / (1 - p θ n)

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma xG_mem (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : G m θ n S w ∈ Icc 0 1 := by
  have h1 := xX_ge h hr hτ w hw
  have h2 := xX_le h hr hτ w hw
  have hp := xp_lt_one h
  unfold G
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_le_one (by linarith)]; linarith

lemma xp_add_G (h : Hyp R m θ n S) (w : ℝ) :
    p θ n + (1 - p θ n) * G m θ n S w = Gam m θ S w ^ (1 / (n : ℝ)) := by
  have hne : 1 - p θ n ≠ 0 := by have := xp_lt_one h; linarith
  unfold G
  field_simp
  ring

lemma xGam_pow (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) :
    (Gam m θ S w ^ (1 / (n : ℝ))) ^ n = Gam m θ S w ∧ 0 ≤ Gam m θ S w := by
  refine ⟨?_, xGam_nonneg h hr hτ w hw⟩
  rw [one_div]
  exact Real.rpow_inv_natCast_pow (xGam_nonneg h hr hτ w hw) (by have := h.hn; omega)

lemma xGam_mul_g (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : g S w * Gam m θ S w = u m θ S := by
  have := (xg_pos h hr hτ w hw).ne'
  unfold Gam
  field_simp

lemma xGam_tau (h : Hyp R m θ n S) (hr : IsRegular R S) :
    Gam m θ S (tau R S) = u m θ S / piS S := by
  unfold Gam; rw [xg_tau h hr]

lemma xG_w0 (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    G m θ n S (w0 R m θ S) = 1 := by
  have hne : 1 - p θ n ≠ 0 := by have := xp_lt_one h; linarith
  have hg := (xw0_mem h hr hτ).2
  unfold G Gam
  rw [hg, div_self (xu_pos h hr).ne', Real.one_rpow, div_self hne]

lemma xG_tau_zero (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) : G m θ n S (tau R S) = 0 := by
  have hΓ : Gam m θ S (tau R S) = θ := by
    rw [xGam_tau h hr, xu_eq_of_w0 h hr hτ hw]
    field_simp [(xpi_pos h hr).ne']
  unfold G
  rw [hΓ]
  show (p θ n - p θ n) / (1 - p θ n) = 0
  simp

lemma xw0_le_tau (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    w0 R m θ S ≤ tau R S := (xw0_mem h hr hτ).1.2

lemma xGam_cont (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    ContinuousOn (Gam m θ S) (Icc (w0 R m θ S) (tau R S)) := by
  have hsub : Icc (w0 R m θ S) (tau R S) ⊆ Icc 0 (tau R S) :=
    Icc_subset_Icc_left (h.hm.le.trans (xw0_mem h hr hτ).1.1)
  show ContinuousOn (fun w => u m θ S / g S w) _
  exact continuousOn_const.div ((xg_cont h hr).mono hsub)
    (fun w hw => (xg_pos h hr hτ w hw).ne')

lemma xGam_anti (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    AntitoneOn (Gam m θ S) (Icc (w0 R m θ S) (tau R S)) := by
  have h0 := h.hm.le.trans (xw0_mem h hr hτ).1.1
  intro x hx y hy hxy
  exact div_le_div_of_nonneg_left (xu_pos h hr).le (xg_pos h hr hτ x hx)
    (xg_mono h hr ⟨h0.trans hx.1, hx.2⟩ ⟨h0.trans hy.1, hy.2⟩ hxy)

lemma xX_cont (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    ContinuousOn (fun w => Gam m θ S w ^ (1 / (n : ℝ))) (Icc (w0 R m θ S) (tau R S)) :=
  (xGam_cont h hr hτ).rpow_const (fun _ _ => Or.inr (by have := xn_pos h; positivity))

lemma xX_anti (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    AntitoneOn (fun w => Gam m θ S w ^ (1 / (n : ℝ))) (Icc (w0 R m θ S) (tau R S)) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow (xGam_nonneg h hr hτ y hy) (xGam_anti h hr hτ hx hy hxy)
    (by have := xn_pos h; positivity)

lemma xG_cont (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    ContinuousOn (G m θ n S) (Icc (w0 R m θ S) (tau R S)) := by
  show ContinuousOn (fun w => (Gam m θ S w ^ (1 / (n : ℝ)) - p θ n) / (1 - p θ n)) _
  exact ((xX_cont h hr hτ).sub continuousOn_const).div_const _

lemma xG_anti (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    AntitoneOn (G m θ n S) (Icc (w0 R m θ S) (tau R S)) := by
  intro x hx y hy hxy
  have := xX_anti h hr hτ hx hy hxy
  have hp := xp_lt_one h
  unfold G
  exact div_le_div_of_nonneg_right (by simp only at this; linarith) (by linarith)

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
noncomputable def Atil (R m θ : ℝ) (S : ℝ → ℝ) (w : ℝ) : ℝ :=
  (w0 R m θ S - m) * w / (w0 R m θ S * (w - m))

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-! ### Ã and A -/
lemma xAtil_cont (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) :
    ContinuousOn (Atil R m θ S) (Icc (w0 R m θ S) (tau R S)) := by
  show ContinuousOn (fun w => (w0 R m θ S - m) * w / (w0 R m θ S * (w - m))) _
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun w hw' => ?_)
  have : 0 < w - m := by linarith [hw'.1]
  have : 0 < w0 R m θ S := by linarith [h.hm]
  positivity

lemma xAtil_anti (h : Hyp R m θ n S) (hw : m < w0 R m θ S) :
    AntitoneOn (Atil R m θ S) (Icc (w0 R m θ S) (tau R S)) := by
  intro x hx y hy hxy
  have hm := h.hm
  have h1 : 0 < x - m := by linarith [hx.1]
  have h2 : 0 < y - m := by linarith [hy.1]
  have hw0 : 0 < w0 R m θ S := by linarith
  unfold Atil
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : (w0 R m θ S - m) * y * (w0 R m θ S * (x - m)) -
      (w0 R m θ S - m) * x * (w0 R m θ S * (y - m)) =
      (w0 R m θ S - m) * w0 R m θ S * m * (x - y) := by ring
  have : (w0 R m θ S - m) * w0 R m θ S * m * (x - y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by have := sub_pos.2 hw; positivity) (by linarith)
  linarith

lemma xAtil_w0 (h : Hyp R m θ n S) (hw : m < w0 R m θ S) : Atil R m θ S (w0 R m θ S) = 1 := by
  have h1 : w0 R m θ S - m ≠ 0 := by linarith
  have h2 : w0 R m θ S ≠ 0 := by linarith [h.hm]
  unfold Atil
  rw [mul_comm (w0 R m θ S - m) (w0 R m θ S)]
  exact div_self (mul_ne_zero h2 h1)

lemma xAtil_nonneg (h : Hyp R m θ n S) (hw : m < w0 R m θ S) (w : ℝ)
    (hw' : w ∈ Icc (w0 R m θ S) (tau R S)) : 0 ≤ Atil R m θ S w := by
  have := h.hm
  have : 0 ≤ w0 R m θ S - m := by linarith
  have : 0 ≤ w - m := by linarith [hw'.1]
  have : 0 ≤ w := by linarith [hw'.1]
  have : 0 ≤ w0 R m θ S := by linarith
  unfold Atil; positivity

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- M's survival function on margins in [w0, τ] -/
noncomputable def A (R m θ : ℝ) (n : ℕ) (S : ℝ → ℝ) (w : ℝ) : ℝ :=
  Atil R m θ S w * Gam m θ S w ^ (1 / (n : ℝ))

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma xA_cont (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) :
    ContinuousOn (A R m θ n S) (Icc (w0 R m θ S) (tau R S)) :=
  (xAtil_cont h hr hτ hw).mul (xX_cont h hr hτ)

lemma xA_anti (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) :
    AntitoneOn (A R m θ n S) (Icc (w0 R m θ S) (tau R S)) := by
  intro x hx y hy hxy
  exact mul_le_mul (xAtil_anti h hw hx hy hxy) (xX_anti h hr hτ hx hy hxy)
    (xX_nonneg h hr hτ y hy) (xAtil_nonneg h hw x hx)

lemma xA_w0 (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) : A R m θ n S (w0 R m θ S) = 1 := by
  have hg := (xw0_mem h hr hτ).2
  unfold A Gam
  rw [xAtil_w0 h hw, hg, div_self (xu_pos h hr).ne', Real.one_rpow, mul_one]

lemma xA_mem (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (w : ℝ) (hw' : w ∈ Icc (w0 R m θ S) (tau R S)) :
    A R m θ n S w ∈ Icc 0 1 := by
  have hw0 : w0 R m θ S ∈ Icc (w0 R m θ S) (tau R S) := ⟨le_rfl, xw0_le_tau h hr hτ⟩
  have h1 : Atil R m θ S w ≤ 1 := by
    rw [← xAtil_w0 h hw]; exact xAtil_anti h hw hw0 hw' hw'.1
  exact ⟨mul_nonneg (xAtil_nonneg h hw w hw') (xX_nonneg h hr hτ w hw'),
    mul_le_one₀ h1 (xX_nonneg h hr hτ w hw') (xX_le h hr hτ w hw')⟩

lemma xA_tau_ge (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hπ : m < θ * piS S) :
    p θ n * (1 - m / (θ * piS S)) ≤ A R m θ n S (tau R S) := by
  have hw := xw0_gt_of h hr hτ hπ
  have hu := xu_eq_of_w0 h hr hτ hw
  have hπ0 := xpi_pos h hr
  have hΓ : Gam m θ S (tau R S) = θ := by
    rw [xGam_tau h hr, hu]; field_simp
  have hX : Gam m θ S (tau R S) ^ (1 / (n : ℝ)) = p θ n := by rw [hΓ]; rfl
  unfold A
  rw [hX, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (xp_pos h).le
  have hle : θ * piS S ≤ w0 R m θ S := hu ▸ xu_le_w0 h hr hτ
  have hm := h.hm
  have hτw := xw0_le_tau h hr hτ
  have hθπ : 0 < θ * piS S := by linarith
  have hw0 : 0 < w0 R m θ S := by linarith
  have s1 : 1 - m / (θ * piS S) ≤ 1 - m / w0 R m θ S := by
    have := div_le_div_of_nonneg_left hm.le hθπ hle
    linarith
  refine s1.trans ?_
  unfold Atil
  rw [le_div_iff₀ (mul_pos hw0 (by linarith))]
  have e : (1 - m / w0 R m θ S) * (w0 R m θ S * (tau R S - m)) =
      (w0 R m θ S - m) * (tau R S - m) := by
    field_simp
  rw [e]
  have : 0 ≤ w0 R m θ S - m := by linarith
  nlinarith

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- the rival's CDF on bids (atom at `R + j`) -/
noncomputable def rivalCDF (R m θ : ℝ) (n : ℕ) (S : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  if x < 1 + w0 R m θ S then 0
  else if x < 1 + tau R S then 1 - G m θ n S (x - 1)
  else if x < R + j then 1 - G m θ n S (tau R S)
  else 1

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-! ### The CDFs as `pw` shapes -/
lemma xrival_eq (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (j : ℕ)
    (hj : 1 ≤ j) :
    rivalCDF R m θ n S j =
      pw (fun x => 1 - G m θ n S (max (w0 R m θ S) (min (x - 1) (tau R S)))) (R + j) := by
  have hwt := xw0_le_tau h hr hτ
  have hτR := xtau_le h hr
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hG1 := xG_w0 h hr hτ
  funext x
  unfold rivalCDF
  by_cases h1 : x < 1 + w0 R m θ S
  · rw [if_pos h1, pw_lt (by linarith), cl_le (by linarith), hG1]; ring
  rw [if_neg h1]
  by_cases h2 : x < 1 + tau R S
  · rw [if_pos h2, pw_lt (by linarith), cl_of_mem ⟨by linarith, by linarith⟩]
  rw [if_neg h2]
  by_cases h3 : x < R + j
  · rw [if_pos h3, pw_lt h3, cl_ge hwt (by linarith)]
  · rw [if_neg h3, pw_ge (not_lt.1 h3)]

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- M's CDF on bids (atom at `1 + τ`), used when `w0 > m` -/
noncomputable def mCDF (R m θ : ℝ) (n : ℕ) (S : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < 1 + w0 R m θ S then 0
  else if x < 1 + tau R S then 1 - A R m θ n S (x - 1)
  else 1

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma xmCDF_eq (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) :
    mCDF R m θ n S =
      pw (fun x => 1 - A R m θ n S (max (w0 R m θ S) (min (x - 1) (tau R S))))
        (1 + tau R S) := by
  have hwt := xw0_le_tau h hr hτ
  have hA1 := xA_w0 h hr hτ hw
  funext x
  unfold mCDF
  by_cases h1 : x < 1 + w0 R m θ S
  · rw [if_pos h1, pw_lt (by linarith), cl_le (by linarith), hA1]; ring
  rw [if_neg h1]
  by_cases h2 : x < 1 + tau R S
  · rw [if_pos h2, pw_lt h2, cl_of_mem ⟨by linarith, by linarith⟩]
  · rw [if_neg h2, pw_ge (not_lt.1 h2)]

lemma xKr_good (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    GoodK (fun x => 1 - G m θ n S (max (w0 R m θ S) (min (x - 1) (tau R S))))
      (1 + w0 R m θ S) :=
  mkK_good (xw0_le_tau h hr hτ) _ (xG_cont h hr hτ) (xG_anti h hr hτ) (xG_w0 h hr hτ)
    (fun w hw => (xG_mem h hr hτ w hw).1)

lemma xKm_good (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) :
    GoodK (fun x => 1 - A R m θ n S (max (w0 R m θ S) (min (x - 1) (tau R S))))
      (1 + w0 R m θ S) :=
  mkK_good (xw0_le_tau h hr hτ) _ (xA_cont h hr hτ hw) (xA_anti h hr hτ hw)
    (xA_w0 h hr hτ hw) (fun w hw' => (xA_mem h hr hτ hw w hw').1)

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! ## The stubs, restated -/
lemma cdfLaw_Iic {F : ℝ → ℝ} (h : IsCDF F) (x : ℝ) :
    cdfLaw F (Iic x) = ENNReal.ofReal (F x) := xlaw_Iic h x

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
alias cdfLaw_Iic := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.cdfLaw_Iic

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma p_pos (h : Hyp R m θ n S) : 0 < p θ n := xp_pos h

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias p_pos := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.p_pos

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma p_lt_one (h : Hyp R m θ n S) : p θ n < 1 := xp_lt_one h

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias p_lt_one := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.p_lt_one

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma p_pow (h : Hyp R m θ n S) : p θ n ^ n = θ := xp_pow h

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias p_pow := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.p_pow

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma g_le_pi (h : Hyp R m θ n S) (w : ℝ) : g S w ≤ piS S := xg_le_pi h w

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias g_le_pi := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.g_le_pi

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- the zero case: no positive profit -/
lemma pi_eq_zero_of_zero (h : Hyp R m θ n S) (hz : ∀ b : ℝ, 1 < b → S b = 0) : piS S = 0 :=
  xpi_eq_zero_of_zero h hz

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias pi_eq_zero_of_zero := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.pi_eq_zero_of_zero

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma pi_pos (h : Hyp R m θ n S) (hr : IsRegular R S) : 0 < piS S := xpi_pos h hr

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias pi_pos := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.pi_pos

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma tau_pos (h : Hyp R m θ n S) (hr : IsRegular R S) : 0 < tau R S := xtau_pos h hr

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias tau_pos := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.tau_pos

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma tau_le (h : Hyp R m θ n S) (hr : IsRegular R S) : tau R S ≤ R - 1 := xtau_le h hr

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias tau_le := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.tau_le

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma g_tau (h : Hyp R m θ n S) (hr : IsRegular R S) : g S (tau R S) = piS S := xg_tau h hr

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias g_tau := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.g_tau

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma pi_le_tau (h : Hyp R m θ n S) (hr : IsRegular R S) : piS S ≤ tau R S := xpi_le_tau h hr

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias pi_le_tau := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.pi_le_tau

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma g_mono (h : Hyp R m θ n S) (hr : IsRegular R S) : MonotoneOn (g S) (Icc 0 (tau R S)) :=
  xg_mono h hr

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias g_mono := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.g_mono

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma u_pos (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) : 0 < u m θ S :=
  xu_pos h hr

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias u_pos := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.u_pos

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma w0_mem (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    w0 R m θ S ∈ Icc m (tau R S) ∧ g S (w0 R m θ S) = u m θ S := xw0_mem h hr hτ

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias w0_mem := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.w0_mem

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma g_le_u (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ≤ w0 R m θ S) : g S w ≤ u m θ S := xg_le_u h hr hτ w hw

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias g_le_u := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.g_le_u

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- if `w0 > m` then `u = θ π`, hence `Γ(τ) = θ` -/
lemma u_eq_of_w0 (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) : u m θ S = θ * piS S := xu_eq_of_w0 h hr hτ hw

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias u_eq_of_w0 := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.u_eq_of_w0

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- if `θ π > m` then `w0 > m` -/
lemma w0_gt_of (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hπ : m < θ * piS S) : m < w0 R m θ S := xw0_gt_of h hr hτ hπ

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias w0_gt_of := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.w0_gt_of

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma G_mem (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : G m θ n S w ∈ Icc 0 1 := xG_mem h hr hτ w hw

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias G_mem := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.G_mem

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- the key identity: `p + (1 - p) G(w) = Γ(w)^(1/n)` -/
lemma p_add_G (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ) :
    p θ n + (1 - p θ n) * G m θ n S w = Gam m θ S w ^ (1 / (n : ℝ)) := xp_add_G h w

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias p_add_G := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.p_add_G

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma Gam_pow (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) :
    (Gam m θ S w ^ (1 / (n : ℝ))) ^ n = Gam m θ S w ∧ 0 ≤ Gam m θ S w :=
  xGam_pow h hr hτ w hw

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias Gam_pow := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.Gam_pow

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma Gam_mul_g (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (w : ℝ)
    (hw : w ∈ Icc (w0 R m θ S) (tau R S)) : g S w * Gam m θ S w = u m θ S :=
  xGam_mul_g h hr hτ w hw

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias Gam_mul_g := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.Gam_mul_g

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma Gam_tau (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) :
    Gam m θ S (tau R S) = u m θ S / piS S := xGam_tau h hr

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias Gam_tau := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.Gam_tau

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- if `w0 > m` then one present rival never bids margin ≥ τ -/
lemma G_tau_zero (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) : G m θ n S (tau R S) = 0 := xG_tau_zero h hr hτ hw

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias G_tau_zero := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.G_tau_zero

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma A_mem (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (w : ℝ) (hw' : w ∈ Icc (w0 R m θ S) (tau R S)) :
    A R m θ n S w ∈ Icc 0 1 := xA_mem h hr hτ hw w hw'

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias A_mem := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.A_mem

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- the bound on M's atom at τ: `A(τ) ≥ θ^(1/n) (1 - m/(θπ))` -/
lemma A_tau_ge (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hπ : m < θ * piS S) :
    p θ n * (1 - m / (θ * piS S)) ≤ A R m θ n S (tau R S) := xA_tau_ge h hr hτ hπ

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias A_tau_ge := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.A_tau_ge

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma rivalCDF_isCDF (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (j : ℕ)
    (hj : 1 ≤ j) : IsCDF (rivalCDF R m θ n S j) := by
  rw [xrival_eq h hr hτ j hj]; exact pw_isCDF (xKr_good h hr hτ) _

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias rivalCDF_isCDF := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.rivalCDF_isCDF

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma mCDF_isCDF (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) : IsCDF (mCDF R m θ n S) := by
  rw [xmCDF_eq h hr hτ hw]; exact pw_isCDF (xKm_good h hr hτ hw) _

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias mCDF_isCDF := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.mCDF_isCDF

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-! Laws of the bids. -/
/-- one present rival's bid law (index `j ≥ 1`) -/
lemma pres_Ioi (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (j : ℕ)
    (hj : 1 ≤ j) (w : ℝ) (hw : w ∈ Icc (w0 R m θ S) (tau R S)) :
    cdfLaw (rivalCDF R m θ n S j) (Ioi (1 + w)) = ENNReal.ofReal (G m θ n S w) ∧
    cdfLaw (rivalCDF R m θ n S j) (Ici (1 + w)) = ENNReal.ofReal (G m θ n S w) := by
  have hK := xKr_good h hr hτ
  have hτR := xtau_le h hr
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hc : 1 + w < R + j := by linarith [hw.2]
  rw [xrival_eq h hr hτ j hj]
  refine ⟨?_, ?_⟩
  · rw [pwl_Ioi hK, pw_lt hc]
    simp only [one_add_sub, cl_of_mem hw, sub_sub_cancel]
  · rw [pwl_Ici hK _ _ hc.le]
    simp only [one_add_sub, cl_of_mem hw, sub_sub_cancel]

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-! Laws of the bids. -/
alias pres_Ioi := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.pres_Ioi

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma pres_Ici_gt (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (j : ℕ)
    (hj : 1 ≤ j) (x : ℝ) (hx : 1 + tau R S < x) :
    cdfLaw (rivalCDF R m θ n S j) (Ici x) ≤ ENNReal.ofReal (G m θ n S (tau R S)) := by
  rw [← (pres_Ioi h hr hτ j hj (tau R S) ⟨xw0_le_tau h hr hτ, le_rfl⟩).1]
  exact measure_mono (fun y hy => lt_of_lt_of_le hx hy)

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias pres_Ici_gt := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.pres_Ici_gt

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma pres_ae (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (j : ℕ)
    (hj : 1 ≤ j) :
    ∀ᵐ b ∂(cdfLaw (rivalCDF R m θ n S j)),
      (1 + w0 R m θ S ≤ b ∧ b < 1 + tau R S) ∨ b = R + j := by
  have hK := xKr_good h hr hτ
  have hτR := xtau_le h hr
  have hwt := xw0_le_tau h hr hτ
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [xrival_eq h hr hτ j hj, ae_iff]
  apply measure_mono_null (t := Iio (1 + w0 R m θ S) ∪ Ico (1 + tau R S) (R + j) ∪ Ioi (R + j))
  · intro b hb
    simp only [mem_ofPred_eq, not_or, not_and, not_lt] at hb
    by_cases h1 : b < 1 + w0 R m θ S
    · exact Or.inl (Or.inl h1)
    have h2 := hb.1 (not_lt.1 h1)
    by_cases h3 : b < R + j
    · exact Or.inl (Or.inr ⟨h2, h3⟩)
    · exact Or.inr (lt_of_le_of_ne (not_lt.1 h3) (Ne.symm hb.2))
  · refine measure_union_null (measure_union_null ?_ ?_) ?_
    · rw [pwl_Iio hK _ _ (by linarith)]
      simp only [one_add_sub, cl_of_mem ⟨le_rfl, hwt⟩, xG_w0 h hr hτ, sub_self,
        ENNReal.ofReal_zero]
    · rw [pwl_Ico hK _ _ _ (by linarith) le_rfl]
      simp only [one_add_sub, cl_of_mem ⟨hwt, le_rfl⟩]
      rw [cl_ge hwt (by linarith)]
      simp
    · rw [pwl_Ioi hK, pw_ge le_rfl]; simp

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias pres_ae := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.pres_ae

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma pres_singleton (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (j : ℕ)
    (hj : 1 ≤ j) (x : ℝ) (hx : x ≠ R + j) :
    cdfLaw (rivalCDF R m θ n S j) {x} = 0 := by
  have hK := xKr_good h hr hτ
  rw [xrival_eq h hr hτ j hj]
  rcases lt_or_gt_of_ne hx with h1 | h1
  · rw [pwl_single hK _ _ h1.le, pw_lt h1]; simp
  · exact pwl_single_gt hK _ _ h1

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias pres_singleton := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.pres_singleton

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-- if `w0 > m` the present rival bids below `1 + τ` almost surely -/
lemma pres_Iio (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (j : ℕ)
    (hj : 1 ≤ j) (hw : m < w0 R m θ S) :
    cdfLaw (rivalCDF R m θ n S j) (Iio (1 + tau R S)) = 1 := by
  have hK := xKr_good h hr hτ
  have hτR := xtau_le h hr
  have hwt := xw0_le_tau h hr hτ
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [xrival_eq h hr hτ j hj, pwl_Iio hK _ _ (by linarith)]
  simp only [one_add_sub, cl_of_mem ⟨hwt, le_rfl⟩, xG_tau_zero h hr hτ hw, sub_zero,
    ENNReal.ofReal_one]

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias pres_Iio := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.pres_Iio

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma mlaw_Ioi (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (w : ℝ) (hw' : w ∈ Ico (w0 R m θ S) (tau R S)) :
    cdfLaw (mCDF R m θ n S) (Ioi (1 + w)) = ENNReal.ofReal (A R m θ n S w) ∧
    cdfLaw (mCDF R m θ n S) (Ici (1 + w)) = ENNReal.ofReal (A R m θ n S w) := by
  have hK := xKm_good h hr hτ hw
  have hc : 1 + w < 1 + tau R S := by linarith [hw'.2]
  have hmem : w ∈ Icc (w0 R m θ S) (tau R S) := ⟨hw'.1, hw'.2.le⟩
  rw [xmCDF_eq h hr hτ hw]
  refine ⟨?_, ?_⟩
  · rw [pwl_Ioi hK, pw_lt hc]
    simp only [one_add_sub, cl_of_mem hmem, sub_sub_cancel]
  · rw [pwl_Ici hK _ _ hc.le]
    simp only [one_add_sub, cl_of_mem hmem, sub_sub_cancel]

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias mlaw_Ioi := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.mlaw_Ioi

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma mlaw_tau (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) :
    cdfLaw (mCDF R m θ n S) {1 + tau R S} = ENNReal.ofReal (A R m θ n S (tau R S)) ∧
    cdfLaw (mCDF R m θ n S) (Ici (1 + tau R S)) = ENNReal.ofReal (A R m θ n S (tau R S)) ∧
    cdfLaw (mCDF R m θ n S) (Ioi (1 + tau R S)) = 0 := by
  have hK := xKm_good h hr hτ hw
  have hwt := xw0_le_tau h hr hτ
  rw [xmCDF_eq h hr hτ hw]
  refine ⟨?_, ?_, ?_⟩
  · rw [pwl_single hK _ _ le_rfl, pw_ge le_rfl]
    simp only [one_add_sub, cl_of_mem ⟨hwt, le_rfl⟩, sub_sub_cancel]
  · rw [pwl_Ici hK _ _ le_rfl]
    simp only [one_add_sub, cl_of_mem ⟨hwt, le_rfl⟩, sub_sub_cancel]
  · rw [pwl_Ioi hK, pw_ge le_rfl]; simp

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias mlaw_tau := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.mlaw_tau

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
lemma mlaw_ae (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) :
    ∀ᵐ b ∂(cdfLaw (mCDF R m θ n S)), 1 + w0 R m θ S ≤ b ∧ b ≤ 1 + tau R S := by
  have hK := xKm_good h hr hτ hw
  have hwt := xw0_le_tau h hr hτ
  rw [xmCDF_eq h hr hτ hw, ae_iff]
  apply measure_mono_null (t := Iio (1 + w0 R m θ S) ∪ Ioi (1 + tau R S))
  · intro b hb
    simp only [mem_ofPred_eq, not_and, not_le] at hb
    by_cases h1 : b < 1 + w0 R m θ S
    · exact Or.inl h1
    · exact Or.inr (hb (not_lt.1 h1))
  · refine measure_union_null ?_ ?_
    · rw [pwl_Iio hK _ _ (by linarith)]
      simp only [one_add_sub, cl_of_mem ⟨le_rfl, hwt⟩, xA_w0 h hr hτ hw, sub_self,
        ENNReal.ofReal_zero]
    · rw [pwl_Ioi hK, pw_ge le_rfl]; simp

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
alias mlaw_ae := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartF.mlaw_ae

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! ## Part G: the profile shape and general auction facts -/
/-- M (index 0) draws from `mLaw`; rival `i ≥ 1` bids `R + i` at cost `R`, else draws from `pres i`. -/
noncomputable def mkProfile (n : ℕ) (R : ℝ) (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ)
    [IsProbabilityMeasure mLaw] [∀ j, IsProbabilityMeasure (pres j)] : MixedProfile n where
  bid i := if i = 0 then Kernel.const ℝ mLaw else
    Kernel.piecewise (measurableSet_singleton R) (Kernel.const ℝ (Measure.dirac (R + (i : ℕ))))
      (Kernel.const ℝ (pres i))
  markov i := by split_ifs <;> infer_instance

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-!
# Lemma A.2, Blueprint Part G (and Part P)

FOUR STUBS OF PART G ARE FALSE AS STATED. The section `variable`s `hm : 0 < m`,
`hmR : m < R - 1`, `hn : 1 ≤ n` are never mentioned in these statements, so Lean does not
include them; the stubs hold for arbitrary real `m`, `R` and any `n`.

* `marginal_rival` (needs `1 + m ≠ R`, i.e. `hmR`). Counterexample: `R = 2`, `m = 1`, `θ = 1/4`,
  `n = 1`, `i = 1`, `mLaw = dirac 0`, `pres = fun _ => dirac 0`, `s = {0}`. The rival's cost law
  `bernoulliMeasure 2 2 p` is `dirac 2`, the kernel at `2` is `dirac 3`, so the marginal is `dirac 3`
  and the LHS is `0`, while the RHS is `ofReal (1/4) * 0 + ofReal (3/4) * 1 = 3/4`.

* `optimal_eq` (needs `0 < m`, `m < R - 1`). Counterexample: `R = 5`, `m = -1/2`, `θ = 1/100`,
  `n = 1`: rival 1 has cost `1/2` with probability `99/100` and `5` otherwise, M has cost 1, so
  `optimalSocialCost = 0.99 * (1/2) + 0.01 * 1 = 0.505 ≠ 1`.

* `socialCost_ge_one` (needs `hm`, `hmR`). Counterexample: same instance (`R = 5`, `m = -1/2`,
  `θ = 1/100`, `n = 1`), `S b = (dirac 5 (Ici b)).toReal` (= 1 for b ≤ 5, else 0; an acceptance
  function for `R = 5`), any tie rule `τ`, `σ = mkProfile 1 5 (dirac 2) (fun _ => dirac 0)`: the rival
  bids `6` at cost 5 (prob. 0.01; M wins at cost 1, S(2) = 1) and `0` at cost `1/2` (prob. 0.99;
  the rival wins at cost 1/2, S(0) = 1), so `acceptSocialCost = 0.01 + 0.495 = 0.505 < 1`.

* `socialCost_ge_loss` (needs `hm`, `hmR`, and `hn`). Counterexample: the same data with `t = 2`
  (`t ≤ R`, `pres 1 (Iio 2) = 1`): the LHS is `1 + ofReal (-1/2) * ... = 1 > 0.505`. (With `n = 0`
  it also fails for good `m`: `p θ 0 = 1`, no rival, M alone wins at cost 1 with `S t = 1`.)

Corrected versions, with exactly the binders `include hmR in` / `include hm hmR in` / `include hm hmR hn in`
would give inside the Blueprint's section, are proved below as `marginal_rival_fixed`,
`optimal_eq_fixed`, `socialCost_ge_one_fixed`, `socialCost_ge_loss_fixed`.
All other Part G stubs and all Part P stubs are proved verbatim.
-/
/-! ### general helpers -/
lemma box_measure' {n : ℕ} (ν : Suppliers n → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    (i : Suppliers n) (A : Set ℝ) :
    Measure.pi ν (Set.pi univ (fun k => if k = i then univ else A))
      = ∏ j : Fin n, ν (i.succAbove j) A := by
  rw [Measure.pi_pi, Fin.prod_univ_succAbove _ i]
  simp [Fin.succAbove_ne]

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hθ : 0 < θ) (hθ1 : θ < 1)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
lemma law_zero : (rivalInstance R m θ n hθ.le hθ1.le).law 0 = Measure.dirac 1 := by
  simp [rivalInstance]

lemma lint_rival (i : Suppliers n) (hi : i ≠ 0) (f : ℝ → ℝ≥0∞) :
    ∫⁻ a, f a ∂((rivalInstance R m θ n hθ.le hθ1.le).law i) =
      ENNReal.ofReal (p θ n) * f R + ENNReal.ofReal (1 - p θ n) * f (1 + m) := by
  simp only [rivalInstance, hi, if_false, rivalLaw, bernoulliMeasure_def]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac]
  have h1 : 0 ≤ p θ n := Real.rpow_nonneg hθ.le _
  have h2 : p θ n ≤ 1 := Real.rpow_le_one hθ.le hθ1.le (by positivity)
  rw [ENNReal.smul_def, ENNReal.smul_def]
  congr 2
  · rw [ENNReal.ofReal, Real.toNNReal_of_nonneg h1]; rfl
  · rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (by linarith)]; rfl

lemma bid_zero (c : ℝ) : (mkProfile n R mLaw pres).bid 0 c = mLaw := by
  simp [mkProfile]

lemma bid_rival (i : Suppliers n) (hi : i ≠ 0) (c : ℝ) :
    (mkProfile n R mLaw pres).bid i c = if c = R then Measure.dirac (R + (i : ℕ)) else pres i := by
  simp [mkProfile, hi, Kernel.piecewise_apply]

lemma marg_apply {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n) (i : Suppliers n) (s : Set ℝ)
    (hs : MeasurableSet s) : marginalBidLaw D σ i s = ∫⁻ a, σ.bid i a s ∂(D.law i) :=
  Measure.bind_apply hs (Kernel.aemeasurable _)

lemma marginal_zero_aux :
    marginalBidLaw (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres) 0 = mLaw := by
  ext s hs
  rw [marg_apply _ _ _ _ hs, law_zero hθ hθ1, lintegral_dirac, bid_zero]

lemma marginal_rival_fixed_aux (hmR : m < R - 1) (i : Suppliers n) (hi : i ≠ 0) (s : Set ℝ) (hs : MeasurableSet s) :
    marginalBidLaw (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres) i s =
      ENNReal.ofReal (p θ n) * Measure.dirac (R + (i : ℕ)) s +
        ENNReal.ofReal (1 - p θ n) * pres i s := by
  rw [marg_apply _ _ _ _ hs, lint_rival hθ hθ1 i hi, bid_rival _ _ i hi, bid_rival _ _ i hi]
  have : (1 + m) ≠ R := by intro h; linarith
  simp [this]

lemma rival_atom (hP1 : ∀ j : ℕ, 1 ≤ j → ∀ x : ℝ, x ≠ R + j → pres j {x} = 0)
    (i : Suppliers n) (hi : i ≠ 0) (y : ℝ) (hy : y ≠ R + (i : ℕ)) :
    marginalBidLaw (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres) i {y} = 0 := by
  have hi1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hi (Fin.ext h))
  have hk : ∀ c, (mkProfile n R mLaw pres).bid i c {y} = 0 := by
    intro c
    rw [bid_rival _ _ i hi]
    split_ifs
    · simp [hy]
    · exact hP1 _ hi1 y hy
  rw [marg_apply _ _ _ _ (measurableSet_singleton y)]
  simp [hk]

lemma playLaw_map' {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n) :
    (playLaw D σ).map (fun (x : Suppliers n → ℝ × ℝ) j => (x j).2)
      = Measure.pi (marginalBidLaw D σ) := by
  unfold playLaw
  rw [Measure.pi_map_pi (f := fun _ => (Prod.snd : ℝ × ℝ → ℝ)) (fun j => measurable_snd.aemeasurable)]
  congr 1
  ext1 j
  show (D.law j ⊗ₘ σ.bid j).snd = _
  rw [Measure.snd_compProd]
  rfl

lemma pi_tie {n : ℕ} (ν : Suppliers n → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    (i : Suppliers n) (k : Fin n) :
    Measure.pi ν {b | b i = b (i.succAbove k)} = ∫⁻ a, ν (i.succAbove k) {a} ∂(ν i) := by
  have hmp := measurePreserving_piFinSuccAbove ν i
  set T : Set (ℝ × (Fin n → ℝ)) := {q | q.1 = q.2 k} with hT
  have hTm : MeasurableSet T :=
    measurableSet_eq_fun measurable_fst ((measurable_pi_apply k).comp measurable_snd)
  have e : {b : Suppliers n → ℝ | b i = b (i.succAbove k)} =
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' T := by
    ext b
    simp [hT, MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]
  rw [e, hmp.measure_preimage_equiv, Measure.prod_apply hTm]
  congr 1
  ext1 a
  have : Prod.mk a ⁻¹' T = (fun y : Fin n → ℝ => y k) ⁻¹' {a} := by
    ext r; simp [hT, eq_comm]
  rw [this, (measurePreserving_eval (fun j => ν (i.succAbove j)) k).measure_preimage
    (measurableSet_singleton a).nullMeasurableSet]

lemma tie_null (hP1 : ∀ j : ℕ, 1 ≤ j → ∀ x : ℝ, x ≠ R + j → pres j {x} = 0)
    (hM : ∀ᵐ y ∂mLaw, y ≤ R) (i j : Suppliers n) (hij : i ≠ j) (hj : j ≠ 0) :
    Measure.pi (marginalBidLaw (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres))
      {b | b i = b j} = 0 := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (Ne.symm hij)
  rw [← hk, pi_tie, hk]
  have hj1 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by
    have : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hj (Fin.ext h))
    exact_mod_cast this
  have hae : ∀ᵐ a ∂(marginalBidLaw (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres) i),
      a ≠ R + ((j : ℕ) : ℝ) := by
    by_cases hi : i = 0
    · subst hi
      rw [marginal_zero_aux hθ hθ1]
      filter_upwards [hM] with a ha
      intro h; linarith
    · apply measure_eq_zero_iff_ae_notMem.1
      apply rival_atom hθ hθ1 mLaw pres hP1 i hi
      intro h
      apply hij
      have : ((j : ℕ) : ℝ) = ((i : ℕ) : ℝ) := by linarith
      exact Fin.ext (by exact_mod_cast this.symm)
  rw [lintegral_congr_ae (g := fun _ => 0)]
  · simp
  · filter_upwards [hae] with a ha
    exact rival_atom hθ hθ1 mLaw pres hP1 j hj a ha

lemma noBidTies_of_aux (hP1 : ∀ j : ℕ, 1 ≤ j → ∀ x : ℝ, x ≠ R + j → pres j {x} = 0)
    (hM : ∀ᵐ y ∂mLaw, y ≤ R) :
    NoBidTies (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres) := by
  unfold NoBidTies
  have hg : Measurable (fun (x : Suppliers n → ℝ × ℝ) j => (x j).2) :=
    measurable_pi_lambda _ (fun j => measurable_snd.comp (measurable_pi_apply j))
  apply ae_of_ae_map (p := fun b : Suppliers n → ℝ => Function.Injective b) hg.aemeasurable
  rw [playLaw_map']
  have h1 : ∀ i j : Suppliers n, ∀ᵐ b ∂(Measure.pi (marginalBidLaw (rivalInstance R m θ n hθ.le hθ1.le)
      (mkProfile n R mLaw pres))), i ≠ j → b i ≠ b j := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · have hz : Measure.pi (marginalBidLaw (rivalInstance R m θ n hθ.le hθ1.le)
          (mkProfile n R mLaw pres)) {b | b i = b j} = 0 := by
        by_cases hj : j = 0
        · have hi : i ≠ 0 := hj ▸ hij
          have : {b : Suppliers n → ℝ | b i = b j} = {b | b j = b i} := by ext; simp [eq_comm]
          rw [this]
          exact tie_null hθ hθ1 mLaw pres hP1 hM j i (Ne.symm hij) hi
        · exact tie_null hθ hθ1 mLaw pres hP1 hM i j hij hj
      rw [ae_iff]
      refine measure_mono_null (fun b hb => ?_) hz
      by_contra hc
      exact hb (fun _ => hc)
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 (h1 i)] with b hb
  intro i j h
  by_contra hne
  exact hb i j hne h

lemma isAcceptBNE_of_aux (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n)
    (hM : ∀ᵐ b ∂mLaw, ∀ a : ℝ,
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S 0 1 a ≤
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S 0 1 b)
    (hP : ∀ i : Suppliers n, i ≠ 0 → ∀ᵐ b ∂(pres i), ∀ a : ℝ,
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S i (1 + m) a ≤
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S i (1 + m) b)
    (hMge : ∀ᵐ b ∂mLaw, 1 ≤ b) (hPge : ∀ j : ℕ, 1 ≤ j → ∀ᵐ b ∂(pres j), 1 + m ≤ b) :
    IsAcceptBNE (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S := by
  have htypes : ∀ i : Suppliers n, i ≠ 0 → ∀ c ∈ (rivalInstance R m θ n hθ.le hθ1.le).types i,
      c = 1 + m ∨ c = R := by
    intro i hi c hc
    simpa [rivalInstance, hi] using hc
  have htype0 : ∀ c ∈ (rivalInstance R m θ n hθ.le hθ1.le).types 0, c = 1 := by
    intro c hc
    simpa [rivalInstance] using hc
  refine ⟨?_, ?_⟩
  · intro i c hc
    by_cases hi : i = 0
    · subst hi
      rw [htype0 c hc, bid_zero]
      exact hMge
    · have hi1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hi (Fin.ext h))
      rw [bid_rival _ _ i hi]
      split_ifs with hcR
      · rw [ae_dirac_eq]
        refine Filter.eventually_pure.2 ?_
        rw [hcR]
        have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
        linarith
      · rcases htypes i hi c hc with h | h
        · rw [h]; exact hPge _ hi1
        · exact absurd h hcR
  · intro i c hc
    by_cases hi : i = 0
    · subst hi
      rw [htype0 c hc, bid_zero]
      exact hM
    · have hi1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by
        have : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hi (Fin.ext h))
        exact_mod_cast this
      rw [bid_rival _ _ i hi]
      split_ifs with hcR
      · rw [ae_dirac_eq]
        refine Filter.eventually_pure.2 ?_
        intro a
        have h0 : S (R + ((i : ℕ) : ℝ)) = 0 := Dev.A1.S_zero hS (by linarith)
        have hr : acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S i c
            (R + ((i : ℕ) : ℝ)) = 0 := by
          simp [acceptUtility, h0]
        rw [hr]
        unfold acceptUtility standardUtility
        have hw := ENNReal.toReal_nonneg (a := interimWin (rivalInstance R m θ n hθ.le hθ1.le) τ
          (mkProfile n R mLaw pres) i a)
        by_cases haR : R < a
        · rw [Dev.A1.S_zero hS haR]; simp
        · have := Dev.A1.S_nonneg hS a
          have : a - c ≤ 0 := by rw [hcR]; linarith
          have := mul_nonpos_of_nonpos_of_nonneg this hw
          exact mul_nonpos_of_nonpos_of_nonneg this (Dev.A1.S_nonneg hS a)
      · rcases htypes i hi c hc with h | h
        · rw [h]; exact hP i hi
        · exact absurd h hcR

lemma ae_cost_mem' {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n) :
    ∀ᵐ x ∂(playLaw D σ), ∀ i, (x i).1 ∈ D.types i := by
  rw [ae_all_iff]
  intro i
  have hq := (measurePreserving_eval (fun i => D.law i ⊗ₘ σ.bid i) i).quasiMeasurePreserving
  have h1 : ∀ᵐ y ∂(D.law i ⊗ₘ σ.bid i), y.1 ∈ D.types i := by
    have h2 : ∀ᵐ y ∂(D.law i ⊗ₘ σ.bid i).fst, y ∈ D.types i := by
      rw [Measure.fst_compProd]
      exact mem_ae_iff.2 (D.concentrated i)
    exact ae_of_ae_map measurable_fst.aemeasurable h2
  exact hq.ae h1

lemma ae_type_mem' {n : ℕ} (D : IndependentTypes n) :
    ∀ᵐ c ∂(typeLaw D), ∀ i, c i ∈ D.types i := by
  rw [ae_all_iff]
  intro i
  have hq := (measurePreserving_eval D.law i).quasiMeasurePreserving
  exact hq.ae (mem_ae_iff.2 (D.concentrated i))

lemma types_ge (hm : 0 < m) (hmR : m < R - 1) (i : Suppliers n) (c : ℝ)
    (hc : c ∈ (rivalInstance R m θ n hθ.le hθ1.le).types i) : 1 ≤ c := by
  by_cases hi : i = 0
  · have : c = 1 := by simpa [rivalInstance, hi] using hc
    rw [this]
  · have : c = 1 + m ∨ c = R := by simpa [rivalInstance, hi] using hc
    rcases this with h | h <;> rw [h] <;> linarith

lemma optimal_eq_aux (hm : 0 < m) (hmR : m < R - 1) :
    optimalSocialCost (rivalInstance R m θ n hθ.le hθ1.le) = 1 := by
  have : IsProbabilityMeasure (typeLaw (rivalInstance R m θ n hθ.le hθ1.le)) := by
    unfold typeLaw; infer_instance
  unfold optimalSocialCost
  have : ∀ᵐ c ∂(typeLaw (rivalInstance R m θ n hθ.le hθ1.le)), ENNReal.ofReal (lowest c) = 1 := by
    filter_upwards [ae_type_mem' (rivalInstance R m θ n hθ.le hθ1.le)] with c hc
    have h0 : c 0 = 1 := by simpa [rivalInstance] using hc 0
    have hl : lowest c = 1 := by
      unfold lowest
      exact le_antisymm (h0 ▸ Finset.inf'_le _ (Finset.mem_univ 0))
        (Finset.le_inf' _ _ fun i _ => types_ge hθ hθ1 hm hmR i (c i) (hc i))
    simp [hl]
  rw [lintegral_congr_ae this]
  simp

lemma winnerCost_ge {n : ℕ} (τ : TieRule n) (x : Suppliers n → ℝ × ℝ) (a : ℝ)
    (h : ∀ i, (∀ j, (x i).2 ≤ (x j).2) → a ≤ (x i).1) : ENNReal.ofReal a ≤ winnerCost τ x := by
  unfold winnerCost
  calc ENNReal.ofReal a = ∑ i, ENNReal.ofReal a * τ.select (fun j => (x j).2) {i} := by
        rw [← Finset.mul_sum, Dev.L31C.sum_select]; simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
        by_cases hl : ∀ j, (x i).2 ≤ (x j).2
        · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (h i hl)) _
        · push Not at hl
          rw [Dev.L31C.sel_zero τ _ i hl]; simp

lemma integrand_ge (a s R : ℝ) (W : ℝ≥0∞) (hW : ENNReal.ofReal a ≤ W) (haR : a ≤ R)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ENNReal.ofReal a ≤ W * ENNReal.ofReal s + ENNReal.ofReal R * ENNReal.ofReal (1 - s) := by
  calc ENNReal.ofReal a = ENNReal.ofReal a * ENNReal.ofReal s + ENNReal.ofReal a * ENNReal.ofReal (1 - s) := by
        rw [← mul_add, ← ENNReal.ofReal_add hs0 (by linarith)]; simp
    _ ≤ _ := add_le_add (mul_le_mul_left hW _) (mul_le_mul_left (ENNReal.ofReal_le_ofReal haR) _)

lemma integrand_one (hm : 0 < m) (hmR : m < R - 1) (S : ℝ → ℝ) (hS : IsAcceptance R S)
    (τ : TieRule n) (x : Suppliers n → ℝ × ℝ)
    (hx : ∀ i, (x i).1 ∈ (rivalInstance R m θ n hθ.le hθ1.le).types i) :
    1 ≤ winnerCost τ x * ENNReal.ofReal (S (lowest (fun i => (x i).2))) +
      ENNReal.ofReal R * ENNReal.ofReal (1 - S (lowest (fun i => (x i).2))) := by
  have := integrand_ge 1 (S (lowest (fun i => (x i).2))) R (winnerCost τ x)
    (winnerCost_ge τ x 1 (fun i _ => types_ge hθ hθ1 hm hmR i _ (hx i))) (by linarith)
    (Dev.A1.S_nonneg hS _) (Dev.A1.S_le_one hS _)
  simpa using this

lemma socialCost_ge_one_aux (hm : 0 < m) (hmR : m < R - 1) (S : ℝ → ℝ) (hS : IsAcceptance R S)
    (τ : TieRule n) (σ : MixedProfile n) :
    1 ≤ acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ σ R S := by
  unfold acceptSocialCost
  calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂(playLaw (rivalInstance R m θ n hθ.le hθ1.le) σ) := by
        unfold playLaw; simp
    _ ≤ _ := lintegral_mono_ae (by
        filter_upwards [ae_cost_mem' (rivalInstance R m θ n hθ.le hθ1.le) σ] with x hx
        exact integrand_one hθ hθ1 hm hmR S hS τ x hx)

lemma law_R (hmR : m < R - 1) (i : Suppliers n) (hi : i ≠ 0) :
    (rivalInstance R m θ n hθ.le hθ1.le).law i {R} = ENNReal.ofReal (p θ n) := by
  rw [← lintegral_indicator_one (measurableSet_singleton R), lint_rival hθ hθ1 i hi]
  have : (1 + m) ≠ R := by intro h; linarith
  simp [this]

lemma p_pow' {θ : ℝ} {n : ℕ} (hθ : 0 < θ) (hn : 1 ≤ n) : p θ n ^ n = θ := by
  unfold p
  rw [one_div]
  exact Real.rpow_inv_natCast_pow hθ.le (by omega)

lemma ae_rival_bid (t : ℝ) (hpres : ∀ j : ℕ, 1 ≤ j → pres j (Iio t) = 1) :
    ∀ᵐ x ∂(playLaw (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres)),
      ∀ i : Suppliers n, i ≠ 0 → ((x i).1 = R → (x i).2 = R + ((i : ℕ) : ℝ)) ∧
        ((x i).1 ≠ R → (x i).2 < t) := by
  rw [ae_all_iff]
  intro i
  by_cases hi : i = 0
  · exact Eventually.of_forall fun _ h => absurd hi h
  have hi1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hi (Fin.ext h))
  have hq := (measurePreserving_eval (fun i => (rivalInstance R m θ n hθ.le hθ1.le).law i ⊗ₘ
    (mkProfile n R mLaw pres).bid i) i).quasiMeasurePreserving
  have hmeas : MeasurableSet {q : ℝ × ℝ | (q.1 = R → q.2 = R + ((i : ℕ) : ℝ)) ∧ (q.1 ≠ R → q.2 < t)} := by
    have e : {q : ℝ × ℝ | (q.1 = R → q.2 = R + ((i : ℕ) : ℝ)) ∧ (q.1 ≠ R → q.2 < t)} =
        ((Prod.fst ⁻¹' {R})ᶜ ∪ Prod.snd ⁻¹' {R + ((i : ℕ) : ℝ)}) ∩
          (Prod.fst ⁻¹' {R} ∪ Prod.snd ⁻¹' Iio t) := by
      ext q
      simp only [mem_ofPred_eq, mem_inter_iff, mem_union, mem_compl_iff, mem_preimage,
        mem_singleton_iff, mem_Iio]
      tauto
    rw [e]
    exact ((measurable_fst (measurableSet_singleton R)).compl.union
      (measurable_snd (measurableSet_singleton _))).inter
      ((measurable_fst (measurableSet_singleton R)).union (measurable_snd measurableSet_Iio))
  have h1 : ∀ᵐ q ∂((rivalInstance R m θ n hθ.le hθ1.le).law i ⊗ₘ (mkProfile n R mLaw pres).bid i),
      (q.1 = R → q.2 = R + ((i : ℕ) : ℝ)) ∧ (q.1 ≠ R → q.2 < t) := by
    apply Measure.ae_compProd_of_ae_ae hmeas
    refine Eventually.of_forall fun a => ?_
    rw [bid_rival _ _ i hi]
    split_ifs with haR
    · rw [ae_dirac_eq]
      exact Filter.eventually_pure.2 ⟨fun _ => rfl, fun h => absurd haR h⟩
    · have : ∀ᵐ y ∂(pres i), y < t := by
        rw [ae_iff]
        have := (prob_compl_eq_zero_iff (μ := pres i) measurableSet_Iio).2 (hpres _ hi1)
        simpa [compl_def] using this
      filter_upwards [this] with y hy
      exact ⟨fun h => absurd h haR, fun _ => hy⟩
  have := hq.ae h1
  filter_upwards [this] with x hx _
  exact hx

lemma socialCost_ge_loss_aux (hm : 0 < m) (hmR : m < R - 1) (hn : 1 ≤ n)
    (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n) (t : ℝ)
    (ht : t ≤ R) (hpres : ∀ j : ℕ, 1 ≤ j → pres j (Iio t) = 1) :
    1 + ENNReal.ofReal m * mLaw {t} * ENNReal.ofReal (1 - θ) ≤
      acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) R S := by
  set D := rivalInstance R m θ n hθ.le hθ1.le with hD
  set σ := mkProfile n R mLaw pres with hσ
  set P := playLaw D σ with hP
  have hPprob : IsProbabilityMeasure P := by rw [hP]; unfold playLaw; infer_instance
  set F : Set (Suppliers n → ℝ × ℝ) := {x | (x 0).2 = t} with hF
  set B : Suppliers n → Set (ℝ × ℝ) := fun i => if i = 0 then Prod.snd ⁻¹' {t} else Prod.fst ⁻¹' {R}
    with hB
  set E := F \ Set.pi univ B with hE
  have hBm : ∀ i, MeasurableSet (B i) := by
    intro i
    simp only [hB]
    split_ifs
    · exact measurable_snd (measurableSet_singleton t)
    · exact measurable_fst (measurableSet_singleton R)
  have hpim : MeasurableSet (Set.pi univ B) := MeasurableSet.univ_pi hBm
  have hFm : MeasurableSet F :=
    measurableSet_eq_fun (measurable_snd.comp (measurable_pi_apply 0)) measurable_const
  have hEm : MeasurableSet E := hFm.diff hpim
  -- P F
  have hPF : P F = mLaw {t} := by
    have : F = (fun x : Suppliers n → ℝ × ℝ => x 0) ⁻¹' (Prod.snd ⁻¹' {t}) := by
      ext x; simp [hF]
    rw [this, hP, playLaw, (measurePreserving_eval _ 0).measure_preimage
      (measurable_snd (measurableSet_singleton t)).nullMeasurableSet,
      ← Measure.snd_apply (measurableSet_singleton t), Measure.snd_compProd]
    show marginalBidLaw D σ 0 {t} = _
    rw [hD, hσ, marginal_zero_aux hθ hθ1]
  have hPB : P (Set.pi univ B) = mLaw {t} * ENNReal.ofReal θ := by
    rw [hP, playLaw, Measure.pi_pi, Fin.prod_univ_succ]
    congr 1
    · simp only [hB, if_true]
      rw [← Measure.snd_apply (measurableSet_singleton t), Measure.snd_compProd]
      show marginalBidLaw D σ 0 {t} = _
      rw [hD, hσ, marginal_zero_aux hθ hθ1]
    · have : ∀ k : Fin n, (D.law k.succ ⊗ₘ σ.bid k.succ) (B k.succ) = ENNReal.ofReal (p θ n) := by
        intro k
        simp only [hB, Fin.succ_ne_zero, if_false]
        rw [← Measure.fst_apply (measurableSet_singleton R), Measure.fst_compProd, hD]
        exact law_R hθ hθ1 hmR _ (Fin.succ_ne_zero k)
      rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← ENNReal.ofReal_pow (show 0 ≤ p θ n from Real.rpow_nonneg hθ.le _), p_pow' hθ hn]
  have hFB : F ∩ Set.pi univ B = Set.pi univ B := by
    apply Set.inter_eq_right.2
    intro x hx
    have := hx 0 (mem_univ _)
    show (x 0).2 = t
    simpa [hB] using this
  have hPE : P E = mLaw {t} * ENNReal.ofReal (1 - θ) := by
    rw [hE, ← Set.sdiff_self_inter, hFB, measure_sdiff (by rw [← hFB]; exact inter_subset_left)
      hpim.nullMeasurableSet (measure_ne_top _ _), hPF, hPB,
      ENNReal.ofReal_sub _ hθ.le, ENNReal.mul_sub (fun _ _ => measure_ne_top _ _), ENNReal.ofReal_one,
      mul_one]
  -- pointwise
  have hpt : ∀ᵐ x ∂P, 1 + ENNReal.ofReal m * E.indicator 1 x ≤
      winnerCost τ x * ENNReal.ofReal (S (lowest (fun i => (x i).2))) +
      ENNReal.ofReal R * ENNReal.ofReal (1 - S (lowest (fun i => (x i).2))) := by
    filter_upwards [ae_cost_mem' D σ, ae_rival_bid hθ hθ1 mLaw pres t hpres] with x hx hr
    by_cases hxE : x ∈ E
    · rw [Set.indicator_of_mem hxE, Pi.one_apply, mul_one, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one hm.le]
      have hx0 : (x 0).2 = t := hxE.1
      have hnot : ¬ ∀ i, x i ∈ B i := fun h => hxE.2 (fun i _ => h i)
      push Not at hnot
      obtain ⟨j, hj⟩ := hnot
      have hj0 : j ≠ 0 := by
        intro h; subst h; exact hj (by simp [hB, hx0])
      have hjR : (x j).1 ≠ R := by
        intro h; exact hj (by simp [hB, hj0, h])
      have hjt : (x j).2 < t := (hr j hj0).2 hjR
      apply integrand_ge (1 + m) _ R _ _ (by linarith) (Dev.A1.S_nonneg hS _) (Dev.A1.S_le_one hS _)
      apply winnerCost_ge
      intro i hi
      have hit : (x i).2 < t := lt_of_le_of_lt (hi j) hjt
      have hi0 : i ≠ 0 := by intro h; subst h; linarith
      have hiR : (x i).1 ≠ R := by
        intro h
        have := (hr i hi0).1 h
        have : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by
          have : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hi0 (Fin.ext h))
          exact_mod_cast this
        linarith
      have := hx i
      have hc : (x i).1 = 1 + m ∨ (x i).1 = R := by simpa [hD, rivalInstance, hi0] using this
      rcases hc with h | h
      · rw [h]
      · exact absurd h hiR
    · rw [Set.indicator_of_notMem hxE, mul_zero, add_zero]
      exact integrand_one hθ hθ1 hm hmR S hS τ x hx
  unfold acceptSocialCost
  refine le_trans ?_ (lintegral_mono_ae hpt)
  rw [lintegral_add_left measurable_const,
    lintegral_const_mul (ENNReal.ofReal m) (f := E.indicator 1) (measurable_one.indicator hEm),
    lintegral_indicator_one hEm, ← hP, hPE, lintegral_one, measure_univ, mul_assoc]

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
/-- interim win sandwich, any instance and profile -/
lemma interimWin_ge (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (b : ℝ) :
    ∏ k : Fin n, marginalBidLaw D σ (i.succAbove k) (Ioi b) ≤ interimWin D τ σ i b := by
  unfold interimWin
  rw [← box_measure' (marginalBidLaw D σ) i (Ioi b)]
  have hmeas : MeasurableSet (Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ioi b)) :=
    MeasurableSet.univ_pi fun k => by by_cases hk : k = i <;> simp [hk, measurableSet_Ioi]
  rw [← lintegral_indicator_one hmeas]
  apply lintegral_mono
  intro bs
  by_cases hbs : bs ∈ Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ioi b)
  · rw [Set.indicator_of_mem hbs]
    simp only [Pi.one_apply]
    rw [Dev.L31C.sel_one τ _ i]
    intro j hj
    have := hbs j (mem_univ j)
    simp only [hj, if_false, mem_Ioi] at this
    simp [Function.update_self, Function.update_of_ne hj, this]
  · rw [Set.indicator_of_notMem hbs]; exact zero_le

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
alias interimWin_ge := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.interimWin_ge

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
lemma interimWin_le (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (b : ℝ) :
    interimWin D τ σ i b ≤ ∏ k : Fin n, marginalBidLaw D σ (i.succAbove k) (Ici b) := by
  unfold interimWin
  rw [← box_measure' (marginalBidLaw D σ) i (Ici b)]
  have hmeas : MeasurableSet (Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ici b)) :=
    MeasurableSet.univ_pi fun k => by by_cases hk : k = i <;> simp [hk, measurableSet_Ici]
  rw [← lintegral_indicator_one hmeas]
  apply lintegral_mono
  intro bs
  by_cases hbs : bs ∈ Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ici b)
  · rw [Set.indicator_of_mem hbs]
    simp only [Pi.one_apply]
    exact prob_le_one
  · rw [Set.indicator_of_notMem hbs]
    have : ∃ j, Function.update bs i b j < Function.update bs i b i := by
      by_contra hcon
      push Not at hcon
      apply hbs
      intro j _
      by_cases hj : j = i
      · simp [hj]
      · simp only [hj, if_false, mem_Ici]
        have := hcon j
        simpa [Function.update_self, Function.update_of_ne hj] using this
    simp only
    rw [Dev.L31C.sel_zero τ _ i this]

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
alias interimWin_le := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.interimWin_le

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
lemma interimWin_le_one (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (b : ℝ) : interimWin D τ σ i b ≤ 1 := by
  unfold interimWin
  calc _ ≤ ∫⁻ _bs, (1 : ℝ≥0∞) ∂(Measure.pi (marginalBidLaw D σ)) :=
        lintegral_mono fun _ => prob_le_one
    _ = 1 := by simp

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
alias interimWin_le_one := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.interimWin_le_one

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
/-- products over the others: M is index 0, rivals are the rest -/
lemma prod_succAbove_zero (f : Suppliers n → ℝ≥0∞) (q : ℝ≥0∞) (hf : ∀ j, j ≠ 0 → f j = q) :
    ∏ k : Fin n, f ((0 : Suppliers n).succAbove k) = q ^ n := by
  rw [Finset.prod_congr rfl (fun k _ => hf _ (Fin.succAbove_ne 0 k))]
  simp

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
alias prod_succAbove_zero := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.prod_succAbove_zero

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
lemma prod_succAbove_rival (f : Suppliers n → ℝ≥0∞) (q : ℝ≥0∞) (i : Suppliers n) (hi : i ≠ 0)
    (hf : ∀ j, j ≠ 0 → j ≠ i → f j = q) :
    ∏ k : Fin n, f (i.succAbove k) = f 0 * q ^ (n - 1) := by
  obtain ⟨k0, hk0⟩ := Fin.exists_succAbove_eq (Ne.symm hi)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0), hk0]
  congr 1
  rw [Finset.prod_congr rfl (fun k hk => hf _ (fun h => (Finset.ne_of_mem_erase hk)
    (Fin.succAbove_right_injective (h.trans hk0.symm))) (Fin.succAbove_ne i k))]
  simp [Finset.card_erase_of_mem]

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
alias prod_succAbove_rival := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.prod_succAbove_rival

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
lemma marginal_zero :
    marginalBidLaw (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres) 0 = mLaw :=
  marginal_zero_aux hθ hθ1 mLaw pres

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
alias marginal_zero := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.marginal_zero

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
include hmR in
lemma marginal_rival (i : Suppliers n) (hi : i ≠ 0) (s : Set ℝ) (hs : MeasurableSet s) :
    marginalBidLaw (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres) i s =
      ENNReal.ofReal (p θ n) * Measure.dirac (R + (i : ℕ)) s +
        ENNReal.ofReal (1 - p θ n) * pres i s :=
  marginal_rival_fixed_aux hθ hθ1 mLaw pres hmR i hi s hs

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
alias marginal_rival := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.marginal_rival

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
/-- the equilibrium criterion: M's and the present rivals' draws are best responses
(the cost-`R` rivals' bid `R + i` always is one) -/
lemma isAcceptBNE_of (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n)
    (hM : ∀ᵐ b ∂mLaw, ∀ a : ℝ,
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S 0 1 a ≤
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S 0 1 b)
    (hP : ∀ i : Suppliers n, i ≠ 0 → ∀ᵐ b ∂(pres i), ∀ a : ℝ,
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S i (1 + m) a ≤
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S i (1 + m) b)
    (hMge : ∀ᵐ b ∂mLaw, 1 ≤ b) (hPge : ∀ j : ℕ, 1 ≤ j → ∀ᵐ b ∂(pres j), 1 + m ≤ b) :
    IsAcceptBNE (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) S :=
  isAcceptBNE_of_aux hθ hθ1 mLaw pres S hS τ hM hP hMge hPge

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
alias isAcceptBNE_of := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.isAcceptBNE_of

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
lemma noBidTies_of (hP1 : ∀ j : ℕ, 1 ≤ j → ∀ x : ℝ, x ≠ R + j → pres j {x} = 0)
    (hM : ∀ᵐ y ∂mLaw, y ≤ R) :
    NoBidTies (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R mLaw pres) :=
  noBidTies_of_aux hθ hθ1 mLaw pres hP1 hM

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
alias noBidTies_of := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.noBidTies_of

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
include hm hmR in
lemma optimal_eq : optimalSocialCost (rivalInstance R m θ n hθ.le hθ1.le) = 1 :=
  optimal_eq_aux hθ hθ1 hm hmR

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
alias optimal_eq := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.optimal_eq

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
include hm hmR in
lemma socialCost_ge_one (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n)
    (σ : MixedProfile n) :
    1 ≤ acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ σ R S :=
  socialCost_ge_one_aux hθ hθ1 hm hmR S hS τ σ

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
alias socialCost_ge_one := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.socialCost_ge_one

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
include hm hmR hn in
lemma socialCost_ge_loss (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n) (t : ℝ)
    (ht : t ≤ R) (hpres : ∀ j : ℕ, 1 ≤ j → pres j (Iio t) = 1) :
    1 + ENNReal.ofReal m * mLaw {t} * ENNReal.ofReal (1 - θ) ≤
      acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R mLaw pres) R S :=
  socialCost_ge_loss_aux hθ hθ1 mLaw pres hm hmR hn S hS τ t ht hpres

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (hn : 1 ≤ n)
variable (mLaw : Measure ℝ) (pres : ℕ → Measure ℝ) [IsProbabilityMeasure mLaw]
  [∀ j, IsProbabilityMeasure (pres j)]
alias socialCost_ge_loss := ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG.socialCost_ge_loss

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! ## Part P: the loss function Φ -/

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! ## Part P: the loss function Φ -/

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartG
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! ## General helpers -/

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (t : ℝ) (pres : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (pres j)]
  (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n)
/-! ## Rivals' best responses when M bids `t ≤ 1 + m` surely -/

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! ## Part E: the equilibrium in each case -/

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE1
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE2
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
/-! # Lemma A.2, Blueprint Part E2: the case `τ > m`, `w0 > m` (`profile_w0_gt`). -/
/-! ## Generic utility bounds -/

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE2
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-! ## The construction -/

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE2
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2.PartE2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.A2

end ProcurementPoA.DeterministicCap.Supplement.Dev.A2
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
/-! Blueprint for Theorem 5.7. Every `sorry` is a stub proved in a Part. -/
/-! ## Part X: the explicit A.2 laws, as functions of the acceptance function -/
/-- the zero case of Lemma A.2 -/
def ZeroCase (S : ℝ → ℝ) : Prop := ∀ b : ℝ, 1 < b → S b = 0

/-- M's bid law in the A.2 equilibrium -/
noncomputable def lawM (R m θ : ℝ) (n : ℕ) (S : ℝ → ℝ) : Measure ℝ := by
  classical
  exact if ZeroCase S then Measure.dirac 1
    else if tau R S ≤ m then Measure.dirac (1 + tau R S)
    else if w0 R m θ S = m then Measure.dirac (1 + m)
    else cdfLaw (mCDF R m θ n S)

/-- a present rival's bid law in the A.2 equilibrium (index `j ≥ 1`) -/
noncomputable def lawP (R m θ : ℝ) (n : ℕ) (S : ℝ → ℝ) (j : ℕ) : Measure ℝ := by
  classical
  exact if ZeroCase S ∨ tau R S ≤ m then Measure.dirac (R + j)
    else cdfLaw (rivalCDF R m θ n S j)

instance lawM_isProb (R m θ : ℝ) (n : ℕ) (S : ℝ → ℝ) : IsProbabilityMeasure (lawM R m θ n S) := by
  unfold lawM; split_ifs <;> infer_instance

instance lawP_isProb (R m θ : ℝ) (n : ℕ) (S : ℝ → ℝ) (j : ℕ) :
    IsProbabilityMeasure (lawP R m θ n S j) := by
  unfold lawP; split_ifs <;> infer_instance

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
/-! # Theorem 5.7, Blueprint Part X: Lemma A.2 for the explicit profile `lawM`/`lawP`.
The four case proofs are adapted from `A2PartE1.lean` and `A2PartE2.lean`. -/
/-! ## General helpers -/
lemma util_eq {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (S : ℝ → ℝ) (i : Suppliers n) (c a : ℝ) :
    acceptUtility D τ σ S i c a = (a - c) * (interimWin D τ σ i a).toReal * S a := rfl

lemma win_toReal_nonneg {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (a : ℝ) : 0 ≤ (interimWin D τ σ i a).toReal := ENNReal.toReal_nonneg

lemma win_toReal_le_one {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (a : ℝ) : (interimWin D τ σ i a).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using interimWin_le_one D τ σ i a)

lemma util_nonpos {R : ℝ} {S : ℝ → ℝ} (hS : IsAcceptance R S) {n : ℕ} (D : IndependentTypes n)
    (τ : TieRule n) (σ : MixedProfile n) (i : Suppliers n) {c a : ℝ} (ha : a ≤ c) :
    acceptUtility D τ σ S i c a ≤ 0 := by
  rw [util_eq]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (win_toReal_nonneg D τ σ i a))
    (Dev.A1.S_nonneg hS a)

lemma util_le {R : ℝ} {S : ℝ → ℝ} (hS : IsAcceptance R S) {n : ℕ} (D : IndependentTypes n)
    (τ : TieRule n) (σ : MixedProfile n) (i : Suppliers n) {c a : ℝ} (ha : c ≤ a) :
    acceptUtility D τ σ S i c a ≤ (a - c) * S a := by
  rw [util_eq]
  have h1 := win_toReal_le_one D τ σ i a
  have h0 := win_toReal_nonneg D τ σ i a
  have hS0 := Dev.A1.S_nonneg hS a
  have : 0 ≤ (a - c) * S a := mul_nonneg (by linarith) hS0
  nlinarith

lemma util_of_win_zero {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (S : ℝ → ℝ) (i : Suppliers n) (c a : ℝ) (h : interimWin D τ σ i a = 0) :
    acceptUtility D τ σ S i c a = 0 := by
  rw [util_eq, h]; simp

lemma win_rival_le {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (hi : i ≠ 0) (a : ℝ) :
    interimWin D τ σ i a ≤ marginalBidLaw D σ 0 (Ici a) := by
  classical
  set f : Suppliers n → ℝ≥0∞ := fun j => marginalBidLaw D σ j (Ici a) with hf
  set f' : Suppliers n → ℝ≥0∞ := fun j => if j = 0 then f 0 else 1 with hf'
  calc interimWin D τ σ i a ≤ ∏ k : Fin n, f (i.succAbove k) := interimWin_le D τ σ i a
    _ ≤ ∏ k : Fin n, f' (i.succAbove k) := by
        apply Finset.prod_le_prod'
        intro k _
        by_cases hj : i.succAbove k = 0
        · simp [hf', hj]
        · simp only [hf', if_neg hj, hf]; exact prob_le_one
    _ = f' 0 * 1 ^ (n - 1) := prod_succAbove_rival f' 1 i hi (fun j hj _ => if_neg hj)
    _ = f 0 := by simp [hf']

lemma win_M_le {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (a : ℝ) (q : ℝ≥0∞) (hq : ∀ j : Suppliers n, j ≠ 0 → marginalBidLaw D σ j (Ici a) ≤ q) :
    interimWin D τ σ 0 a ≤ q ^ n := by
  calc interimWin D τ σ 0 a ≤ ∏ k : Fin n, marginalBidLaw D σ ((0 : Suppliers n).succAbove k) (Ici a) :=
        interimWin_le D τ σ 0 a
    _ ≤ ∏ _k : Fin n, q := Finset.prod_le_prod' (fun k _ => hq _ (Fin.succAbove_ne 0 k))
    _ = q ^ n := by simp

lemma win_M_eq_one {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (a : ℝ) (hq : ∀ j : Suppliers n, j ≠ 0 → marginalBidLaw D σ j (Ioi a) = 1) :
    interimWin D τ σ 0 a = 1 := by
  refine le_antisymm (interimWin_le_one D τ σ 0 a) ?_
  calc (1 : ℝ≥0∞) = ∏ k : Fin n, marginalBidLaw D σ ((0 : Suppliers n).succAbove k) (Ioi a) := by
        rw [prod_succAbove_zero (fun j => marginalBidLaw D σ j (Ioi a)) 1 hq, one_pow]
    _ ≤ interimWin D τ σ 0 a := interimWin_ge D τ σ 0 a

lemma one_le_val {n : ℕ} (j : Suppliers n) (hj : j ≠ 0) : 1 ≤ (j : ℕ) := by
  exact Nat.one_le_iff_ne_zero.mpr (fun h => hj (Fin.ext (by simpa using h)))

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
variable {R m θ : ℝ} {n : ℕ} (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
  (t : ℝ) (pres : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (pres j)]
  (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n)
/-! ## Rivals' best responses when M bids `t ≤ 1 + m` surely -/
lemma rival_high (ht : t ≤ 1 + m) (i : Suppliers n) (hi : i ≠ 0) (a : ℝ) (ha : 1 + m < a) :
    acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ
      (mkProfile n R (Measure.dirac t) pres) S i (1 + m) a = 0 := by
  apply util_of_win_zero
  refine le_antisymm ?_ bot_le
  refine (win_rival_le _ τ _ i hi a).trans ?_
  rw [marginal_zero hθ hθ1]
  have : t ∉ Ici a := by simp; linarith
  simp [Measure.dirac_apply' _ measurableSet_Ici, this]

include hS in
lemma rival_br (ht : t ≤ 1 + m) (i : Suppliers n) (hi : i ≠ 0)
    (hpres : ∀ᵐ b ∂(pres i), 1 + m ≤ b) :
    ∀ᵐ b ∂(pres i), ∀ a : ℝ,
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ
        (mkProfile n R (Measure.dirac t) pres) S i (1 + m) a ≤
      acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ
        (mkProfile n R (Measure.dirac t) pres) S i (1 + m) b := by
  filter_upwards [hpres] with b hb a
  have hb0 : acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ
      (mkProfile n R (Measure.dirac t) pres) S i (1 + m) b = 0 := by
    rcases hb.eq_or_lt with h | h
    · rw [util_eq, ← h]; simp
    · exact rival_high hθ hθ1 t pres S τ ht i hi b h
  rw [hb0]
  rcases le_or_gt a (1 + m) with ha | ha
  · exact util_nonpos hS _ τ _ i ha
  · exact (rival_high hθ hθ1 t pres S τ ht i hi a ha).le

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
lemma cost_of_not_lt {R m θ : ℝ} (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    {n : ℕ} (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n) (σ : MixedProfile n)
    (hlt : ¬ m < θ * monopolyProfit S 1) :
    1 + ENNReal.ofReal (rivalHighProbability θ n * Phi m θ (monopolyProfit S 1)) ≤
      acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ σ R S := by
  simp only [Phi, if_neg hlt, mul_zero, ENNReal.ofReal_zero, add_zero]
  exact socialCost_ge_one hm hmR hθ hθ1 S hS τ σ

lemma dirac_singleton_ne (y x : ℝ) (hx : x ≠ y) : Measure.dirac y {x} = 0 := by
  rw [Measure.dirac_apply' _ (measurableSet_singleton x)]
  simp [Ne.symm hx]

/-- zero case: M bids 1, rival `i` bids `R + i` -/
lemma profile_zero (R m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (n : ℕ) (hn : 1 ≤ n) (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n)
    (hz : ∀ b : ℝ, 1 < b → S b = 0) :
    IsAcceptBNE (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R (Measure.dirac 1) (fun j => Measure.dirac (R + j))) S ∧
      NoBidTies (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R (Measure.dirac 1) (fun j => Measure.dirac (R + j))) ∧
      1 + ENNReal.ofReal (rivalHighProbability θ n * Phi m θ (monopolyProfit S 1)) ≤
        acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R (Measure.dirac 1) (fun j => Measure.dirac (R + j))) R S := by
  have h : Hyp R m θ n S := ⟨hm, hmR, hθ, hθ1, hn, hS⟩
  have hπ : piS S = 0 := pi_eq_zero_of_zero h hz
  refine ⟨?_, ?_, ?_⟩
  · apply isAcceptBNE_of hθ hθ1 _ _ S hS τ
    · rw [ae_dirac_eq, eventually_pure]
      intro a
      rw [show acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ
        (mkProfile n R (Measure.dirac 1) (fun j => Measure.dirac (R + j))) S 0 1 1 = 0 by
          rw [util_eq]; simp]
      rcases le_or_gt a 1 with ha | ha
      · exact util_nonpos hS _ τ _ 0 ha
      · rw [util_eq, hz a ha]; simp
    · intro i hi
      refine rival_br hθ hθ1 1 _ S hS τ (by linarith) i hi ?_
      rw [ae_dirac_eq, eventually_pure]
      have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [ae_dirac_eq, eventually_pure]
    · intro j _
      rw [ae_dirac_eq, eventually_pure]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith
  · refine noBidTies_of hθ hθ1 _ _ (fun j _ x hx => dirac_singleton_ne _ x hx) ?_
    rw [ae_dirac_eq, eventually_pure]
    linarith
  · refine cost_of_not_lt hm hmR hθ hθ1 S hS τ _ ?_
    show ¬ m < θ * piS S
    rw [hπ]; simp; exact hm.le

/-- case τ ≤ m: M bids `1 + τ`, every rival bids `R + i` -/
lemma profile_tau_le (R m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (n : ℕ) (hn : 1 ≤ n) (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n)
    (hr : IsRegular R S) (hτ : tau R S ≤ m) :
    IsAcceptBNE (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R (Measure.dirac (1 + tau R S)) (fun j => Measure.dirac (R + j))) S ∧
      NoBidTies (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R (Measure.dirac (1 + tau R S)) (fun j => Measure.dirac (R + j))) ∧
      1 + ENNReal.ofReal (rivalHighProbability θ n * Phi m θ (monopolyProfit S 1)) ≤
        acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R (Measure.dirac (1 + tau R S)) (fun j => Measure.dirac (R + j))) R S := by
  have h : Hyp R m θ n S := ⟨hm, hmR, hθ, hθ1, hn, hS⟩
  have hπ0 := pi_pos h hr
  have hτ0 := tau_pos h hr
  have hgτ := g_tau h hr
  have hπτ := pi_le_tau h hr
  have hp0 := p_pos h
  have hp1 := p_lt_one h
  set T := tau R S with hT
  refine ⟨?_, ?_, ?_⟩
  · apply isAcceptBNE_of hθ hθ1 _ _ S hS τ
    · rw [ae_dirac_eq, eventually_pure]
      intro a
      have hwin : interimWin (rivalInstance R m θ n hθ.le hθ1.le) τ
          (mkProfile n R (Measure.dirac (1 + T)) (fun j => Measure.dirac (R + j))) 0 (1 + T) = 1 := by
        apply win_M_eq_one
        intro j hj
        rw [marginal_rival hmR hθ hθ1 _ _ j hj _ measurableSet_Ioi]
        have hj1 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast one_le_val j hj
        have hmem : R + ((j : ℕ) : ℝ) ∈ Ioi (1 + T) := by simp; linarith
        simp only [Measure.dirac_apply_of_mem hmem, mul_one]
        rw [← ENNReal.ofReal_add hp0.le (by linarith)]
        simp
      have hb : acceptUtility (rivalInstance R m θ n hθ.le hθ1.le) τ
          (mkProfile n R (Measure.dirac (1 + T)) (fun j => Measure.dirac (R + j))) S 0 1 (1 + T) =
          piS S := by
        rw [util_eq, hwin, ← hgτ]; simp [g]
      rw [hb]
      rcases le_or_gt a 1 with ha | ha
      · exact (util_nonpos hS _ τ _ 0 ha).trans hπ0.le
      · refine (util_le hS _ τ _ 0 ha.le).trans ?_
        have := g_le_pi h (a - 1)
        simp only [g, add_sub_cancel] at this
        exact this
    · intro i hi
      refine rival_br hθ hθ1 (1 + T) _ S hS τ (by linarith) i hi ?_
      rw [ae_dirac_eq, eventually_pure]
      have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [ae_dirac_eq, eventually_pure]; linarith
    · intro j _
      rw [ae_dirac_eq, eventually_pure]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith
  · refine noBidTies_of hθ hθ1 _ _ (fun j _ x hx => dirac_singleton_ne _ x hx) ?_
    rw [ae_dirac_eq, eventually_pure]
    linarith
  · refine cost_of_not_lt hm hmR hθ hθ1 S hS τ _ ?_
    show ¬ m < θ * piS S
    have : θ * piS S ≤ piS S := by nlinarith
    linarith

/-- case τ > m, w0 = m: M bids `1 + m`, present rivals draw from `cdfLaw (rivalCDF ..)` -/
lemma profile_w0_eq (R m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (n : ℕ) (hn : 1 ≤ n) (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n)
    (hr : IsRegular R S) (hτ : m < tau R S) (hw : w0 R m θ S = m) :
    IsAcceptBNE (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R (Measure.dirac (1 + m)) (fun j => cdfLaw (rivalCDF R m θ n S j))) S ∧
      NoBidTies (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R (Measure.dirac (1 + m)) (fun j => cdfLaw (rivalCDF R m θ n S j))) ∧
      1 + ENNReal.ofReal (rivalHighProbability θ n * Phi m θ (monopolyProfit S 1)) ≤
        acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R (Measure.dirac (1 + m)) (fun j => cdfLaw (rivalCDF R m θ n S j))) R S := by
  have h : Hyp R m θ n S := ⟨hm, hmR, hθ, hθ1, hn, hS⟩
  have hπ0 := pi_pos h hr
  have hp0 := p_pos h
  have hp1 := p_lt_one h
  have hu := u_pos h hr hτ
  have hτR := tau_le h hr
  have hgm : g S m = u m θ S := by have := (w0_mem h hr hτ).2; rwa [hw] at this
  have hmI : m ∈ Icc (w0 R m θ S) (tau R S) := by rw [hw]; exact ⟨le_rfl, hτ.le⟩
  have hτI : tau R S ∈ Icc (w0 R m θ S) (tau R S) := by rw [hw]; exact ⟨hτ.le, le_rfl⟩
  have hGm : G m θ n S m = 1 := by
    have h1 := p_add_G h hr hτ m
    have h2 : Gam m θ S m = 1 := by unfold Gam; rw [hgm]; exact div_self hu.ne'
    rw [h2, Real.one_rpow] at h1
    have h3 : (1 - p θ n) * G m θ n S m = (1 - p θ n) * 1 := by linarith
    exact mul_left_cancel₀ (sub_ne_zero.mpr hp1.ne') h3
  set D := rivalInstance R m θ n hθ.le hθ1.le with hD
  set σ := mkProfile n R (Measure.dirac (1 + m)) (fun j => cdfLaw (rivalCDF R m θ n S j)) with hσ
  -- M's utility at margin `w ≥ 0`, bounded through a present rival's survival `G x`
  have key : ∀ w x : ℝ, 0 ≤ w → x ∈ Icc (w0 R m θ S) (tau R S) →
      (∀ j : ℕ, 1 ≤ j → cdfLaw (rivalCDF R m θ n S j) (Ici (1 + w)) ≤ ENNReal.ofReal (G m θ n S x)) →
      acceptUtility D τ σ S 0 1 (1 + w) ≤ g S w * Gam m θ S x := by
    intro w x hw0 hx hpres
    obtain ⟨hGpow, hGam0⟩ := Gam_pow h hr hτ x hx
    have hG0 := (G_mem h hr hτ x hx).1
    have hq0 : 0 ≤ Gam m θ S x ^ (1 / (n : ℝ)) := Real.rpow_nonneg hGam0 _
    have hwin : interimWin D τ σ 0 (1 + w) ≤ ENNReal.ofReal (Gam m θ S x) := by
      have := win_M_le D τ σ (1 + w) (ENNReal.ofReal (Gam m θ S x ^ (1 / (n : ℝ)))) (by
        intro j hj
        rw [hσ, hD, marginal_rival hmR hθ hθ1 _ _ j hj _ measurableSet_Ici]
        calc ENNReal.ofReal (p θ n) * Measure.dirac (R + ((j : ℕ) : ℝ)) (Ici (1 + w)) +
              ENNReal.ofReal (1 - p θ n) * cdfLaw (rivalCDF R m θ n S j) (Ici (1 + w))
            ≤ ENNReal.ofReal (p θ n) * 1 + ENNReal.ofReal (1 - p θ n) * ENNReal.ofReal (G m θ n S x) :=
              add_le_add (mul_le_mul_right prob_le_one _)
                (mul_le_mul_right (hpres j (one_le_val j hj)) _)
          _ = ENNReal.ofReal (Gam m θ S x ^ (1 / (n : ℝ))) := by
              rw [mul_one, ← ENNReal.ofReal_mul (by linarith),
                ← ENNReal.ofReal_add hp0.le (mul_nonneg (by linarith) hG0), p_add_G h hr hτ x])
      rwa [← ENNReal.ofReal_pow hq0, hGpow] at this
    have hwr : (interimWin D τ σ 0 (1 + w)).toReal ≤ Gam m θ S x :=
      ENNReal.toReal_le_of_le_ofReal hGam0 hwin
    have hg0 : 0 ≤ g S w := mul_nonneg hw0 (Dev.A1.S_nonneg hS _)
    calc acceptUtility D τ σ S 0 1 (1 + w)
        = g S w * (interimWin D τ σ 0 (1 + w)).toReal := by rw [util_eq]; simp only [g]; ring
      _ ≤ g S w * Gam m θ S x := mul_le_mul_of_nonneg_left hwr hg0
  refine ⟨?_, ?_, ?_⟩
  · apply isAcceptBNE_of hθ hθ1 _ _ S hS τ
    · rw [ae_dirac_eq, eventually_pure]
      intro a
      have hwin : interimWin D τ σ 0 (1 + m) = 1 := by
        apply win_M_eq_one
        intro j hj
        rw [hσ, hD, marginal_rival hmR hθ hθ1 _ _ j hj _ measurableSet_Ioi]
        have hj1 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast one_le_val j hj
        have hmem : R + ((j : ℕ) : ℝ) ∈ Ioi (1 + m) := by simp; linarith
        have hP := (pres_Ioi h hr hτ j (one_le_val j hj) m hmI).1
        simp only [Measure.dirac_apply_of_mem hmem, mul_one]
        rw [hP, hGm, ENNReal.ofReal_one, mul_one, ← ENNReal.ofReal_add hp0.le (by linarith)]
        simp
      have hb : acceptUtility D τ σ S 0 1 (1 + m) = u m θ S := by
        rw [util_eq, hwin, ← hgm]; simp [g]
      rw [hb]
      obtain ⟨w, rfl⟩ : ∃ w, a = 1 + w := ⟨a - 1, by ring⟩
      rcases le_or_gt w 0 with hw1 | hw1
      · exact (util_nonpos hS _ τ _ 0 (by linarith)).trans hu.le
      rcases le_or_gt w m with hw2 | hw2
      · refine (util_le hS _ τ _ 0 (by linarith)).trans ?_
        have := g_le_u h hr hτ w (by rw [hw]; exact hw2)
        simp only [g] at this
        simpa using this
      rcases le_or_gt w (tau R S) with hw3 | hw3
      · have hwI : w ∈ Icc (w0 R m θ S) (tau R S) := by rw [hw]; exact ⟨hw2.le, hw3⟩
        refine (key w w hw1.le hwI (fun j hj => (pres_Ioi h hr hτ j hj w hwI).2.le)).trans ?_
        rw [Gam_mul_g h hr hτ w hwI]
      · refine (key w (tau R S) hw1.le hτI
          (fun j hj => pres_Ici_gt h hr hτ j hj (1 + w) (by linarith))).trans ?_
        rw [Gam_tau h hr hτ]
        have hg := g_le_pi h w
        have hg0 : 0 ≤ g S w := mul_nonneg hw1.le (Dev.A1.S_nonneg hS _)
        have hq : 0 ≤ u m θ S / piS S := div_nonneg hu.le hπ0.le
        calc g S w * (u m θ S / piS S) ≤ piS S * (u m θ S / piS S) :=
              mul_le_mul_of_nonneg_right hg hq
          _ = u m θ S := by field_simp
    · intro i hi
      refine rival_br hθ hθ1 (1 + m) _ S hS τ le_rfl i hi ?_
      filter_upwards [pres_ae h hr hτ i (one_le_val i hi)] with b hb
      have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [hw] at hb
      rcases hb with hb | hb
      · exact hb.1
      · rw [hb]; linarith
    · rw [ae_dirac_eq, eventually_pure]; linarith
    · intro j hj
      filter_upwards [pres_ae h hr hτ j hj] with b hb
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      rw [hw] at hb
      rcases hb with hb | hb
      · exact hb.1
      · rw [hb]; linarith
  · refine noBidTies_of hθ hθ1 _ _ (fun j hj x hx => pres_singleton h hr hτ j hj x hx) ?_
    rw [ae_dirac_eq, eventually_pure]
    linarith
  · refine cost_of_not_lt hm hmR hθ hθ1 S hS τ _ ?_
    intro hlt
    have := w0_gt_of h hr hτ hlt
    rw [hw] at this
    exact lt_irrefl _ this

/-! ## Generic utility bounds -/
lemma util_le_of_win {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (S : ℝ → ℝ) (hS0 : ∀ b, 0 ≤ S b) (i : Suppliers n) (c b q : ℝ) (hq : 0 ≤ q)
    (hcb : c ≤ b) (hw : interimWin D τ σ i b ≤ ENNReal.ofReal q) :
    acceptUtility D τ σ S i c b ≤ (b - c) * q * S b := by
  unfold acceptUtility standardUtility
  have h1 : (interimWin D τ σ i b).toReal ≤ q := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
    rwa [ENNReal.toReal_ofReal hq] at this
  have h2 := hS0 b
  have h3 : 0 ≤ b - c := sub_nonneg.mpr hcb
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) h2

lemma util_le_one {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (S : ℝ → ℝ) (hS0 : ∀ b, 0 ≤ S b) (i : Suppliers n) (c b : ℝ) (hcb : c ≤ b) :
    acceptUtility D τ σ S i c b ≤ (b - c) * S b := by
  have := util_le_of_win D τ σ S hS0 i c b 1 zero_le_one hcb
    (by rw [ENNReal.ofReal_one]; exact interimWin_le_one D τ σ i b)
  simpa using this

lemma util_nonpos2 {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (S : ℝ → ℝ) (hS0 : ∀ b, 0 ≤ S b) (i : Suppliers n) (c b : ℝ) (hcb : b ≤ c) :
    acceptUtility D τ σ S i c b ≤ 0 := by
  unfold acceptUtility standardUtility
  have h1 : 0 ≤ (interimWin D τ σ i b).toReal := ENNReal.toReal_nonneg
  have h2 := hS0 b
  have h3 : b - c ≤ 0 := by linarith
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h3 h1) h2

lemma util_eq_of_win {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (S : ℝ → ℝ) (i : Suppliers n) (c b q : ℝ) (hq : 0 ≤ q)
    (hw : interimWin D τ σ i b = ENNReal.ofReal q) :
    acceptUtility D τ σ S i c b = (b - c) * q * S b := by
  unfold acceptUtility standardUtility
  rw [hw, ENNReal.toReal_ofReal hq]

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
variable {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ}
/-! ## The construction -/
/-- a present rival's marginal on `[w0, τ]` -/
lemma marg_mid (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (j : Suppliers n) (hj : j ≠ 0) (w : ℝ) (hw' : w ∈ Icc (w0 R m θ S) (tau R S)) :
    marginalBidLaw (rivalInstance R m θ n h.hθ.le h.hθ1.le)
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) j
        (Ioi (1 + w)) = ENNReal.ofReal (Gam m θ S w ^ (1 / (n : ℝ))) ∧
    marginalBidLaw (rivalInstance R m θ n h.hθ.le h.hθ1.le)
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) j
        (Ici (1 + w)) = ENNReal.ofReal (Gam m θ S w ^ (1 / (n : ℝ))) := by
  have hj1 := one_le_val j hj
  have hj1' : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj1
  have htR := tau_le h hr
  have hRj : 1 + w < R + ((j : ℕ) : ℝ) := by linarith [hw'.2]
  have hp0 := (p_pos h).le
  have hp1 := p_lt_one h
  obtain ⟨hI, hC⟩ := pres_Ioi h hr hτ (j : ℕ) hj1 w hw'
  have hG := (G_mem h hr hτ w hw').1
  have key : ENNReal.ofReal (p θ n) * 1 + ENNReal.ofReal (1 - p θ n) *
      ENNReal.ofReal (G m θ n S w) = ENNReal.ofReal (Gam m θ S w ^ (1 / (n : ℝ))) := by
    rw [← p_add_G h hr hτ w, ENNReal.ofReal_add hp0 (mul_nonneg (by linarith) hG),
      ENNReal.ofReal_mul (by linarith), mul_one]
  constructor
  · rw [marginal_rival h.hmR h.hθ h.hθ1 _ _ j hj _ measurableSet_Ioi,
      Measure.dirac_apply_of_mem (show R + ((j : ℕ) : ℝ) ∈ Ioi (1 + w) from hRj)]
    rw [hI, key]
  · rw [marginal_rival h.hmR h.hθ h.hθ1 _ _ j hj _ measurableSet_Ici,
      Measure.dirac_apply_of_mem (show R + ((j : ℕ) : ℝ) ∈ Ici (1 + w) from hRj.le)]
    rw [hC, key]

/-- a present rival's marginal above `1 + τ` (up to `R`) -/
lemma marg_high (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (j : Suppliers n) (hj : j ≠ 0) (x : ℝ) (hx : 1 + tau R S < x) :
    marginalBidLaw (rivalInstance R m θ n h.hθ.le h.hθ1.le)
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) j
        (Ici x) ≤ ENNReal.ofReal (p θ n) := by
  have hj1 := one_le_val j hj
  have h1 := pres_Ici_gt h hr hτ (j : ℕ) hj1 x hx
  rw [G_tau_zero h hr hτ hw, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at h1
  rw [marginal_rival h.hmR h.hθ h.hθ1 _ _ j hj _ measurableSet_Ici]
  rw [h1, mul_zero, add_zero]
  calc ENNReal.ofReal (p θ n) * Measure.dirac (R + ((j : ℕ) : ℝ)) (Ici x)
      ≤ ENNReal.ofReal (p θ n) * 1 := by gcongr; exact prob_le_one
    _ = _ := mul_one _

/-- M's interim win on `[1 + w0, 1 + τ]` is `Γ` -/
lemma winM_mid (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S) (tr : TieRule n)
    (w : ℝ) (hw' : w ∈ Icc (w0 R m θ S) (tau R S)) :
    interimWin (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) 0
        (1 + w) = ENNReal.ofReal (Gam m θ S w) := by
  have hlo := interimWin_ge (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
    (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) 0 (1 + w)
  have hhi := interimWin_le (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
    (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) 0 (1 + w)
  rw [prod_succAbove_zero _ (ENNReal.ofReal (Gam m θ S w ^ (1 / (n : ℝ))))
    (fun j hj => (marg_mid h hr hτ j hj w hw').1)] at hlo
  rw [prod_succAbove_zero _ (ENNReal.ofReal (Gam m θ S w ^ (1 / (n : ℝ))))
    (fun j hj => (marg_mid h hr hτ j hj w hw').2)] at hhi
  have hG := Gam_pow h hr hτ w hw'
  have hq : ENNReal.ofReal (Gam m θ S w ^ (1 / (n : ℝ))) ^ n = ENNReal.ofReal (Gam m θ S w) := by
    rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hG.2 _), hG.1]
  rw [hq] at hlo hhi
  exact le_antisymm hhi hlo

/-- M's interim win above `1 + τ` is at most `θ` -/
lemma winM_high (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (tr : TieRule n) (x : ℝ) (hx : 1 + tau R S < x) :
    interimWin (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) 0
        x ≤ ENNReal.ofReal θ := by
  refine (interimWin_le _ tr _ 0 x).trans ?_
  calc ∏ k : Fin n, marginalBidLaw (rivalInstance R m θ n h.hθ.le h.hθ1.le)
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j)))
        ((0 : Suppliers n).succAbove k) (Ici x)
      ≤ ∏ _k : Fin n, ENNReal.ofReal (p θ n) :=
        Finset.prod_le_prod' (fun k _ =>
          marg_high h hr hτ hw _ (Fin.succAbove_ne _ _) x hx)
    _ = ENNReal.ofReal θ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← ENNReal.ofReal_pow (p_pos h).le, p_pow h]

/-- a present rival's interim win on `[1 + w0, 1 + τ]`: upper bound -/
lemma winR_le (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (tr : TieRule n) (i : Suppliers n) (hi : i ≠ 0)
    (w : ℝ) (hw' : w ∈ Icc (w0 R m θ S) (tau R S)) :
    interimWin (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) i
        (1 + w) ≤
      ENNReal.ofReal (A R m θ n S w * (Gam m θ S w ^ (1 / (n : ℝ))) ^ (n - 1)) := by
  have hhi := interimWin_le (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
    (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) i (1 + w)
  rw [prod_succAbove_rival _ (ENNReal.ofReal (Gam m θ S w ^ (1 / (n : ℝ)))) i hi
    (fun j hj _ => (marg_mid h hr hτ j hj w hw').2), marginal_zero h.hθ h.hθ1] at hhi
  have hM : cdfLaw (mCDF R m θ n S) (Ici (1 + w)) = ENNReal.ofReal (A R m θ n S w) := by
    rcases eq_or_lt_of_le hw'.2 with he | hlt
    · rw [he]; exact (mlaw_tau h hr hτ hw).2.1
    · exact (mlaw_Ioi h hr hτ hw w ⟨hw'.1, hlt⟩).2
  have hG := Gam_pow h hr hτ w hw'
  have hA := (A_mem h hr hτ hw w hw').1
  rw [hM, ← ENNReal.ofReal_pow (Real.rpow_nonneg hG.2 _), ← ENNReal.ofReal_mul hA] at hhi
  exact hhi

/-- a present rival's interim win on `[1 + w0, 1 + τ)`: lower bound -/
lemma winR_ge (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (tr : TieRule n) (i : Suppliers n) (hi : i ≠ 0)
    (w : ℝ) (hw' : w ∈ Ico (w0 R m θ S) (tau R S)) :
    ENNReal.ofReal (A R m θ n S w * (Gam m θ S w ^ (1 / (n : ℝ))) ^ (n - 1)) ≤
    interimWin (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) i
        (1 + w) := by
  have hw'' : w ∈ Icc (w0 R m θ S) (tau R S) := ⟨hw'.1, hw'.2.le⟩
  have hlo := interimWin_ge (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
    (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) i (1 + w)
  rw [prod_succAbove_rival _ (ENNReal.ofReal (Gam m θ S w ^ (1 / (n : ℝ)))) i hi
    (fun j hj _ => (marg_mid h hr hτ j hj w hw'').1), marginal_zero h.hθ h.hθ1,
    (mlaw_Ioi h hr hτ hw w hw').1] at hlo
  have hG := Gam_pow h hr hτ w hw''
  have hA := (A_mem h hr hτ hw w hw'').1
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hG.2 _), ← ENNReal.ofReal_mul hA] at hlo
  exact hlo

/-- a present rival's interim win above `1 + τ` is zero -/
lemma winR_high (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (tr : TieRule n) (i : Suppliers n) (hi : i ≠ 0)
    (x : ℝ) (hx : 1 + tau R S < x) :
    interimWin (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) i
        x ≤ ENNReal.ofReal 0 := by
  rw [ENNReal.ofReal_zero]
  refine (interimWin_le _ tr _ i x).trans (le_of_eq ?_)
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := (0 : Suppliers n)) (y := i) (Ne.symm hi)
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  rw [hk, marginal_zero h.hθ h.hθ1]
  refine le_antisymm ?_ (zero_le)
  calc cdfLaw (mCDF R m θ n S) (Ici x) ≤ cdfLaw (mCDF R m θ n S) (Ioi (1 + tau R S)) :=
        measure_mono (fun y hy => lt_of_lt_of_le hx hy)
    _ = 0 := (mlaw_tau h hr hτ hw).2.2

/-- the rival's equilibrium utility identity -/
lemma V_formula (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (w : ℝ) (hw' : w ∈ Icc (w0 R m θ S) (tau R S)) :
    (1 + w - (1 + m)) * (A R m θ n S w * (Gam m θ S w ^ (1 / (n : ℝ))) ^ (n - 1)) * S (1 + w) =
      u m θ S * (w0 R m θ S - m) / w0 R m θ S := by
  have hG := Gam_pow h hr hτ w hw'
  have hgm := Gam_mul_g h hr hτ w hw'
  have hm := h.hm
  have hwm : w - m ≠ 0 := by linarith [hw'.1]
  have hw0 : w0 R m θ S ≠ 0 := by linarith
  have hpow : Gam m θ S w ^ (1 / (n : ℝ)) * (Gam m θ S w ^ (1 / (n : ℝ))) ^ (n - 1) =
      Gam m θ S w := by
    rw [← pow_succ', Nat.sub_add_cancel h.hn, hG.1]
  unfold g at hgm
  unfold A Atil
  rw [show 1 + w - (1 + m) = w - m by ring]
  have : (w - m) * ((w0 R m θ S - m) * w / (w0 R m θ S * (w - m)) *
      Gam m θ S w ^ (1 / (n : ℝ)) * (Gam m θ S w ^ (1 / (n : ℝ))) ^ (n - 1)) * S (1 + w) =
      (w0 R m θ S - m) / w0 R m θ S * (w * S (1 + w) *
        (Gam m θ S w ^ (1 / (n : ℝ)) * (Gam m θ S w ^ (1 / (n : ℝ))) ^ (n - 1))) := by
    field_simp
  rw [this, hpow, hgm]
  ring

/-- M's utility: `u` on `[1 + w0, 1 + τ]`, at most `u` everywhere -/
lemma utilM (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (tr : TieRule n) :
    (∀ w ∈ Icc (w0 R m θ S) (tau R S),
      acceptUtility (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) S 0 1
        (1 + w) = u m θ S) ∧
    (∀ a : ℝ,
      acceptUtility (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) S 0 1
        a ≤ u m θ S) := by
  have hS0 : ∀ b, 0 ≤ S b := fun b => Dev.A1.S_nonneg h.hS b
  have hu := u_pos h hr hτ
  have heq : ∀ w ∈ Icc (w0 R m θ S) (tau R S),
      acceptUtility (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) S 0 1
        (1 + w) = u m θ S := by
    intro w hw'
    rw [util_eq_of_win _ tr _ S 0 1 (1 + w) _ (Gam_pow h hr hτ w hw').2 (winM_mid h hr hτ tr w hw'),
      ← Gam_mul_g h hr hτ w hw']
    unfold g; ring
  refine ⟨heq, fun a => ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w, a = 1 + w := ⟨a - 1, by ring⟩
  rcases lt_or_ge w 0 with h0 | h0
  · exact (util_nonpos2 _ tr _ S hS0 0 1 (1 + w) (by linarith)).trans hu.le
  rcases le_or_gt w (w0 R m θ S) with h1 | h1
  · refine (util_le_one _ tr _ S hS0 0 1 (1 + w) (by linarith)).trans ?_
    have := g_le_u h hr hτ w h1
    unfold g at this
    simpa using this
  rcases le_or_gt w (tau R S) with h2 | h2
  · exact (heq w ⟨h1.le, h2⟩).le
  · refine (util_le_of_win _ tr _ S hS0 0 1 (1 + w) θ h.hθ.le (by linarith)
      (winM_high h hr hτ hw tr (1 + w) (by linarith))).trans ?_
    rw [u_eq_of_w0 h hr hτ hw]
    have := g_le_pi h w
    unfold g at this
    have hθ := h.hθ
    calc (1 + w - 1) * θ * S (1 + w) = θ * (w * S (1 + w)) := by ring
      _ ≤ θ * piS S := mul_le_mul_of_nonneg_left this hθ.le

/-- a present rival's utility: `V` on `[1 + w0, 1 + τ)`, at most `V` everywhere -/
lemma utilR (h : Hyp R m θ n S) (hr : IsRegular R S) (hτ : m < tau R S)
    (hw : m < w0 R m θ S) (tr : TieRule n) (i : Suppliers n) (hi : i ≠ 0) :
    (∀ w ∈ Ico (w0 R m θ S) (tau R S),
      acceptUtility (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) S i
        (1 + m) (1 + w) = u m θ S * (w0 R m θ S - m) / w0 R m θ S) ∧
    (∀ a : ℝ,
      acceptUtility (rivalInstance R m θ n h.hθ.le h.hθ1.le) tr
        (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) S i
        (1 + m) a ≤ u m θ S * (w0 R m θ S - m) / w0 R m θ S) := by
  have hS0 : ∀ b, 0 ≤ S b := fun b => Dev.A1.S_nonneg h.hS b
  have hu := u_pos h hr hτ
  have hm := h.hm
  have hw0 : 0 < w0 R m θ S := by linarith
  have hV : 0 ≤ u m θ S * (w0 R m θ S - m) / w0 R m θ S :=
    div_nonneg (mul_nonneg hu.le (by linarith)) hw0.le
  have hq : ∀ w ∈ Icc (w0 R m θ S) (tau R S),
      0 ≤ A R m θ n S w * (Gam m θ S w ^ (1 / (n : ℝ))) ^ (n - 1) := fun w hw' =>
    mul_nonneg (A_mem h hr hτ hw w hw').1
      (pow_nonneg (Real.rpow_nonneg (Gam_pow h hr hτ w hw').2 _) _)
  refine ⟨fun w hw' => ?_, fun a => ?_⟩
  · have hw'' : w ∈ Icc (w0 R m θ S) (tau R S) := ⟨hw'.1, hw'.2.le⟩
    rw [util_eq_of_win _ tr _ S i (1 + m) (1 + w) _ (hq w hw'')
      (le_antisymm (winR_le h hr hτ hw tr i hi w hw'') (winR_ge h hr hτ hw tr i hi w hw')),
      V_formula h hr hτ hw w hw'']
  obtain ⟨w, rfl⟩ : ∃ w, a = 1 + w := ⟨a - 1, by ring⟩
  rcases lt_or_ge w m with h0 | h0
  · exact (util_nonpos2 _ tr _ S hS0 i (1 + m) (1 + w) (by linarith)).trans hV
  rcases lt_or_ge w (w0 R m θ S) with h1 | h1
  · refine (util_le_one _ tr _ S hS0 i (1 + m) (1 + w) (by linarith)).trans ?_
    have hgu := g_le_u h hr hτ w h1.le
    unfold g at hgu
    have hs := hS0 (1 + w)
    rw [le_div_iff₀ hw0]
    nlinarith [mul_le_mul_of_nonneg_right hgu (le_of_lt (sub_pos.2 hw)),
      mul_nonneg (mul_nonneg hm.le hs) (sub_nonneg.2 h1.le)]
  rcases le_or_gt w (tau R S) with h2 | h2
  · have hw'' : w ∈ Icc (w0 R m θ S) (tau R S) := ⟨h1, h2⟩
    exact (util_le_of_win _ tr _ S hS0 i (1 + m) (1 + w) _ (hq w hw'') (by linarith)
      (winR_le h hr hτ hw tr i hi w hw'')).trans (V_formula h hr hτ hw w hw'').le
  · refine (util_le_of_win _ tr _ S hS0 i (1 + m) (1 + w) 0 le_rfl (by linarith)
      (winR_high h hr hτ hw tr i hi (1 + w) (by linarith))).trans ?_
    simpa using hV

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
/-- case τ > m, w0 > m: M draws from `cdfLaw (mCDF ..)`, present rivals from `cdfLaw (rivalCDF ..)` -/
lemma profile_w0_gt (R m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (n : ℕ) (hn : 1 ≤ n) (S : ℝ → ℝ) (hS : IsAcceptance R S) (τ : TieRule n)
    (hr : IsRegular R S) (hτ : m < tau R S) (hw : m < w0 R m θ S) :
    IsAcceptBNE (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) S ∧
      NoBidTies (rivalInstance R m θ n hθ.le hθ1.le) (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) ∧
      1 + ENNReal.ofReal (rivalHighProbability θ n * Phi m θ (monopolyProfit S 1)) ≤
        acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ (mkProfile n R (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j))) R S := by
  have h : Hyp R m θ n S := ⟨hm, hmR, hθ, hθ1, hn, hS⟩
  have htR := tau_le h hr
  have hMae := mlaw_ae h hr hτ hw
  refine ⟨?_, ?_, ?_⟩
  · refine isAcceptBNE_of hθ hθ1 _ _ S hS τ ?_ ?_ ?_ ?_
    · obtain ⟨hMeq, hMle⟩ := utilM h hr hτ hw τ
      filter_upwards [hMae] with b hb a
      obtain ⟨w, rfl⟩ : ∃ w, b = 1 + w := ⟨b - 1, by ring⟩
      rw [hMeq w ⟨by linarith [hb.1], by linarith [hb.2]⟩]
      exact hMle a
    · intro i hi
      obtain ⟨hReq, hRle⟩ := utilR h hr hτ hw τ i hi
      have hi1 := one_le_val i hi
      have hI : ∀ᵐ b ∂(cdfLaw (rivalCDF R m θ n S (i : ℕ))), b ∈ Iio (1 + tau R S) :=
        mem_ae_iff.2 ((prob_compl_eq_zero_iff measurableSet_Iio).2 (pres_Iio h hr hτ _ hi1 hw))
      filter_upwards [pres_ae h hr hτ _ hi1, hI] with b hb hb' a
      have hb1 : 1 + w0 R m θ S ≤ b := by
        rcases hb with hb | hb
        · exact hb.1
        · exfalso
          have : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hi1
          have hb'' : b < 1 + tau R S := hb'
          linarith
      obtain ⟨w, rfl⟩ : ∃ w, b = 1 + w := ⟨b - 1, by ring⟩
      have hb'' : 1 + w < 1 + tau R S := hb'
      rw [hReq w ⟨by linarith, by linarith⟩]
      exact hRle a
    · filter_upwards [hMae] with b hb
      linarith [hb.1]
    · intro j hj
      filter_upwards [pres_ae h hr hτ j hj] with b hb
      rcases hb with hb | hb
      · linarith [hb.1]
      · have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
  · exact noBidTies_of hθ hθ1 _ _ (fun j hj x hx => pres_singleton h hr hτ j hj x hx)
      (by filter_upwards [hMae] with b hb; linarith [hb.2])
  · unfold Phi
    split_ifs with hπ
    · have hL := socialCost_ge_loss hm hmR hθ hθ1 hn
        (cdfLaw (mCDF R m θ n S)) (fun j => cdfLaw (rivalCDF R m θ n S j)) S hS τ
        (1 + tau R S) (by linarith) (fun j hj => pres_Iio h hr hτ j hj hw)
      rw [(mlaw_tau h hr hτ hw).1] at hL
      refine le_trans ?_ hL
      have hA := A_tau_ge h hr hτ hπ
      have hA0 := (A_mem h hr hτ hw (tau R S) ⟨(w0_mem h hr hτ).1.2, le_rfl⟩).1
      rw [← ENNReal.ofReal_mul hm.le, ← ENNReal.ofReal_mul (mul_nonneg hm.le hA0)]
      refine add_le_add_right (ENNReal.ofReal_le_ofReal ?_) _
      change p θ n * (m * (1 - θ) * (1 - m / (θ * piS S))) ≤ m * A R m θ n S (tau R S) * (1 - θ)
      have h1 : 0 ≤ m * (1 - θ) := mul_nonneg hm.le (by linarith)
      calc p θ n * (m * (1 - θ) * (1 - m / (θ * piS S)))
          = m * (1 - θ) * (p θ n * (1 - m / (θ * piS S))) := by ring
        _ ≤ m * (1 - θ) * A R m θ n S (tau R S) := mul_le_mul_of_nonneg_left hA h1
        _ = m * A R m θ n S (tau R S) * (1 - θ) := by ring
    · rw [mul_zero, ENNReal.ofReal_zero, add_zero]
      exact socialCost_ge_one hm hmR hθ hθ1 S hS τ _

lemma mkProfile_congr (n : ℕ) (R : ℝ) (μ μ' : Measure ℝ) (ν ν' : ℕ → Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [∀ j, IsProbabilityMeasure (ν j)]
    [∀ j, IsProbabilityMeasure (ν' j)] (h1 : μ = μ') (h2 : ν = ν') :
    mkProfile n R μ ν = mkProfile n R μ' ν' := by
  subst h1; subst h2; rfl

lemma not_zero_of_regular {R : ℝ} {S : ℝ → ℝ} (hr : IsRegular R S) : ¬ ZeroCase S := by
  intro hz
  obtain ⟨b, hb, hSb⟩ := hr.1
  rw [hz b hb] at hSb
  exact lt_irrefl _ hSb

/-- Lemma A.2 for the explicit profile -/
lemma explicit_good (R m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (n : ℕ) (hn : 1 ≤ n) (S : ℝ → ℝ) (hS : IsAcceptance R S)
    (hreg : IsRegular R S ∨ ZeroCase S) (τ : TieRule n) :
    IsAcceptBNE (rivalInstance R m θ n hθ.le hθ1.le) τ
        (mkProfile n R (lawM R m θ n S) (lawP R m θ n S)) S ∧
      1 + ENNReal.ofReal (rivalHighProbability θ n * Phi m θ (monopolyProfit S 1)) ≤
        acceptSocialCost (rivalInstance R m θ n hθ.le hθ1.le) τ
          (mkProfile n R (lawM R m θ n S) (lawP R m θ n S)) R S := by
  rcases hreg with hr | hz
  · have hnz := not_zero_of_regular hr
    rcases le_or_gt (tau R S) m with hτ | hτ
    · have e := mkProfile_congr n R (lawM R m θ n S) (Measure.dirac (1 + tau R S))
        (lawP R m θ n S) (fun j => Measure.dirac (R + j))
        (by unfold lawM; rw [if_neg hnz, if_pos hτ])
        (by funext j; unfold lawP; rw [if_pos (Or.inr hτ)])
      rw [e]
      obtain ⟨h1, -, h3⟩ := profile_tau_le R m θ hm hmR hθ hθ1 n hn S hS τ hr hτ
      exact ⟨h1, h3⟩
    · have h : Hyp R m θ n S := ⟨hm, hmR, hθ, hθ1, hn, hS⟩
      have hnτ : ¬ tau R S ≤ m := not_le.mpr hτ
      have hP : lawP R m θ n S = fun j => cdfLaw (rivalCDF R m θ n S j) := by
        funext j; unfold lawP; rw [if_neg (by tauto)]
      rcases eq_or_lt_of_le (w0_mem h hr hτ).1.1 with hw | hw
      · have e := mkProfile_congr n R (lawM R m θ n S) (Measure.dirac (1 + m))
          (lawP R m θ n S) (fun j => cdfLaw (rivalCDF R m θ n S j))
          (by unfold lawM; rw [if_neg hnz, if_neg hnτ, if_pos hw.symm]) hP
        rw [e]
        obtain ⟨h1, -, h3⟩ := profile_w0_eq R m θ hm hmR hθ hθ1 n hn S hS τ hr hτ hw.symm
        exact ⟨h1, h3⟩
      · have e := mkProfile_congr n R (lawM R m θ n S) (cdfLaw (mCDF R m θ n S))
          (lawP R m θ n S) (fun j => cdfLaw (rivalCDF R m θ n S j))
          (by unfold lawM; rw [if_neg hnz, if_neg hnτ, if_neg hw.ne']) hP
        rw [e]
        obtain ⟨h1, -, h3⟩ := profile_w0_gt R m θ hm hmR hθ hθ1 n hn S hS τ hr hτ hw
        exact ⟨h1, h3⟩
  · have e := mkProfile_congr n R (lawM R m θ n S) (Measure.dirac 1)
      (lawP R m θ n S) (fun j => Measure.dirac (R + j))
      (by unfold lawM; rw [if_pos hz])
      (by funext j; unfold lawP; rw [if_pos (Or.inl hz)])
    rw [e]
    obtain ⟨h1, -, h3⟩ := profile_zero R m θ hm hmR hθ hθ1 n hn S hS τ hz
    exact ⟨h1, h3⟩

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
alias explicit_good := ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartX.explicit_good

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
/-! ## Part K: the measurable family over signals -/
/-- the good signals: phantom bounded by `R`, and the acceptance function regular or zero above 1 -/
def GoodSig (M : PhantomMechanism R Sig) (s : Sig) : Prop :=
  M.phantom s (Ioi R) = 0 ∧ (IsRegular R (signalAcceptance M s) ∨ ZeroCase (signalAcceptance M s))

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
/-! Theorem 5.7, Blueprint Part K: the measurable family over signals. -/
/-- for `y ≥ m`, the sublevel sets of `w0` in terms of `g`, `u`, `τ` -/
lemma w0_le_iff {R m θ : ℝ} {n : ℕ} {S : ℝ → ℝ} (h : Hyp R m θ n S) (hr : IsRegular R S)
    (hτ : m < tau R S) (y : ℝ) :
    w0 R m θ S ≤ y ↔ m ≤ y ∧ (tau R S ≤ y ∨ u m θ S ≤ g S y) := by
  obtain ⟨⟨hm0, hwτ⟩, hgw⟩ := w0_mem h hr hτ
  have hm := h.hm
  constructor
  · intro hy
    refine ⟨hm0.trans hy, ?_⟩
    rcases le_or_gt (tau R S) y with h1 | h1
    · exact Or.inl h1
    · right
      rw [← hgw]
      exact g_mono h hr ⟨by linarith, hwτ⟩ ⟨by linarith, h1.le⟩ hy
  · rintro ⟨hmy, h1 | h1⟩
    · exact hwτ.trans h1
    · rcases le_or_gt (tau R S) y with h2 | h2
      · exact hwτ.trans h2
      by_contra hlt
      push Not at hlt
      have h3 := g_le_u h hr hτ y hlt.le
      have heq : g S y = u m θ S := le_antisymm h3 h1
      have h4 : w0 R m θ S ≤ y := csInf_le ⟨m, fun w hw => hw.1.1⟩ ⟨⟨hmy, h2.le⟩, heq⟩
      linarith

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
lemma isAcceptance_of_good (M : PhantomMechanism R Sig) {s : Sig} (hs : GoodSig M s) :
    IsAcceptance R (signalAcceptance M s) :=
  ⟨M.phantom s, inferInstance, hs.1, fun _ => rfl⟩

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
alias isAcceptance_of_good := ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK.isAcceptance_of_good

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
/-- a measurable set of good signals of full measure -/
lemma exists_goodSet (M : PhantomMechanism R Sig) (hreg : IsRegularMechanism M) :
    ∃ G : Set Sig, MeasurableSet G ∧ (∀ s ∈ G, GoodSig M s) ∧ M.signalLaw Gᶜ = 0 := by
  have h : ∀ᵐ s ∂M.signalLaw, GoodSig M s := by
    filter_upwards [M.bounded, hreg] with s h1 h2 using ⟨h1, h2⟩
  refine ⟨(toMeasurable M.signalLaw {s | ¬ GoodSig M s})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · intro s hs
    by_contra hc
    exact hs (subset_toMeasurable _ _ hc)
  · rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 h

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
alias exists_goodSet := ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK.exists_goodSet

/-- the raw bid map of bidder `i` at (signal, cost) -/
noncomputable def rawBid (M : PhantomMechanism R Sig) (G : Set Sig) (m θ : ℝ) (n : ℕ)
    (i : Suppliers n) (x : Sig × ℝ) : Measure ℝ := by
  classical
  exact if x.1 ∈ G then
    (mkProfile n R (lawM R m θ n (signalAcceptance M x.1))
      (lawP R m θ n (signalAcceptance M x.1))).bid i x.2
  else Measure.dirac 0

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
lemma zeroCase_iff (M : PhantomMechanism R Sig) (s : Sig) :
    ZeroCase (signalAcceptance M s) ↔
      ∀ q : ℚ, 1 < (q : ℝ) → signalAcceptance M s q = 0 := by
  constructor
  · intro h q hq; exact h q hq
  · intro h b hb
    obtain ⟨q, h1q, hqb⟩ := exists_rat_btwn hb
    have h0 := h q h1q
    apply le_antisymm _ ENNReal.toReal_nonneg
    rw [← h0]
    unfold signalAcceptance
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ici_subset_Ici.2 hqb.le))

lemma measurableSet_zero (M : PhantomMechanism R Sig) :
    MeasurableSet {s | ZeroCase (signalAcceptance M s)} := by
  have : {s | ZeroCase (signalAcceptance M s)} =
      ⋂ q : ℚ, {s | 1 < (q : ℝ) → signalAcceptance M s q = 0} := by
    ext s; simp only [mem_ofPred_eq, mem_iInter, zeroCase_iff]
  rw [this]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : 1 < (q : ℝ)
  · simp only [hq, true_implies]
    exact M5B.meas_Sacc M q (measurableSet_singleton 0)
  · simp [hq]

/-- the monopoly margin, measurably -/
noncomputable def Tf (M : PhantomMechanism R Sig) (s : Sig) : ℝ := M5B.Bs M 1 s - 1

lemma measurable_Tf (M : PhantomMechanism R Sig) : Measurable (Tf M) :=
  (M5B.measurable_Bs M 1).sub_const 1

lemma Tf_eq (M : PhantomMechanism R Sig) {s : Sig} (hs : M.phantom s (Ioi R) = 0) :
    Tf M s = tau R (signalAcceptance M s) := by
  simp [Tf, M5B.Bs, hs, tau]

lemma measurable_g (M : PhantomMechanism R Sig) (y : ℝ) :
    Measurable fun s => g (signalAcceptance M s) y :=
  (M5B.meas_Sacc M (1 + y)).const_mul y

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
lemma rawBid_isProb (M : PhantomMechanism R Sig) (G : Set Sig) (m θ : ℝ) (n : ℕ)
    (i : Suppliers n) (x : Sig × ℝ) : IsProbabilityMeasure (rawBid M G m θ n i x) := by
  unfold rawBid; split_ifs <;> infer_instance

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
lemma rival_inCostInterval (R m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (n : ℕ) : InCostInterval (rivalInstance R m θ n hθ.le hθ1.le) 1 R := by
  intro i
  simp only [rivalInstance]
  split_ifs
  · intro x hx
    simp only [mem_singleton_iff] at hx
    subst hx
    exact ⟨le_rfl, by linarith⟩
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, le_rfl⟩

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
/-! ## Part A: analysis and assembly -/

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
/-- the segment bound on Φ_{m,1/2} with m = (X-1)/4 -/
lemma phi_lower (X π : ℝ) (hX : 1 < X) (hπ : 0 ≤ π) :
    chi * (X - 1) - 2 * chi * max (X - 1 - π) 0 ≤ Phi ((X - 1) / 4) (1 / 2) π := by
  unfold Phi chi
  have hY : 0 < X - 1 := by linarith
  split_ifs with h
  · have hπ' : 0 < π := by nlinarith
    have e : (X - 1) / 4 * (1 - 1 / 2) * (1 - (X - 1) / 4 / (1 / 2 * π)) =
        (X - 1) * (2 * π - (X - 1)) / (16 * π) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    rcases le_total (X - 1 - π) 0 with h1 | h1
    · rw [max_eq_right h1]; nlinarith
    · rw [max_eq_left h1]; nlinarith
  · push Not at h
    rcases le_total (X - 1 - π) 0 with h1 | h1
    · rw [max_eq_right h1]; nlinarith
    · rw [max_eq_left h1]; nlinarith

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
lemma second_ineq (R : ℝ) (hR : 1 < R) : Real.sqrt R / 8 + 15 / 32 ≤ Lall R := by
  unfold Lall chi
  have h1 : Real.sqrt R / 4 ≤ Real.sqrt ((1 - 1 / 16) ^ 2 + 1 / 16 * R) := by
    have : Real.sqrt R / 4 = Real.sqrt (R / 16) := by
      rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 16)]
      rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
    apply Real.sqrt_le_sqrt
    nlinarith
  linarith

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
alias second_ineq := ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA.second_ineq

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
/-- the final arithmetic of the paper's proof -/
lemma Lall_le (R L : ℝ) (hR : 1 < R) (hL : 1 ≤ L)
    (h : L < R / 2 → chi * R / (4 * L) - chi + chi * L / R ≤ L - 1) : Lall R ≤ L := by
  unfold Lall
  have hc : chi = 1 / 16 := rfl
  set D := (1 - chi) ^ 2 + chi * R with hD
  have hD0 : 0 ≤ D := by rw [hD, hc]; positivity
  have hs := Real.sq_sqrt hD0
  have hs0 := Real.sqrt_nonneg D
  by_cases hLR : L < R / 2
  · have h1 := h hLR
    have hL0 : 0 < L := by linarith
    -- L (L - 1 + chi) ≥ chi R / 4
    have h2 : chi * R / 4 ≤ L * (L - 1 + chi) := by
      have h3 : chi * R / (4 * L) ≤ L - 1 + chi := by
        have : 0 ≤ chi * L / R := by rw [hc]; positivity
        linarith
      rw [div_le_iff₀ (by positivity)] at h3
      nlinarith
    by_contra hcon
    push Not at hcon
    set s := Real.sqrt D
    -- s > 2L - 1 + chi ≥ 0
    have h4 : 2 * L - (1 - chi) < s := by linarith
    have h5 : 0 ≤ 2 * L - (1 - chi) := by rw [hc]; linarith
    have h6 : (2 * L - (1 - chi)) ^ 2 < s ^ 2 := by nlinarith
    rw [hs, hD] at h6
    nlinarith
  · push Not at hLR
    by_cases hR4 : R ≤ 4
    · have : Real.sqrt D ≤ 1 + chi := by
        rw [Real.sqrt_le_left (by rw [hc]; norm_num)]
        rw [hD, hc]; nlinarith
      linarith
    · push Not at hR4
      have : Real.sqrt D ≤ R - 1 + chi := by
        rw [Real.sqrt_le_left (by rw [hc]; linarith)]
        rw [hD, hc]; nlinarith
      linarith

/-- telescoped key inequality -/
lemma tele (R : ℝ) (S : ℝ → ℝ) (hS : IsAcceptance R S) (Δ : ℝ) (hΔ : 0 < Δ) (i : ℕ) :
    ∑ j ∈ Finset.range i, Δ * sigma R S (1 + ((j : ℝ) + 1) * Δ) ≤
      monopolyProfit S 1 - monopolyProfit S (1 + (i : ℝ) * Δ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have hk := A1.key hS (c := 1 + (i : ℝ) * Δ) (c' := 1 + ((i : ℝ) + 1) * Δ) (by nlinarith)
    have e : 1 + ((i : ℝ) + 1) * Δ - (1 + (i : ℝ) * Δ) = Δ := by ring
    rw [e] at hk
    push_cast
    linarith

/-- the lower Riemann sum form of Lemma A.1's argument -/
lemma riemann (R : ℝ) (hR : 1 ≤ R) (S : ℝ → ℝ) (hS : IsAcceptance R S) (X : ℝ) (hX : 1 ≤ X)
    (k : ℕ) (hk : 1 ≤ k) :
    max (X - 1 - monopolyProfit S 1) 0 ≤
      ∑ j ∈ Finset.range k, (X - 1) / k * (1 - sigma R S (1 + (j + 1) * (X - 1) / k)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hnn : 0 ≤ ∑ j ∈ Finset.range k, (X - 1) / k * (1 - sigma R S (1 + (j + 1) * (X - 1) / k)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (by linarith) hk0.le)
      (by linarith [A1.sigma_le_one hS (1 + (j + 1) * (X - 1) / k)])
  refine max_le ?_ hnn
  rcases hX.eq_or_lt with hX1 | hX1
  · subst hX1; simp only [sub_self]; linarith [A1.P_nonneg hS 1]
  set Δ := (X - 1) / k with hΔ
  have hΔ0 : 0 < Δ := div_pos (by linarith) hk0
  have ht := tele R S hS Δ hΔ0 k
  have e1 : ∀ j : ℕ, (1 + ((j : ℝ) + 1) * (X - 1) / k) = 1 + ((j : ℝ) + 1) * Δ := by
    intro j; rw [hΔ]; ring
  simp_rw [e1]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have e2 : ∑ j ∈ Finset.range k, Δ * 1 = X - 1 := by
    simp [hΔ]; field_simp
  rw [e2]
  have := A1.P_nonneg hS (1 + (k : ℝ) * Δ)
  linarith

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
/-! ## General survival functions (no bound on the phantom) -/
/-- survival function of an arbitrary probability law (support not necessarily bounded) -/
def IsSurv (S : ℝ → ℝ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ b, S b = (μ (Ici b)).toReal

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {S : ℝ → ℝ}
lemma surv_nonneg (hS : IsSurv S) (b : ℝ) : 0 ≤ S b := by
  obtain ⟨μ, _, h⟩ := hS
  rw [h]; exact ENNReal.toReal_nonneg

lemma surv_le_one (hS : IsSurv S) (b : ℝ) : S b ≤ 1 := by
  obtain ⟨μ, hp, h⟩ := hS
  rw [h]
  have : μ (Set.Ici b) ≤ 1 := prob_le_one
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

lemma surv_anti (hS : IsSurv S) : Antitone S := by
  intro b b' hbb'
  obtain ⟨μ, hp, h⟩ := hS
  rw [h, h]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ici_subset_Ici.2 hbb'))

lemma surv_leftcont (hS : IsSurv S) (b ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ b', b - δ < b' → S b' ≤ S b + ε := by
  obtain ⟨μ, hp, h⟩ := hS
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
      push Not at hlt
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

lemma surv_usc (hS : IsSurv S) {c : ℝ} {b : ℕ → ℝ} {b0 t : ℝ}
    (hb : Tendsto b atTop (𝓝 b0)) (hcb : ∀ k, c ≤ b k)
    (ht : Tendsto (fun k => (b k - c) * S (b k)) atTop (𝓝 t)) :
    t ≤ (b0 - c) * S b0 := by
  have key : ∀ ε > 0, t ≤ (b0 - c) * (S b0 + ε) := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := surv_leftcont hS b0 ε hε
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

lemma surv_rat_approx (hS : IsSurv S) (c : ℝ) {a b : ℝ} (hab : a < b) (hca : c ≤ a)
    (ε : ℝ) (hε : 0 < ε) : ∃ q : ℚ, a < q ∧ (q : ℝ) < b ∧ M5A.phi S c b - ε < M5A.phi S c q := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max a (b - ε) < b from max_lt hab (by linarith))
  have hqa : a < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hqb : b - ε < q := lt_of_le_of_lt (le_max_right _ _) hq1
  refine ⟨q, hqa, hq2, ?_⟩
  unfold M5A.phi
  have h1 := surv_anti hS hq2.le
  have h2 := surv_le_one hS b
  have h3 := surv_nonneg hS b
  nlinarith

lemma phi_pos_gt (hS : IsSurv S) {c b : ℝ} (h : 0 < M5A.phi S c b) : c < b := by
  by_contra hb; push Not at hb
  have : M5A.phi S c b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (surv_nonneg hS b)
  linarith

/-- boundedness of the profit, tested on rationals -/
def RatBdd (S : ℝ → ℝ) (c : ℝ) : Prop := ∃ N : ℕ, ∀ q : ℚ, M5A.phi S c q ≤ N

lemma bdd_of_ratBdd (hS : IsSurv S) (c : ℝ) (h : RatBdd S c) :
    BddAbove (Set.range fun b : ℝ => (b - c) * S b) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, ?_⟩
  rintro _ ⟨b, rfl⟩
  by_cases hbc : b ≤ c
  · have : (b - c) * S b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (surv_nonneg hS b)
    have : (0 : ℝ) ≤ N := by positivity
    linarith
  · push Not at hbc
    obtain ⟨q, -, -, hq⟩ := surv_rat_approx hS c (a := c) (b := b) hbc le_rfl 1 one_pos
    have := hN q
    unfold M5A.phi at hq this
    show (b - c) * S b ≤ N + 1
    linarith

lemma ratBdd_of_bdd (c : ℝ) (h : BddAbove (Set.range fun b : ℝ => (b - c) * S b)) :
    RatBdd S c := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨N, hN⟩ := exists_nat_ge B
  exact ⟨N, fun q => (hB ⟨(q : ℝ), rfl⟩).trans hN⟩

lemma P_eq_gen (hS : IsSurv S) (c : ℝ) (h : RatBdd S c) :
    monopolyProfit S c = ⨆ q : ℚ, M5A.phi S c q := by
  have hb := bdd_of_ratBdd hS c h
  have hbr : BddAbove (Set.range fun q : ℚ => M5A.phi S c q) := by
    obtain ⟨B, hB⟩ := hb
    exact ⟨B, by rintro _ ⟨q, rfl⟩; exact hB ⟨(q : ℝ), rfl⟩⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨b, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hbc : b ≤ c
    · obtain ⟨q, hq⟩ := exists_rat_gt c
      have h1 : M5A.phi S c b ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (surv_nonneg hS b)
      have h2 : 0 ≤ M5A.phi S c q := mul_nonneg (by linarith) (surv_nonneg hS _)
      have := le_ciSup hbr q
      show M5A.phi S c b ≤ _
      linarith
    · push Not at hbc
      obtain ⟨q, -, -, hq⟩ := surv_rat_approx hS c hbc le_rfl ε hε
      have := le_ciSup hbr q
      show M5A.phi S c b ≤ _
      linarith
  · apply ciSup_le
    intro q
    exact le_csSup hb ⟨(q : ℝ), rfl⟩

lemma P_eq_zero_gen (c : ℝ) (h : ¬ RatBdd S c) : monopolyProfit S c = 0 := by
  unfold monopolyProfit
  exact Real.sSup_of_not_bddAbove fun hb => h (ratBdd_of_bdd c hb)

lemma P_nonneg_gen (hS : IsSurv S) (c : ℝ) : 0 ≤ monopolyProfit S c := by
  by_cases h : RatBdd S c
  · have := le_csSup (bdd_of_ratBdd hS c h) ⟨c, rfl⟩
    simpa [monopolyProfit] using this
  · rw [P_eq_zero_gen c h]

lemma le_P_gen (hS : IsSurv S) (c : ℝ) (hP : monopolyProfit S c ≠ 0) (b : ℝ) :
    M5A.phi S c b ≤ monopolyProfit S c := by
  have h : RatBdd S c := by
    by_contra h; exact hP (P_eq_zero_gen c h)
  exact le_csSup (bdd_of_ratBdd hS c h) ⟨b, rfl⟩

/-- the maximizers in a compact window, tested on rationals -/
lemma Q_iff (hS : IsSurv S) (c P : ℝ) (hP : 0 < P) (hle : ∀ b, M5A.phi S c b ≤ P)
    {a a' : ℝ} (haa : a < a') :
    (∃ b ∈ Icc a a', M5A.phi S c b = P) ↔
      P ≤ max (M5A.phi S c a)
        (⨆ q : {q : ℚ // a < (q : ℝ) ∧ (q : ℝ) < a'}, M5A.phi S c (q : ℚ)) := by
  have hbdd : BddAbove (Set.range fun q : {q : ℚ // a < (q : ℝ) ∧ (q : ℝ) < a'} =>
      M5A.phi S c (q : ℚ)) := ⟨P, by rintro _ ⟨q, rfl⟩; exact hle _⟩
  have hne : Nonempty {q : ℚ // a < (q : ℝ) ∧ (q : ℝ) < a'} := by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn haa
    exact ⟨⟨q, h1, h2⟩⟩
  constructor
  · rintro ⟨b, hb, hbP⟩
    rcases hb.1.eq_or_lt with h | h
    · subst h; rw [hbP]; exact le_max_left _ _
    refine le_max_of_le_right (le_of_forall_pos_le_add fun ε hε => ?_)
    have hcb : c < b := phi_pos_gt hS (by rw [hbP]; exact hP)
    obtain ⟨q, hq1, hq2, hq⟩ := surv_rat_approx hS c (a := max a c) (b := b)
      (max_lt h hcb) (le_max_right _ _) ε hε
    have := le_ciSup hbdd ⟨q, lt_of_le_of_lt (le_max_left _ _) hq1, lt_of_lt_of_le hq2 hb.2⟩
    simp only at this
    linarith
  · intro h
    by_cases h1 : P ≤ M5A.phi S c a
    · exact ⟨a, left_mem_Icc.2 haa.le, le_antisymm (hle a) h1⟩
    push Not at h1
    have h2 : P ≤ ⨆ q : {q : ℚ // a < (q : ℝ) ∧ (q : ℝ) < a'}, M5A.phi S c (q : ℚ) := by
      rcases le_max_iff.1 h with h' | h'
      · exact absurd h' (not_le.2 h1)
      · exact h'
    have happ : ∀ k : ℕ, ∃ q : {q : ℚ // a < (q : ℝ) ∧ (q : ℝ) < a'},
        P - P / 2 * (1 / ((k : ℝ) + 1)) < M5A.phi S c (q : ℚ) := by
      intro k
      have hδ : 0 < P / 2 * (1 / ((k : ℝ) + 1)) := by positivity
      exact exists_lt_of_lt_ciSup (by linarith)
    choose qs hqs using happ
    let b : ℕ → ℝ := fun k => ((qs k : ℚ) : ℝ)
    have hpos : ∀ k, 0 < M5A.phi S c (b k) := by
      intro k
      have h1 : P / 2 * (1 / ((k : ℝ) + 1)) ≤ P / 2 := by
        have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ k := by positivity
          linarith
        nlinarith
      have := hqs k
      show 0 < M5A.phi S c ((qs k : ℚ) : ℝ)
      linarith
    have hmem : ∀ k, b k ∈ Set.Icc a a' := fun k => ⟨(qs k).2.1.le, (qs k).2.2.le⟩
    obtain ⟨x, hx, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
    have hf : Tendsto (fun k => (b k - c) * S (b k)) atTop (𝓝 P) := by
      have hlow : Tendsto (fun k : ℕ => P - P / 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 P) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (P / 2)
        simpa using (tendsto_const_nhds (x := P)).sub this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
        (fun k => (hqs k).le) (fun k => hle (b k))
    have := surv_usc hS (c := c) (b := b ∘ φ) hlim
      (fun k => (phi_pos_gt hS (hpos (φ k))).le) (hf.comp hφ.tendsto_atTop)
    exact ⟨x, hx, le_antisymm (hle x) this⟩

lemma max_mem_gen (hS : IsSurv S) (c P : ℝ) (hP : 0 < P) (hle : ∀ b, M5A.phi S c b ≤ P)
    (hne : {b | M5A.phi S c b = P}.Nonempty) (hbdd : BddAbove {b | M5A.phi S c b = P}) :
    M5A.phi S c (sSup {b | M5A.phi S c b = P}) = P := by
  obtain ⟨u, -, hu, humem⟩ := exists_seq_tendsto_sSup hne hbdd
  have hcu : ∀ k, c ≤ u k := fun k =>
    (phi_pos_gt hS (by rw [show M5A.phi S c (u k) = P from humem k]; exact hP)).le
  have hconst : Tendsto (fun k => (u k - c) * S (u k)) atTop (𝓝 P) := by
    have : (fun k => (u k - c) * S (u k)) = fun _ => P := funext fun k => humem k
    rw [this]; exact tendsto_const_nhds
  exact le_antisymm (hle _) (surv_usc hS hu hcu hconst)

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
lemma isSurv_sig (M : PhantomMechanism R Sig) (s : Sig) : IsSurv (signalAcceptance M s) :=
  ⟨M.phantom s, inferInstance, fun _ => rfl⟩

lemma meas_S (M : PhantomMechanism R Sig) (b : ℝ) :
    Measurable fun s => signalAcceptance M s b :=
  (Kernel.measurable_coe M.phantom measurableSet_Ici).ennreal_toReal

lemma meas_phi' (M : PhantomMechanism R Sig) (c b : ℝ) :
    Measurable fun s => M5A.phi (signalAcceptance M s) c b :=
  (meas_S M b).const_mul (b - c)

lemma meas_S_joint (M : PhantomMechanism R Sig) :
    Measurable fun p : Sig × ℝ => signalAcceptance M p.1 p.2 := by
  have ht : MeasurableSet {p : (Sig × ℝ) × ℝ | p.1.2 ≤ p.2} :=
    measurableSet_le measurable_fst.snd measurable_snd
  have := (Kernel.measurable_kernel_prodMk_left
    (κ := M.phantom.comap Prod.fst measurable_fst) ht).ennreal_toReal
  convert this using 2 with p
  rw [Kernel.comap_apply]
  rfl

lemma measurable_P_gen (M : PhantomMechanism R Sig) (c : ℝ) :
    Measurable fun s => monopolyProfit (signalAcceptance M s) c := by
  classical
  have hA : MeasurableSet {s | RatBdd (signalAcceptance M s) c} := by
    have : {s | RatBdd (signalAcceptance M s) c} =
        ⋃ N : ℕ, ⋂ q : ℚ, {s | M5A.phi (signalAcceptance M s) c q ≤ N} := by
      ext s; simp [RatBdd]
    rw [this]
    exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun q =>
      measurableSet_le (meas_phi' M c q) measurable_const
  have e : (fun s => monopolyProfit (signalAcceptance M s) c) = fun s =>
      if RatBdd (signalAcceptance M s) c then ⨆ q : ℚ, M5A.phi (signalAcceptance M s) c q
      else 0 := by
    funext s
    split_ifs with h
    · exact P_eq_gen (isSurv_sig M s) c h
    · exact P_eq_zero_gen c h
  rw [e]
  exact Measurable.ite hA (Measurable.iSup fun q => meas_phi' M c q) measurable_const

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
lemma measurable_pi {R : ℝ} {Sig : Type u} [MeasurableSpace Sig] (M : PhantomMechanism R Sig) :
    Measurable fun s => monopolyProfit (signalAcceptance M s) 1 :=
  measurable_P_gen M 1

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
lemma measurable_bid_gen (M : PhantomMechanism R Sig) (c : ℝ) :
    Measurable fun s => monopolyBid R (signalAcceptance M s) c := by
  classical
  set Pf : Sig → ℝ := fun s => monopolyProfit (signalAcceptance M s) c with hPf
  have hPm : Measurable Pf := measurable_P_gen M c
  set E : Sig → Set ℝ := fun s => {b | M5A.phi (signalAcceptance M s) c b = Pf s} with hE
  let Qs : ℝ → ℝ → Set Sig := fun a a' => {s | Pf s ≤ max (M5A.phi (signalAcceptance M s) c a)
        (⨆ q : {q : ℚ // a < (q : ℝ) ∧ (q : ℝ) < a'}, M5A.phi (signalAcceptance M s) c (q : ℚ))}
  have hQm : ∀ a a', MeasurableSet (Qs a a') := fun a a' =>
    measurableSet_le hPm ((meas_phi' M c a).max (Measurable.iSup fun q => meas_phi' M c _))
  have hQ : ∀ s, Pf s ≠ 0 → ∀ a a', a < a' →
      (s ∈ Qs a a' ↔ ∃ b ∈ Icc a a', b ∈ E s) := by
    intro s hs a a' haa
    exact (Q_iff (isSurv_sig M s) c (Pf s)
      (lt_of_le_of_ne (P_nonneg_gen (isSurv_sig M s) c) (Ne.symm hs))
      (le_P_gen (isSurv_sig M s) c hs) haa).symm
  obtain ⟨Ne', hNem, hNe⟩ : ∃ A : Set Sig, MeasurableSet A ∧
      ∀ s, Pf s ≠ 0 → (s ∈ A ↔ (E s).Nonempty) := by
    refine ⟨⋃ N : ℕ, Qs (-((N : ℝ) + 1)) ((N : ℝ) + 1),
      MeasurableSet.iUnion fun N => hQm _ _, fun s hs => ?_⟩
    rw [mem_iUnion]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨b, -, hb⟩ := (hQ s hs _ _ (by linarith)).1 hN
      exact ⟨b, hb⟩
    · rintro ⟨b, hb⟩
      obtain ⟨N, hN⟩ := exists_nat_ge |b|
      refine ⟨N, (hQ s hs _ _ (by linarith)).2 ⟨b, ⟨?_, ?_⟩, hb⟩⟩
      · linarith [neg_abs_le b]
      · linarith [le_abs_self b]
  obtain ⟨Bd', hBdm, hBd⟩ : ∃ A : Set Sig, MeasurableSet A ∧
      ∀ s, Pf s ≠ 0 → (s ∈ A ↔ BddAbove (E s)) := by
    refine ⟨⋃ N : ℕ, ⋂ K : ℕ, (Qs N (N + K + 1))ᶜ,
      MeasurableSet.iUnion fun N => MeasurableSet.iInter fun K => (hQm _ _).compl,
      fun s hs => ?_⟩
    simp only [mem_iUnion, mem_iInter, mem_compl_iff]
    constructor
    · rintro ⟨N, hN⟩
      refine ⟨N, fun b hb => ?_⟩
      by_contra hlt; push Not at hlt
      obtain ⟨K, hK⟩ := exists_nat_ge (b - N)
      exact hN K ((hQ s hs _ _ (by linarith)).2 ⟨b, ⟨hlt.le, by linarith⟩, hb⟩)
    · rintro ⟨B, hB⟩
      obtain ⟨N, hN⟩ := exists_nat_gt B
      refine ⟨N, fun K hK => ?_⟩
      obtain ⟨b, hb, hbE⟩ := (hQ s hs _ _ (by linarith)).1 hK
      have := hB hbE
      linarith [hb.1]
  obtain ⟨Ge', hGem, hGe⟩ : ∃ A : ℝ → Set Sig, (∀ y, MeasurableSet (A y)) ∧
      ∀ y s, Pf s ≠ 0 → (s ∈ A y ↔ ∃ b ∈ E s, y ≤ b) := by
    refine ⟨fun y => ⋃ K : ℕ, Qs y (y + K + 1),
      fun y => MeasurableSet.iUnion fun K => hQm _ _, fun y s hs => ?_⟩
    simp only [mem_iUnion]
    constructor
    · rintro ⟨K, hK⟩
      obtain ⟨b, hb, hbE⟩ := (hQ s hs _ _ (by linarith)).1 hK
      exact ⟨b, hbE, hb.1⟩
    · rintro ⟨b, hbE, hb⟩
      obtain ⟨K, hK⟩ := exists_nat_ge (b - y)
      exact ⟨K, (hQ s hs _ _ (by linarith)).2 ⟨b, ⟨hb, by linarith⟩, hbE⟩⟩
  apply measurable_of_Ici
  intro y
  have e : (fun s => monopolyBid R (signalAcceptance M s) c) ⁻¹' Ici y =
      ({s | Pf s = 0} ∩ {_s | y ≤ R + 1}) ∪
        ({s | Pf s = 0}ᶜ ∩ ((Ne' ∩ Bd' ∩ Ge' y) ∪ ((Ne' ∩ Bd')ᶜ ∩ {_s | y ≤ 0}))) := by
    ext s
    by_cases hs : Pf s = 0
    · have h0 : monopolyProfit (signalAcceptance M s) c = 0 := hs
      simp [monopolyBid, h0, hs]
    · have hs' : monopolyProfit (signalAcceptance M s) c ≠ 0 := hs
      have hb : monopolyBid R (signalAcceptance M s) c = sSup (E s) := by
        unfold monopolyBid; rw [if_neg hs']; rfl
      simp only [mem_preimage, mem_Ici, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff,
        hs, false_and, false_or, not_false_eq_true, true_and, hb]
      rw [hNe s hs, hBd s hs, hGe y s hs]
      have hP : 0 < Pf s := lt_of_le_of_ne (P_nonneg_gen (isSurv_sig M s) c) (Ne.symm hs)
      by_cases hK : (E s).Nonempty ∧ BddAbove (E s)
      · have hmem : sSup (E s) ∈ E s :=
          max_mem_gen (isSurv_sig M s) c (Pf s) hP (le_P_gen (isSurv_sig M s) c hs) hK.1 hK.2
        simp only [hK, and_self, true_and, not_true_eq_false, false_and, or_false]
        constructor
        · intro h; exact ⟨_, hmem, h⟩
        · rintro ⟨b, hbE, hyb⟩; exact hyb.trans (le_csSup hK.2 hbE)
      · have h0 : sSup (E s) = 0 := by
          by_cases hne : (E s).Nonempty
          · have : ¬ BddAbove (E s) := fun h => hK ⟨hne, h⟩
            exact Real.sSup_of_not_bddAbove this
          · rw [Set.not_nonempty_iff_eq_empty.1 hne]; exact Real.sSup_empty
        rw [h0]
        simp [hK]
  rw [e]
  refine MeasurableSet.union ((measurableSet_eq_fun hPm measurable_const).inter
    (MeasurableSet.const _)) ((measurableSet_eq_fun hPm measurable_const).compl.inter ?_)
  exact ((hNem.inter hBdm).inter (hGem y)).union ((hNem.inter hBdm).compl.inter
    (MeasurableSet.const _))

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
lemma measurable_sigma {R : ℝ} {Sig : Type u} [MeasurableSpace Sig] (M : PhantomMechanism R Sig)
    (t : ℝ) : Measurable fun s => sigma R (signalAcceptance M s) t := by
  classical
  have hb := measurable_bid_gen M t
  have hj := (meas_S_joint M).comp (measurable_id.prodMk hb)
  unfold sigma
  exact Measurable.ite (measurableSet_eq_fun (measurable_P_gen M t) measurable_const)
    measurable_const hj

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u

alias measurable_pi := ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA.measurable_pi

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
lemma measurable_u (M : PhantomMechanism R Sig) (m θ : ℝ) :
    Measurable fun s => u m θ (signalAcceptance M s) :=
  (measurable_g M m).max ((T57.measurable_pi M).const_mul θ)

/-- the region where the interior construction applies -/
def Reg (M : PhantomMechanism R Sig) (Gs : Set Sig) (m : ℝ) : Set Sig :=
  Gs ∩ {s | ¬ ZeroCase (signalAcceptance M s)} ∩ {s | m < Tf M s}

lemma measurableSet_Reg (M : PhantomMechanism R Sig) (Gs : Set Sig) (hG : MeasurableSet Gs)
    (m : ℝ) : MeasurableSet (Reg M Gs m) :=
  (hG.inter (measurableSet_zero M).compl).inter (measurableSet_lt measurable_const (measurable_Tf M))

lemma reg_facts (M : PhantomMechanism R Sig) (Gs : Set Sig) (hgood : ∀ s ∈ Gs, GoodSig M s)
    (m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n)
    {s : Sig} (hs : s ∈ Reg M Gs m) :
    Hyp R m θ n (signalAcceptance M s) ∧ IsRegular R (signalAcceptance M s) ∧
      Tf M s = tau R (signalAcceptance M s) ∧ m < tau R (signalAcceptance M s) := by
  obtain ⟨⟨hsG, hz⟩, hτ⟩ := hs
  have hgs := hgood s hsG
  have hT := Tf_eq M hgs.1
  refine ⟨⟨hm, hmR, hθ, hθ1, hn, isAcceptance_of_good M hgs⟩, ?_, hT, hT ▸ hτ⟩
  rcases hgs.2 with h | h
  · exact h
  · exact absurd h hz

/-- `w0`, measurably -/
noncomputable def Wf (M : PhantomMechanism R Sig) (Gs : Set Sig) (m θ : ℝ) (s : Sig) : ℝ := by
  classical
  exact if s ∈ Reg M Gs m then w0 R m θ (signalAcceptance M s) else m

lemma measurable_Wf (M : PhantomMechanism R Sig) (Gs : Set Sig) (hG : MeasurableSet Gs)
    (hgood : ∀ s ∈ Gs, GoodSig M s)
    (m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1) :
    Measurable (Wf M Gs m θ) := by
  apply measurable_of_Iic
  intro y
  have hR := measurableSet_Reg M Gs hG m
  have e : Wf M Gs m θ ⁻¹' Iic y =
      (Reg M Gs m ∩ ({_s | m ≤ y} ∩ ({s | Tf M s ≤ y} ∪
        {s | u m θ (signalAcceptance M s) ≤ g (signalAcceptance M s) y}))) ∪
      ((Reg M Gs m)ᶜ ∩ {_s | m ≤ y}) := by
    ext s
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
    by_cases hs : s ∈ Reg M Gs m
    · obtain ⟨h, hr, hT, hτ⟩ := reg_facts M Gs hgood m θ hm hmR hθ hθ1 1 le_rfl hs
      simp only [Wf, hs, true_and, not_true_eq_false, false_and, or_false, hT]
      exact w0_le_iff h hr hτ y
    · simp [Wf, hs]
  rw [e]
  exact (hR.inter ((MeasurableSet.const _).inter ((measurableSet_le (measurable_Tf M)
    measurable_const).union (measurableSet_le (measurable_u M m θ) (measurable_g M y))))).union
    (hR.compl.inter (MeasurableSet.const _))

lemma Wf_eq (M : PhantomMechanism R Sig) (Gs : Set Sig) (m θ : ℝ) {s : Sig}
    (hs : s ∈ Reg M Gs m) : Wf M Gs m θ s = w0 R m θ (signalAcceptance M s) := by
  simp [Wf, hs]

/-- probability-valued maps are measurable once their values on `Iic x` are -/
lemma measurable_of_Iic_values {μ : Sig → Measure ℝ} [∀ s, IsProbabilityMeasure (μ s)]
    (h : ∀ x : ℝ, Measurable fun s => μ s (Iic x)) : Measurable μ :=
  .measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic <| by
    rintro _ ⟨x, rfl⟩
    exact h x

/-- the interior part of M's law -/
noncomputable def HM (M : PhantomMechanism R Sig) (Gs : Set Sig) (m θ : ℝ) (n : ℕ) (s : Sig) :
    Measure ℝ := by
  classical
  exact if s ∈ Reg M Gs m ∧ Wf M Gs m θ s ≠ m then cdfLaw (mCDF R m θ n (signalAcceptance M s))
    else Measure.dirac 0

instance HM_isProb (M : PhantomMechanism R Sig) (Gs : Set Sig) (m θ : ℝ) (n : ℕ) (s : Sig) :
    IsProbabilityMeasure (HM M Gs m θ n s) := by
  unfold HM; split_ifs <;> infer_instance

lemma measurable_HM (M : PhantomMechanism R Sig) (Gs : Set Sig) (hG : MeasurableSet Gs)
    (hgood : ∀ s ∈ Gs, GoodSig M s)
    (m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n) :
    Measurable (HM M Gs m θ n) := by
  classical
  have hW := measurable_Wf M Gs hG hgood m θ hm hmR hθ hθ1
  have hT := measurable_Tf M
  have hR := measurableSet_Reg M Gs hG m
  apply measurable_of_Iic_values
  intro x
  let FM : Sig → ℝ := fun s =>
    if x < 1 + Wf M Gs m θ s then 0
    else if x < 1 + Tf M s then
      1 - ((Wf M Gs m θ s - m) * (x - 1) / (Wf M Gs m θ s * ((x - 1) - m))) *
        (u m θ (signalAcceptance M s) / g (signalAcceptance M s) (x - 1)) ^ (1 / (n : ℝ))
    else 1
  have hFM : Measurable FM := by
    have hu := measurable_u M m θ
    have hg := measurable_g M (x - 1)
    refine Measurable.ite (measurableSet_lt measurable_const (hW.const_add 1)) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const (hT.const_add 1)) ?_ measurable_const)
    exact measurable_const.sub ((((hW.sub_const m).mul_const _).div (hW.mul_const _)).mul
      ((hu.div hg).pow_const _))
  have e : (fun s => HM M Gs m θ n s (Iic x)) = fun s =>
      if s ∈ Reg M Gs m ∧ Wf M Gs m θ s ≠ m then ENNReal.ofReal (FM s)
      else Measure.dirac (0 : ℝ) (Iic x) := by
    funext s
    by_cases hs : s ∈ Reg M Gs m ∧ Wf M Gs m θ s ≠ m
    · rw [if_pos hs]
      unfold HM
      rw [if_pos hs]
      obtain ⟨h, hr, hTs, hτ⟩ := reg_facts M Gs hgood m θ hm hmR hθ hθ1 n hn hs.1
      have hWs := Wf_eq M Gs m θ (s := s) hs.1
      have hw : m < w0 R m θ (signalAcceptance M s) :=
        lt_of_le_of_ne (w0_mem h hr hτ).1.1 (fun e => hs.2 (hWs.trans e.symm))
      rw [cdfLaw_Iic (mCDF_isCDF h hr hτ hw)]
      congr 1
      simp only [FM, hWs, hTs, mCDF, A, Atil, Gam]
    · rw [if_neg hs]
      unfold HM
      rw [if_neg hs]
  rw [e]
  exact Measurable.ite ((hR.inter (measurableSet_eq_fun hW measurable_const).compl))
    hFM.ennreal_ofReal measurable_const

/-- M's law over signals -/
noncomputable def LM (M : PhantomMechanism R Sig) (Gs : Set Sig) (m θ : ℝ) (n : ℕ) (s : Sig) :
    Measure ℝ := by
  classical
  exact if s ∈ Gs then lawM R m θ n (signalAcceptance M s) else Measure.dirac 0

lemma measurable_LM (M : PhantomMechanism R Sig) (Gs : Set Sig) (hG : MeasurableSet Gs)
    (hgood : ∀ s ∈ Gs, GoodSig M s)
    (m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n) :
    Measurable (LM M Gs m θ n) := by
  classical
  have hW := measurable_Wf M Gs hG hgood m θ hm hmR hθ hθ1
  have hT := measurable_Tf M
  have e : LM M Gs m θ n = fun s =>
      if s ∈ Gs then
        (if s ∈ {s | ZeroCase (signalAcceptance M s)} then Measure.dirac 1
        else if Tf M s ≤ m then Measure.dirac (1 + Tf M s)
        else if Wf M Gs m θ s = m then Measure.dirac (1 + m)
        else HM M Gs m θ n s)
      else Measure.dirac 0 := by
    funext s
    by_cases hsG : s ∈ Gs
    · have hTs := Tf_eq M (hgood s hsG).1
      simp only [LM, if_pos hsG, lawM, mem_ofPred_eq, hTs]
      by_cases hz : ZeroCase (signalAcceptance M s)
      · simp only [if_pos hz]
      · simp only [if_neg hz]
        by_cases hτ : tau R (signalAcceptance M s) ≤ m
        · simp only [if_pos hτ]
        · simp only [if_neg hτ]
          have hreg : s ∈ Reg M Gs m := ⟨⟨hsG, hz⟩, by rw [mem_ofPred_eq, hTs]; exact not_le.1 hτ⟩
          rw [Wf_eq M Gs m θ hreg]
          by_cases hw : w0 R m θ (signalAcceptance M s) = m
          · simp only [if_pos hw]
          · simp only [if_neg hw]
            unfold HM
            rw [if_pos ⟨hreg, by rw [Wf_eq M Gs m θ hreg]; exact hw⟩]
    · simp only [LM, if_neg hsG]
  rw [e]
  refine Measurable.ite hG (Measurable.ite (measurableSet_zero M) measurable_const
    (Measurable.ite (measurableSet_le hT measurable_const)
      (Measure.measurable_dirac.comp (hT.const_add 1))
      (Measurable.ite (measurableSet_eq_fun hW measurable_const) measurable_const
        (measurable_HM M Gs hG hgood m θ hm hmR hθ hθ1 n hn)))) measurable_const

/-- the interior part of a present rival's law -/
noncomputable def HP (M : PhantomMechanism R Sig) (Gs : Set Sig) (m θ : ℝ) (n : ℕ) (j : ℕ)
    (s : Sig) : Measure ℝ := by
  classical
  exact if s ∈ Reg M Gs m then cdfLaw (rivalCDF R m θ n (signalAcceptance M s) j)
    else Measure.dirac 0

instance HP_isProb (M : PhantomMechanism R Sig) (Gs : Set Sig) (m θ : ℝ) (n j : ℕ) (s : Sig) :
    IsProbabilityMeasure (HP M Gs m θ n j s) := by
  unfold HP; split_ifs <;> infer_instance

lemma measurable_HP (M : PhantomMechanism R Sig) (Gs : Set Sig) (hG : MeasurableSet Gs)
    (hgood : ∀ s ∈ Gs, GoodSig M s)
    (m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n)
    (j : ℕ) (hj : 1 ≤ j) :
    Measurable (HP M Gs m θ n j) := by
  classical
  have hW := measurable_Wf M Gs hG hgood m θ hm hmR hθ hθ1
  have hT := measurable_Tf M
  have hR := measurableSet_Reg M Gs hG m
  apply measurable_of_Iic_values
  intro x
  let FP : Sig → ℝ := fun s =>
    if x < 1 + Wf M Gs m θ s then 0
    else if x < 1 + Tf M s then
      1 - ((u m θ (signalAcceptance M s) / g (signalAcceptance M s) (x - 1)) ^ (1 / (n : ℝ))
        - p θ n) / (1 - p θ n)
    else if x < R + j then
      1 - ((u m θ (signalAcceptance M s) / piS (signalAcceptance M s)) ^ (1 / (n : ℝ))
        - p θ n) / (1 - p θ n)
    else 1
  have hFP : Measurable FP := by
    have hu := measurable_u M m θ
    have hg := measurable_g M (x - 1)
    have hπ : Measurable fun s => piS (signalAcceptance M s) := T57.measurable_pi M
    refine Measurable.ite (measurableSet_lt measurable_const (hW.const_add 1)) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const (hT.const_add 1)) ?_
        (Measurable.ite (MeasurableSet.const _) ?_ measurable_const))
    · exact measurable_const.sub ((((hu.div hg).pow_const _).sub_const _).div_const _)
    · exact measurable_const.sub ((((hu.div hπ).pow_const _).sub_const _).div_const _)
  have e : (fun s => HP M Gs m θ n j s (Iic x)) = fun s =>
      if s ∈ Reg M Gs m then ENNReal.ofReal (FP s)
      else Measure.dirac (0 : ℝ) (Iic x) := by
    funext s
    by_cases hs : s ∈ Reg M Gs m
    · rw [if_pos hs]
      unfold HP
      rw [if_pos hs]
      obtain ⟨h, hr, hTs, hτ⟩ := reg_facts M Gs hgood m θ hm hmR hθ hθ1 n hn hs
      have hWs := Wf_eq M Gs m θ (s := s) hs
      rw [cdfLaw_Iic (rivalCDF_isCDF h hr hτ j hj)]
      congr 1
      simp only [FP, hWs, hTs, rivalCDF, A2.G, Gam, g_tau h hr]
    · rw [if_neg hs]
      unfold HP
      rw [if_neg hs]
  rw [e]
  exact Measurable.ite hR hFP.ennreal_ofReal measurable_const

/-- a present rival's law over signals -/
noncomputable def LP (M : PhantomMechanism R Sig) (Gs : Set Sig) (m θ : ℝ) (n j : ℕ) (s : Sig) :
    Measure ℝ := by
  classical
  exact if s ∈ Gs then lawP R m θ n (signalAcceptance M s) j else Measure.dirac 0

lemma measurable_LP (M : PhantomMechanism R Sig) (Gs : Set Sig) (hG : MeasurableSet Gs)
    (hgood : ∀ s ∈ Gs, GoodSig M s)
    (m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n)
    (j : ℕ) (hj : 1 ≤ j) :
    Measurable (LP M Gs m θ n j) := by
  classical
  have hT := measurable_Tf M
  have e : LP M Gs m θ n j = fun s =>
      if s ∈ Gs then
        (if s ∈ {s | ZeroCase (signalAcceptance M s)} ∪ {s | Tf M s ≤ m}
          then Measure.dirac (R + j)
        else HP M Gs m θ n j s)
      else Measure.dirac 0 := by
    funext s
    by_cases hsG : s ∈ Gs
    · have hTs := Tf_eq M (hgood s hsG).1
      simp only [LP, if_pos hsG, lawP, mem_union, mem_ofPred_eq, hTs]
      by_cases hc : ZeroCase (signalAcceptance M s) ∨ tau R (signalAcceptance M s) ≤ m
      · simp only [if_pos hc]
      · simp only [if_neg hc]
        push Not at hc
        have hreg : s ∈ Reg M Gs m := ⟨⟨hsG, hc.1⟩, by rw [mem_ofPred_eq, hTs]; exact hc.2⟩
        unfold HP
        rw [if_pos hreg]
    · simp only [LP, if_neg hsG]
  rw [e]
  exact Measurable.ite hG (Measurable.ite ((measurableSet_zero M).union
    (measurableSet_le hT measurable_const)) measurable_const
    (measurable_HP M Gs hG hgood m θ hm hmR hθ hθ1 n hn j hj)) measurable_const

lemma measurable_rawBid (M : PhantomMechanism R Sig) (G : Set Sig) (hG : MeasurableSet G)
    (hgood : ∀ s ∈ G, GoodSig M s) (m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ)
    (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n) (i : Suppliers n) :
    Measurable (rawBid M G m θ n i) := by
  classical
  by_cases hi : i = 0
  · have e : rawBid M G m θ n i = fun x => LM M G m θ n x.1 := by
      funext x
      unfold rawBid LM mkProfile
      by_cases hx : x.1 ∈ G
      · simp only [if_pos hx, hi, if_true, Kernel.const_apply]
      · simp only [if_neg hx]
    rw [e]
    exact (measurable_LM M G hG hgood m θ hm hmR hθ hθ1 n hn).comp measurable_fst
  · have hj : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hi (Fin.ext h))
    have e : rawBid M G m θ n i = fun x =>
        if x.2 = R then (if x.1 ∈ G then Measure.dirac (R + (i : ℕ)) else Measure.dirac 0)
        else LP M G m θ n i x.1 := by
      funext x
      unfold rawBid LP mkProfile
      by_cases hx : x.1 ∈ G
      · by_cases h2 : x.2 = R
        · simp only [if_pos hx, hi, if_false, Kernel.piecewise_apply, mem_singleton_iff, h2,
            if_true, Kernel.const_apply]
        · simp only [if_pos hx, hi, if_false, Kernel.piecewise_apply, mem_singleton_iff, h2,
            Kernel.const_apply]
      · by_cases h2 : x.2 = R
        · simp only [if_neg hx, h2, if_true]
        · simp only [if_neg hx, h2, if_false]
    rw [e]
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      (Measurable.ite (measurable_fst hG) measurable_const measurable_const)
      ((measurable_LP M G hG hgood m θ hm hmR hθ hθ1 n hn i hj).comp measurable_fst)

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
alias measurable_rawBid := ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK.measurable_rawBid

/-- the mechanism profile -/
noncomputable def mechProfile (M : PhantomMechanism R Sig) (G : Set Sig) (hG : MeasurableSet G)
    (hgood : ∀ s ∈ G, GoodSig M s) (m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ)
    (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n) : MechanismProfile Sig n where
  bid i := ⟨rawBid M G m θ n i, measurable_rawBid M G hG hgood m θ hm hmR hθ hθ1 n hn i⟩
  markov i := ⟨fun x => rawBid_isProb M G m θ n i x⟩

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
lemma mixedProfile_ext {n : ℕ} {σ τ : MixedProfile n} (h : ∀ i, σ.bid i = τ.bid i) : σ = τ := by
  cases σ; cases τ
  simp only [MixedProfile.mk.injEq]
  funext i
  exact h i

lemma slice_eq (M : PhantomMechanism R Sig) (G : Set Sig) (hG : MeasurableSet G)
    (hgood : ∀ s ∈ G, GoodSig M s) (m θ : ℝ) (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ)
    (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n) (s : Sig) (hs : s ∈ G) :
    sliceProfile (mechProfile M G hG hgood m θ hm hmR hθ hθ1 n hn) s =
      mkProfile n R (lawM R m θ n (signalAcceptance M s)) (lawP R m θ n (signalAcceptance M s)) := by
  classical
  apply mixedProfile_ext
  intro i
  refine Kernel.ext fun c => ?_
  show rawBid M G m θ n i (s, c) = _
  unfold rawBid
  simp only [if_pos hs]

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
alias slice_eq := ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartK.slice_eq

/-- the family is an equilibrium of the mechanism, with the averaged loss bound -/
theorem mech_bound (M : PhantomMechanism R Sig) (hreg : IsRegularMechanism M) (m θ : ℝ)
    (hm : 0 < m) (hmR : m < R - 1) (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) (hn : 1 ≤ n)
    (τ : TieRule n) :
    ∃ σ : MechanismProfile Sig n,
      IsMechanismBNE M (rivalInstance R m θ n hθ.le hθ1.le) τ σ ∧
      ∫⁻ s, (1 + ENNReal.ofReal (rivalHighProbability θ n *
          Phi m θ (monopolyProfit (signalAcceptance M s) 1))) ∂M.signalLaw ≤
        mechanismSocialCost M (rivalInstance R m θ n hθ.le hθ1.le) τ σ := by
  obtain ⟨G, hG, hgood, hnull⟩ := exists_goodSet M hreg
  refine ⟨mechProfile M G hG hgood m θ hm hmR hθ hθ1 n hn, ?_, ?_⟩
  · have hae : ∀ᵐ s ∂M.signalLaw, s ∈ G := by
      exact measure_eq_zero_iff_ae_notMem.1 (by simpa using hnull) |>.mono fun s hs => by simpa using hs
    filter_upwards [hae] with s hs
    rw [slice_eq M G hG hgood m θ hm hmR hθ hθ1 n hn s hs]
    exact (explicit_good R m θ hm hmR hθ hθ1 n hn _ (isAcceptance_of_good M (hgood s hs))
      (hgood s hs).2 τ).1
  · unfold mechanismSocialCost
    apply lintegral_mono_ae
    have hae : ∀ᵐ s ∂M.signalLaw, s ∈ G := by
      exact measure_eq_zero_iff_ae_notMem.1 (by simpa using hnull) |>.mono fun s hs => by simpa using hs
    filter_upwards [hae] with s hs
    rw [slice_eq M G hG hgood m θ hm hmR hθ hθ1 n hn s hs]
    exact (explicit_good R m θ hm hmR hθ hθ1 n hn _ (isAcceptance_of_good M (hgood s hs))
      (hgood s hs).2 τ).2

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
/-! ## Assembly -/
lemma integ_of (μ : Measure Sig) [IsFiniteMeasure μ] {f : Sig → ℝ} (hf : Measurable f) (a b : ℝ)
    (h : ∀ s, a ≤ f s ∧ f s ≤ b) : Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable (max |a| |b|) (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have := h s
  constructor
  · linarith [neg_abs_le a, le_max_left |a| |b|]
  · linarith [le_abs_self b, le_max_right |a| |b|]

lemma lint_eq (μ : Measure Sig) [IsFiniteMeasure μ] {f : Sig → ℝ} (hf : Measurable f) (a b : ℝ)
    (h : ∀ s, a ≤ f s ∧ f s ≤ b) (h0 : ∀ s, 0 ≤ f s) :
    ∫⁻ s, ENNReal.ofReal (f s) ∂μ = ENNReal.ofReal (∫ s, f s ∂μ) :=
  (ofReal_integral_eq_lintegral_ofReal (integ_of μ hf a b h) (ae_of_all _ h0)).symm

lemma sigma_mem (M : PhantomMechanism R Sig) (s : Sig) (t : ℝ) :
    0 ≤ sigma R (signalAcceptance M s) t ∧ sigma R (signalAcceptance M s) t ≤ 1 := by
  unfold sigma; split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨surv_nonneg (isSurv_sig M s) _, surv_le_one (isSurv_sig M s) _⟩

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2 ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
lemma Phi_mem (m θ π : ℝ) (hm : 0 < m) (hθ : 0 < θ) (hθ1 : θ < 1) :
    0 ≤ Phi m θ π ∧ Phi m θ π ≤ m := by
  unfold Phi; split_ifs with h
  · have hp : 0 < θ * π := hm.trans h
    have h1 : m / (θ * π) < 1 := (div_lt_one hp).2 h
    have h2 : 0 < m / (θ * π) := div_pos hm hp
    have h3 : 0 ≤ m * (1 - θ) := mul_nonneg hm.le (by linarith)
    constructor
    · exact mul_nonneg h3 (by linarith)
    · have : m * (1 - θ) ≤ m := by nlinarith
      nlinarith
  · exact ⟨le_rfl, hm.le⟩

lemma measurable_Phi (m θ : ℝ) : Measurable (Phi m θ) := by
  classical
  unfold Phi
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_const.mul measurable_id))
    (by fun_prop) measurable_const

lemma sum_succ (k : ℕ) : ∑ j ∈ Finset.range k, ((j : ℝ) + 1) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- assembly -/
theorem main (R : ℝ) (hR : 1 < R) {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) (hreg : IsRegularMechanism M) :
    ENNReal.ofReal (Lall R) ≤ mechanismPoA M := by
  by_cases htop : mechanismPoA M = ⊤
  · rw [htop]; exact le_top
  set L := (mechanismPoA M).toReal with hLdef
  have hPL : mechanismPoA M = ENNReal.ofReal L := (ENNReal.ofReal_toReal htop).symm
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  set μ := M.signalLaw with hμ
  have hsb : ∀ t s, 0 ≤ 1 - sigma R (signalAcceptance M s) t ∧
      1 - sigma R (signalAcceptance M s) t ≤ 1 := fun t s => by
    have := sigma_mem M s t; constructor <;> linarith
  have hsm : ∀ t, Measurable fun s => 1 - sigma R (signalAcceptance M s) t := fun t =>
    measurable_const.sub (measurable_sigma M t)
  have hint1 : ∀ t, Integrable (fun s => 1 - sigma R (signalAcceptance M s) t) μ := fun t =>
    integ_of μ (hsm t) 0 1 (hsb t)
  have hI1 : ∀ t, ∫ s, (1 - sigma R (signalAcceptance M s) t) ∂μ ≤ 1 := by
    intro t
    have := integral_mono (hint1 t) (integrable_const (1:ℝ)) (fun s => (hsb t s).2)
    simpa using this
  have h55 : ∀ t ∈ Icc 1 R,
      1 + (R - t) / t * ∫ s, (1 - sigma R (signalAcceptance M s) t) ∂μ ≤ L := by
    intro t ht
    have h := lemma_5_5 R hR.le M t ht
    have hnn : 0 ≤ ∫ s, (1 - sigma R (signalAcceptance M s) t) ∂μ :=
      integral_nonneg fun s => (hsb t s).1
    have ha : 0 ≤ (R - t) / t := div_nonneg (by linarith [ht.2]) (by linarith [ht.1])
    rw [lint_eq μ (hsm t) 0 1 (hsb t) (fun s => (hsb t s).1), ← ENNReal.ofReal_mul ha,
      ← ENNReal.ofReal_add zero_le_one (mul_nonneg ha hnn), hPL,
      ENNReal.ofReal_le_ofReal_iff hL0] at h
    exact h
  have hL1 : 1 ≤ L := by
    have := h55 R ⟨hR.le, le_rfl⟩
    simpa using this
  rw [hPL]
  refine ENNReal.ofReal_le_ofReal (Lall_le R L hR hL1 fun hLR => ?_)
  set X := R / (2 * L) with hX
  have hLpos : 0 < L := by linarith
  have hX1 : 1 < X := by rw [hX, one_lt_div (by positivity)]; linarith
  have hXR : X ≤ R := by rw [hX, div_le_iff₀ (by positivity)]; nlinarith
  -- step (1)
  have hstep1 : ∀ t, 1 ≤ t → t ≤ X →
      ∫ s, (1 - sigma R (signalAcceptance M s) t) ∂μ ≤ L * t / R := by
    intro t ht1 htX
    have h := h55 t ⟨ht1, htX.trans hXR⟩
    have hI := hI1 t
    set I := ∫ s, (1 - sigma R (signalAcceptance M s) t) ∂μ
    have ht0 : 0 < t := by linarith
    have e : (R - t) / t * I * t = (R - t) * I := by field_simp
    have h2 : (R - t) * I ≤ (L - 1) * t := by
      rw [← e]; nlinarith
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hI ht0.le]
  -- step (2)
  have hmaxm : Measurable fun s => max (X - 1 - monopolyProfit (signalAcceptance M s) 1) 0 :=
    (measurable_const.sub (measurable_pi M)).max measurable_const
  have hmaxb : ∀ s, 0 ≤ max (X - 1 - monopolyProfit (signalAcceptance M s) 1) 0 ∧
      max (X - 1 - monopolyProfit (signalAcceptance M s) 1) 0 ≤ X - 1 := fun s =>
    ⟨le_max_right _ _, max_le (by linarith [P_nonneg_gen (isSurv_sig M s) 1]) (by linarith)⟩
  have hintmax := integ_of μ hmaxm 0 (X - 1) hmaxb
  have hgood : ∀ᵐ s ∂μ, IsAcceptance R (signalAcceptance M s) :=
    M.bounded.mono fun s hs => ⟨M.phantom s, inferInstance, hs, fun _ => rfl⟩
  have hkb : ∀ k : ℕ, 1 ≤ k →
      ∫ s, max (X - 1 - monopolyProfit (signalAcceptance M s) 1) 0 ∂μ ≤
        L / R * ((X - 1) + (X - 1) ^ 2 / 2) + L * (X - 1) ^ 2 / (2 * R) * (1 / (k : ℝ)) := by
    intro k hk1
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk1
    have h1 : ∫ s, max (X - 1 - monopolyProfit (signalAcceptance M s) 1) 0 ∂μ ≤
        ∫ s, ∑ j ∈ Finset.range k, (X - 1) / k *
          (1 - sigma R (signalAcceptance M s) (1 + (j + 1) * (X - 1) / k)) ∂μ := by
      apply integral_mono_ae hintmax (integrable_finsetSum _ fun j _ => (hint1 _).const_mul _)
      filter_upwards [hgood] with s hs
      exact riemann R hR.le _ hs X hX1.le k hk1
    rw [integral_finsetSum _ fun j _ => (hint1 _).const_mul _] at h1
    simp_rw [integral_const_mul] at h1
    have h2 : ∑ j ∈ Finset.range k, (X - 1) / k *
          ∫ s, (1 - sigma R (signalAcceptance M s) (1 + (j + 1) * (X - 1) / k)) ∂μ ≤
        ∑ j ∈ Finset.range k, (X - 1) / k * (L * (1 + (j + 1) * (X - 1) / k) / R) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith) hk0.le)
      apply hstep1
      · have : 0 ≤ ((j:ℝ) + 1) * (X - 1) / k :=
          div_nonneg (mul_nonneg (by positivity) (by linarith)) hk0.le
        linarith
      · have hj' : (j:ℝ) + 1 ≤ k := by
          have := Finset.mem_range.1 hj; exact_mod_cast this
        have : ((j:ℝ) + 1) * (X - 1) / k ≤ X - 1 := by
          rw [div_le_iff₀ hk0]; nlinarith
        linarith
    have h3 : ∑ j ∈ Finset.range k, (X - 1) / k * (L * (1 + (j + 1) * (X - 1) / k) / R) =
        L / R * ((X - 1) + (X - 1) ^ 2 / 2) + L * (X - 1) ^ 2 / (2 * R) * (1 / (k : ℝ)) := by
      have e : ∀ j : ℕ, (X - 1) / k * (L * (1 + (j + 1) * (X - 1) / k) / R) =
          (X - 1) / k * (L / R) + (X - 1) ^ 2 * L / (k ^ 2 * R) * ((j:ℝ) + 1) := by
        intro j; field_simp
      simp_rw [e]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum, sum_succ]
      field_simp
      ring
    linarith
  have hE2 : ∫ s, max (X - 1 - monopolyProfit (signalAcceptance M s) 1) 0 ∂μ ≤
      L / R * ((X - 1) + (X - 1) ^ 2 / 2) := by
    have ht : Tendsto (fun k : ℕ => L / R * ((X - 1) + (X - 1) ^ 2 / 2) +
        L * (X - 1) ^ 2 / (2 * R) * (1 / (k : ℝ))) atTop
        (𝓝 (L / R * ((X - 1) + (X - 1) ^ 2 / 2) + L * (X - 1) ^ 2 / (2 * R) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)
    rw [mul_zero, add_zero] at ht
    exact ge_of_tendsto ht (eventually_atTop.2 ⟨1, fun k hk => hkb k hk⟩)
  -- step (3)
  set m := (X - 1) / 4 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hmR : m < R - 1 := by rw [hm]; linarith
  have hθ : (0:ℝ) < 1 / 2 := by norm_num
  have hθ1 : (1:ℝ) / 2 < 1 := by norm_num
  have hPhim : Measurable fun s => Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) :=
    (measurable_Phi m (1 / 2)).comp (measurable_pi M)
  have hPhib : ∀ s, 0 ≤ Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) ∧
      Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) ≤ m := fun s =>
    Phi_mem _ _ _ hm0 hθ hθ1
  have hn : ∀ n : ℕ, 1 ≤ n → 1 + rivalHighProbability (1 / 2) n *
      ∫ s, Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) ∂μ ≤ L := by
    intro n hn1
    obtain ⟨σ, hB, hC⟩ := mech_bound M hreg m (1 / 2) hm0 hmR hθ hθ1 n hn1 (M5C.tie n)
    have hle : mechanismSocialCost M (rivalInstance R m (1 / 2) n hθ.le hθ1.le) (M5C.tie n) σ /
        optimalSocialCost (rivalInstance R m (1 / 2) n hθ.le hθ1.le) ≤ mechanismPoA M :=
      le_sSup ⟨n, rivalInstance R m (1 / 2) n hθ.le hθ1.le, M5C.tie n, σ,
        rival_inCostInterval R m (1 / 2) hm0 hmR hθ hθ1 n, hB, rfl⟩
    rw [optimal_eq hm0 hmR hθ hθ1, div_one] at hle
    have hp0 : 0 ≤ rivalHighProbability (1 / 2) n := Real.rpow_nonneg hθ.le _
    have hfm : Measurable fun s => rivalHighProbability (1 / 2) n *
        Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) := hPhim.const_mul _
    have hfb : ∀ s, 0 ≤ rivalHighProbability (1 / 2) n *
          Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) ∧
        rivalHighProbability (1 / 2) n *
          Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) ≤
        rivalHighProbability (1 / 2) n * m := fun s =>
      ⟨mul_nonneg hp0 (hPhib s).1, mul_le_mul_of_nonneg_left (hPhib s).2 hp0⟩
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lint_eq μ hfm 0 _ hfb (fun s => (hfb s).1), integral_const_mul] at hC
    have h := hC.trans (hle.trans hPL.le)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
      (mul_nonneg hp0 (integral_nonneg fun s => (hPhib s).1)),
      ENNReal.ofReal_le_ofReal_iff hL0] at h
    exact h
  have hlimp : Tendsto (fun n : ℕ => rivalHighProbability (1 / 2) n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 := ((Real.continuousAt_const_rpow (a := (1 / 2 : ℝ)) (b := 0)
      (by norm_num)).tendsto).comp h1
    rw [Real.rpow_zero] at h2
    exact h2
  have hPhiI : 1 + ∫ s, Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) ∂μ ≤ L := by
    have ht : Tendsto (fun n : ℕ => 1 + rivalHighProbability (1 / 2) n *
        ∫ s, Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) ∂μ) atTop
        (𝓝 (1 + 1 * ∫ s, Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) ∂μ)) :=
      tendsto_const_nhds.add (hlimp.mul_const _)
    rw [one_mul] at ht
    exact le_of_tendsto ht (eventually_atTop.2 ⟨1, fun n hn1 => hn n hn1⟩)
  -- step (4)
  have hlow : chi * (X - 1) - 2 * chi *
      ∫ s, max (X - 1 - monopolyProfit (signalAcceptance M s) 1) 0 ∂μ ≤
      ∫ s, Phi m (1 / 2) (monopolyProfit (signalAcceptance M s) 1) ∂μ := by
    have hi : Integrable (fun s => chi * (X - 1) - 2 * chi *
        max (X - 1 - monopolyProfit (signalAcceptance M s) 1) 0) μ :=
      (integrable_const _).sub (hintmax.const_mul _)
    have := integral_mono hi (integ_of μ hPhim 0 m hPhib)
      (fun s => phi_lower X _ hX1 (P_nonneg_gen (isSurv_sig M s) 1))
    rw [integral_sub (integrable_const _) (hintmax.const_mul _), integral_const] at this
    simpa [integral_const_mul] using this
  have e : chi * (X - 1) - 2 * chi * (L / R * ((X - 1) + (X - 1) ^ 2 / 2)) =
      chi * R / (4 * L) - chi + chi * L / R := by
    rw [hX]; field_simp; ring
  have hchi : 0 ≤ chi := by unfold chi; norm_num
  have := mul_le_mul_of_nonneg_left hE2 (by positivity : 0 ≤ 2 * chi)
  linarith

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
alias main := ProcurementPoA.DeterministicCap.Supplement.Dev.T57.PartA.main

theorem theorem_5_7_dev (R : ℝ) (hR : 1 < R) {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) (hreg : IsRegularMechanism M) :
    ENNReal.ofReal (Lall R) ≤ mechanismPoA M ∧
    Real.sqrt R / 8 + 15 / 32 ≤ Lall R :=
  ⟨main R hR M hreg, second_ineq R hR⟩

end ProcurementPoA.DeterministicCap.Supplement.Dev.T57
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev.A2
open ProcurementPoA
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Supplement.Dev
open ProcurementPoA.DeterministicCap.Supplement.Dev.T57
universe u
theorem solution (R : ℝ) (hR : 1 < R) {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) (hreg : IsRegularMechanism M) :
    ENNReal.ofReal (Lall R) ≤ mechanismPoA M ∧
    Real.sqrt R / 8 + 15 / 32 ≤ Lall R := by
  exact ProcurementPoA.DeterministicCap.Supplement.Dev.T57.theorem_5_7_dev R hR M hreg
end
