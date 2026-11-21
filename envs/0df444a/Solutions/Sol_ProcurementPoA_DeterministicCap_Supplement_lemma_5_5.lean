-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.Supplement.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:48:00.279653+00:00
-- url     : https://prove2.me/submissions/ec4720a7-2853-4c39-8010-8d15748b428b

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Monopoly
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Mechanism
universe u

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

lemma sigma_nonneg (hS : IsAcceptance R S) (c : ℝ) : 0 ≤ sigma R S c := by
  unfold sigma; split_ifs
  · exact le_rfl
  · exact S_nonneg hS _

lemma sigma_le_one (hS : IsAcceptance R S) (c : ℝ) : sigma R S c ≤ 1 := by
  unfold sigma; split_ifs
  · exact zero_le_one
  · exact S_le_one hS _

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

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Classical
open ProcurementPoA.DeterministicCap.Supplement.Dev.A1
open ProcurementPoA.DeterministicCap.Supplement.Dev.M5A

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.M5B


variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]

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

lemma sel_one {n : ℕ} (τ : TieRule n) (v : Suppliers n → ℝ) (i : Suppliers n)
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

lemma sel_zero {n : ℕ} (τ : TieRule n) (v : Suppliers n → ℝ) (i : Suppliers n)
    (h : ∃ j, v j < v i) : τ.select v {i} = 0 := by
  obtain ⟨j, hj⟩ := h
  have h1 := τ.lowest_only v
  have h2 : ∀ᵐ k ∂(τ.select v), k ≠ i := by
    filter_upwards [h1] with k hk hki
    subst hki
    exact absurd (hk j) (not_le.2 hj)
  exact measure_mono_null (fun k hk => not_not.2 (mem_singleton_iff.1 hk)) (ae_iff.1 h2)

/-! ### Dirac helpers -/

lemma ae_pi_dirac {n : ℕ} {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Fin (n + 1) → Measure α) (p : Fin (n + 1) → α) (h : ∀ j, μ j = Measure.dirac (p j))
    [∀ j, IsProbabilityMeasure (μ j)] : ∀ᵐ x ∂(Measure.pi μ), x = p := by
  have : ∀ j, ∀ᵐ x ∂(Measure.pi μ), x j = p j := by
    intro j
    have hq := (measurePreserving_eval μ j).quasiMeasurePreserving
    exact hq.ae (p := fun y : α => y = p j) (by rw [h j, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl)
  filter_upwards [ae_all_iff.2 this] with x hx
  exact funext hx

lemma dirac_compProd_dirac (a b : ℝ) (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (h : κ a = Measure.dirac b) :
    Measure.dirac a ⊗ₘ κ = Measure.dirac (a, b) := by
  ext s hs
  rw [Measure.compProd_apply hs, lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left hs), h,
    Measure.dirac_apply' _ (measurable_prodMk_left hs), Measure.dirac_apply' _ hs]
  simp [Set.indicator]


/-! ### the two-supplier instance -/

variable {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]

noncomputable def cv (R c : ℝ) : Suppliers 1 → ℝ := fun i => if i = 0 then c else R

noncomputable def Dm (R c : ℝ) : IndependentTypes 1 := deterministicTypes (cv R c)

noncomputable def kM (M : PhantomMechanism R Sig) (c : ℝ) : Kernel (Sig × ℝ) ℝ :=
  Kernel.deterministic (fun p : Sig × ℝ => if p.2 = c then Bs M c p.1 else 0)
    (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      ((measurable_Bs M c).comp measurable_fst) measurable_const)

noncomputable def kD (R : ℝ) (Sig : Type u) [MeasurableSpace Sig] : Kernel (Sig × ℝ) ℝ :=
  Kernel.deterministic (fun _ => R + 1) measurable_const

noncomputable def prof (M : PhantomMechanism R Sig) (c : ℝ) : MechanismProfile Sig 1 where
  bid i := if i = 0 then kM M c else kD R Sig
  markov i := by
    by_cases hi : i = 0
    · simp only [hi, if_true]; unfold kM; infer_instance
    · simp only [hi, if_false]; unfold kD; infer_instance

noncomputable def bvec (M : PhantomMechanism R Sig) (c : ℝ) (s : Sig) : Suppliers 1 → ℝ :=
  fun i => if i = 0 then Bs M c s else R + 1

lemma slice_apply (M : PhantomMechanism R Sig) (c : ℝ) (s : Sig) (i : Suppliers 1) :
    (sliceProfile (prof M c) s).bid i (cv R c i) = Measure.dirac (bvec M c s i) := by
  by_cases hi : i = 0
  · subst hi
    simp [sliceProfile, prof, kM, cv, bvec, Kernel.comap_apply, Kernel.deterministic_apply]
  · simp [sliceProfile, prof, kD, cv, bvec, hi, Kernel.comap_apply, Kernel.deterministic_apply]

lemma marg_eq (M : PhantomMechanism R Sig) (c : ℝ) (s : Sig) (j : Suppliers 1) :
    marginalBidLaw (Dm R c) (sliceProfile (prof M c) s) j = Measure.dirac (bvec M c s j) := by
  unfold marginalBidLaw
  simp only [Dm, deterministicTypes]
  exact (Measure.dirac_bind (Kernel.measurable _) _).trans (slice_apply M c s j)

lemma interimWin_le_one' {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (b : ℝ) : interimWin D τ σ i b ≤ 1 := by
  unfold interimWin
  calc _ ≤ ∫⁻ _bs, (1 : ℝ≥0∞) ∂(Measure.pi (marginalBidLaw D σ)) :=
        lintegral_mono fun _ => prob_le_one
    _ = 1 := by simp

lemma win_toReal_mem {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (i : Suppliers n) (b : ℝ) : 0 ≤ (interimWin D τ σ i b).toReal ∧ (interimWin D τ σ i b).toReal ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using interimWin_le_one' D τ σ i b)⟩

lemma win_M_one (M : PhantomMechanism R Sig) (c : ℝ) (s : Sig) (τ : TieRule 1) {b : ℝ}
    (hb : b < R + 1) :
    interimWin (Dm R c) τ (sliceProfile (prof M c) s) 0 b = 1 := by
  haveI : ∀ j, IsProbabilityMeasure (marginalBidLaw (Dm R c) (sliceProfile (prof M c) s) j) :=
    fun j => inferInstance
  unfold interimWin
  have hae := ae_pi_dirac (marginalBidLaw (Dm R c) (sliceProfile (prof M c) s)) (bvec M c s)
    (marg_eq M c s)
  have : ∀ᵐ bs ∂(Measure.pi (marginalBidLaw (Dm R c) (sliceProfile (prof M c) s))),
      τ.select (Function.update bs 0 b) {0} = 1 := by
    filter_upwards [hae] with bs hbs
    apply sel_one
    intro j hj
    have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst hj1
    simp [hbs, bvec, hb]
  rw [lintegral_congr_ae this]
  simp


lemma Bs_good (M : PhantomMechanism R Sig) (c : ℝ) {s : Sig} (hs : M.phantom s (Ioi R) = 0) :
    Bs M c s = monopolyBid R (signalAcceptance M s) c := by
  unfold Bs; rw [if_pos hs]

lemma c_le_Bs (M : PhantomMechanism R Sig) (c : ℝ) (hcR : c ≤ R) {s : Sig}
    (hs : M.phantom s (Ioi R) = 0) : c ≤ Bs M c s := by
  rw [Bs_good M c hs]
  have hacc := isAcc_of_good M hs
  by_cases hP : monopolyProfit (signalAcceptance M s) c = 0
  · unfold monopolyBid; rw [if_pos hP]; linarith
  · obtain ⟨h1, _⟩ := bid_spec hacc c hP
    have hpos := lt_of_le_of_ne (P_nonneg hacc c) (Ne.symm hP)
    by_contra hlt; push_neg at hlt
    have := mul_nonpos_of_nonpos_of_nonneg (by linarith : monopolyBid R (signalAcceptance M s) c - c ≤ 0)
      (S_nonneg hacc (monopolyBid R (signalAcceptance M s) c))
    linarith

theorem slice_BNE (M : PhantomMechanism R Sig) (c : ℝ) (hcR : c ≤ R) {s : Sig}
    (hs : M.phantom s (Ioi R) = 0) (τ : TieRule 1) :
    IsAcceptBNE (Dm R c) τ (sliceProfile (prof M c) s) (signalAcceptance M s) := by
  have hacc := isAcc_of_good M hs
  set S := signalAcceptance M s with hSdef
  refine ⟨?_, ?_⟩
  · intro i c' hc'
    simp only [Dm, deterministicTypes, mem_singleton_iff] at hc'
    subst hc'
    rw [slice_apply M c s i, ae_dirac_eq]
    refine Filter.eventually_pure.2 ?_
    by_cases hi : i = 0
    · simp only [cv, bvec, hi, if_true]; exact c_le_Bs M c hcR hs
    · simp only [cv, bvec, hi, if_false]; linarith
  · intro i c' hc'
    simp only [Dm, deterministicTypes, mem_singleton_iff] at hc'
    subst hc'
    rw [slice_apply M c s i, ae_dirac_eq]
    refine Filter.eventually_pure.2 ?_
    intro a
    unfold acceptUtility standardUtility
    by_cases hi : i = 0
    · subst hi
      simp only [cv, bvec, if_true]
      set B := Bs M c s with hB
      have hPnn := P_nonneg hacc c
      obtain ⟨hw0, hw1⟩ := win_toReal_mem (Dm R c) τ (sliceProfile (prof M c) s) 0 a
      have hupper : (a - c) * (interimWin (Dm R c) τ (sliceProfile (prof M c) s) 0 a).toReal * S a
          ≤ monopolyProfit S c := by
        have hS0 := S_nonneg hacc a
        have hf := f_le_P hacc c a
        by_cases hac : a ≤ c
        · have : (a - c) * (interimWin (Dm R c) τ (sliceProfile (prof M c) s) 0 a).toReal * S a ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hw0) hS0
          linarith
        · push_neg at hac
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ a - c) hS0) (sub_nonneg.2 hw1)]
      by_cases hP : monopolyProfit S c = 0
      · have hBR : B = R + 1 := by
          rw [hB, Bs_good M c hs]; unfold monopolyBid; rw [if_pos hP]
        have : S B = 0 := by rw [hBR]; exact S_zero hacc (by linarith)
        rw [this]; simp only [mul_zero]; linarith
      · obtain ⟨h1, _⟩ := bid_spec hacc c hP
        have hBeq : B = monopolyBid R S c := Bs_good M c hs
        have hpos := lt_of_le_of_ne hPnn (Ne.symm hP)
        have hSB : 0 < S B := by
          rw [hBeq]
          by_contra hle; push_neg at hle
          have h0 := S_nonneg hacc (monopolyBid R S c)
          have : S (monopolyBid R S c) = 0 := le_antisymm hle h0
          rw [this] at h1; simp at h1; linarith
        have hBR : B < R + 1 := by
          by_contra hge; push_neg at hge
          have := S_zero hacc (show R < B by linarith)
          linarith
        rw [win_M_one M c s τ hBR]
        simp only [ENNReal.toReal_one, mul_one]
        rw [hBeq, h1]; linarith
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst hi1
      simp only [cv, bvec, show (1 : Suppliers 1) ≠ 0 by decide, if_false]
      obtain ⟨hw0, hw1⟩ := win_toReal_mem (Dm R c) τ (sliceProfile (prof M c) s) 1 a
      have hSR : S (R + 1) = 0 := S_zero hacc (by linarith)
      rw [hSR]; simp only [mul_zero]
      have hS0 := S_nonneg hacc a
      by_cases haR : a ≤ R
      · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hw0) hS0
      · push_neg at haR
        rw [S_zero hacc haR]; simp


lemma lowest_two (v : Suppliers 1 → ℝ) (h : v 0 ≤ v 1) : lowest v = v 0 := by
  unfold lowest
  apply le_antisymm (Finset.inf'_le _ (Finset.mem_univ 0))
  exact Finset.le_inf' _ _ fun i _ => by fin_cases i <;> simp [h]

lemma slice_cost (M : PhantomMechanism R Sig) (c : ℝ) (hc : c ∈ Icc 1 R) {s : Sig}
    (hs : M.phantom s (Ioi R) = 0) (τ : TieRule 1) :
    acceptSocialCost (Dm R c) τ (sliceProfile (prof M c) s) R (signalAcceptance M s)
      = ENNReal.ofReal (c + (R - c) * (1 - sigma R (signalAcceptance M s) c)) := by
  have hacc := isAcc_of_good M hs
  set S := signalAcceptance M s with hSdef
  set σ' := sliceProfile (prof M c) s with hσ'
  have hlaw : playLaw (Dm R c) σ' =
      Measure.pi (fun i => Measure.dirac (cv R c i, bvec M c s i)) := by
    unfold playLaw
    congr 1
    ext1 i
    exact dirac_compProd_dirac (cv R c i) (bvec M c s i) _ (slice_apply M c s i)
  have hae := ae_pi_dirac (fun i => Measure.dirac (cv R c i, bvec M c s i))
    (fun i => (cv R c i, bvec M c s i)) (fun j => rfl)
  unfold acceptSocialCost
  rw [hlaw]
  set x0 : Suppliers 1 → ℝ × ℝ := fun i => (cv R c i, bvec M c s i) with hx0
  rw [lintegral_congr_ae (g := fun _ => winnerCost τ x0 * ENNReal.ofReal (S (lowest (fun i => (x0 i).2))) +
      ENNReal.ofReal R * ENNReal.ofReal (1 - S (lowest (fun i => (x0 i).2)))) (by
    filter_upwards [hae] with x hx
    rw [hx])]
  rw [lintegral_const, measure_univ, mul_one]
  have hl0 : (fun i => (x0 i).2) = bvec M c s := rfl
  rw [hl0]
  have hRc : c ≤ R := hc.2
  have hc0 : 0 ≤ c := by linarith [hc.1]
  by_cases hP : monopolyProfit S c = 0
  · have hBR : Bs M c s = R + 1 := by
      rw [Bs_good M c hs]; unfold monopolyBid; rw [if_pos hP]
    have hv : bvec M c s 0 ≤ bvec M c s 1 := by simp [bvec, hBR]
    rw [lowest_two _ hv]
    have h0 : bvec M c s 0 = R + 1 := by simp [bvec, hBR]
    rw [h0, S_zero hacc (by linarith)]
    have hsig : sigma R S c = 0 := by unfold sigma; rw [if_pos hP]
    rw [hsig]
    simp only [ENNReal.ofReal_zero, mul_zero, zero_add, sub_zero, ENNReal.ofReal_one, mul_one]
    congr 1; ring
  · obtain ⟨h1, _⟩ := bid_spec hacc c hP
    have hBeq : Bs M c s = monopolyBid R S c := Bs_good M c hs
    have hpos := lt_of_le_of_ne (P_nonneg hacc c) (Ne.symm hP)
    have hSB : 0 < S (Bs M c s) := by
      rw [hBeq]
      by_contra hle; push_neg at hle
      have h0 := S_nonneg hacc (monopolyBid R S c)
      have : S (monopolyBid R S c) = 0 := le_antisymm hle h0
      rw [this] at h1; simp at h1; linarith
    have hBR : Bs M c s < R + 1 := by
      by_contra hge; push_neg at hge
      have := S_zero hacc (show R < Bs M c s by linarith)
      linarith
    have hv : bvec M c s 0 ≤ bvec M c s 1 := by simp [bvec]; linarith
    rw [lowest_two _ hv]
    have h0 : bvec M c s 0 = Bs M c s := by simp [bvec]
    have hsig : sigma R S c = S (Bs M c s) := by
      unfold sigma; rw [if_neg hP, hBeq]
    have hwc : winnerCost τ x0 = ENNReal.ofReal c := by
      unfold winnerCost
      rw [Fin.sum_univ_two]
      have a0 : τ.select (fun j => (x0 j).2) {0} = 1 := by
        apply sel_one
        intro j hj
        have : j = 1 := by fin_cases j <;> simp_all
        subst this
        show bvec M c s 0 < bvec M c s 1
        simp [bvec]; linarith
      have a1 : τ.select (fun j => (x0 j).2) {1} = 0 := by
        apply sel_zero
        refine ⟨0, ?_⟩
        show bvec M c s 0 < bvec M c s 1
        simp [bvec]; linarith
      rw [a0, a1]
      simp [x0, cv]
    rw [hwc, h0, hsig]
    have hS1 := S_le_one hacc (Bs M c s)
    have hS0 := S_nonneg hacc (Bs M c s)
    rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add
      (mul_nonneg hc0 hS0) (mul_nonneg (by linarith) (by linarith))]
    congr 1; ring


lemma optimal_Dm (c : ℝ) (hc : c ∈ Icc 1 R) : optimalSocialCost (Dm R c) = ENNReal.ofReal c := by
  haveI : IsProbabilityMeasure (typeLaw (Dm R c)) := by unfold typeLaw; infer_instance
  unfold optimalSocialCost
  have hae := ae_pi_dirac (Dm R c).law (cv R c) (fun j => rfl)
  have : ∀ᵐ x ∂(typeLaw (Dm R c)), ENNReal.ofReal (lowest x) = ENNReal.ofReal c := by
    filter_upwards [hae] with x hx
    rw [hx, lowest_two _ (by simp [cv, hc.2])]
    simp [cv]
  rw [lintegral_congr_ae this]
  simp

end ProcurementPoA.DeterministicCap.Supplement.Dev.M5C

namespace ProcurementPoA.DeterministicCap.Supplement


open Dev.M5C Dev.M5B Dev.A1 in
theorem chk_lemma_5_5 (R : ℝ) (hR : 1 ≤ R) {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) (c : ℝ) (hc : c ∈ Set.Icc 1 R) :
    ENNReal.ofReal 1 + ENNReal.ofReal ((R - c) / c) *
      (∫⁻ s, ENNReal.ofReal (1 - sigma R (signalAcceptance M s) c) ∂M.signalLaw) ≤
    mechanismPoA M := by
  have hc0 : 0 < c := by linarith [hc.1]
  have hbne : IsMechanismBNE M (Dm R c) (tie 1) (prof M c) := by
    filter_upwards [M.bounded] with s hs
    exact slice_BNE M c hc.2 hs (tie 1)
  have hcost : InCostInterval (Dm R c) 1 R := by
    intro i x hx
    simp only [Dm, deterministicTypes, Set.mem_singleton_iff] at hx
    subst hx
    by_cases hi : i = 0
    · simp only [cv, hi, if_true]; exact hc
    · simp only [cv, hi, if_false]; exact ⟨hR, le_rfl⟩
  set I := ∫⁻ s, ENNReal.ofReal (1 - sigma R (signalAcceptance M s) c) ∂M.signalLaw with hI
  have hSC : mechanismSocialCost M (Dm R c) (tie 1) (prof M c) =
      ENNReal.ofReal c + ENNReal.ofReal (R - c) * I := by
    unfold mechanismSocialCost
    have : ∀ᵐ s ∂M.signalLaw, acceptSocialCost (Dm R c) (tie 1) (sliceProfile (prof M c) s) R
        (signalAcceptance M s) = ENNReal.ofReal c + ENNReal.ofReal (R - c) *
          ENNReal.ofReal (1 - sigma R (signalAcceptance M s) c) := by
      filter_upwards [M.bounded] with s hs
      rw [slice_cost M c hc hs (tie 1)]
      have hacc := isAcc_of_good M hs
      have h1 := sigma_le_one hacc c
      have h0 := sigma_nonneg hacc c
      rw [← ENNReal.ofReal_mul (by linarith [hc.2]), ← ENNReal.ofReal_add hc0.le
        (mul_nonneg (by linarith [hc.2]) (by linarith))]
    rw [lintegral_congr_ae this, lintegral_add_left measurable_const,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const, measure_univ, mul_one]
  have hq : mechanismSocialCost M (Dm R c) (tie 1) (prof M c) / optimalSocialCost (Dm R c) =
      ENNReal.ofReal 1 + ENNReal.ofReal ((R - c) / c) * I := by
    rw [hSC, optimal_Dm c hc, ENNReal.add_div, ENNReal.div_self (by simpa using hc0) ENNReal.ofReal_ne_top,
      ENNReal.mul_div_right_comm, ← ENNReal.ofReal_div_of_pos hc0]
    simp
  rw [← hq]
  unfold mechanismPoA
  exact le_sSup ⟨1, Dm R c, tie 1, prof M c, hcost, hbne, rfl⟩

end ProcurementPoA.DeterministicCap.Supplement
end

theorem solution : type_of% @ProcurementPoA.DeterministicCap.Supplement.chk_lemma_5_5 := @ProcurementPoA.DeterministicCap.Supplement.chk_lemma_5_5
