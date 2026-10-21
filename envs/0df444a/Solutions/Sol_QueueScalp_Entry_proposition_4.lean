-- Prove2me | solution 1 for QueueScalp.Entry.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:11:48.394055+00:00
-- url     : https://prove2.me/submissions/f62c4c9e-8268-4091-ae54-5526b8838a9f

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model
import Theorems.Thm_QueueScalp_Entry_optimal_revenue
import Theorems.Thm_QueueScalp_Entry_proposition_3
import Theorems.Thm_QueueScalp_Entry_revenue_limits

open QueueScalp.Entry Filter Topology

namespace QSProp4Aux

lemma optRev_unique {P : Params} {Lam R R' : ℝ} (h : IsOptRevenue P Lam R)
    (h' : IsOptRevenue P Lam R') : R = R' := by
  obtain ⟨⟨p, l, q, c, t, hp, he, hR⟩, hb⟩ := h
  obtain ⟨⟨p', l', q', c', t', hp', he', hR'⟩, hb'⟩ := h'
  have h1 := hb p' l' q' c' t' hp' he'
  have h2 := hb' p l q c t hp he
  linarith

noncomputable def c1 (P : Params) (L : ℝ) : ℝ :=
  (P.mu - Real.sqrt (P.mu ^ 2 - L * 1 * P.mu)) / L

noncomputable def f1 (P : Params) (L : ℝ) : ℝ :=
  L ^ 3 * c1 P L * (1 - c1 P L) / (P.mu ^ 2 * (P.mu - L * c1 P L))

noncomputable def f2 (P : Params) (L : ℝ) : ℝ :=
  L * P.V ^ 2 *
    (-Real.sqrt (P.mu ^ 2 * (L * P.V + 1)) + L * P.mu * P.V + P.mu) *
    (Real.sqrt (P.mu ^ 2 * (L * P.V + 1)) - P.mu) /
    ((L * P.V + 1) ^ 3 * Real.sqrt (P.mu ^ 2 * (L * P.V + 1)))

lemma Pi_left (P : Params) (L : ℝ) (h : L ≤ P.mu - 1 / P.V) : PiStar P L = f1 P L := by
  simp only [PiStar, ctStar, cSOf, if_pos h, f1, c1]

lemma Pi_right (P : Params) (L : ℝ) (h : ¬ L ≤ P.mu - 1 / P.V) : PiStar P L = f2 P L := by
  simp only [PiStar, if_neg h, f2]

lemma c1_aux (P : Params) (L : ℝ) (hL0 : 0 < L) :
    P.mu - L * c1 P L = Real.sqrt (P.mu ^ 2 - L * 1 * P.mu) := by
  unfold c1; field_simp; ring

lemma f1_cont (P : Params) (hS : P.Standing) (L : ℝ) (hL0 : 0 < L) (hLmu : L < P.mu) :
    ContinuousAt (f1 P) L := by
  obtain ⟨hmu, -, -⟩ := hS
  have hc : ContinuousAt (c1 P) L := by
    unfold c1
    exact ((continuousAt_const.sub
      ((continuousAt_const.sub ((continuousAt_id.mul continuousAt_const).mul
        continuousAt_const)).sqrt)).div continuousAt_id hL0.ne')
  have hpos : 0 < P.mu ^ 2 - L * 1 * P.mu := by nlinarith
  apply ContinuousAt.div
  · exact ((continuousAt_id.pow 3).mul hc).mul (continuousAt_const.sub hc)
  · exact continuousAt_const.mul (continuousAt_const.sub (continuousAt_id.mul hc))
  · rw [c1_aux P L hL0]
    have := Real.sqrt_pos.2 hpos
    positivity

lemma f2_cont (P : Params) (hS : P.Standing) (L : ℝ) (hL : 0 < L * P.V + 1) :
    ContinuousAt (f2 P) L := by
  obtain ⟨hmu, -, -⟩ := hS
  have hsq : ContinuousAt (fun L : ℝ => Real.sqrt (P.mu ^ 2 * (L * P.V + 1))) L :=
    (continuousAt_const.mul ((continuousAt_id.mul continuousAt_const).add
      continuousAt_const)).sqrt
  have hlin : ContinuousAt (fun L : ℝ => L * P.V + 1) L :=
    (continuousAt_id.mul continuousAt_const).add continuousAt_const
  apply ContinuousAt.div
  · exact (((continuousAt_id.mul continuousAt_const).mul
      ((hsq.neg.add ((continuousAt_id.mul continuousAt_const).mul continuousAt_const)).add
        continuousAt_const))).mul (hsq.sub continuousAt_const)
  · exact (hlin.pow 3).mul hsq
  · have : 0 < Real.sqrt (P.mu ^ 2 * (L * P.V + 1)) := Real.sqrt_pos.2 (by positivity)
    positivity

lemma agree (P : Params) (hS : P.Standing) :
    f1 P (P.mu - 1 / P.V) = f2 P (P.mu - 1 / P.V) := by
  obtain ⟨hmu, hV, -⟩ := hS
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hmV : 1 < P.mu * P.V := by
    have := (div_lt_iff₀ hmu).1 hV; linarith
  set s := Real.sqrt (P.mu * P.V) with hs_def
  have hs2 : s ^ 2 = P.mu * P.V := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : 1 < s := by nlinarith
  have hmu' : P.mu = s ^ 2 / P.V := by field_simp; linarith
  have e1 : Real.sqrt (P.mu ^ 2 - (P.mu - 1 / P.V) * 1 * P.mu) = s / P.V := by
    have : P.mu ^ 2 - (P.mu - 1 / P.V) * 1 * P.mu = (s / P.V) ^ 2 := by
      rw [div_pow, hs2]; field_simp; ring
    rw [this, Real.sqrt_sq (by positivity)]
  have e2 : Real.sqrt (P.mu ^ 2 * ((P.mu - 1 / P.V) * P.V + 1)) = P.mu * s := by
    have : P.mu ^ 2 * ((P.mu - 1 / P.V) * P.V + 1) = (P.mu * s) ^ 2 := by
      rw [mul_pow, hs2]; field_simp; ring
    rw [this, Real.sqrt_sq (by positivity)]
  unfold f1 c1 f2
  rw [e1, e2, hmu']
  have hs1' : s - 1 ≠ 0 := by linarith
  have hs1'' : s + 1 ≠ 0 := by linarith
  have hs0' : s ≠ 0 := by linarith
  have hV' : P.V ≠ 0 := hV0.ne'
  have hsq1 : s ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

lemma Pi_cont (P : Params) (hS : P.Standing) (L : ℝ) (hL : 0 < L) :
    ContinuousAt (PiStar P) L := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hlt : P.mu - 1 / P.V < P.mu := by have : 0 < 1 / P.V := by positivity
                                         linarith
  rcases lt_trichotomy L (P.mu - 1 / P.V) with h | h | h
  · have hev : f1 P =ᶠ[𝓝 L] PiStar P :=
      Filter.mem_of_superset (Iio_mem_nhds h) fun x hx => (Pi_left P x (le_of_lt hx)).symm
    exact (f1_cont P hS L hL (lt_trans h hlt)).congr hev
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · exact (f1_cont P hS L hL (h ▸ hlt)).continuousWithinAt.congr
        (fun x hx => Pi_left P x (le_trans hx h.le)) (Pi_left P L h.le)
    · have hLV : 0 < L * P.V + 1 := by positivity
      have key : ∀ y ∈ Set.Ici L, PiStar P y = f2 P y := by
        intro y hy
        rcases eq_or_lt_of_le (Set.mem_Ici.1 hy) with h' | h'
        · rw [← h', Pi_left P L h.le, h]; exact agree P hS
        · exact Pi_right P y (by rw [← h]; exact not_le.2 h')
      exact (f2_cont P hS L hLV).continuousWithinAt.congr key (key L (Set.mem_Ici.2 le_rfl))
  · have hLV : 0 < L * P.V + 1 := by positivity
    have hev : f2 P =ᶠ[𝓝 L] PiStar P :=
      Filter.mem_of_superset (Ioi_mem_nhds h) fun x hx => (Pi_right P x (not_le.2 hx)).symm
    exact (f2_cont P hS L hLV).congr hev

end QSProp4Aux

open QSProp4Aux in
theorem solution (P : Params) (hS : P.Standing) (hk : 0 < P.k) :
    ∃ LamLo LamHi : ℝ, LamLo ≤ LamHi ∧
      ∀ Lam : ℝ, 0 < Lam →
        (∃ R, IsOptRevenue P Lam R) ∧
        ∀ R, IsOptRevenue P Lam R →
          ((LamLo < Lam ∧ Lam < LamHi) → entry P R = 1) ∧
          (¬ (LamLo < Lam ∧ Lam < LamHi) → entry P R = 0) := by
  set E : Set ℝ := {L : ℝ | 0 < L ∧ P.k < PiStar P L} with hE
  have hopen : IsOpen E := by
    refine isOpen_iff_mem_nhds.2 fun L hL => ?_
    exact (lt_mem_nhds hL.1).and ((Pi_cont P hS L hL.1).eventually (lt_mem_nhds hL.2))
  obtain ⟨M, hM⟩ : ∃ M, ∀ L ∈ E, L < M := by
    have h := (revenue_limits P hS hk).2
    have hev := h.eventually (gt_mem_nhds (by linarith : -P.k < 0))
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    refine ⟨M, fun L hL => ?_⟩
    by_contra hc
    have := hM L (not_lt.1 hc)
    have := hL.2
    linarith
  obtain ⟨-, hinc, hdec⟩ := (proposition_3 P hS).2
  have hconv : ∀ a b c, a ∈ E → c ∈ E → a < b → b < c → b ∈ E := by
    intro a b c ha hc hab hbc
    refine ⟨lt_trans ha.1 hab, ?_⟩
    by_cases hb : b ≤ LamStar P
    · have := hinc a b _ _ ha.1 hab hb (optimal_revenue P hS a ha.1)
        (optimal_revenue P hS b (lt_trans ha.1 hab))
      linarith [ha.2]
    · have := hdec b c _ _ (not_le.1 hb) hbc
        (optimal_revenue P hS b (lt_trans ha.1 hab))
        (optimal_revenue P hS c (lt_trans (lt_trans ha.1 hab) hbc))
      linarith [hc.2]
  have key : ∃ lo hi : ℝ, lo ≤ hi ∧ ∀ L, 0 < L → (L ∈ E ↔ lo < L ∧ L < hi) := by
    by_cases hne : E.Nonempty
    · have hbb : BddBelow E := ⟨0, fun x hx => hx.1.le⟩
      have hba : BddAbove E := ⟨M, fun x hx => (hM x hx).le⟩
      refine ⟨sInf E, sSup E, csInf_le_csSup hne hbb hba, fun L hL => ⟨fun hLE => ?_, ?_⟩⟩
      · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen L hLE
        have h1 : L - ε / 2 ∈ E := hball (by
          rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
        have h2 : L + ε / 2 ∈ E := hball (by
          rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
        constructor
        · linarith [csInf_le hbb h1]
        · linarith [le_csSup hba h2]
      · rintro ⟨h1, h2⟩
        obtain ⟨a, ha, hal⟩ := exists_lt_of_csInf_lt hne h1
        obtain ⟨c, hc, hcl⟩ := exists_lt_of_lt_csSup hne h2
        exact hconv a L c ha hc hal hcl
    · refine ⟨0, 0, le_rfl, fun L hL => ⟨fun hLE => absurd ⟨L, hLE⟩ hne, ?_⟩⟩
      rintro ⟨h1, h2⟩; linarith
  obtain ⟨lo, hi, hle, hiff⟩ := key
  refine ⟨lo, hi, hle, fun L hL => ⟨⟨_, optimal_revenue P hS L hL⟩, fun R hR => ?_⟩⟩
  have hRe : R = PiStar P L := optRev_unique hR (optimal_revenue P hS L hL)
  subst hRe
  unfold entry
  constructor
  · intro h
    have := ((hiff L hL).2 h).2
    simp [this]
  · intro h
    have : ¬ P.k < PiStar P L := fun h' => h ((hiff L hL).1 ⟨hL, h'⟩)
    simp [this]
