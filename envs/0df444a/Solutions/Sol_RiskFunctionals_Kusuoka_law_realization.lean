-- Prove2me | solution 1 for RiskFunctionals.Kusuoka.law_realization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:23:29.107989+00:00
-- url     : https://prove2.me/submissions/2d7a4b09-2006-4f2c-a274-951f1f763e17

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
open MeasureTheory

noncomputable def g79q_F (μ : Measure ℝ) (u : ℝ) : ℝ := μ.real (Set.Iic u)

noncomputable def g79q_q (μ : Measure ℝ) (p : ℝ) : ℝ := sInf {u : ℝ | p ≤ g79q_F μ u}

theorem g79q_cdf_eq_real (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    ProbabilityTheory.cdf μ v = g79q_F μ v := ProbabilityTheory.cdf_eq_real μ v

theorem g79q_qle (μ : Measure ℝ) [IsProbabilityMeasure μ] (p u : ℝ)
    (hp : 0 < p) (hfin : ∃ v : ℝ, p ≤ g79q_F μ v) :
    g79q_q μ p ≤ u ↔ p ≤ g79q_F μ u := by
  have hF : ∀ v, g79q_F μ v = ProbabilityTheory.cdf μ v := fun v =>
    (g79q_cdf_eq_real μ v).symm
  set S := {u : ℝ | p ≤ g79q_F μ u} with hS
  have hne : S.Nonempty := hfin
  have hbdd : BddBelow S := by
    have h := (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (gt_mem_nhds hp)
    obtain ⟨L, hL⟩ := Filter.eventually_atBot.1 h
    refine ⟨L, fun v hv => ?_⟩
    by_contra hlt
    have := hL v (le_of_lt (lt_of_not_ge hlt))
    have hv' : p ≤ g79q_F μ v := hv
    rw [hF] at hv'
    linarith
  have hmono : Monotone (g79q_F μ) := fun a b hab => by
    rw [hF, hF]; exact (ProbabilityTheory.cdf μ).mono hab
  constructor
  · intro hq
    have hQ : p ≤ g79q_F μ (g79q_q μ p) := by
      have hev : ∀ᶠ v in nhdsWithin (g79q_q μ p) (Set.Ioi (g79q_q μ p)),
          p ≤ ProbabilityTheory.cdf μ v := by
        filter_upwards [self_mem_nhdsWithin] with v hv
        obtain ⟨w, hwS, hwv⟩ := exists_lt_of_csInf_lt hne hv
        have : p ≤ g79q_F μ w := hwS
        rw [← hF]; exact this.trans (hmono hwv.le)
      have ht : Filter.Tendsto (ProbabilityTheory.cdf μ)
          (nhdsWithin (g79q_q μ p) (Set.Ioi (g79q_q μ p)))
          (nhds (ProbabilityTheory.cdf μ (g79q_q μ p))) :=
        ((ProbabilityTheory.cdf μ).right_continuous _).tendsto.mono_left
          (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      rw [hF]
      exact ge_of_tendsto ht hev
    exact hQ.trans (hmono hq)
  · intro hu
    exact csInf_le hbdd hu

theorem g79q_q_nonpos (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : p ≤ 0) :
    g79q_q μ p = 0 := by
  unfold g79q_q
  have : {u : ℝ | p ≤ g79q_F μ u} = Set.univ := by
    ext u
    simp only [Set.mem_univ, iff_true]
    refine le_trans hp ?_
    unfold g79q_F; exact measureReal_nonneg
  rw [this]
  exact Real.sInf_of_not_bddBelow not_bddBelow_univ

theorem g79q_q_nowit (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ)
    (h : ¬ ∃ v, p ≤ g79q_F μ v) : g79q_q μ p = 0 := by
  unfold g79q_q
  have : {u : ℝ | p ≤ g79q_F μ u} = ∅ := by
    ext u; simp only [Set.mem_empty_iff_false, iff_false]; exact fun hu => h ⟨u, hu⟩
  rw [this, Real.sInf_empty]

theorem g79q_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] : Monotone (g79q_F μ) := by
  intro a b hab
  unfold g79q_F
  exact measureReal_mono (Set.Iic_subset_Iic.2 hab)

theorem g79q_meas (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (g79q_q μ) := by
  set A : Set ℝ := Set.Ioi 0 ∩ ⋃ n : ℕ, Set.Iic (g79q_F μ n) with hA
  have hAm : MeasurableSet A :=
    measurableSet_Ioi.inter (MeasurableSet.iUnion (fun _ => measurableSet_Iic))
  have hAiff : ∀ p, p ∈ A ↔ 0 < p ∧ ∃ v, p ≤ g79q_F μ v := by
    intro p
    simp only [hA, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · rintro ⟨h0, n, hn⟩; exact ⟨h0, n, hn⟩
    · rintro ⟨h0, v, hv⟩
      obtain ⟨n, hn⟩ := exists_nat_ge v
      exact ⟨h0, n, hv.trans (g79q_mono μ hn)⟩
  refine measurable_of_Iic (fun x => ?_)
  have : g79q_q μ ⁻¹' Set.Iic x =
      (A ∩ Set.Iic (g79q_F μ x)) ∪ (Aᶜ ∩ {_p | 0 ≤ x}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq]
    by_cases hp : p ∈ A
    · have := (hAiff p).1 hp
      rw [g79q_qle μ p x this.1 this.2]
      simp [hp]
    · have h0 : g79q_q μ p = 0 := by
        by_cases hp0 : p ≤ 0
        · exact g79q_q_nonpos μ p hp0
        · exact g79q_q_nowit μ p (fun hw => hp ((hAiff p).2 ⟨lt_of_not_ge hp0, hw⟩))
      simp [hp, h0]
  rw [this]
  exact (hAm.inter measurableSet_Iic).union (hAm.compl.inter (MeasurableSet.const _))

theorem g79q_transform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U) (hunif : P.map U = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    P.map (fun ω => g79q_q μ (U ω)) = μ := by
  have hf := g79q_meas μ
  have hcomp : P.map (fun ω => g79q_q μ (U ω)) =
      (P.map U).map (g79q_q μ) := by
    rw [Measure.map_map hf hU]; rfl
  rw [hcomp, hunif]
  have hrestr : (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  rw [hrestr]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    constructor; rw [Measure.restrict_apply_univ]; simp
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply hf measurableSet_Iic,
    Measure.restrict_apply (hf measurableSet_Iic)]
  set g := g79q_F μ x with hg
  have hset : g79q_q μ ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 = Set.Iic g ∩ Set.Ioo 0 1 := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h0, h1'⟩
      refine ⟨?_, h0, h1'⟩
      have hw : ∃ v, p ≤ g79q_F μ v := by
        have hlim : Filter.Tendsto (g79q_F μ) Filter.atTop (nhds 1) := by
          have := ProbabilityTheory.tendsto_cdf_atTop μ
          refine this.congr (fun v => ?_)
          exact g79q_cdf_eq_real μ v
        obtain ⟨v, hv⟩ := (hlim.eventually (lt_mem_nhds h1')).exists
        exact ⟨v, hv.le⟩
      exact (g79q_qle μ p x h0 hw).1 h1
    · rintro ⟨h1, h0, h1'⟩
      exact ⟨(g79q_qle μ p x h0 ⟨x, h1⟩).2 h1, h0, h1'⟩
  rw [hset]
  have hg0 : 0 ≤ g := measureReal_nonneg
  have hg1 : g ≤ 1 := by
    rw [hg]; unfold g79q_F; exact measureReal_le_one
  have hμx : μ (Set.Iic x) = ENNReal.ofReal g := by
    rw [hg]; unfold g79q_F
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hμx]
  apply le_antisymm
  · calc volume (Set.Iic g ∩ Set.Ioo 0 1) ≤ volume (Set.Ioc 0 g) := by
          apply measure_mono
          rintro p ⟨h1, h0, -⟩; exact ⟨h0, h1⟩
      _ = ENNReal.ofReal g := by simp
  · calc ENNReal.ofReal g = volume (Set.Ioo 0 g) := by simp
      _ ≤ volume (Set.Iic g ∩ Set.Ioo 0 1) := by
          apply measure_mono
          rintro p ⟨h0, h1⟩; exact ⟨h1.le, h0, lt_of_lt_of_le h1 hg1⟩



open MeasureTheory ProbabilityTheory Set Filter Topology

namespace KU82

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- one halving step: a non-null set contains a non-null subset of at most half its mass -/
theorem half (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {A : Set Ω} (hA : MeasurableSet A)
    (hpos : 0 < P.real A) : ∃ B ⊆ A, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ P.real A / 2 := by
  have hna := hP A
  simp only [RiskFunctionals.Kusuoka.IsAtomOf, not_and, not_forall, not_or] at hna
  have hpos' : 0 < P A := by
    rw [measureReal_def] at hpos; exact pos_of_ne_zero (fun h => by simp [h] at hpos)
  obtain ⟨A', hA'A, hA'm, hne1, hne0⟩ := hna hA hpos'
  have hr1 : P.real A' ≠ P.real A := fun h => hne1 (by
    rw [measureReal_def, measureReal_def] at h
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h)
  have hr0 : P.real A' ≠ 0 := fun h => hne0 (by
    rw [measureReal_def] at h
    exact (ENNReal.toReal_eq_zero_iff _).1 h |>.resolve_right (measure_ne_top _ _))
  have hle : P.real A' ≤ P.real A := measureReal_mono hA'A
  have hlt : P.real A' < P.real A := lt_of_le_of_ne hle hr1
  have h0 : 0 < P.real A' := lt_of_le_of_ne measureReal_nonneg (Ne.symm hr0)
  have hdiff : P.real (A \ A') = P.real A - P.real A' := measureReal_diff hA'A hA'm
  rcases le_or_gt (P.real A') (P.real A / 2) with h | h
  · exact ⟨A', hA'A, hA'm, h0, h⟩
  · refine ⟨A \ A', diff_subset, hA.diff hA'm, ?_, ?_⟩ <;> rw [hdiff] <;> linarith

theorem small (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {A : Set Ω} (hA : MeasurableSet A)
    (hpos : 0 < P.real A) (n : ℕ) :
    ∃ B ⊆ A, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ P.real A / 2 ^ n := by
  induction n with
  | zero => exact ⟨A, subset_rfl, hA, hpos, by simp⟩
  | succ n ih =>
    obtain ⟨B, hBA, hBm, hB0, hBle⟩ := ih
    obtain ⟨C, hCB, hCm, hC0, hCle⟩ := half P hP hBm hB0
    refine ⟨C, hCB.trans hBA, hCm, hC0, ?_⟩
    rw [pow_succ]
    calc P.real C ≤ P.real B / 2 := hCle
      _ ≤ P.real A / 2 ^ n / 2 := by linarith
      _ = _ := by ring

theorem small_eps (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {A : Set Ω} (hA : MeasurableSet A)
    (hpos : 0 < P.real A) {ε : ℝ} (hε : 0 < ε) :
    ∃ B ⊆ A, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith [measureReal_le_one (μ := P) (s := A)] : (0:ℝ) < 2)) (by norm_num : (1/2:ℝ) < 1)
  obtain ⟨B, hBA, hBm, hB0, hBle⟩ := small P hP hA hpos n
  refine ⟨B, hBA, hBm, hB0, hBle.trans ?_⟩
  have h1 : P.real A ≤ 1 := measureReal_le_one
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ h2]
  have : (1/2:ℝ)^n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  nlinarith

/-- admissible increments -/
def Adm (A B : Set Ω) (t : ℝ) (C : Set Ω) : Prop :=
  C ⊆ A \ B ∧ MeasurableSet C ∧ P.real B + P.real C ≤ t

theorem exists_greedy (A B : Set Ω) (t : ℝ) (hB : P.real B ≤ t) :
    ∃ C, Adm P A B t C ∧ ∀ C', Adm P A B t C' → P.real C' ≤ 2 * P.real C := by
  set S := {x | ∃ C, Adm P A B t C ∧ x = P.real C}
  have hne : S.Nonempty := ⟨0, ∅, ⟨empty_subset _, MeasurableSet.empty, by simpa using hB⟩, by simp⟩
  have hbdd : BddAbove S := ⟨1, by rintro x ⟨C, -, rfl⟩; exact measureReal_le_one⟩
  rcases le_or_gt (sSup S) 0 with h0 | h0
  · refine ⟨∅, ⟨empty_subset _, MeasurableSet.empty, by simpa using hB⟩, fun C' hC' => ?_⟩
    have := le_csSup hbdd ⟨C', hC', rfl⟩
    simp only [measureReal_empty, mul_zero]; linarith
  · obtain ⟨x, ⟨C, hC, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hne (half_lt_self h0)
    refine ⟨C, hC, fun C' hC' => ?_⟩
    have := le_csSup hbdd ⟨C', hC', rfl⟩
    linarith

open scoped Classical in
/-- the greedy step -/
noncomputable def nxt (A : Set Ω) (t : ℝ) (B : Set Ω) : Set Ω :=
  B ∪ (if h : ∃ C, Adm P A B t C ∧ ∀ C', Adm P A B t C' → P.real C' ≤ 2 * P.real C
    then h.choose else ∅)

noncomputable def gseq (A : Set Ω) (t : ℝ) : ℕ → Set Ω
  | 0 => ∅
  | n + 1 => nxt P A t (gseq A t n)

theorem seq_inv (A : Set Ω) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    gseq P A t n ⊆ A ∧ MeasurableSet (gseq P A t n) ∧ P.real (gseq P A t n) ≤ t := by
  induction n with
  | zero => exact ⟨empty_subset _, MeasurableSet.empty, by simpa [gseq] using ht⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hex := exists_greedy P A (gseq P A t n) t h3
    simp only [gseq, nxt, dif_pos hex]
    obtain ⟨⟨hCs, hCm, hCt⟩, -⟩ := hex.choose_spec
    refine ⟨union_subset h1 (hCs.trans diff_subset), h2.union hCm, ?_⟩
    exact (measureReal_union_le _ _).trans hCt

theorem seq_step (A : Set Ω) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    ∃ C, gseq P A t (n + 1) = gseq P A t n ∪ C ∧ Adm P A (gseq P A t n) t C ∧
      ∀ C', Adm P A (gseq P A t n) t C' → P.real C' ≤ 2 * P.real C := by
  have hex := exists_greedy P A (gseq P A t n) t (seq_inv P A t ht n).2.2
  refine ⟨hex.choose, ?_, hex.choose_spec⟩
  simp only [gseq, nxt, dif_pos hex]

/-- Sierpiński: a non-atomic probability takes every intermediate value on subsets. -/
theorem sierpinski (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {A : Set Ω} (hA : MeasurableSet A)
    {t : ℝ} (ht0 : 0 ≤ t) (htA : t ≤ P.real A) :
    ∃ B ⊆ A, MeasurableSet B ∧ P.real B = t := by
  set Bn := gseq P A t
  have hinv := seq_inv P A t ht0
  have hmono : Monotone Bn := monotone_nat_of_le_succ fun n => by
    obtain ⟨C, hC, -⟩ := seq_step P A t ht0 n
    show gseq P A t n ⊆ gseq P A t (n+1)
    rw [hC]; exact subset_union_left
  set B := ⋃ n, Bn n
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun n => (hinv n).2.1
  have hBA : B ⊆ A := iUnion_subset fun n => (hinv n).1
  have hlim : Tendsto (fun n => P.real (Bn n)) atTop (𝓝 (P.real B)) := by
    have := tendsto_measure_iUnion_atTop (μ := P) hmono
    have h2 := (ENNReal.tendsto_toReal (measure_ne_top P B)).comp this
    simpa [measureReal_def, Function.comp_def] using h2
  have hBt : P.real B ≤ t := le_of_tendsto' hlim fun n => (hinv n).2.2
  refine ⟨B, hBA, hBm, le_antisymm hBt ?_⟩
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hD : 0 < P.real (A \ B) := by
    rw [measureReal_diff hBA hBm]; linarith
  obtain ⟨C, hCD, hCm, hC0, hCle⟩ := small_eps P hP (hA.diff hBm) hD (sub_pos.2 hlt)
  -- increments tend to zero
  have hinc : ∀ n, ∃ Cn, P.real (Bn (n+1)) = P.real (Bn n) + P.real Cn ∧ P.real C ≤ 2 * P.real Cn := by
    intro n
    obtain ⟨Cn, hCn, ⟨hCs, hCnm, -⟩, hgr⟩ := seq_step P A t ht0 n
    refine ⟨Cn, ?_, hgr C ⟨fun x hx => ⟨(hCD hx).1, fun hxB => (hCD hx).2
      (mem_iUnion.2 ⟨n, hxB⟩)⟩, hCm, ?_⟩⟩
    · show P.real (gseq P A t (n+1)) = P.real (gseq P A t n) + _
      rw [hCn, measureReal_union (disjoint_left.2 fun x hx hx' => (hCs hx').2 hx) hCnm]
    · have : P.real (Bn n) ≤ P.real B := measureReal_mono (subset_iUnion Bn n)
      linarith
  have hdiff : Tendsto (fun n => P.real (Bn (n+1)) - P.real (Bn n)) atTop (𝓝 0) := by
    have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    simpa using this
  have hev := (hdiff.eventually (gt_mem_nhds (half_pos hC0))).exists
  obtain ⟨n, hn⟩ := hev
  obtain ⟨Cn, h1, h2⟩ := hinc n
  linarith

end KU82


open MeasureTheory ProbabilityTheory Set Filter Topology

namespace KU82

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

open scoped Classical in
noncomputable def between (B C : Set Ω) (t : ℝ) : Set Ω :=
  if h : ∃ D, B ⊆ D ∧ D ⊆ C ∧ MeasurableSet D ∧ P.real D = t then h.choose else ∅

theorem between_spec (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {B C : Set Ω}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : B ⊆ C) {t : ℝ}
    (h1 : P.real B ≤ t) (h2 : t ≤ P.real C) :
    B ⊆ between P B C t ∧ between P B C t ⊆ C ∧ MeasurableSet (between P B C t) ∧
      P.real (between P B C t) = t := by
  have hex : ∃ D, B ⊆ D ∧ D ⊆ C ∧ MeasurableSet D ∧ P.real D = t := by
    obtain ⟨E, hE, hEm, hEt⟩ := sierpinski P hP (hC.diff hB) (t := t - P.real B) (by linarith)
      (by rw [measureReal_diff hBC hB]; linarith)
    refine ⟨B ∪ E, subset_union_left, union_subset hBC (hE.trans diff_subset), hB.union hEm, ?_⟩
    rw [measureReal_union (disjoint_left.2 fun x hx hx' => (hE hx').2 hx) hEm, hEt]; ring
  simp only [between, dif_pos hex]; exact hex.choose_spec

noncomputable def dy : ℕ → ℕ → Set Ω
  | 0, k => if k = 0 then ∅ else univ
  | n + 1, k => if k % 2 = 0 then dy n (k / 2) else
      between P (dy n (k / 2)) (dy n (k / 2 + 1)) (min ((k : ℝ) / 2 ^ (n + 1)) 1)

theorem dy_even (n j : ℕ) : dy P (n + 1) (2 * j) = dy P n j := by
  simp only [dy, show 2 * j % 2 = 0 by omega, if_true, show 2 * j / 2 = j by omega]

theorem dy_odd (n j : ℕ) : dy P (n + 1) (2 * j + 1) =
    between P (dy P n j) (dy P n (j + 1)) (min (((2 * j + 1 : ℕ) : ℝ) / 2 ^ (n + 1)) 1) := by
  simp only [dy, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]
  rfl

theorem dy_inv (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (n : ℕ) :
    (∀ k, MeasurableSet (dy P n k) ∧ P.real (dy P n k) = min ((k : ℝ) / 2 ^ n) 1) ∧
      ∀ k, dy P n k ⊆ dy P n (k + 1) := by
  induction n with
  | zero =>
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [dy]
      · simp only [dy, Nat.pos_iff_ne_zero.1 hk, if_false, MeasurableSet.univ, true_and,
          probReal_univ, pow_zero, div_one]
        have : (1:ℝ) ≤ k := by exact_mod_cast hk
        rw [min_eq_right this]
    · simp only [dy, Nat.succ_ne_zero, if_false]; split_ifs <;> simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpow : (2:ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hp : (0:ℝ) < 2 ^ n := by positivity
    have hodd : ∀ j, dy P n j ⊆ dy P (n + 1) (2 * j + 1) ∧ dy P (n + 1) (2 * j + 1) ⊆ dy P n (j + 1) ∧
        MeasurableSet (dy P (n + 1) (2 * j + 1)) ∧
        P.real (dy P (n + 1) (2 * j + 1)) = min ((((2 * j + 1 : ℕ)) : ℝ) / 2 ^ (n + 1)) 1 := by
      intro j
      rw [dy_odd]
      refine between_spec P hP (ih1 j).1 (ih1 (j + 1)).1 (ih2 j) ?_ ?_
      · rw [(ih1 j).2]; apply min_le_min_right
        rw [hpow, div_le_div_iff₀ hp (by positivity)]; push_cast; nlinarith
      · rw [(ih1 (j + 1)).2]; apply min_le_min_right
        rw [hpow, div_le_div_iff₀ (by positivity) hp]; push_cast; nlinarith
    refine ⟨fun k => ?_, fun k => ?_⟩
    · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [dy_even]; refine ⟨(ih1 j).1, ?_⟩
        rw [(ih1 j).2, hpow]; push_cast
        rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
      · exact ⟨(hodd j).2.2.1, (hodd j).2.2.2⟩
    · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [dy_even]; exact (hodd j).1
      · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, dy_even]; exact (hodd j).2.1

theorem dy_lift (n k i : ℕ) : dy P (n + i) (k * 2 ^ i) = dy P n k := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc, show k * 2 ^ (i + 1) = 2 * (k * 2 ^ i) by ring, dy_even, ih]

theorem dy_sub (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {n m k k' : ℕ}
    (h : (k : ℝ) / 2 ^ n ≤ (k' : ℝ) / 2 ^ m) : dy P n k ⊆ dy P m k' := by
  have hmono : Monotone (dy P (n + m)) := monotone_nat_of_le_succ (dy_inv P hP (n + m)).2
  have hle : k * 2 ^ m ≤ k' * 2 ^ n := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
    exact_mod_cast h
  rw [← dy_lift P n k m, ← dy_lift P m k' n, add_comm m n]
  exact hmono hle

/-- the uniform variable -/
noncomputable def U (ω : Ω) : ℝ := sInf {x | ∃ n k, ω ∈ dy P n k ∧ x = (k : ℝ) / 2 ^ n}

theorem U_lt (ω : Ω) (x : ℝ) : U P ω < x ↔ ∃ n k, ω ∈ dy P n k ∧ (k : ℝ) / 2 ^ n < x := by
  have hne : {x | ∃ n k, ω ∈ dy P n k ∧ x = (k : ℝ) / 2 ^ n}.Nonempty :=
    ⟨1, 0, 1, by simp [dy], by norm_num⟩
  have hbdd : BddBelow {x | ∃ n k, ω ∈ dy P n k ∧ x = (k : ℝ) / 2 ^ n} :=
    ⟨0, by rintro _ ⟨n, k, -, rfl⟩; positivity⟩
  rw [U, csInf_lt_iff hbdd hne]
  constructor
  · rintro ⟨_, ⟨n, k, h, rfl⟩, hlt⟩; exact ⟨n, k, h, hlt⟩
  · rintro ⟨n, k, h, hlt⟩; exact ⟨_, ⟨n, k, h, rfl⟩, hlt⟩

theorem U_set (x : ℝ) : {ω | U P ω < x} =
    ⋃ n, ⋃ k, dy P n k ∩ {_ω | (k : ℝ) / 2 ^ n < x} := by
  ext ω; simp only [mem_setOf_eq, U_lt, mem_iUnion, mem_inter_iff]

theorem U_meas (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) : Measurable (U P) := by
  refine measurable_of_Iio fun x => ?_
  change MeasurableSet {ω | U P ω < x}
  rw [U_set]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k =>
    ((dy_inv P hP n).1 k).1.inter (MeasurableSet.const _)

theorem U_lo (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {x : ℝ} {n k : ℕ}
    (h : (k : ℝ) / 2 ^ n < x) : dy P n k ⊆ {ω | U P ω < x} :=
  fun ω hω => (U_lt P ω x).2 ⟨n, k, hω, h⟩

theorem U_hi (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {x : ℝ} {N k : ℕ}
    (h : x ≤ (k : ℝ) / 2 ^ N) : {ω | U P ω < x} ⊆ dy P N k := by
  intro ω hω
  obtain ⟨n, k', hω', hlt⟩ := (U_lt P ω x).1 hω
  exact dy_sub P hP (hlt.le.trans h) hω'

theorem U_prob_lt (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (x : ℝ) :
    P.real {ω | U P ω < x} = max 0 (min x 1) := by
  rcases le_or_gt x 0 with hx0 | hx0
  · have : {ω | U P ω < x} = ∅ := by
      apply subset_eq_empty (U_hi P hP (N := 0) (k := 0) (by simpa using hx0))
      simp [dy]
    rw [this, measureReal_empty, max_eq_left (min_le_of_left_le hx0)]
  rcases lt_or_ge 1 x with hx1 | hx1
  · have : {ω | U P ω < x} = univ :=
      univ_subset_iff.1 (by
        have := U_lo P hP (n := 0) (k := 1) (x := x) (by simpa using hx1)
        simpa [dy] using this)
    rw [this, probReal_univ, min_eq_right hx1.le, max_eq_right zero_le_one]
  rw [min_eq_left hx1, max_eq_right hx0.le]
  have hinv := dy_inv P hP
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ) < 1)
    have hy : 0 ≤ x * 2 ^ N := by positivity
    have hk := Nat.ceil_lt_add_one hy
    have hk' := Nat.le_ceil (x * 2 ^ N)
    have h2 : (0:ℝ) < 2 ^ N := by positivity
    have hinvN : (1/2:ℝ) ^ N = 1 / 2 ^ N := by rw [div_pow, one_pow]
    calc P.real {ω | U P ω < x} ≤ P.real (dy P N ⌈x * 2 ^ N⌉₊) :=
          measureReal_mono (U_hi P hP (by rw [le_div_iff₀ h2]; exact hk'))
      _ = min ((⌈x * 2 ^ N⌉₊ : ℝ) / 2 ^ N) 1 := ((hinv N).1 _).2
      _ ≤ (⌈x * 2 ^ N⌉₊ : ℝ) / 2 ^ N := min_le_left _ _
      _ ≤ x + ε := by
          rw [div_le_iff₀ h2]
          have : 1 < ε * 2 ^ N := by
            rw [hinvN, div_lt_iff₀ h2] at hN; linarith
          nlinarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ) < 1)
    have h2 : (0:ℝ) < 2 ^ N := by positivity
    have hy : 0 < x * 2 ^ N := by positivity
    have hk := Nat.ceil_lt_add_one hy.le
    have hk' := Nat.le_ceil (x * 2 ^ N)
    have hk1 : 1 ≤ ⌈x * 2 ^ N⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hy).ne'
    have hinvN : (1/2:ℝ) ^ N = 1 / 2 ^ N := by rw [div_pow, one_pow]
    have hcast : ((⌈x * 2 ^ N⌉₊ - 1 : ℕ) : ℝ) = (⌈x * 2 ^ N⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hk1, Nat.cast_one]
    have hlt : ((⌈x * 2 ^ N⌉₊ - 1 : ℕ) : ℝ) / 2 ^ N < x := by
      rw [div_lt_iff₀ h2, hcast]; linarith
    have hmeas := ((hinv N).1 (⌈x * 2 ^ N⌉₊ - 1)).2
    have hle1 : ((⌈x * 2 ^ N⌉₊ - 1 : ℕ) : ℝ) / 2 ^ N ≤ 1 := hlt.le.trans hx1
    have := measureReal_mono (μ := P) (U_lo P hP hlt)
    rw [hmeas, min_eq_left hle1] at this
    have : 1 < ε * 2 ^ N := by
      rw [hinvN, div_lt_iff₀ h2] at hN; linarith
    have h3 : x ≤ ((⌈x * 2 ^ N⌉₊ - 1 : ℕ) : ℝ) / 2 ^ N + ε := by
      rw [hcast, div_add' _ _ _ h2.ne', le_div_iff₀ h2]; nlinarith
    linarith

theorem U_unif (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) :
    P.map (U P) = volume.restrict (Icc (0:ℝ) 1) := by
  have hm := U_meas P hP
  set Φ : ℝ → ℝ := fun x => max 0 (min x 1)
  have hΦ : ∀ x, P.real {ω | U P ω < x} = Φ x := U_prob_lt P hP
  have hΦle : ∀ x, P.real {ω | U P ω ≤ x} = Φ x := by
    intro x
    apply le_antisymm
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      calc P.real {ω | U P ω ≤ x} ≤ P.real {ω | U P ω < x + ε} :=
            measureReal_mono fun ω (h : U P ω ≤ x) => show U P ω < x + ε by linarith
        _ = Φ (x + ε) := hΦ _
        _ ≤ Φ x + ε := by
            simp only [Φ]
            have h1 : min (x + ε) 1 ≤ min x 1 + ε := by
              rcases le_total x 1 with h | h
              · rw [min_eq_left h]; exact min_le_left _ _
              · rw [min_eq_right h]; linarith [min_le_right (x + ε) 1]
            exact max_le (by linarith [le_max_left 0 (min x 1)])
              (by linarith [le_max_right 0 (min x 1)])
    · rw [← hΦ]; exact measureReal_mono fun ω (h : U P ω < x) => show U P ω ≤ x from h.le
  haveI : IsProbabilityMeasure (P.map (U P)) := Measure.isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  have hL : P (U P ⁻¹' Iic x) = ENNReal.ofReal (Φ x) := by
    rw [← hΦle x, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]; rfl
  rw [hL]
  rcases lt_or_ge x 0 with hx | hx
  · have : Iic x ∩ Icc (0:ℝ) 1 = ∅ := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩; linarith
    rw [this, measure_empty]; simp only [Φ]
    rw [min_eq_left (by linarith), max_eq_left hx.le, ENNReal.ofReal_zero]
  rcases le_or_gt x 1 with hx1 | hx1
  · have : Iic x ∩ Icc (0:ℝ) 1 = Icc 0 x := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [this, Real.volume_Icc, sub_zero]; simp only [Φ]
    rw [min_eq_left hx1, max_eq_right hx]
  · have : Iic x ∩ Icc (0:ℝ) 1 = Icc 0 1 := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨h1', h2⟩; exact ⟨by linarith, h1', h2⟩
    rw [this, Real.volume_Icc]; simp only [Φ]
    rw [min_eq_right hx1.le, max_eq_right zero_le_one]; simp

end KU82


open MeasureTheory ProbabilityTheory Set Filter Topology RiskFunctionals.Kusuoka

theorem solution {X : Type*} [MetricSpace X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsNonAtomic P) :
    ∃ Y : Ω → X, Measurable Y ∧ P.map Y = μ := by
  haveI : PolishSpace X := inferInstance
  haveI : StandardBorelSpace X := inferInstance
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure μ
  set e := MeasureTheory.embeddingReal X
  have he : MeasurableEmbedding e := MeasureTheory.measurableEmbedding_embeddingReal X
  obtain ⟨g, hg, hge⟩ := he.exists_measurable_extend (g := id) measurable_id (fun _ => inferInstance)
  set ν := μ.map e
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  have hU := KU82.U_meas P hP
  have hZ : P.map (fun ω => g79q_q ν (KU82.U P ω)) = ν :=
    g79q_transform ν P (KU82.U P) hU (KU82.U_unif P hP)
  have hZm : Measurable (fun ω => g79q_q ν (KU82.U P ω)) := (g79q_meas ν).comp hU
  refine ⟨fun ω => g (g79q_q ν (KU82.U P ω)), hg.comp hZm, ?_⟩
  rw [show (fun ω => g (g79q_q ν (KU82.U P ω))) = g ∘ (fun ω => g79q_q ν (KU82.U P ω)) from rfl,
    ← Measure.map_map hg hZm, hZ, Measure.map_map hg he.measurable, hge,
    Measure.map_id]

