-- Prove2me | solution 1 for TailRiskSharing.VaRConv.theorem1_var_inf_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T13:46:40.168853+00:00
-- url     : https://prove2.me/submissions/b10ab3c2-3a1d-47ab-9cd7-1c677f5f355e

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace TRS70

open TailRiskSharing.VaRConv

variable {Ω : Type*} [MeasurableSpace Ω]

section Sierp

variable (P : Measure Ω) [IsProbabilityMeasure P]

lemma real_le_one (s : Set Ω) : P.real s ≤ 1 := by
  calc P.real s ≤ P.real univ := measureReal_mono (subset_univ s)
    _ = 1 := probReal_univ

lemma small_piece_pow (hP : IsAtomless P) {S : Set Ω} (hS : MeasurableSet S) (hpos : 0 < P S)
    (k : ℕ) : ∃ T ⊆ S, MeasurableSet T ∧ 0 < P T ∧ P T ≤ (2⁻¹ : ENNReal) ^ k := by
  induction k with
  | zero => exact ⟨S, subset_rfl, hS, hpos, by rw [pow_zero]; exact prob_le_one⟩
  | succ k ih =>
    obtain ⟨T, hTS, hT, hTpos, hTle⟩ := ih
    obtain ⟨t, htT, ht, htpos, htlt⟩ := hP T hT hTpos
    have hfin : P t ≠ ⊤ := measure_ne_top P t
    have hTfin : P T ≠ ⊤ := measure_ne_top P T
    have key : P T / 2 ≤ (2⁻¹ : ENNReal) ^ (k + 1) := by
      rw [pow_succ, div_eq_mul_inv]; gcongr
    by_cases h : P t ≤ P T / 2
    · exact ⟨t, htT.trans hTS, ht, htpos, h.trans key⟩
    · push Not at h
      have hd : P (T \ t) = P T - P t := measure_sdiff htT ht.nullMeasurableSet hfin
      refine ⟨T \ t, sdiff_subset.trans hTS, hT.diff ht, ?_, ?_⟩
      · rw [hd]; exact tsub_pos_of_lt htlt
      · rw [hd]
        calc P T - P t ≤ P T - P T / 2 := tsub_le_tsub_left h.le _
          _ = P T / 2 := ENNReal.sub_half hTfin
          _ ≤ _ := key

lemma small_piece (hP : IsAtomless P) {S : Set Ω} (hS : MeasurableSet S) (hpos : 0 < P S)
    {δ : ENNReal} (hδ : δ ≠ 0) : ∃ T ⊆ S, MeasurableSet T ∧ 0 < P T ∧ P T ≤ δ := by
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hδ
  obtain ⟨T, hTS, hT, hpos', hle⟩ := small_piece_pow P hP hS hpos k
  exact ⟨T, hTS, hT, hpos', hle.trans hk.le⟩

lemma greedy_ext {S : Set Ω} {c : ℝ} (T : Set Ω) (hT : MeasurableSet T) (hTS : T ⊆ S)
    (hTc : P.real T ≤ c) :
    ∃ T', MeasurableSet T' ∧ T ⊆ T' ∧ T' ⊆ S ∧ P.real T' ≤ c ∧
      ∀ U, MeasurableSet U → U ⊆ S \ T → P.real T + P.real U ≤ c →
        P.real U ≤ 2 * (P.real T' - P.real T) := by
  set V : Set ℝ := {r | ∃ U, MeasurableSet U ∧ U ⊆ S \ T ∧ P.real T + P.real U ≤ c ∧
    P.real U = r} with hV
  have h0 : (0:ℝ) ∈ V := ⟨∅, MeasurableSet.empty, empty_subset _, by simpa using hTc, by simp⟩
  have hbdd : BddAbove V := ⟨1, by rintro r ⟨U, -, -, -, rfl⟩; exact real_le_one P U⟩
  obtain ⟨U0, hU0, hU0S, hU0c, hU0m⟩ : ∃ U0, MeasurableSet U0 ∧ U0 ⊆ S \ T ∧
      P.real T + P.real U0 ≤ c ∧ sSup V / 2 ≤ P.real U0 := by
    by_cases hm : 0 < sSup V
    · obtain ⟨r, ⟨U, hU, hUS, hUc, rfl⟩, hr⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ (half_lt_self hm)
      exact ⟨U, hU, hUS, hUc, hr.le⟩
    · push Not at hm
      refine ⟨∅, MeasurableSet.empty, empty_subset _, by simpa using hTc, ?_⟩
      simp only [measureReal_empty]; linarith
  have hdisj : Disjoint T U0 := by
    rw [Set.disjoint_left]; intro x hxT hxU; exact (hU0S hxU).2 hxT
  have hun : P.real (T ∪ U0) = P.real T + P.real U0 := measureReal_union hdisj hU0
  refine ⟨T ∪ U0, hT.union hU0, subset_union_left, union_subset hTS (hU0S.trans sdiff_subset),
    by rw [hun]; exact hU0c, ?_⟩
  intro U hU hUS hUc
  have : P.real U ≤ sSup V := le_csSup hbdd ⟨U, hU, hUS, hUc, rfl⟩
  rw [hun]; linarith

lemma sierp_real (hP : IsAtomless P) {S : Set Ω} (hS : MeasurableSet S) {c : ℝ} (hc0 : 0 ≤ c)
    (hcS : c ≤ P.real S) : ∃ T ⊆ S, MeasurableSet T ∧ P.real T = c := by
  classical
  let G := {T : Set Ω // MeasurableSet T ∧ T ⊆ S ∧ P.real T ≤ c}
  have hext : ∀ T : G, ∃ T' : G, T.1 ⊆ T'.1 ∧ ∀ U, MeasurableSet U → U ⊆ S \ T.1 →
      P.real T.1 + P.real U ≤ c → P.real U ≤ 2 * (P.real T'.1 - P.real T.1) := by
    intro T
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := greedy_ext P (S := S) T.1 T.2.1 T.2.2.1 T.2.2.2
    exact ⟨⟨T', h1, h3, h4⟩, h2, h5⟩
  choose nxt hnxt1 hnxt2 using hext
  let T0 : G := ⟨∅, MeasurableSet.empty, empty_subset _, by simpa using hc0⟩
  let sq : ℕ → G := fun k => nxt^[k] T0
  have hsq_succ : ∀ k, sq (k+1) = nxt (sq k) := fun k => Function.iterate_succ_apply' _ _ _
  have hmono : Monotone (fun k => (sq k).1) := by
    refine monotone_nat_of_le_succ fun k => ?_
    simp only [hsq_succ]; exact hnxt1 _
  set Tinf := ⋃ k, (sq k).1 with hTinf
  have hTm : MeasurableSet Tinf := MeasurableSet.iUnion fun k => (sq k).2.1
  have hTS : Tinf ⊆ S := iUnion_subset fun k => (sq k).2.2.1
  have hTle : P.real Tinf ≤ c := by
    have h1 : P Tinf = ⨆ k, P (sq k).1 := hmono.measure_iUnion
    have h2 : P Tinf ≤ ENNReal.ofReal c := by
      rw [h1]; refine iSup_le fun k => ?_
      rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal (sq k).2.2.2
    exact ENNReal.toReal_le_of_le_ofReal hc0 h2
  refine ⟨Tinf, hTS, hTm, le_antisymm hTle ?_⟩
  by_contra hlt
  push Not at hlt
  have hdiff : P.real (S \ Tinf) = P.real S - P.real Tinf := measureReal_sdiff hTS hTm
  have hpos : 0 < P (S \ Tinf) := by
    have h : 0 < P.real (S \ Tinf) := by rw [hdiff]; linarith
    exact (ENNReal.toReal_pos_iff.1 h).1
  obtain ⟨W, hWS, hW, hWpos, hWle⟩ := small_piece P hP (hS.diff hTm) hpos
    (δ := ENNReal.ofReal (c - P.real Tinf)) (ENNReal.ofReal_pos.2 (sub_pos.2 hlt)).ne'
  have hw : 0 < P.real W := ENNReal.toReal_pos hWpos.ne' (measure_ne_top P W)
  have hwle : P.real W ≤ c - P.real Tinf := ENNReal.toReal_le_of_le_ofReal (by linarith) hWle
  have hstep : ∀ k, P.real W ≤ 2 * (P.real (sq (k+1)).1 - P.real (sq k).1) := by
    intro k
    have hsub : (sq k).1 ⊆ Tinf := subset_iUnion (fun k => (sq k).1) k
    have hle : P.real (sq k).1 ≤ P.real Tinf := measureReal_mono hsub
    have hWk : W ⊆ S \ (sq k).1 := fun x hx => ⟨(hWS hx).1, fun h => (hWS hx).2 (hsub h)⟩
    rw [hsq_succ]
    exact hnxt2 (sq k) W hW hWk (by linarith)
  have hgrow : ∀ k : ℕ, (k : ℝ) * P.real W ≤ 2 * P.real (sq k).1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hstep k
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / P.real W)
  have h1 := hgrow k
  have h2 := real_le_one P (sq k).1
  have h3 : 2 < (k : ℝ) * P.real W := by
    have := (div_lt_iff₀ hw).1 hk
    linarith
  linarith

lemma sierp (hP : IsAtomless P) {S : Set Ω} (hS : MeasurableSet S) {c : ENNReal} (hc : c ≤ P S) :
    ∃ T ⊆ S, MeasurableSet T ∧ P T = c := by
  have hcfin : c ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top P S) hc
  obtain ⟨T, hTS, hT, hTc⟩ := sierp_real P hP hS (c := c.toReal) ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (measure_ne_top P S) hc)
  refine ⟨T, hTS, hT, ?_⟩
  rw [← ofReal_measureReal, hTc, ENNReal.ofReal_toReal hcfin]

lemma split (hP : IsAtomless P) (m : ℕ) : ∀ (S : Set Ω), MeasurableSet S →
    ∀ c : Fin (m+1) → ENNReal, ∑ i, c i = P S →
    ∃ B : Fin (m+1) → Set Ω, (∀ i, MeasurableSet (B i)) ∧ (∀ i, B i ⊆ S) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧ (∀ ω ∈ S, ∃ i, ω ∈ B i) ∧
      ∀ i, P (B i) ≤ c i := by
  induction m with
  | zero =>
    intro S hS c hc
    refine ⟨fun _ => S, fun _ => hS, fun _ => subset_rfl, ?_, fun ω hω => ⟨0, hω⟩, ?_⟩
    · intro i j hij; exact absurd (Fin.ext (by have := i.2; have := j.2; omega)) hij
    · intro i; rw [Fin.sum_univ_one] at hc; rw [show i = 0 from Fin.ext (by have := i.2; omega), hc]
  | succ m ih =>
    intro S hS c hc
    rw [Fin.sum_univ_succ] at hc
    have hc0 : c 0 ≤ P S := by rw [← hc]; exact le_self_add
    obtain ⟨T, hTS, hT, hTc⟩ := sierp P hP hS hc0
    have hc0fin : c 0 ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top P S) hc0
    have hrest : ∑ i : Fin (m+1), c i.succ = P (S \ T) := by
      rw [measure_sdiff hTS hT.nullMeasurableSet (measure_ne_top P T), hTc, ← hc,
        ENNReal.add_sub_cancel_left hc0fin]
    obtain ⟨B', hB'm, hB'S, hB'd, hB'c, hB'le⟩ :=
      ih (S \ T) (hS.diff hT) (fun i => c i.succ) hrest
    refine ⟨(Fin.cons T B' : Fin (m+1+1) → Set Ω), ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hT
      | succ i => simpa using hB'm i
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hTS
      | succ i => simpa using (hB'S i).trans sdiff_subset
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact Set.disjoint_left.2 fun x hxT hxB => (hB'S j hxB).2 hxT
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact Set.disjoint_left.2 fun x hxB hxT => (hB'S i hxB).2 hxT
        | succ j =>
          simp only [Fin.cons_succ]
          exact hB'd (fun h => hij (by rw [h]))
    · intro ω hω
      by_cases hωT : ω ∈ T
      · exact ⟨0, by simpa using hωT⟩
      · obtain ⟨i, hi⟩ := hB'c ω ⟨hω, hωT⟩
        exact ⟨i.succ, by simpa using hi⟩
    · intro i
      induction i using Fin.cases with
      | zero => simp [hTc]
      | succ i => simpa using hB'le i

end Sierp

section VaR

variable (P : Measure Ω) [IsProbabilityMeasure P]

lemma distFn_eq_cdf {Y : Ω → ℝ} (hY : Measurable Y) :
    distFn P Y = cdf (P.map Y) := by
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  funext x
  rw [cdf_eq_real, map_measureReal_apply hY measurableSet_Iic]; rfl

lemma tail_real {Y : Ω → ℝ} (hY : Measurable Y) (x : ℝ) :
    P.real {ω | x < Y ω} = 1 - distFn P Y x := by
  have h : {ω | x < Y ω} = {ω | Y ω ≤ x}ᶜ := by ext ω; simp
  rw [h, measureReal_compl (measurableSet_le hY measurable_const), probReal_univ]; rfl

lemma mono_F {Y : Ω → ℝ} (hY : Measurable Y) : Monotone (distFn P Y) := by
  rw [distFn_eq_cdf P hY]; exact monotone_cdf _

lemma bddBelow_ge {Y : Ω → ℝ} (hY : Measurable Y) {b : ℝ} (hb : 0 < b) :
    BddBelow {x | b ≤ distFn P Y x} := by
  have ht : Tendsto (distFn P Y) atBot (𝓝 0) := by
    rw [distFn_eq_cdf P hY]; exact tendsto_cdf_atBot _
  obtain ⟨x0, hx0⟩ := Filter.eventually_atBot.1 (ht.eventually (gt_mem_nhds hb))
  refine ⟨x0, fun x hx => ?_⟩
  by_contra h
  push Not at h
  exact (not_le.2 (hx0 x h.le)) hx

lemma exists_gt {Y : Ω → ℝ} (hY : Measurable Y) {b : ℝ} (hb : b < 1) :
    ∃ x, b < distFn P Y x := by
  have ht : Tendsto (distFn P Y) atTop (𝓝 1) := by
    rw [distFn_eq_cdf P hY]; exact tendsto_cdf_atTop _
  exact (ht.eventually (lt_mem_nhds hb)).exists

lemma ge_at_sInf {Y : Ω → ℝ} (hY : Measurable Y) {a : ℝ} {S : Set ℝ} (hne : S.Nonempty)
    (hS : ∀ s ∈ S, 1 - a ≤ distFn P Y s) : 1 - a ≤ distFn P Y (sInf S) := by
  have hrc : ContinuousWithinAt (distFn P Y) (Ici (sInf S)) (sInf S) := by
    rw [distFn_eq_cdf P hY]; exact (cdf _).right_continuous _
  have hc : ContinuousWithinAt (distFn P Y) (Ioi (sInf S)) (sInf S) :=
    hrc.mono Ioi_subset_Ici_self
  refine ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun x hx => ?_)
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx
  exact (hS s hs).trans (mono_F P hY hsx.le)

lemma var_ge (Λ : Side) {Y : Ω → ℝ} (hY : Measurable Y) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    1 - a ≤ distFn P Y (VaRS P Λ a Y) := by
  cases Λ with
  | L =>
    show 1 - a ≤ distFn P Y (sInf {x | 1 - a ≤ distFn P Y x})
    obtain ⟨x, hx⟩ := exists_gt P hY (b := 1 - a) (by linarith)
    exact ge_at_sInf P hY ⟨x, hx.le⟩ fun s hs => hs
  | R =>
    show 1 - a ≤ distFn P Y (sInf {x | 1 - a < distFn P Y x})
    exact ge_at_sInf P hY (exists_gt P hY (by linarith)) fun s hs => le_of_lt hs

lemma varR_lt {Y : Ω → ℝ} (hY : Measurable Y) {a x : ℝ} (ha0 : 0 < a)
    (hx : VaRS P Side.R a Y < x) : 1 - a < distFn P Y x := by
  change sInf {x | 1 - a < distFn P Y x} < x at hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (exists_gt P hY (by linarith)) hx
  exact lt_of_lt_of_le hs (mono_F P hY hsx.le)

lemma varL_le {Y : Ω → ℝ} (hY : Measurable Y) {a x : ℝ} (ha1 : a < 1)
    (hx : 1 - a ≤ distFn P Y x) : VaRS P Side.L a Y ≤ x := by
  show sInf {x | 1 - a ≤ distFn P Y x} ≤ x
  exact csInf_le (bddBelow_ge P hY (by linarith)) hx

lemma varR_le {Y : Ω → ℝ} (hY : Measurable Y) {a x : ℝ} (ha1 : a < 1)
    (hx : ∀ y, x < y → 1 - a < distFn P Y y) : VaRS P Side.R a Y ≤ x := by
  show sInf {x | 1 - a < distFn P Y x} ≤ x
  refine le_of_forall_gt_imp_ge_of_dense fun y hy => ?_
  obtain ⟨x0, hx0⟩ := bddBelow_ge P hY (b := 1 - a) (by linarith)
  exact csInf_le ⟨x0, fun z (hz : 1 - a < distFn P Y z) => hx0 (show 1 - a ≤ distFn P Y z from le_of_lt hz)⟩ (hx y hy)

lemma alpha_lt_one {m : ℕ} (αs : Fin (m+1) → ℝ) (hα : ∀ i, 0 < αs i) (hsum : ∑ i, αs i < 1)
    (i : Fin (m+1)) : αs i < 1 :=
  lt_of_le_of_lt (Finset.single_le_sum (fun j _ => (hα j).le) (Finset.mem_univ i)) hsum

lemma lower {m : ℕ} (αs : Fin (m+1) → ℝ) (hα : ∀ i, 0 < αs i) (hsum : ∑ i, αs i < 1)
    (Λs : Fin (m+1) → Side) {X : Ω → ℝ} (hX : Measurable X) (Xs : Fin (m+1) → Ω → ℝ)
    (hXs : Xs ∈ Allocations L0 (m+1) X) :
    VaRS P (aggSide Λs) (∑ i, αs i) X ≤ ∑ i, VaRS P (Λs i) (αs i) (Xs i) := by
  obtain ⟨hmeas, hsumX⟩ := hXs
  have hm : ∀ i, Measurable (Xs i) := hmeas
  have hα1 := alpha_lt_one αs hα hsum
  obtain ⟨q, hq⟩ : ∃ q : Fin (m+1) → ℝ, q = fun i => VaRS P (Λs i) (αs i) (Xs i) := ⟨_, rfl⟩
  rw [show (∑ i, VaRS P (Λs i) (αs i) (Xs i)) = ∑ i, q i by rw [hq]]
  have hαpos : 0 < ∑ i, αs i := Finset.sum_pos (fun i _ => hα i) Finset.univ_nonempty
  have key : ∀ t : ℝ, 0 ≤ t → 1 - distFn P X ((∑ i, q i) + t) ≤
      ∑ i, (1 - distFn P (Xs i) (q i + t / ((m:ℝ)+1))) := by
    intro t ht
    rw [← tail_real P hX]
    calc P.real {ω | (∑ i, q i) + t < X ω}
        ≤ P.real (⋃ i, {ω | q i + t / ((m:ℝ)+1) < Xs i ω}) := by
          refine measureReal_mono ?_
          intro ω hω
          simp only [mem_iUnion, mem_setOf_eq] at hω ⊢
          by_contra hcon
          push Not at hcon
          have : X ω ≤ ∑ i, q i + t := by
            rw [← hsumX ω]
            calc ∑ i, Xs i ω ≤ ∑ i, (q i + t / ((m:ℝ)+1)) := Finset.sum_le_sum fun i _ => hcon i
              _ = ∑ i, q i + t := by
                rw [Finset.sum_add_distrib]; simp only [Finset.sum_const, Finset.card_univ,
                  Fintype.card_fin, nsmul_eq_mul]; push_cast; field_simp
          linarith
      _ ≤ ∑ i, P.real {ω | q i + t / ((m:ℝ)+1) < Xs i ω} := measureReal_iUnion_fintype_le _
      _ = _ := Finset.sum_congr rfl fun i _ => tail_real P (hm i) _
  have hge : ∀ i, ∀ s, 0 ≤ s → 1 - αs i ≤ distFn P (Xs i) (q i + s) := by
    intro i s hs
    have h1 := var_ge P (Λs i) (hm i) (hα i) (hα1 i)
    have h2 := mono_F P (hm i) (show q i ≤ q i + s by linarith)
    rw [hq] at h2 ⊢
    exact h1.trans h2
  by_cases hall : ∀ i, Λs i = Side.L
  · have hagg : aggSide Λs = Side.L := if_pos hall
    rw [hagg]
    apply varL_le P hX hsum
    have h1 := key 0 le_rfl
    have h2 : ∑ i, (1 - distFn P (Xs i) (q i + 0 / ((m:ℝ)+1))) ≤ ∑ i, αs i :=
      Finset.sum_le_sum fun i _ => by have := hge i (0 / ((m:ℝ)+1)) (by simp); linarith
    rw [add_zero] at h1
    linarith
  · have hagg : aggSide Λs = Side.R := if_neg hall
    push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hjR : Λs j = Side.R := by
      cases h : Λs j
      · exact absurd h hj
      · rfl
    rw [hagg]
    apply varR_le P hX hsum
    intro y hy
    have ht : 0 < y - ∑ i, q i := sub_pos.2 hy
    have htn : 0 < (y - ∑ i, q i) / ((m:ℝ)+1) := by positivity
    have h1 := key (y - ∑ i, q i) ht.le
    have h2 : ∑ i, (1 - distFn P (Xs i) (q i + (y - ∑ i, q i) / ((m:ℝ)+1))) < ∑ i, αs i := by
      apply Finset.sum_lt_sum
      · intro i _; have := hge i _ htn.le; linarith
      · refine ⟨j, Finset.mem_univ j, ?_⟩
        have hlt : VaRS P Side.R (αs j) (Xs j) < q j + (y - ∑ i, q i) / ((m:ℝ)+1) := by
          have hqj : q j = VaRS P Side.R (αs j) (Xs j) := by rw [hq, ← hjR]
          rw [← hqj]; linarith
        have := varR_lt P (hm j) (hα j) hlt
        linarith
    rw [show ∑ i, q i + (y - ∑ i, q i) = y by ring] at h1
    linarith

end VaR

section Alloc

variable (P : Measure Ω) [IsProbabilityMeasure P]

lemma alloc_mem {m : ℕ} {X : Ω → ℝ} (hX : Measurable X) (v : ℝ) {A : Fin (m+1) → Set Ω}
    (hA : IsMeasPartition A) : partitionAllocation X v A ∈ Allocations L0 (m+1) X := by
  obtain ⟨hAm, hAd, hAu⟩ := hA
  refine ⟨fun i => ?_, fun ω => ?_⟩
  · change Measurable (fun ω => (X ω - v) * (A i).indicator 1 ω + v / ((m + 1 : ℕ) : ℝ))
    exact ((hX.sub measurable_const).mul (measurable_one.indicator (hAm i))).add measurable_const
  · obtain ⟨i0, hi0⟩ : ∃ i, ω ∈ A i := by
      have : ω ∈ ⋃ i, A i := hAu ▸ mem_univ ω
      exact mem_iUnion.1 this
    have hind : ∑ i, (A i).indicator (1 : Ω → ℝ) ω = 1 := by
      rw [Finset.sum_eq_single i0]
      · simp [hi0]
      · intro j _ hj
        have : ω ∉ A j := fun h => Set.disjoint_left.1 (hAd hj) h hi0
        simp [this]
      · simp
    simp only [partitionAllocation]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hind, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
    ring

lemma alloc_var_le {m : ℕ} {X : Ω → ℝ} (hX : Measurable X) (v : ℝ) {A : Fin (m+1) → Set Ω}
    (hA : IsMeasPartition A) (i : Fin (m+1)) (Λ : Side) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hPL : P.real (A i ∩ {ω | v < X ω}) ≤ a)
    (hPR : Λ = Side.R → ∀ ε, 0 < ε → P.real (A i ∩ {ω | v + ε < X ω}) < a) :
    VaRS P Λ a (partitionAllocation X v A i) ≤ v / ((m + 1 : ℕ) : ℝ) := by
  have hmeas : Measurable (partitionAllocation X v A i) := (alloc_mem hX v hA).1 i
  have hset : ∀ s, 0 ≤ s → {ω | v / ((m + 1 : ℕ) : ℝ) + s < partitionAllocation X v A i ω} =
      A i ∩ {ω | v + s < X ω} := by
    intro s hs; ext ω
    simp only [partitionAllocation, mem_setOf_eq, mem_inter_iff]
    by_cases h : ω ∈ A i
    · simp only [h, indicator_of_mem, Pi.one_apply, mul_one, true_and]
      constructor <;> intro <;> linarith
    · simp only [h, not_false_eq_true, indicator_of_notMem, mul_zero, zero_add, false_and,
        iff_false, not_lt]
      linarith
  have htail : ∀ s, 0 ≤ s → 1 - distFn P (partitionAllocation X v A i)
      (v / ((m + 1 : ℕ) : ℝ) + s) = P.real (A i ∩ {ω | v + s < X ω}) := by
    intro s hs; rw [← tail_real P hmeas, hset s hs]
  cases Λ with
  | L =>
    apply varL_le P hmeas ha1
    have := htail 0 le_rfl
    rw [add_zero, add_zero] at this
    linarith
  | R =>
    apply varR_le P hmeas ha1
    intro y hy
    have h := htail (y - v / ((m + 1 : ℕ) : ℝ)) (by linarith)
    have e : v / ((m + 1 : ℕ) : ℝ) + (y - v / ((m + 1 : ℕ) : ℝ)) = y := by ring
    rw [e] at h
    have := hPR rfl _ (by linarith : 0 < y - v / ((m + 1 : ℕ) : ℝ))
    linarith

lemma opt_of_props {m : ℕ} (αs : Fin (m+1) → ℝ) (hα : ∀ i, 0 < αs i) (hsum : ∑ i, αs i < 1)
    (Λs : Fin (m+1) → Side) {X : Ω → ℝ} (hX : Measurable X) {A : Fin (m+1) → Set Ω}
    (hA : IsMeasPartition A)
    (hPL : ∀ i, P.real (A i ∩ {ω | VaRS P (aggSide Λs) (∑ i, αs i) X < X ω}) ≤ αs i)
    (hPR : ∀ i, Λs i = Side.R → ∀ ε, 0 < ε →
      P.real (A i ∩ {ω | VaRS P (aggSide Λs) (∑ i, αs i) X + ε < X ω}) < αs i) :
    infConv L0 (fun i => VaRS P (Λs i) (αs i)) X =
      ((VaRS P (aggSide Λs) (∑ i, αs i) X : ℝ) : EReal) ∧
    IsOptimalAllocation L0 (fun i => VaRS P (Λs i) (αs i)) X
      (partitionAllocation X (VaRS P (aggSide Λs) (∑ i, αs i) X) A) := by
  set v := VaRS P (aggSide Λs) (∑ i, αs i) X with hv
  have hα1 := alpha_lt_one αs hα hsum
  have hmem := alloc_mem hX v hA
  have hle : ∑ i, VaRS P (Λs i) (αs i) (partitionAllocation X v A i) ≤ v := by
    calc _ ≤ ∑ _i : Fin (m+1), v / ((m+1 : ℕ) : ℝ) := Finset.sum_le_sum fun i _ =>
          alloc_var_le P hX v hA i (Λs i) (hα i) (hα1 i) (hPL i) (hPR i)
      _ = v := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; field_simp
  have hge := lower P αs hα hsum Λs hX _ hmem
  have heq : ∑ i, VaRS P (Λs i) (αs i) (partitionAllocation X v A i) = v := le_antisymm hle hge
  have hinf : infConv L0 (fun i => VaRS P (Λs i) (αs i)) X = (v : EReal) := by
    unfold infConv
    apply le_antisymm
    · refine (iInf₂_le (partitionAllocation X v A) hmem).trans_eq ?_
      exact congrArg (fun r : ℝ => (r : EReal)) heq
    · exact le_iInf₂ fun Ys hYs => EReal.coe_le_coe_iff.2 (lower P αs hα hsum Λs hX Ys hYs)
  refine ⟨hinf, hmem, ?_⟩
  rw [hinf]
  exact congrArg (fun r : ℝ => (r : EReal)) heq

lemma construct (hP : IsAtomless P) {m : ℕ} (αs : Fin (m+1) → ℝ) (hα : ∀ i, 0 < αs i)
    (hsum : ∑ i, αs i < 1) (Λs : Fin (m+1) → Side) {X : Ω → ℝ} (hX : Measurable X) :
    ∃ A : Fin (m+1) → Set Ω, IsMeasPartition A ∧
      (∀ i, P.real (A i ∩ {ω | VaRS P (aggSide Λs) (∑ i, αs i) X < X ω}) ≤ αs i) ∧
      (∀ i, Λs i = Side.R → ∀ ε, 0 < ε →
        P.real (A i ∩ {ω | VaRS P (aggSide Λs) (∑ i, αs i) X + ε < X ω}) < αs i) := by
  classical
  set v := VaRS P (aggSide Λs) (∑ i, αs i) X with hv
  set α := ∑ i, αs i with hαdef
  have hαpos : 0 < α := Finset.sum_pos (fun i _ => hα i) Finset.univ_nonempty
  set w : Fin (m+1) → ℝ := fun i => αs i / α with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => div_nonneg (hα i).le hαpos.le
  have hwsum : ∑ i, w i = 1 := by
    simp only [hw]; rw [← Finset.sum_div]; exact div_self hαpos.ne'
  have hwα : ∀ i, w i * α = αs i := fun i => div_mul_cancel₀ _ hαpos.ne'
  let g : ℕ → ℝ := fun k => v + 1 / ((k : ℝ) + 1)
  have hg : ∀ k, v < g k := fun k => by
    have : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
    simp only [g]; linarith
  have hgmono : ∀ k K, k ≤ K → g K ≤ g k := fun k K h => by
    have hk : (k:ℝ) ≤ K := by exact_mod_cast h
    have : 1 / ((K:ℝ) + 1) ≤ 1 / ((k:ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    simp only [g]; linarith
  let f : ℕ → Set Ω := fun k => {ω | g k < X ω}
  have hfm : ∀ k, MeasurableSet (f k) := fun k => measurableSet_lt measurable_const hX
  let D := disjointed f
  have hDm : ∀ k, MeasurableSet (D k) := MeasurableSet.disjointed hfm
  have hDf : ∀ k, D k ⊆ f k := disjointed_subset f
  have hcs : ∀ k, ∑ i, ENNReal.ofReal (w i) * P (D k) = P (D k) := by
    intro k
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hwsum,
      ENNReal.ofReal_one, one_mul]
  choose B hBm hBS hBd hBc hBle using fun k =>
    split P hP m (D k) (hDm k) (fun i => ENNReal.ofReal (w i) * P (D k)) (hcs k)
  let A : Fin (m+1) → Set Ω := fun i => (⋃ k, B k i) ∪ (if i = 0 then {ω | X ω ≤ v} else ∅)
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    refine (MeasurableSet.iUnion fun k => hBm k i).union ?_
    split_ifs
    · exact measurableSet_le hX measurable_const
    · exact MeasurableSet.empty
  have hAd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hxi
      obtain ⟨l, hl⟩ := mem_iUnion.1 hxj
      by_cases hkl : k = l
      · subst hkl; exact Set.disjoint_left.1 (hBd k hij) hk hl
      · exact Set.disjoint_left.1 (disjoint_disjointed f hkl) (hBS k i hk) (hBS l j hl)
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hxi
      split_ifs at hxj with h0
      · have h1 : g k < X x := hDf k (hBS k i hk)
        have h2 : X x ≤ v := hxj
        linarith [hg k]
      · exact hxj
    · obtain ⟨l, hl⟩ := mem_iUnion.1 hxj
      split_ifs at hxi with h0
      · have h1 : g l < X x := hDf l (hBS l j hl)
        have h2 : X x ≤ v := hxi
        linarith [hg l]
      · exact hxi
    · split_ifs at hxi hxj with h0 h1
      · exact hij (h0.trans h1.symm)
      all_goals assumption
  have hAu : (⋃ i, A i) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    by_cases hx : X x ≤ v
    · refine ⟨0, Or.inr ?_⟩
      rw [if_pos rfl]; exact hx
    · push Not at hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      have hxf : x ∈ ⋃ k, f k := mem_iUnion.2 ⟨k, show g k < X x by simp only [g]; linarith⟩
      rw [← iUnion_disjointed] at hxf
      obtain ⟨l, hl⟩ := mem_iUnion.1 hxf
      obtain ⟨i, hi⟩ := hBc l x hl
      exact ⟨i, Or.inl (mem_iUnion.2 ⟨l, hi⟩)⟩
  refine ⟨A, ⟨hAm, hAd, hAu⟩, ?_, ?_⟩
  · intro i
    have hvα : P.real {ω | v < X ω} ≤ α := by
      rw [tail_real P hX]; have := var_ge P (aggSide Λs) hX hαpos hsum; linarith
    have hsub : A i ∩ {ω | v < X ω} ⊆ ⋃ k, B k i := by
      rintro x ⟨hxA, hxv⟩
      rcases hxA with hx | hx
      · exact hx
      · split_ifs at hx with h0
        · exact absurd (show X x ≤ v from hx) (not_le.2 hxv)
        · exact hx.elim
    have h1 : P (A i ∩ {ω | v < X ω}) ≤ ENNReal.ofReal (w i * P.real {ω | v < X ω}) := by
      calc P (A i ∩ {ω | v < X ω}) ≤ P (⋃ k, B k i) := measure_mono hsub
        _ ≤ ∑' k, P (B k i) := measure_iUnion_le _
        _ ≤ ∑' k, ENNReal.ofReal (w i) * P (D k) := ENNReal.tsum_le_tsum fun k => hBle k i
        _ = ENNReal.ofReal (w i) * P (⋃ k, D k) := by
            rw [ENNReal.tsum_mul_left, measure_iUnion (disjoint_disjointed f) hDm]
        _ ≤ ENNReal.ofReal (w i) * P {ω | v < X ω} := by
            gcongr
            rw [iUnion_disjointed]
            exact iUnion_subset fun k x hx => lt_trans (hg k) hx
        _ = _ := by rw [ENNReal.ofReal_mul (hw0 i), ofReal_measureReal]
    have h2 : P.real (A i ∩ {ω | v < X ω}) ≤ w i * P.real {ω | v < X ω} :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg (hw0 i) measureReal_nonneg) h1
    calc _ ≤ w i * P.real {ω | v < X ω} := h2
      _ ≤ w i * α := mul_le_mul_of_nonneg_left hvα (hw0 i)
      _ = αs i := hwα i
  · intro i hiR ε hε
    have hagg : aggSide Λs = Side.R := by
      refine if_neg (fun h => ?_)
      rw [h i] at hiR
      exact Side.noConfusion hiR
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    have hsub : A i ∩ {ω | v + ε < X ω} ⊆ ⋃ k ∈ Finset.range (K+1), B k i := by
      rintro x ⟨hxA, hxv⟩
      have hxv' : v + ε < X x := hxv
      rcases hxA with hx | hx
      · obtain ⟨k, hk⟩ := mem_iUnion.1 hx
        refine mem_iUnion₂.2 ⟨k, Finset.mem_range.2 ?_, hk⟩
        by_contra hkK
        push Not at hkK
        have hxD : x ∈ disjointed f k := hBS k i hk
        rw [disjointed_eq_inter_compl] at hxD
        have hnot : x ∉ f K := mem_iInter₂.1 hxD.2 K (by omega)
        apply hnot
        show g K < X x
        simp only [g]; linarith
      · split_ifs at hx with h0
        · have : X x ≤ v := hx
          linarith
        · exact hx.elim
    have hfK : P.real (f K) < α := by
      have hlt : VaRS P Side.R α X < g K := by
        rw [← hagg]; exact hg K
      have := varR_lt P hX hαpos hlt
      show P.real {ω | g K < X ω} < α
      rw [tail_real P hX]; linarith
    have h1 : P (A i ∩ {ω | v + ε < X ω}) ≤ ENNReal.ofReal (w i * P.real (f K)) := by
      calc P (A i ∩ {ω | v + ε < X ω}) ≤ P (⋃ k ∈ Finset.range (K+1), B k i) := measure_mono hsub
        _ ≤ ∑ k ∈ Finset.range (K+1), P (B k i) := measure_biUnion_finset_le _ _
        _ ≤ ∑ k ∈ Finset.range (K+1), ENNReal.ofReal (w i) * P (D k) :=
            Finset.sum_le_sum fun k _ => hBle k i
        _ = ENNReal.ofReal (w i) * P (⋃ k ∈ Finset.range (K+1), D k) := by
            rw [← Finset.mul_sum, measure_biUnion_finset
              (fun a _ b _ hab => disjoint_disjointed f hab) (fun k _ => hDm k)]
        _ ≤ ENNReal.ofReal (w i) * P (f K) := by
            gcongr
            refine iUnion₂_subset fun k hk x hx => ?_
            have hkK : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
            exact lt_of_le_of_lt (hgmono k K hkK) (hDf k hx)
        _ = _ := by rw [ENNReal.ofReal_mul (hw0 i), ofReal_measureReal]
    have h2 : P.real (A i ∩ {ω | v + ε < X ω}) ≤ w i * P.real (f K) :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg (hw0 i) measureReal_nonneg) h1
    have hwpos : 0 < w i := div_pos (hα i) hαpos
    calc _ ≤ w i * P.real (f K) := h2
      _ < w i * α := mul_lt_mul_of_pos_left hfK hwpos
      _ = αs i := hwα i

lemma indep_props {m : ℕ} (αs : Fin (m+1) → ℝ) (hα : ∀ i, 0 < αs i)
    (hsum : ∑ i, αs i < 1) (Λs : Fin (m+1) → Side) {X : Ω → ℝ} (hX : Measurable X)
    (A : Fin (m+1) → Set Ω)
    (hPA : ∀ i, P (A i) = ENNReal.ofReal (αs i / ∑ j, αs j))
    (hind : Indep (MeasurableSpace.generateFrom (Set.range A))
        (MeasurableSpace.comap X inferInstance) P) :
    (∀ i, P.real (A i ∩ {ω | VaRS P (aggSide Λs) (∑ i, αs i) X < X ω}) ≤ αs i) ∧
      (∀ i, Λs i = Side.R → ∀ ε, 0 < ε →
        P.real (A i ∩ {ω | VaRS P (aggSide Λs) (∑ i, αs i) X + ε < X ω}) < αs i) := by
  set v := VaRS P (aggSide Λs) (∑ i, αs i) X with hv
  set α := ∑ i, αs i with hαdef
  have hαpos : 0 < α := Finset.sum_pos (fun i _ => hα i) Finset.univ_nonempty
  have hmul : ∀ i t, P.real (A i ∩ {ω | t < X ω}) = (αs i / α) * P.real {ω | t < X ω} := by
    intro i t
    have h := (Indep_iff _ _ P).1 hind (A i) {ω | t < X ω}
      (MeasurableSpace.measurableSet_generateFrom ⟨i, rfl⟩) ⟨Set.Ioi t, measurableSet_Ioi, rfl⟩
    rw [measureReal_def, h, ENNReal.toReal_mul, hPA i,
      ENNReal.toReal_ofReal (div_nonneg (hα i).le hαpos.le)]
    rfl
  have hw : ∀ i, 0 < αs i / α := fun i => div_pos (hα i) hαpos
  have hwα : ∀ i, αs i / α * α = αs i := fun i => div_mul_cancel₀ _ hαpos.ne'
  refine ⟨fun i => ?_, fun i hiR ε hε => ?_⟩
  · have hvα : P.real {ω | v < X ω} ≤ α := by
      rw [tail_real P hX]; have := var_ge P (aggSide Λs) hX hαpos hsum; linarith
    rw [hmul]
    calc αs i / α * P.real {ω | v < X ω} ≤ αs i / α * α :=
          mul_le_mul_of_nonneg_left hvα (hw i).le
      _ = αs i := hwα i
  · have hagg : aggSide Λs = Side.R := by
      refine if_neg (fun h => ?_)
      rw [h i] at hiR
      exact Side.noConfusion hiR
    have hlt : VaRS P Side.R α X < v + ε := by
      rw [← hagg]; linarith
    have h1 : P.real {ω | v + ε < X ω} < α := by
      rw [tail_real P hX]; have := varR_lt P hX hαpos hlt; linarith
    rw [hmul]
    calc αs i / α * P.real {ω | v + ε < X ω} < αs i / α * α :=
          mul_lt_mul_of_pos_left h1 (hw i)
      _ = αs i := hwα i

theorem main (hP : IsAtomless P) {m : ℕ} (αs : Fin (m+1) → ℝ) (hα : ∀ i, 0 < αs i)
    (hsum : ∑ i, αs i < 1) (Λs : Fin (m+1) → Side) (X : Ω → ℝ)
    (hX : X ∈ (L0 : Set (Ω → ℝ))) :
    infConv L0 (fun i => VaRS P (Λs i) (αs i)) X =
      ((VaRS P (aggSide Λs) (∑ i, αs i) X : ℝ) : EReal) ∧
    (∃ A : Fin (m+1) → Set Ω, IsMeasPartition A ∧
      IsOptimalAllocation L0 (fun i => VaRS P (Λs i) (αs i)) X
        (partitionAllocation X (VaRS P (aggSide Λs) (∑ i, αs i) X) A)) ∧
    (∀ A : Fin (m+1) → Set Ω, IsMeasPartition A →
      (∀ i, P (A i) = ENNReal.ofReal (αs i / ∑ j, αs j)) →
      Indep (MeasurableSpace.generateFrom (Set.range A))
        (MeasurableSpace.comap X inferInstance) P →
      IsOptimalAllocation L0 (fun i => VaRS P (Λs i) (αs i)) X
        (partitionAllocation X (VaRS P (aggSide Λs) (∑ i, αs i) X) A)) := by
  have hXm : Measurable X := hX
  obtain ⟨A, hA, hPL, hPR⟩ := construct P hP αs hα hsum Λs hXm
  obtain ⟨h1, h2⟩ := opt_of_props P αs hα hsum Λs hXm hA hPL hPR
  refine ⟨h1, ⟨A, hA, h2⟩, fun A' hA' hPA hind => ?_⟩
  obtain ⟨hPL', hPR'⟩ := indep_props P αs hα hsum Λs hXm A' hPA hind
  exact (opt_of_props P αs hα hsum Λs hXm hA' hPL' hPR').2

end Alloc

end TRS70

open MeasureTheory ProbabilityTheory TailRiskSharing.VaRConv in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (n : ℕ) (hn : 1 ≤ n) (αs : Fin n → ℝ) (hα : ∀ i, 0 < αs i) (hsum : ∑ i, αs i < 1)
    (Λs : Fin n → Side) (X : Ω → ℝ) (hX : X ∈ (L0 : Set (Ω → ℝ))) :
    -- (i)
    infConv L0 (fun i => VaRS P (Λs i) (αs i)) X =
      ((VaRS P (aggSide Λs) (∑ i, αs i) X : ℝ) : EReal) ∧
    -- (ii)
    (∃ A : Fin n → Set Ω, IsMeasPartition A ∧
      IsOptimalAllocation L0 (fun i => VaRS P (Λs i) (αs i)) X
        (partitionAllocation X (VaRS P (aggSide Λs) (∑ i, αs i) X) A)) ∧
    -- (iii)
    (∀ A : Fin n → Set Ω, IsMeasPartition A →
      (∀ i, P (A i) = ENNReal.ofReal (αs i / ∑ j, αs j)) →
      Indep (MeasurableSpace.generateFrom (Set.range A))
        (MeasurableSpace.comap X inferInstance) P →
      IsOptimalAllocation L0 (fun i => VaRS P (Λs i) (αs i)) X
        (partitionAllocation X (VaRS P (aggSide Λs) (∑ i, αs i) X) A)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact TRS70.main P hP αs hα hsum Λs X hX
