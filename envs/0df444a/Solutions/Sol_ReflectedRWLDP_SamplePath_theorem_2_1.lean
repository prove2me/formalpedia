-- Prove2me | solution 1 for ReflectedRWLDP.SamplePath.theorem_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T20:55:41.899068+00:00
-- url     : https://prove2.me/submissions/b15f76ef-9646-4523-9121-6bc50e51504d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction
import Theorems.Thm_ReflectedRWLDP_SamplePath_sum_LDP
import Theorems.Thm_ReflectedRWLDP_SamplePath_dM1_pseudoMetric
import Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_3_7
import Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_3_8

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ReflectedRWLDP.SamplePath.Transfer

variable {Ω S : Type*} [MeasurableSpace Ω]

lemma speedLog_split (s : ℝ) (hs : 0 < s) (a b c : ℝ≥0∞) (h : a ≤ b + c) :
    speedLog s a ≤ ((s⁻¹ * Real.log 2 : ℝ) : EReal) + max (speedLog s b) (speedLog s c) := by
  have h2 : a ≤ 2 * max b c := by
    calc a ≤ b + c := h
      _ ≤ max b c + max b c := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max b c := (two_mul _).symm
  have hsn : (0 : EReal) ≤ ((s⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.mpr hs).le
  have hmono : Monotone (fun z : EReal => ((s⁻¹ : ℝ) : EReal) * z) := fun x y hxy =>
    mul_le_mul_of_nonneg_left hxy hsn
  unfold speedLog
  calc ((s⁻¹ : ℝ) : EReal) * ENNReal.log a
      ≤ ((s⁻¹ : ℝ) : EReal) * ENNReal.log (2 * max b c) := hmono (ENNReal.log_monotone h2)
    _ = ((s⁻¹ : ℝ) : EReal) * (((Real.log 2 : ℝ) : EReal) +
          max (ENNReal.log b) (ENNReal.log c)) := by
        rw [ENNReal.log_mul_add, ENNReal.log_monotone.map_max]
        congr 2
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ENNReal.log_ofReal_of_pos (by norm_num)]
    _ = ((s⁻¹ * Real.log 2 : ℝ) : EReal) + max (((s⁻¹ : ℝ) : EReal) * ENNReal.log b)
          (((s⁻¹ : ℝ) : EReal) * ENNReal.log c) := by
        rw [EReal.left_distrib_of_nonneg_of_ne_top hsn (EReal.coe_ne_top _), hmono.map_max,
          EReal.coe_mul]

lemma limsup_le_of_split {f g h : ℕ → EReal} {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hf : ∀ᶠ n in atTop, f n ≤ (c n : EReal) + max (g n) (h n)) {L : EReal}
    (hg : limsup g atTop ≤ L) (hh : limsup h atTop ≤ L) : limsup f atTop ≤ L := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro b' hLb'
  obtain ⟨b, hLb, hbb'⟩ := EReal.lt_iff_exists_real_btwn.mp hLb'
  have hbb'r : b < b' := by exact_mod_cast hbb'
  have eg : ∀ᶠ n in atTop, g n < b := eventually_lt_of_limsup_lt (lt_of_le_of_lt hg hLb)
  have eh : ∀ᶠ n in atTop, h n < b := eventually_lt_of_limsup_lt (lt_of_le_of_lt hh hLb)
  have ec : ∀ᶠ n in atTop, c n < b' - b := (tendsto_order.1 hc).2 _ (by linarith)
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hf, eg, eh, ec] with n h1 h2 h3 h4
  calc f n ≤ (c n : EReal) + max (g n) (h n) := h1
    _ ≤ (c n : EReal) + (b : EReal) := add_le_add le_rfl (max_le h2.le h3.le)
    _ = ((c n + b : ℝ) : EReal) := by rw [EReal.coe_add]
    _ ≤ (b' : EReal) := by exact_mod_cast (by linarith : c n + b ≤ b')

lemma le_liminf_of_split {f g h : ℕ → EReal} {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hf : ∀ᶠ n in atTop, f n ≤ (c n : EReal) + max (g n) (h n)) {L : EReal}
    (hfL : L ≤ liminf f atTop) (hh : limsup h atTop = ⊥) : L ≤ liminf g atTop := by
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro b hbL
  obtain ⟨b', hbb', hb'L⟩ := EReal.lt_iff_exists_real_btwn.mp hbL
  have hbb'r : b < b' := by exact_mod_cast hbb'
  have ef : ∀ᶠ n in atTop, (b' : EReal) < f n :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hb'L hfL)
  have eh : ∀ᶠ n in atTop, h n < ((b - 1 : ℝ) : EReal) :=
    eventually_lt_of_limsup_lt (by rw [hh]; exact EReal.bot_lt_coe _)
  have ec : ∀ᶠ n in atTop, c n < b' - b := (tendsto_order.1 hc).2 _ (by linarith)
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hf, ef, eh, ec] with n h1 h2 h3 h4
  by_contra hgn
  push Not at hgn
  have hmax : max (g n) (h n) ≤ (b : EReal) :=
    max_le hgn.le (h3.le.trans (by exact_mod_cast (by linarith : b - 1 ≤ b)))
  have : f n ≤ (b' : EReal) := by
    calc f n ≤ (c n : EReal) + max (g n) (h n) := h1
      _ ≤ (c n : EReal) + (b : EReal) := add_le_add le_rfl hmax
      _ = ((c n + b : ℝ) : EReal) := by rw [EReal.coe_add]
      _ ≤ (b' : EReal) := by exact_mod_cast (by linarith : c n + b ≤ b')
  exact absurd h2 (not_lt.mpr this)

/-- `−↑(inf_G I) ≤ L` from pointwise bounds. -/
lemma neg_iInf_le {I : S → ℝ≥0∞} {G : Set S} {L : EReal}
    (h : ∀ ζ ∈ G, -((I ζ : ℝ≥0∞) : EReal) ≤ L) : -(((⨅ ζ ∈ G, I ζ : ℝ≥0∞)) : EReal) ≤ L := by
  rw [EReal.neg_le]
  rcases le_total (-L) 0 with hL | hL
  · exact hL.trans (EReal.coe_ennreal_nonneg _)
  · rw [← EReal.coe_toENNReal hL, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine le_iInf₂ fun ζ hζ => ?_
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal hL]
    have := h ζ hζ
    rwa [EReal.neg_le] at this

/-- `x ≤ −↑m` from bounds `x ≤ −↑a` for all `a < m`, when `x ≤ 0`. -/
lemma le_neg_of_forall {x : EReal} (hx : x ≤ 0) {m : ℝ≥0∞}
    (h : ∀ a : NNReal, (a : ℝ≥0∞) < m → x ≤ -((a : ℝ≥0∞) : EReal)) : x ≤ -((m : ℝ≥0∞) : EReal) := by
  have hx' : 0 ≤ -x := by simpa using EReal.neg_le_neg_iff.mpr hx
  rw [EReal.le_neg, ← EReal.coe_toENNReal hx', EReal.coe_ennreal_le_coe_ennreal_iff]
  refine ENNReal.le_of_forall_nnreal_lt fun a ha => ?_
  have := h a ha
  rw [EReal.le_neg, ← EReal.coe_toENNReal hx', EReal.coe_ennreal_le_coe_ennreal_iff] at this
  exact this

/-- Dembo–Zeitouni, Theorem 4.2.13: an LDP with a good rate function transfers to an exponentially
equivalent sequence, for a pseudo-metric `D` valued in `[0, ∞]`. -/
theorem transfer (P : Measure Ω) [IsProbabilityMeasure P] (D : S → S → ℝ≥0∞)
    (hD0 : ∀ x, D x x = 0) (hsymm : ∀ x y, D x y = D y x)
    (htri : ∀ x y z, D x z ≤ D x y + D y z)
    (Y Y' : ℕ → Ω → S) (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (I : S → ℝ≥0∞)
    (hLDP : SatisfiesLDP P Y' D s I) (hgood : MFGLimit.LDP.IsGoodRate D I)
    (hexp : ExpEquivalent P Y Y' D s) : SatisfiesLDP P Y D s I := by
  have hc : Tendsto (fun n => (s n)⁻¹ * Real.log 2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hs).mul_const (Real.log 2)
  have hspos : ∀ᶠ n in atTop, 0 < s n := hs.eventually_gt_atTop 0
  constructor
  · -- lower bound
    intro G hG
    apply neg_iInf_le
    intro ζ hζ
    obtain ⟨ε, hε, hball⟩ := hG ζ hζ
    obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    set δ : ℝ := (r : ℝ) / 2 with hδ
    have hδpos : 0 < δ := by
      have : (0 : ℝ) < r := by exact_mod_cast hr0
      positivity
    set B : Set S := {y | D ζ y < ENNReal.ofReal δ} with hB
    have hBopen : MFGLimit.LDP.IsOpenD D B := by
      intro y hy
      refine ⟨ENNReal.ofReal δ - D ζ y, tsub_pos_of_lt hy, fun y' hy' => ?_⟩
      show D ζ y' < ENNReal.ofReal δ
      calc D ζ y' ≤ D ζ y + D y y' := htri _ _ _
        _ < ENNReal.ofReal δ := by
          rw [add_comm]; exact lt_tsub_iff_right.mp hy'
    have hζB : ζ ∈ B := by
      show D ζ ζ < ENNReal.ofReal δ
      rw [hD0]; exact ENNReal.ofReal_pos.mpr hδpos
    have hlowB := hLDP.1 B hBopen
    have hζle : -((I ζ : ℝ≥0∞) : EReal) ≤ -(((⨅ ξ ∈ B, I ξ : ℝ≥0∞)) : EReal) := by
      rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
      exact iInf₂_le ζ hζB
    have hsub : ∀ n, {ω | Y' n ω ∈ B} ⊆ {ω | Y n ω ∈ G} ∪
        {ω | ENNReal.ofReal δ < D (Y n ω) (Y' n ω)} := by
      intro n ω hω
      by_contra hcon
      simp only [mem_union, mem_setOf_eq, not_or, not_lt] at hcon hω
      apply hcon.1
      apply hball
      show D ζ (Y n ω) < ε
      calc D ζ (Y n ω) ≤ D ζ (Y' n ω) + D (Y' n ω) (Y n ω) := htri _ _ _
        _ < ENNReal.ofReal δ + ENNReal.ofReal δ := by
            rw [hsymm (Y' n ω)]
            exact ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcon.2) hω hcon.2
        _ = (r : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_add hδpos.le hδpos.le, hδ, add_halves, ENNReal.ofReal_coe_nnreal]
        _ < ε := hrε
    refine hζle.trans (le_liminf_of_split hc ?_ hlowB (hexp δ hδpos))
    filter_upwards [hspos] with n hn
    exact speedLog_split (s n) hn _ _ _ ((measure_mono (hsub n)).trans (measure_union_le _ _))
  · -- upper bound
    intro F hF
    have hnonpos : limsup (fun n => speedLog (s n) (P {ω | Y n ω ∈ F})) atTop ≤ 0 := by
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [hspos] with n hn
      unfold speedLog
      have h1 : ENNReal.log (P {ω | Y n ω ∈ F}) ≤ 0 :=
        ENNReal.log_le_zero_iff.mpr prob_le_one
      have h2 : (0 : EReal) ≤ (((s n)⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.mpr hn).le
      simpa using mul_le_mul_of_nonneg_left h1 h2
    apply le_neg_of_forall hnonpos
    intro a ha
    -- choose `δ > 0` with `a ≤ inf_{F_δ} I`
    set infD : S → ℝ≥0∞ := fun y => ⨅ z ∈ F, D z y with hinfD
    set Fd : ℝ → Set S := fun δ => {y | infD y ≤ ENNReal.ofReal δ} with hFd
    have hFdclosed : ∀ δ, MFGLimit.LDP.IsClosedD D (Fd δ) := by
      intro δ y hy
      simp only [hFd, mem_compl_iff, mem_setOf_eq, not_le] at hy
      refine ⟨infD y - ENNReal.ofReal δ, tsub_pos_of_lt hy, fun y' hy' => ?_⟩
      simp only [hFd, mem_compl_iff, mem_setOf_eq, not_le]
      have hle : infD y - D y y' ≤ infD y' := by
        refine le_iInf₂ fun z hz => ?_
        rw [tsub_le_iff_right]
        calc infD y ≤ D z y := iInf₂_le z hz
          _ ≤ D z y' + D y' y := htri _ _ _
          _ = D z y' + D y y' := by rw [hsymm y']
      refine lt_of_lt_of_le ?_ hle
      have h1 : D y y' + ENNReal.ofReal δ < infD y := lt_tsub_iff_right.mp hy'
      exact lt_tsub_iff_left.mpr h1
    have hexists : ∃ δ : ℝ, 0 < δ ∧ (a : ℝ≥0∞) ≤ ⨅ x ∈ Fd δ, I x := by
      by_contra hne
      push Not at hne
      have hx : ∀ k : ℕ, ∃ x ∈ Fd (1 / ((k : ℝ) + 1)), I x < a := by
        intro k
        have := hne (1 / ((k : ℝ) + 1)) (by positivity)
        simpa [iInf_lt_iff] using this
      choose x hxF hxI using hx
      obtain ⟨x0, hx0, φ, hφ, hconv⟩ :=
        hgood.2 a x (fun k => (hxI k).le)
      have hx0F : x0 ∈ F := by
        by_contra hx0F
        obtain ⟨ε, hε, hball⟩ := hF x0 hx0F
        obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
        set η : ℝ := (r : ℝ) / 2 with hη
        have hηpos : 0 < η := by
          have : (0 : ℝ) < r := by exact_mod_cast hr0
          positivity
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hηpos
        have hev : ∀ᶠ k in atTop, D (x (φ k)) x0 < ENNReal.ofReal η :=
          (tendsto_order.1 hconv).2 _ (ENNReal.ofReal_pos.mpr hηpos)
        obtain ⟨k, hkN, hk⟩ := ((eventually_ge_atTop N).and hev).exists
        have hφk : N ≤ φ k := hkN.trans (hφ.id_le k)
        have hδk : 1 / ((φ k : ℝ) + 1) < η := by
          refine lt_of_le_of_lt ?_ hN
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hφk 1
        have hin := hxF (φ k)
        simp only [hFd, mem_setOf_eq] at hin
        have hlt : infD (x (φ k)) < ENNReal.ofReal η :=
          lt_of_le_of_lt hin ((ENNReal.ofReal_lt_ofReal_iff hηpos).mpr hδk)
        simp only [hinfD, iInf_lt_iff] at hlt
        obtain ⟨z, hzF, hz⟩ := hlt
        apply hball (show D x0 z < ε from ?_) hzF
        calc D x0 z ≤ D x0 (x (φ k)) + D (x (φ k)) z := htri _ _ _
          _ = D (x (φ k)) x0 + D z (x (φ k)) := by rw [hsymm x0 (x (φ k)), hsymm (x (φ k)) z]
          _ < ENNReal.ofReal η + ENNReal.ofReal η :=
              ENNReal.add_lt_add hk hz
          _ = (r : ℝ≥0∞) := by
              rw [← ENNReal.ofReal_add hηpos.le hηpos.le, hη, add_halves,
                ENNReal.ofReal_coe_nnreal]
          _ < ε := hrε
      have : (⨅ ξ ∈ F, I ξ) ≤ (a : ℝ≥0∞) := (iInf₂_le x0 hx0F).trans hx0
      exact absurd ha (not_lt.mpr this)
    obtain ⟨δ, hδpos, hδa⟩ := hexists
    have hupF := hLDP.2 (Fd δ) (hFdclosed δ)
    have hsub : ∀ n, {ω | Y n ω ∈ F} ⊆ {ω | Y' n ω ∈ Fd δ} ∪
        {ω | ENNReal.ofReal δ < D (Y n ω) (Y' n ω)} := by
      intro n ω hω
      by_contra hcon
      simp only [mem_union, mem_setOf_eq, not_or, not_lt] at hcon hω
      apply hcon.1
      show infD (Y' n ω) ≤ ENNReal.ofReal δ
      exact (iInf₂_le (Y n ω) hω).trans hcon.2
    have hmain := limsup_le_of_split hc (f := fun n => speedLog (s n) (P {ω | Y n ω ∈ F}))
      (g := fun n => speedLog (s n) (P {ω | Y' n ω ∈ Fd δ}))
      (h := fun n => speedLog (s n) (P {ω | ENNReal.ofReal δ < D (Y n ω) (Y' n ω)}))
      (by
        filter_upwards [hspos] with n hn
        exact speedLog_split (s n) hn _ _ _
          ((measure_mono (hsub n)).trans (measure_union_le _ _)))
      hupF (by rw [hexp δ hδpos]; exact bot_le)
    refine hmain.trans ?_
    rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
    exact hδa

lemma dM1_symm {T : ℝ} (ξ ζ : DPath T) : dM1 ξ ζ = dM1 ζ ξ := by
  have key : ∀ ξ ζ : DPath T, dM1 ξ ζ ≤ dM1 ζ ξ := by
    intro ξ ζ
    unfold dM1
    refine le_iInf fun v => le_iInf fun r => le_iInf fun u => le_iInf fun t =>
      le_iInf fun hv => le_iInf fun hu => ?_
    refine iInf_le_of_le u (iInf_le_of_le t (iInf_le_of_le v (iInf_le_of_le r
      (iInf_le_of_le hu (iInf_le_of_le hv (le_of_eq ?_))))))
    have hs : ∀ f g : ℝ → ℝ, supDist T f g = supDist T g f := by
      intro f g
      unfold supDist
      simp_rw [abs_sub_comm]
    rw [hs u v, hs t r]
  exact le_antisymm (key ξ ζ) (key ζ ξ)

end ReflectedRWLDP.SamplePath.Transfer

open ReflectedRWLDP.SamplePath in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    SatisfiesLDP P (Ybar U p) dM1 (fun n => (n : ℝ) ^ alpha p) (rateY P U p) := by
  have := h.isProbability
  have hα : 0 < alpha p := by
    unfold alpha; have := h.p_pos; positivity
  have hs : Tendsto (fun n : ℕ => (n : ℝ) ^ alpha p) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  obtain ⟨h0, htri⟩ := dM1_pseudoMetric 1 one_pos
  exact Transfer.transfer P dM1 h0 Transfer.dM1_symm htri (Ybar U p)
    (fun n ω => Zbar U p n ω + Sbar U p n ω) _ hs (rateY P U p) (sum_LDP P U p h)
    (lemma_3_7 P U p h).2 (lemma_3_8 P U p h)
