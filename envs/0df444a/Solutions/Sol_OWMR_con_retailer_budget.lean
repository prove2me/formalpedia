-- Prove2me | solution 1 for OWMR.con_retailer_budget
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:45.730193+00:00
-- url     : https://prove2.me/submissions/83f7b5ef-8187-4b65-891b-4e2fe93e505f

import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_arb_mean_demand
import Theorems.Thm_OWMR_arb_width_bound
import Theorems.Thm_OWMR_arb_local_comparison
import Theorems.Thm_OWMR_half_window_shift
import Theorems.Thm_OWMR_renewal_doubling
import Theorems.Thm_OWMR_renewal_depletion_mean
import Theorems.Thm_OWMR_canonical_width_bound
import Theorems.Thm_OWMR_F_properties
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace OWMR.Ret

lemma params (m : ℝ) (hm : 1 ≤ m) :
    0 < conZeta m ∧ conZeta m < 2 ∧ 1 < conB m ∧ 1 < conZeta m * (conB m - 1) ∧ 0 ≤ conU m := by
  have hm0 : 0 < m := by linarith
  have h32 : 0 < 32 / (57 * m) := by positivity
  have h32' : 32 / (57 * m) ≤ 32 / 57 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hg1 : 13 / 6 < conG m := by unfold conG conGammaBar; linarith
  have hg2 : conG m < 3 := by unfold conG conGammaBar; linarith
  have hgm : 0 < conG m - 1 := by linarith
  have hz : conZeta m = 1 + 1 / (conG m - 1) := by unfold conZeta; field_simp; ring
  have hz0 : 0 < conZeta m := by rw [hz]; positivity
  have hz1 : 1 < conZeta m := by rw [hz]; have : 0 < 1 / (conG m - 1) := by positivity
                                 linarith
  have hz2 : conZeta m < 2 := by
    rw [hz]; have : 1 / (conG m - 1) < 1 := by rw [div_lt_one hgm]; linarith
    linarith
  have hB : conB m = 2 * (conG m - 1) := rfl
  refine ⟨hz0, hz2, by rw [hB]; linarith, ?_, ?_⟩
  · rw [hB]
    have : 1 < 2 * (conG m - 1) - 1 := by linarith
    nlinarith
  · unfold conU; positivity

lemma renewalM_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) :
    renewalM ρ w = renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalM renewalMeasure
  rw [Measure.sum_apply _ measurableSet_Ico]
  refine tsum_congr fun k => ?_
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ico]
  exact ⟨fun h => ⟨Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _, h⟩, fun h => h.2⟩

lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ =>
    (measurable_pi_apply j).coe_nnreal_real) measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

lemma mean_marg_pos {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    0 < ∫⁻ x, (x : ℝ≥0∞) ∂N.marginal i := by
  unfold Network.marginal
  rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
  exact hN.mean_pos i

/-- Mean demand bound (arb-rK) in real form. -/
lemma mean_alg (a Gr M k I κ u : ℝ) (ha : 0 ≤ a) (hGr : 0 < Gr) (hM : 1 ≤ M) (hk : 0 < k)
    (hI : 0 ≤ I) (hkI : k + I = Gr * M) (hmean : a * (M - 1) ≤ I) (hκ : 1 < κ)
    (hkκ : κ * Gr < k) (hu : u = k / (Gr * M)) (hu1 : u ≤ 1) :
    a ≤ Gr * ((1 - u) / (1 - u / κ)) := by
  have hM0 : 0 < M := by linarith
  have hκ0 : 0 < κ := by linarith
  have hD : 0 < 1 - u / κ := by
    have : u / κ < 1 := by rw [div_lt_one hκ0]; linarith
    linarith
  have hD2 : 1 - u / κ ≤ 1 - 1 / M := by
    have : 1 / M ≤ u / κ := by
      rw [hu, div_div, div_le_div_iff₀ hM0 (by positivity)]
      nlinarith
    linarith
  have h1 : a * (1 - 1 / M) ≤ Gr * (1 - u) := by
    have e1 : a * (1 - 1 / M) = a * (M - 1) / M := by field_simp
    have e2 : Gr * (1 - u) = I / M := by
      rw [hu]; field_simp; linarith
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hmean hM0.le
  rw [mul_div_assoc', le_div_iff₀ hD]
  calc a * (1 - u / κ) ≤ a * (1 - 1 / M) := mul_le_mul_of_nonneg_left hD2 ha
    _ ≤ Gr * (1 - u) := h1

lemma width_alg (h p H m wh Gr : ℝ) (hh : 0 < h) (hpp : 0 < p) (hHH : 0 < H) (hm : 1 ≤ m)
    (hHm : m * h ≤ H) (hp : h ≤ p) (hGr0 : 0 ≤ Gr) (hcw : p * wh * H ≤ (H + p) * Gr) :
    h * wh ≤ (1 + 1 / m) * Gr := by
  have hm0 : 0 < m := by linarith
  have h1 : h * wh * (p * H * m) = (h * m) * (p * wh * H) := by ring
  have h2 : (h * m) * (p * wh * H) ≤ (h * m) * ((H + p) * Gr) :=
    mul_le_mul_of_nonneg_left hcw (by positivity)
  have e3 : (m + 1) * Gr * (p * H) - (h * m) * ((H + p) * Gr)
      = Gr * (m * H) * (p - h) + Gr * p * (H - m * h) := by ring
  have h3a : 0 ≤ Gr * (m * H) * (p - h) :=
    mul_nonneg (mul_nonneg hGr0 (by positivity)) (sub_nonneg.2 hp)
  have h3b : 0 ≤ Gr * p * (H - m * h) := mul_nonneg (mul_nonneg hGr0 hpp.le) (sub_nonneg.2 hHm)
  have h4 : (1 + 1 / m) * Gr * (p * H * m) = (m + 1) * Gr * (p * H) := by field_simp
  have key : h * wh * (p * H * m) ≤ (1 + 1 / m) * Gr * (p * H * m) := by
    rw [h1, h4]; linarith
  exact le_of_mul_le_mul_right key (by positivity)

end OWMR.Ret

open OWMR OWMR.Ret

set_option maxHeartbeats 4000000 in
theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (m : ℝ) (hm : 1 ≤ m)
    (hH : ∀ i, m * N.h ≤ N.H i) (hp : N.h ≤ N.p) (c : ConChoice n) (hc : IsConChoice N m c)
    (i : Fin n) :
    (c.batch i = false → c.s i = c.S i ∧ (∀ y, N.F i (c.S i) ≤ N.F i y) ∧
      ENNReal.ofReal (N.F i (c.S i) + N.K i)
        ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i)) ∧
    (c.batch i = true → c.s i < c.S i ∧
      ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
        + ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i)
        + min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
            (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
              * ssAvgCost (N.marginal i)
                  (fun y => max (1 - 4 * ((c.S i - y) / (c.S i - c.s i)) / 3) 0 ^ 2 / (8 / 3)) 0
                  (c.s i) (c.S i))
        + ENNReal.ofReal (3 / 8 * N.h * ∫ x, (x : ℝ) ∂(N.marginal i))
      ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i)) := by
  obtain ⟨hFnn, hFconv, hFlip, hFslope⟩ := F_properties N hN i
  have hFc : Continuous (N.F i) := by
    refine Metric.continuous_iff.2 fun y ε hε => ⟨ε / (N.H i + N.p + 1), by
      have := hN.H_pos i; have := hN.p_pos; positivity, fun y' hy' => ?_⟩
    rw [Real.dist_eq] at hy' ⊢
    have h1 := hFlip y' y
    have hc0 : 0 < N.H i + N.p + 1 := by have := hN.H_pos i; have := hN.p_pos; linarith
    calc |N.F i y' - N.F i y| ≤ (N.H i + N.p) * |y' - y| := h1
      _ ≤ (N.H i + N.p + 1) * |y' - y| := by nlinarith [abs_nonneg (y' - y)]
      _ < (N.H i + N.p + 1) * (ε / (N.H i + N.p + 1)) := by
          exact mul_lt_mul_of_pos_left hy' hc0
      _ = ε := by field_simp
  have hFm : Measurable (N.F i) := hFc.measurable
  set ρ := N.marginal i with hρ
  have hρpos : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ := mean_marg_pos N hN i
  set U := renewalMeasure ρ with hU
  have hUfin : ∀ w, U (Set.Ico 0 w) < ∞ := renewalMeasure_Ico_lt_top ρ hρpos
  have hInt : ∀ (w : ℝ) (f : ℝ → ℝ) (B : ℝ), Measurable f → (∀ x ∈ Set.Ico (0 : ℝ) w, ‖f x‖ ≤ B) →
      IntegrableOn f (Set.Ico 0 w) U := fun w f B hf hb =>
    Measure.integrableOn_of_bounded (hUfin w).ne hf.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ico).2 (Filter.Eventually.of_forall hb))
  obtain ⟨hζ0, hζ2, hB1, hκ1, hU0⟩ := params m hm
  have hbdd : BddBelow (Set.range (N.F i)) := ⟨0, by rintro _ ⟨y, rfl⟩; exact hFnn y⟩
  have hΛ : ∀ y, (⨅ y, N.F i y) ≤ N.F i y := fun y => ciInf_le hbdd y
  obtain ⟨hcas1, hcas2⟩ := hc.1 i
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · -- an immediate retailer
    have hle : ENNReal.ofReal ((⨅ y, N.F i y) + N.K i)
        ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i) := by
      by_contra hlt
      have := (hcas2 (lt_of_not_ge hlt)).1
      rw [hb] at this
      exact Bool.false_ne_true this
    obtain ⟨-, hsS, hmin⟩ := hcas1 hle
    refine ⟨hsS, hmin, ?_⟩
    have : (⨅ y, N.F i y) = N.F i (c.S i) := le_antisymm (hΛ _) (le_ciInf hmin)
    rwa [this] at hle
  · -- a batch retailer
    have hlt : ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i)
        < ENNReal.ofReal ((⨅ y, N.F i y) + N.K i) := by
      by_contra hle
      have := (hcas1 (le_of_not_gt hle)).1
      rw [hb] at this
      exact Bool.false_ne_true this.symm
    obtain ⟨-, sh, Sh, hcan, hhalf, hfull⟩ := hcas2 hlt
    have hcan' := hcan
    obtain ⟨hsS, hss, hFs, hFS, hFI⟩ := hcan
    set k := conZeta m * N.K i with hk
    set G := N.J i k with hG
    have hGv : G = slValue ρ (N.F i) k := rfl
    set Gr := N.F i sh with hGr
    have hGr0 : 0 ≤ Gr := hFnn sh
    have hGeq : G = ENNReal.ofReal Gr := by rw [hGv, hFs]
    have hFI' : ∀ y ∈ Set.Icc sh Sh, N.F i y ≤ Gr := fun y hy => by
      have := hFI y hy
      rw [← hGv, hGeq] at this
      exact (ENNReal.ofReal_le_ofReal_iff hGr0).1 this
    set wh := Sh - sh with hwh
    have hwh0 : 0 < wh := sub_pos.2 hsS
    set M := (U (Set.Ico 0 wh)).toReal with hM
    have hM1 : 1 ≤ M := by
      have h2 := ENNReal.toReal_mono (hUfin wh).ne (one_le_renewal ρ wh hwh0)
      rwa [ENNReal.toReal_one] at h2
    have hM0 : 0 < M := by linarith
    have hUM : U (Set.Ico 0 wh) = ENNReal.ofReal M := (ENNReal.ofReal_toReal (hUfin wh).ne).symm
    set I := ∫ x in Set.Ico 0 wh, N.F i (Sh - x) ∂U with hI
    have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ico fun x _ => hFnn _
    have hk0 : 0 ≤ k := mul_nonneg hζ0.le (hN.K_nonneg i)
    have hFb : ∀ y ∈ Set.Icc sh Sh, N.F i y ≤ Gr := hFI'
    have hrr := ss_renewal_reward ρ hρpos (N.F i) hFm hFnn k sh Sh hk0 hsS ⟨Gr, hFb⟩
    have hkI : k + I = Gr * M := by
      have h1 : ENNReal.ofReal ((k + I) / M) = ENNReal.ofReal Gr := by
        rw [← hrr, hss, ← hGv, hGeq]
      have h2 := (ENNReal.ofReal_eq_ofReal_iff (div_nonneg (by linarith) hM0.le) hGr0).1 h1
      field_simp at h2
      linarith
    -- the base-stock floor is at most the canonical holding cost
    have hΛI : (⨅ y, N.F i y) * M ≤ I := by
      have h1 : ∫ x in Set.Ico 0 wh, (⨅ y, N.F i y) ∂U = M * (⨅ y, N.F i y) := by
        rw [setIntegral_const, smul_eq_mul]; rfl
      have h2 : ∫ x in Set.Ico 0 wh, (⨅ y, N.F i y) ∂U ≤ I :=
        setIntegral_mono_on (hInt wh _ |⨅ y, N.F i y| measurable_const fun x _ => le_rfl)
          (hInt wh _ Gr (hFm.comp (measurable_const.sub measurable_id)) fun x hx => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]
            exact hFb _ ⟨by linarith [hx.2], by linarith [hx.1]⟩)
          measurableSet_Ico fun x _ => hΛ _
      rw [h1] at h2; linarith
    -- the strict threshold
    have hthr : conB m * Gr < (⨅ y, N.F i y) + N.K i := by
      rw [hGeq, ← ENNReal.ofReal_mul (by linarith)] at hlt
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
    have hK0 : 0 < N.K i := by
      rcases eq_or_lt_of_le (hN.K_nonneg i) with h0 | h0
      · exfalso
        have hk' : k = 0 := by rw [hk, ← h0, mul_zero]
        have : (⨅ y, N.F i y) ≤ Gr := by
          have := hΛI; rw [hk'] at hkI
          nlinarith
        rw [← h0] at hthr
        nlinarith
      · exact h0
    have hkpos : 0 < k := mul_pos hζ0 hK0
    have hGrpos : 0 < Gr := by
      by_contra h
      have h' : Gr = 0 := le_antisymm (not_lt.1 h) hGr0
      rw [h', zero_mul] at hkI
      linarith
    set u := k / (Gr * M) with hu
    have hu1 : u ≤ 1 := by
      rw [hu, div_le_one (by positivity)]; linarith
    have hu0 : 0 ≤ u := by positivity
    have hkM : k / M = u * Gr := by rw [hu]; field_simp
    have hKk : N.K i = k / conZeta m := by rw [hk]; field_simp
    -- the threshold in terms of `u`
    have hkκ : conZeta m * (conB m - 1 + u) * Gr < k := by
      have h1 : (⨅ y, N.F i y) ≤ Gr - u * Gr := by
        rw [← hkM]
        have : (⨅ y, N.F i y) ≤ I / M := by rw [le_div_iff₀ hM0]; linarith
        have e : I / M = Gr - k / M := by field_simp; linarith
        linarith
      rw [hKk] at hthr
      have h2 : conB m * Gr < Gr - u * Gr + k / conZeta m := by linarith
      have h3 : conZeta m * (conB m * Gr) < conZeta m * (Gr - u * Gr + k / conZeta m) :=
        mul_lt_mul_of_pos_left h2 hζ0
      have e : conZeta m * (Gr - u * Gr + k / conZeta m) = conZeta m * (Gr - u * Gr) + k := by
        field_simp
      nlinarith
    have hκ' : 1 < conZeta m * (conB m - 1 + u) := by nlinarith
    -- the mean demand term
    have hmeanR : 3 / 8 * N.h * ∫ x, (x : ℝ) ∂ρ
        ≤ 3 / 8 * (Gr * ((1 - u) / (1 - u / (conZeta m * (conB m - 1 + u))))) := by
      have hmd := arb_mean_demand N hN i sh Sh hsS
      have hμ0 : 0 ≤ ∫ x, (x : ℝ) ∂ρ := integral_nonneg fun x => NNReal.coe_nonneg _
      have hhH : N.h ≤ min (N.H i) N.p := le_min (by nlinarith [hH i, hN.h_pos]) hp
      have hmean : N.h * (∫ x, (x : ℝ) ∂ρ) * (M - 1) ≤ I := by
        refine le_trans ?_ hmd
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhH hμ0) (by linarith)
      have := mean_alg (N.h * ∫ x, (x : ℝ) ∂ρ) Gr M k I _ u (mul_nonneg hN.h_pos.le hμ0) hGrpos hM1
        hkpos hI0 hkI hmean hκ' hkκ hu hu1
      nlinarith
    -- the offset-share comparison
    have hUeq : ENNReal.ofReal (conZeta m * N.K i) / (N.J i (conZeta m * N.K i)
        * renewalM (N.marginal i) (Sh - sh)) = ENNReal.ofReal u := by
      rw [renewalM_eq]
      have e1 : renewalMeasure (N.marginal i) (Set.Ico 0 (Sh - sh)) = ENNReal.ofReal M := hUM
      have e2 : N.J i (conZeta m * N.K i) = ENNReal.ofReal Gr := hGeq
      rw [e1, e2, ← ENNReal.ofReal_mul hGr0, ← ENNReal.ofReal_div_of_pos (by positivity)]
    have hGB : ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i)
        = ENNReal.ofReal (conB m * Gr) := by
      rw [ENNReal.ofReal_mul (by linarith)]
      rw [show N.J i (conZeta m * N.K i) = ENNReal.ofReal Gr from hGeq]
    -- the bound `h ŵ ≤ (1 + 1/m) G`
    have hwG : N.h * wh ≤ (1 + 1 / m) * Gr := by
      have hcw := canonical_width_bound N hN i k sh Sh hcan'
      have hh := hN.h_pos; have hpp := hN.p_pos; have hHH := hN.H_pos i; have hHm := hH i
      have hm0 : 0 < m := by linarith
      have hc1 : 0 ≤ N.h * (N.H i + N.p) / (N.H i * (N.h + N.p)) := by positivity
      rw [show N.J i k = ENNReal.ofReal Gr from hGeq, ← ENNReal.ofReal_mul hc1] at hcw
      have hcw' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc1 hGr0)).1 hcw
      have e1 : N.h * N.p / (N.h + N.p) * (Sh - sh) = N.h * (N.p * wh) / (N.h + N.p) := by ring
      have e2 : N.h * (N.H i + N.p) / (N.H i * (N.h + N.p)) * Gr
          = N.h * ((N.H i + N.p) * Gr / N.H i) / (N.h + N.p) := by field_simp
      rw [e1, e2, div_le_div_iff_of_pos_right (by linarith),
        mul_le_mul_iff_of_pos_left hh, le_div_iff₀ hHH] at hcw'
      exact width_alg N.h N.p (N.H i) m wh Gr hh hpp hHH hm hHm hp hGr0 hcw'
    rcases le_or_gt (ENNReal.ofReal u) (ENNReal.ofReal (conU m)) with hle | hgt
    · -- the half-cycle policy
      have huU : u ≤ conU m := (ENNReal.ofReal_le_ofReal_iff hU0).1 hle
      obtain ⟨hs1, hs2, hs3, hs4, hbest⟩ := hhalf (by rw [hUeq]; exact hle)
      refine ⟨hs2, ?_⟩
      have hh := hN.h_pos; have hpp := hN.p_pos
      set w := c.S i - c.s i with hw
      have hw0 : 0 < w := sub_pos.2 hs2
      have hw2 : wh = 2 * w := by rw [hs4, hwh]; ring
      set Mw := (U (Set.Ico 0 w)).toReal with hMw
      have hMw1 : 1 ≤ Mw := by
        have h2 := ENNReal.toReal_mono (hUfin w).ne (one_le_renewal ρ w hw0)
        rwa [ENNReal.toReal_one] at h2
      have hMw0 : 0 < Mw := by linarith
      have hdbl : M ≤ 2 * Mw := by
        have h1 := renewal_doubling ρ w hw0.le
        have h2 : U (Set.Ico 0 wh) ≤ 2 * U (Set.Ico 0 w) := by rw [hw2]; exact h1
        have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) (hUfin w).ne) h2
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h3
      -- the maximizing shift
      have hgc : ContinuousOn (fun x => Gr - N.F i (Sh - x)) (Set.Icc 0 (2 * w)) :=
        (continuous_const.sub (hFc.comp (continuous_const.sub continuous_id))).continuousOn
      have hg0 : ∀ x ∈ Set.Icc (0 : ℝ) (2 * w), 0 ≤ Gr - N.F i (Sh - x) := fun x hx =>
        sub_nonneg.2 (hFb _ ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      have hgconc : ConcaveOn ℝ (Set.Icc 0 (2 * w)) (fun x => Gr - N.F i (Sh - x)) := by
        refine ⟨convex_Icc _ _, fun x _ y _ a b ha hb hab => ?_⟩
        have hcv := hFconv.2 (Set.mem_univ (Sh - x)) (Set.mem_univ (Sh - y)) ha hb hab
        simp only [smul_eq_mul] at hcv ⊢
        have e : a * (Sh - x) + b * (Sh - y) = Sh - (a * x + b * y) := by
          have : a * Sh + b * Sh = Sh := by rw [← add_mul, hab, one_mul]
          linarith
        rw [e] at hcv
        have : a * Gr + b * Gr = Gr := by rw [← add_mul, hab, one_mul]
        nlinarith
      obtain ⟨υ, hυ, hshift⟩ := half_window_shift ρ hρpos w hw0 _ hgc hg0 hgconc
      have iF : ∀ (a v : ℝ), 0 ≤ v → IntegrableOn (fun x => N.F i (a - x)) (Set.Ico 0 v) U :=
        fun a v hv => hInt v _ (N.F i a + (N.H i + N.p) * v)
          (hFm.comp (measurable_const.sub measurable_id)) fun x hx => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]
            have h1 := hFlip (a - x) a
            have h2 : |a - x - a| = x := by rw [show a - x - a = -x by ring, abs_neg, abs_of_nonneg hx.1]
            rw [h2] at h1
            have h3 := (abs_le.1 h1).2
            have : (N.H i + N.p) * x ≤ (N.H i + N.p) * v :=
              mul_le_mul_of_nonneg_left hx.2.le (by have := hN.H_pos i; linarith)
            linarith
      have iC : ∀ (v c' : ℝ), IntegrableOn (fun _ : ℝ => c') (Set.Ico 0 v) U := fun v c' =>
        hInt v _ |c'| measurable_const fun x _ => le_of_eq (Real.norm_eq_abs c')
      -- the full-window savings equal `k`
      have hgk : ∫ x in Set.Ico 0 (2 * w), (Gr - N.F i (Sh - x)) ∂U = k := by
        rw [← hw2, integral_sub (iC wh Gr) (iF Sh wh hwh0.le), setIntegral_const, smul_eq_mul]
        change M * Gr - I = k
        linarith
      rw [hgk, integral_sub (iC w Gr) (by
          have := iF (Sh - υ) w hw0.le
          refine this.congr_fun (fun x _ => by
            show N.F i (Sh - υ - x) = N.F i (Sh - (υ + x)); congr 1; ring) measurableSet_Ico),
        setIntegral_const, smul_eq_mul] at hshift
      set Iυ := ∫ x in Set.Ico 0 w, N.F i (Sh - (υ + x)) ∂U with hIυ
      have hIυb : Iυ ≤ Gr * Mw - k / 2 := by
        have : U.real (Set.Ico 0 w) = Mw := rfl
        rw [this] at hshift
        linarith
      -- the best half window
      have hcmp := hbest (Sh - υ - w) (Sh - υ) (by linarith [hυ.2]) (by linarith) (by linarith [hυ.1])
        (by rw [hwh] at hw2; linarith)
      have hrs := ss_renewal_reward ρ hρpos (N.F i) hFm hFnn 0 (c.s i) (c.S i) le_rfl hs2
        ⟨Gr, fun y hy => hFb y ⟨le_trans hs1 hy.1, le_trans hy.2 hs3⟩⟩
      have hrυ := ss_renewal_reward ρ hρpos (N.F i) hFm hFnn 0 (Sh - υ - w) (Sh - υ) le_rfl
        (by linarith) ⟨Gr, fun y hy => hFb y ⟨by linarith [hy.1, hυ.2], by linarith [hy.2, hυ.1]⟩⟩
      rw [show Sh - υ - (Sh - υ - w) = w by ring] at hrυ
      rw [hrs, hrυ] at hcmp
      set Is := ∫ x in Set.Ico 0 w, N.F i (c.S i - x) ∂renewalMeasure ρ with hIs
      have hIυ' : ∫ x in Set.Ico 0 w, N.F i (Sh - υ - x) ∂renewalMeasure ρ = Iυ :=
        setIntegral_congr_fun measurableSet_Ico fun x _ => by
          show N.F i (Sh - υ - x) = N.F i (Sh - (υ + x)); congr 1; ring
      rw [hIυ'] at hcmp
      have hIυ0 : 0 ≤ Iυ := setIntegral_nonneg measurableSet_Ico fun x _ => hFnn _
      have hIsυ : Is ≤ Iυ := by
        have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcmp
        rw [zero_add, zero_add] at this
        exact (div_le_div_iff_of_pos_right hMw0).1 this
      have hK73 : 0 ≤ 7 / 3 * N.K i := by have := hN.K_nonneg i; positivity
      have hbS : ∃ C, ∀ y ∈ Set.Icc (c.s i) (c.S i), N.F i y ≤ C :=
        ⟨Gr, fun y hy => hFb y ⟨le_trans hs1 hy.1, le_trans hy.2 hs3⟩⟩
      -- the setup and holding part
      have hT1 : ssAvgCost ρ (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
          ≤ ENNReal.ofReal (Gr + (14 / (3 * conZeta m) - 1) * (u * Gr)) := by
        rw [ss_renewal_reward ρ hρpos (N.F i) hFm hFnn _ _ _ hK73 hs2 hbS]
        refine ENNReal.ofReal_le_ofReal ?_
        change (7 / 3 * N.K i + Is) / Mw ≤ _
        have ha0 : 0 ≤ 7 / 3 * N.K i - k / 2 := by
          rw [hKk]
          have h1 : k / 2 ≤ k / conZeta m := div_le_div_of_nonneg_left hk0 hζ0 hζ2.le
          have h2 : 0 ≤ k / conZeta m := div_nonneg hk0 hζ0.le
          linarith
        have h1 : (7 / 3 * N.K i + Is) / Mw ≤ Gr + (7 / 3 * N.K i - k / 2) / Mw := by
          rw [div_le_iff₀ hMw0, add_mul, div_mul_cancel₀ _ hMw0.ne']
          nlinarith
        have h2 : (7 / 3 * N.K i - k / 2) / Mw ≤ (7 / 3 * N.K i - k / 2) / (M / 2) :=
          div_le_div_of_nonneg_left ha0 (by positivity) (by linarith)
        have h3 : (7 / 3 * N.K i - k / 2) / (M / 2) = (14 / (3 * conZeta m) - 1) * (u * Gr) := by
          rw [← hkM, hKk]; field_simp; ring
        linarith
      -- the mirror part
      have hT2 : ssAvgCost ρ (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i)
          ≤ ENNReal.ofReal (N.h * w / 2) := by
        have hm2 : Measurable fun y : ℝ => N.h * max (c.S i - y) 0 := by fun_prop
        rw [ss_renewal_reward ρ hρpos (fun y => N.h * max (c.S i - y) 0) hm2
          (fun y => mul_nonneg hh.le (le_max_right _ _)) 0 (c.s i) (c.S i) le_rfl hs2
          ⟨N.h * w, fun y hy => mul_le_mul_of_nonneg_left
            (max_le (by rw [hw]; linarith [hy.1]) hw0.le) hh.le⟩]
        refine ENNReal.ofReal_le_ofReal ?_
        have e : ∫ x in Set.Ico 0 (c.S i - c.s i), N.h * max (c.S i - (c.S i - x)) 0
            ∂renewalMeasure ρ = N.h * ∫ x in Set.Ico 0 w, x ∂U := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ico fun x hx => ?_
          rw [show c.S i - (c.S i - x) = x by ring, max_eq_left hx.1]
        rw [e, zero_add]
        have hdm := renewal_depletion_mean ρ w hw0.le
        have hIx : ∫ x in Set.Ico 0 w, x ∂U ≤ w / 2 * Mw := by
          have h0 : 0 ≤ᵐ[U.restrict (Set.Ico 0 w)] fun x : ℝ => x :=
            (ae_restrict_iff' measurableSet_Ico).2 (Filter.Eventually.of_forall fun x hx => hx.1)
          rw [integral_eq_lintegral_of_nonneg_ae (μ := U.restrict (Set.Ico 0 w)) (f := fun x => x)
            h0 measurable_id.aestronglyMeasurable]
          have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hUfin w).ne) hdm
          rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
        show N.h * (∫ x in Set.Ico 0 w, x ∂U) / Mw ≤ N.h * w / 2
        rw [div_le_iff₀ hMw0]
        have := mul_le_mul_of_nonneg_left hIx hh.le
        nlinarith
      have hT3 : min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
          (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
            * ssAvgCost (N.marginal i)
              (fun y => max (1 - 4 * ((c.S i - y) / (c.S i - c.s i)) / 3) 0 ^ 2 / (8 / 3)) 0
              (c.s i) (c.S i)) ≤ ENNReal.ofReal (N.h * (3 / 8) * w) := min_le_left _ _
      have hμ0 : 0 ≤ ∫ x, (x : ℝ) ∂ρ := integral_nonneg fun x => NNReal.coe_nonneg _
      have hR0 : 0 ≤ Gr + (14 / (3 * conZeta m) - 1) * (u * Gr) := by
        have : 0 ≤ 14 / (3 * conZeta m) - 1 := by
          rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
        positivity
      calc _ ≤ ENNReal.ofReal (Gr + (14 / (3 * conZeta m) - 1) * (u * Gr))
            + ENNReal.ofReal (N.h * w / 2) + ENNReal.ofReal (N.h * (3 / 8) * w)
            + ENNReal.ofReal (3 / 8 * N.h * ∫ x, (x : ℝ) ∂ρ) := by gcongr
        _ = ENNReal.ofReal (Gr + (14 / (3 * conZeta m) - 1) * (u * Gr) + N.h * w / 2
            + N.h * (3 / 8) * w + 3 / 8 * N.h * ∫ x, (x : ℝ) ∂ρ) := by
          have h0b : 0 ≤ N.h * w / 2 := div_nonneg (mul_nonneg hh.le hw0.le) (by norm_num)
          have h0c : 0 ≤ N.h * (3 / 8) * w := mul_nonneg (mul_nonneg hh.le (by norm_num)) hw0.le
          have h0d : 0 ≤ 3 / 8 * N.h * ∫ x, (x : ℝ) ∂ρ :=
            mul_nonneg (mul_nonneg (by norm_num) hh.le) hμ0
          rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hR0 h0b) h0c) h0d,
            ENNReal.ofReal_add (add_nonneg hR0 h0b) h0c, ENNReal.ofReal_add hR0 h0b]
        _ ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i) := by
          rw [hGB]
          refine ENNReal.ofReal_le_ofReal ?_
          have h6 := (arb_local_comparison m hm u).1 hu0 huU
          have h6' := mul_le_mul_of_nonneg_left h6 hGr0
          have hw' : N.h * w ≤ (1 + 1 / m) * Gr / 2 := by
            have : N.h * wh = 2 * (N.h * w) := by rw [hw2]; ring
            linarith
          set R := (1 - u) / (1 - u / (conZeta m * (conB m - 1 + u))) with hR
          calc Gr + (14 / (3 * conZeta m) - 1) * (u * Gr) + N.h * w / 2 + N.h * (3 / 8) * w
                + 3 / 8 * N.h * ∫ x, (x : ℝ) ∂ρ
              = Gr + (14 / (3 * conZeta m) - 1) * (u * Gr) + 7 / 8 * (N.h * w)
                + 3 / 8 * N.h * ∫ x, (x : ℝ) ∂ρ := by ring
            _ ≤ Gr + (14 / (3 * conZeta m) - 1) * (u * Gr) + 7 / 8 * ((1 + 1 / m) * Gr / 2)
                + 3 / 8 * (Gr * R) := by gcongr
            _ = Gr * (1 + 7 * (1 + 1 / m) / 16 + (14 / (3 * conZeta m) - 1) * u + 3 / 8 * R) := by
              ring
            _ ≤ Gr * conB m := h6'
            _ = conB m * Gr := by ring
    · -- the full-cycle policy
      have huU : conU m < u := (ENNReal.ofReal_lt_ofReal_iff'.1 hgt).1
      obtain ⟨hs_eq, hS_eq⟩ := hfull (by rw [hUeq]; exact hgt)
      rw [hs_eq, hS_eq]
      refine ⟨hsS, ?_⟩
      have hh := hN.h_pos; have hpp := hN.p_pos
      have hK73 : 0 ≤ 7 / 3 * N.K i := by have := hN.K_nonneg i; positivity
      have hT1 := ss_renewal_reward ρ hρpos (N.F i) hFm hFnn (7 / 3 * N.K i) sh Sh hK73 hsS
        ⟨Gr, hFb⟩
      have hm2 : Measurable fun y : ℝ => N.h * max (Sh - y) 0 := by fun_prop
      have hT2 := ss_renewal_reward ρ hρpos (fun y => N.h * max (Sh - y) 0) hm2
        (fun y => mul_nonneg hh.le (le_max_right _ _)) 0 sh Sh le_rfl hsS
        ⟨N.h * wh, fun y hy => mul_le_mul_of_nonneg_left (max_le (by linarith [hy.1]) hwh0.le) hh.le⟩
      set ψf : ℝ → ℝ := fun y => max (1 - 4 * ((Sh - y) / (Sh - sh)) / 3) 0 ^ 2 / (8 / 3) with hψf
      have hm3 : Measurable ψf := by rw [hψf]; fun_prop
      have hψ0 : ∀ y, 0 ≤ ψf y := fun y => by rw [hψf]; positivity
      have hψ1 : ∀ y ∈ Set.Icc sh Sh, ψf y ≤ 1 := fun y hy => by
        rw [hψf]
        have h0 : 0 ≤ (Sh - y) / (Sh - sh) := div_nonneg (by linarith [hy.2]) hwh0.le
        have h1 : max (1 - 4 * ((Sh - y) / (Sh - sh)) / 3) 0 ≤ 1 := max_le (by linarith) zero_le_one
        have h2 : max (1 - 4 * ((Sh - y) / (Sh - sh)) / 3) 0 ^ 2 ≤ 1 := by
          have := le_max_right (1 - 4 * ((Sh - y) / (Sh - sh)) / 3) 0
          nlinarith
        rw [div_le_one (by norm_num)]; linarith
      have hT3 := ss_renewal_reward ρ hρpos ψf hm3 hψ0 0 sh Sh le_rfl hsS ⟨1, hψ1⟩
      rw [hT1, hT2, hT3]
      -- the integrands on `[0, ŵ)`
      have eT2 : ∫ x in Set.Ico 0 (Sh - sh), N.h * max (Sh - (Sh - x)) 0 ∂renewalMeasure ρ
          = N.h * ∫ x in Set.Ico 0 wh, x ∂U := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ico fun x hx => ?_
        rw [show Sh - (Sh - x) = x by ring, max_eq_left hx.1]
      have eT3 : ∫ x in Set.Ico 0 (Sh - sh), ψf (Sh - x) ∂renewalMeasure ρ
          = ∫ x in Set.Ico 0 (Sh - sh), max (1 - 4 * (x / (Sh - sh)) / 3) 0 ^ 2 / (8 / 3)
              ∂renewalMeasure (N.marginal i) := by
        refine setIntegral_congr_fun measurableSet_Ico fun x hx => ?_
        simp only [hψf]
        rw [show Sh - (Sh - x) = x by ring]
      rw [eT2, eT3]
      set Ix := ∫ x in Set.Ico 0 wh, x ∂U with hIx
      set Jψ := ∫ x in Set.Ico 0 (Sh - sh), max (1 - 4 * (x / (Sh - sh)) / 3) 0 ^ 2 / (8 / 3)
        ∂renewalMeasure (N.marginal i) with hJψ
      have hIx0 : 0 ≤ Ix := setIntegral_nonneg measurableSet_Ico fun x hx => hx.1
      have hJψ0 : 0 ≤ Jψ := setIntegral_nonneg measurableSet_Ico fun x _ => by positivity
      have h5 := arb_width_bound N hN i m hm (hH i) hp k sh Sh hkpos hcan'
      have hJr : (N.J i k).toReal = Gr := by
        rw [show N.J i k = ENNReal.ofReal Gr from hGeq]; exact ENNReal.toReal_ofReal hGr0
      rw [hJr] at h5
      have h6 := (arb_local_comparison m hm u).2 huU.le hu1
      -- collect into one real number
      have hnn1 : 0 ≤ (7 / 3 * N.K i + I) / M := by positivity
      have hnn2 : 0 ≤ (0 + N.h * Ix) / M := by positivity
      have hnn3 : 0 ≤ (0 + Jψ) / M := by positivity
      have hnn4 : 0 ≤ (N.h + N.p) * (Sh - sh) := by positivity
      have hμ0 : 0 ≤ ∫ x, (x : ℝ) ∂ρ := integral_nonneg fun x => NNReal.coe_nonneg _
      have hnn5 : 0 ≤ 3 / 8 * N.h * ∫ x, (x : ℝ) ∂ρ := by positivity
      rw [← ENNReal.ofReal_mul hnn4, ← ENNReal.ofReal_min, ← ENNReal.ofReal_add hnn1 hnn2,
        ← ENNReal.ofReal_add (by positivity) (le_min (by positivity) (by positivity)),
        ← ENNReal.ofReal_add (by positivity) hnn5, hGB]
      refine ENNReal.ofReal_le_ofReal ?_
      -- the real inequality
      have eA : (7 / 3 * N.K i + I) / M = Gr + (7 / (3 * conZeta m) - 1) * (u * Gr) := by
        rw [← hkM, hKk]
        have hIe : I = Gr * M - k := by linarith
        rw [hIe]; field_simp; ring
      have eB : (0 + N.h * Ix) / M = N.h * Ix / M := by ring
      have eC : (N.h + N.p) * (Sh - sh) * ((0 + Jψ) / M) = (N.h + N.p) * (Sh - sh) * Jψ / M := by
        ring
      have eD : 7 / (12 * m) * k / M = 7 * (1 / m) / 12 * (u * Gr) := by
        rw [← hkM]; field_simp
      rw [eA, eB, eC]
      rw [eD] at h5
      have h5' : N.h * Ix / M + min (N.h * (3 / 8) * (Sh - sh)) ((N.h + N.p) * (Sh - sh) * Jψ / M)
          ≤ 7 / 8 * (1 + 1 / m) * Gr - 7 * (1 / m) / 12 * (u * Gr) := h5
      have h6' := mul_le_mul_of_nonneg_left h6 hGr0
      set R := (1 - u) / (1 - u / (conZeta m * (conB m - 1 + u))) with hR
      calc Gr + (7 / (3 * conZeta m) - 1) * (u * Gr) + N.h * Ix / M
            + min (N.h * (3 / 8) * (Sh - sh)) ((N.h + N.p) * (Sh - sh) * Jψ / M)
            + 3 / 8 * N.h * ∫ x, (x : ℝ) ∂ρ
          = Gr + (7 / (3 * conZeta m) - 1) * (u * Gr)
            + (N.h * Ix / M + min (N.h * (3 / 8) * (Sh - sh)) ((N.h + N.p) * (Sh - sh) * Jψ / M))
            + 3 / 8 * N.h * ∫ x, (x : ℝ) ∂ρ := by ring
        _ ≤ Gr + (7 / (3 * conZeta m) - 1) * (u * Gr)
            + (7 / 8 * (1 + 1 / m) * Gr - 7 * (1 / m) / 12 * (u * Gr)) + 3 / 8 * (Gr * R) :=
          add_le_add (add_le_add le_rfl h5') hmeanR
        _ = Gr * (1 + 7 * (1 + 1 / m) / 8 + (7 / (3 * conZeta m) - 1 - 7 * (1 / m) / 12) * u
              + 3 / 8 * R) := by ring
        _ ≤ Gr * conB m := h6'
        _ = conB m * Gr := by ring
