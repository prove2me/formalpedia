-- Prove2me | solution 1 for OWMR.fifo_retailer_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T01:38:24.395617+00:00
-- url     : https://prove2.me/submissions/d01832a2-ed32-4e68-bb7b-c1daac32c875

import Definitions.Def_owmr_fifo_policy
import Theorems.Thm_OWMR_fifo_candidate_comparison
import Theorems.Thm_OWMR_canonical_width_bound

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

/-- Base stock never drops below its target: the pre-action position of the `(S,S)` policy
started at `S` is at most `S`. -/
private lemma ssPre_base_le (S : ℝ) (d : ℕ → ℝ≥0) : ∀ t, ssPre S S d t ≤ S
  | 0 => le_rfl
  | t + 1 => by
      simp only [ssPre]
      rw [if_pos (ssPre_base_le S d t)]
      have := NNReal.coe_nonneg (d t)
      linarith

/-- Base stock keeps the post-action position at its target. -/
private lemma ssPost_base (S : ℝ) (d : ℕ → ℝ≥0) (t : ℕ) : ssPost S S d t = S := by
  simp [ssPost, ssPre_base_le]

/-- At zero setup cost, the base-stock policy at `S` has average cost at most `f S`. -/
private lemma ssAvgCost_base_le (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ)
    (S : ℝ) : ssAvgCost ρ f 0 S S ≤ ENNReal.ofReal (f S) := by
  unfold ssAvgCost
  refine Filter.limsup_le_of_le (h := Filter.Eventually.of_forall fun T => ?_)
  have hterm : ∀ z : Fin T → ℝ≥0, ∑ t ∈ Finset.range T,
      ENNReal.ofReal (ssPeriodCost f 0 S S (padHist T z) t) = T * ENNReal.ofReal (f S) := by
    intro z
    simp [ssPeriodCost, ssPost_base]
  simp only [hterm, lintegral_const, measure_univ, mul_one]
  rcases Nat.eq_zero_or_pos T with hT | hT
  · simp [hT]
  · rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hT.ne') (ENNReal.natCast_ne_top T),
      one_mul]

/-- Base stock has zero mirror cost (center at its target). -/
private lemma mirrorCost_base (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p S : ℝ) :
    mirrorCost ρ h p S S = 0 := by
  refine le_antisymm ((iInf_le _ S).trans ?_) (by positivity)
  unfold mirrorAvg
  refine Filter.limsup_le_of_le (h := Filter.Eventually.of_forall fun T => ?_)
  simp [whLoss, ssPost_base]

/-- The single-location value is at least the minimum of the running cost. -/
private lemma slValue_ge_min (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (S : ℝ)
    (hS : ∀ y, f S ≤ f y) (K : ℝ) (hK : 0 ≤ K) : ENNReal.ofReal (f S) ≤ slValue ρ f K := by
  unfold slValue
  refine le_iInf fun U => le_iInf fun _ => le_iInf fun ν => le_iInf fun _ =>
    le_iInf fun q => le_iInf fun _ => ?_
  unfold slAvgCost
  refine Filter.le_limsup_of_frequently_le ?_
  refine (Filter.eventually_atTop.2 ⟨1, fun T hT => ?_⟩).frequently
  have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  have hlow : ∀ ω : U × (Fin T → ℝ≥0), (T : ℝ≥0∞) * ENNReal.ofReal (f S)
      ≤ ∑ t ∈ Finset.range T, ENNReal.ofReal (slPeriodCost f K 0 q ω.1 (padHist T ω.2) t) := by
    intro ω
    calc (T : ℝ≥0∞) * ENNReal.ofReal (f S)
        = ∑ t ∈ Finset.range T, ENNReal.ofReal (f S) := by simp
      _ ≤ _ := by
        refine Finset.sum_le_sum fun t _ => ENNReal.ofReal_le_ofReal ?_
        unfold slPeriodCost
        have h1 := hS (slPos 0 q ω.1 (padHist T ω.2) t)
        split_ifs <;> nlinarith
  calc ENNReal.ofReal (f S)
      = (T : ℝ≥0∞)⁻¹ * ((T : ℝ≥0∞) * ENNReal.ofReal (f S)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T), one_mul]
    _ = (T : ℝ≥0∞)⁻¹ * ∫⁻ _ω, (T : ℝ≥0∞) * ENNReal.ofReal (f S)
          ∂(ν.prod (Measure.pi fun _ : Fin T => ρ)) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
        gcongr with ω
        exact hlow ω

theorem solution {n : ℕ} (N : Network n) (hN : N.Standing)
    (m : ℝ) (hm : 1 ≤ m) (c : FIFOChoice n) (hc : IsFIFOChoice N c) (i : Fin n)
    (hH : m * N.h ≤ N.H i) (hp : N.h ≤ N.p) :
    N.augCost i (c.s i) (c.S i)
      ≤ ENNReal.ofReal (5 / 4 + 1 / (4 * m)) * N.J i (5 * N.K i / 3) := by
  have hh : 0 < N.h := hN.h_pos
  have hHpos : 0 < N.H i := hN.H_pos i
  have hppos : 0 < N.p := hN.p_pos
  have hm0 : 0 < m := by linarith
  have hcoef1 : (1 : ℝ) ≤ 5 / 4 + 1 / (4 * m) := by
    have : (0 : ℝ) < 1 / (4 * m) := by positivity
    linarith
  rcases (hN.K_nonneg i).lt_or_eq with hK | hK
  · -- `K_i > 0`: the cheaper of the canonical window and its best half window
    obtain ⟨sh, Sh, s', S', hcan, hhalf, hsel, -⟩ := hc.1 i hK
    have hmin : N.augCost i (c.s i) (c.S i) = min (N.augCost i sh Sh) (N.augCost i s' S') := by
      rcases hsel with ⟨hs, hS, hle⟩ | ⟨hs, hS, hle⟩
      · rw [hs, hS, min_eq_left hle]
      · rw [hs, hS, min_eq_right hle]
    have hHh : N.h ≤ N.H i := le_trans (by nlinarith) hH
    have h1 := fifo_candidate_comparison N hN i hHh hp hK sh Sh s' S' hcan hhalf
    have h2 := canonical_width_bound N hN i (5 * N.K i / 3) sh Sh hcan
    set J := N.J i (5 * N.K i / 3) with hJ
    set β := N.h * N.p / (N.h + N.p) with hβ
    set cw := N.h * (N.H i + N.p) / (N.H i * (N.h + N.p)) with hcwdef
    have hβ0 : 0 ≤ β := by positivity
    have hcw0 : 0 ≤ cw := by positivity
    -- `c_w ≤ (m+1)/(2m)`, from `H_i ≥ m h` and `p ≥ h`
    have hcw : cw ≤ (m + 1) / (2 * m) := by
      rw [hcwdef, div_le_div_iff₀ (by positivity) (by positivity)]
      have hq : (0 : ℝ) ≤ N.p * (m + 1) - N.h * (m - 1) := by
        nlinarith [mul_le_mul_of_nonneg_right hp (by linarith : (0 : ℝ) ≤ m + 1)]
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hp)) hh.le) hm0.le,
        mul_nonneg (sub_nonneg.2 hH) hq]
    have hhalfw : ENNReal.ofReal (β * (Sh - sh) / 2) ≤ ENNReal.ofReal (cw / 2) * J := by
      have e1 : β * (Sh - sh) / 2 = 1 / 2 * (β * (Sh - sh)) := by ring
      have e2 : cw / 2 = 1 / 2 * cw := by ring
      rw [e1, e2, ENNReal.ofReal_mul (q := β * (Sh - sh)) (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_mul (q := cw) (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_assoc]
      gcongr
    rw [hmin]
    calc min (N.augCost i sh Sh) (N.augCost i s' S')
        ≤ J + ENNReal.ofReal (β * (Sh - sh) / 2) := h1
      _ ≤ J + ENNReal.ofReal (cw / 2) * J := add_le_add le_rfl hhalfw
      _ = ENNReal.ofReal (1 + cw / 2) * J := by
        rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one, add_mul, one_mul]
      _ ≤ ENNReal.ofReal (5 / 4 + 1 / (4 * m)) * J := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by positivity)
        have h4 : (m + 1) / (2 * m) / 2 = 1 / 4 + 1 / (4 * m) := by field_simp; ring
        linarith [hcw, h4]
  · -- `K_i = 0`: base stock at a minimizer of `F_i`
    obtain ⟨hsS, hmin, -⟩ := hc.2.1 i hK.symm
    have hK0 : N.K i = 0 := hK.symm
    have haug : N.augCost i (c.s i) (c.S i) ≤ ENNReal.ofReal (N.F i (c.S i)) := by
      unfold Network.augCost
      rw [hsS, hK0, mirrorCost_base, add_zero]
      exact ssAvgCost_base_le _ _ _
    have hJ0 : ENNReal.ofReal (N.F i (c.S i)) ≤ N.J i (5 * N.K i / 3) :=
      slValue_ge_min _ _ _ hmin _ (by rw [hK0]; norm_num)
    calc N.augCost i (c.s i) (c.S i) ≤ N.J i (5 * N.K i / 3) := haug.trans hJ0
      _ ≤ ENNReal.ofReal (5 / 4 + 1 / (4 * m)) * N.J i (5 * N.K i / 3) := by
        refine le_mul_of_one_le_left (by positivity) ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hcoef1
