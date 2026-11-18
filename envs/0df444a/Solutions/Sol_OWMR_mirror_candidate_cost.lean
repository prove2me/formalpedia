-- Prove2me | solution 1 for OWMR.mirror_candidate_cost
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:48:09.2102+00:00
-- url     : https://prove2.me/submissions/b75ec604-f259-4f07-9938-2dad17eb2b4c

import Theorems.Thm_OWMR_F_properties
import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Theorems.Thm_OWMR_renewal_depletion_mean
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.Monotone

/-!
Lemma 4 (Mirror Bounds and Candidate Cost). `X_w` has law `U(· ∩ [0, w)) / M(w)` and
`B_w = min_z 𝔼[p (z - X_w)⁺ + h (X_w - z)⁺]`. At the center `z = h w / (h + p)` the loss is at
most `β w` on `[0, w]`; at `z = 0` it equals `h y`, and Lemma 2 gives `𝔼 X_w ≤ w / 2`. For the
candidate cost, the renewal-reward identity (10) gives the setup, holding and backlog average
`(K + ∫_{[0,w)} F(Ŝ - υ - x) U(dx)) / M(w)`, and for every center `a = Γ - z` the long-run average
mirror loss is `𝔼[p (z - X_w)⁺ + h (X_w - z)⁺]`, so the mirror cost is `B_w`.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

namespace MCand

lemma marg_pos {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    0 < ∫⁻ x, (x : ℝ≥0∞) ∂(N.marginal i) := by
  unfold Network.marginal
  rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
  exact hN.mean_pos i

lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

lemma intOn_Ico (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (F : ℝ → ℝ) (hF : Continuous F) (w : ℝ) :
    IntegrableOn F (Set.Ico 0 w) (renewalMeasure ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := w)).exists_bound_of_continuousOn
    hF.continuousOn
  exact Measure.integrableOn_of_bounded (renewalMeasure_Ico_lt_top ρ hρ w).ne
    hF.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ico fun x hx =>
      hC x (Set.Ico_subset_Icc_self hx))

lemma bdd_Icc (f : ℝ → ℝ) (hfc : Continuous f) (s S : ℝ) : ∃ C, ∀ y ∈ Set.Icc s S, f y ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := S)).exists_bound_of_continuousOn
    hfc.continuousOn
  exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩

lemma F_cont {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) : Continuous (N.F i) := by
  obtain ⟨-, -, hlip, -⟩ := F_properties N hN i
  have hK : 0 ≤ N.H i + N.p := by linarith [hN.H_pos i, hN.p_pos]
  exact (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (N.H i + N.p)) fun a b => by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]; exact hlip a b).continuous

lemma mirrorAvg_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p s S a : ℝ) :
    mirrorAvg ρ h p s S a = ssAvgCost ρ (fun y => whLoss h p (a - y)) 0 s S := by
  unfold mirrorAvg ssAvgCost ssPeriodCost
  simp only [zero_mul, zero_add]

/-- Integrals against the depletion law `X_w`. -/
lemma integral_X (U : Measure ℝ) (w : ℝ) (φ : ℝ → ℝ) :
    ∫ y, φ y ∂((U (Set.Ico 0 w))⁻¹ • U.restrict (Set.Ico 0 w))
      = (∫ y in Set.Ico 0 w, φ y ∂U) / (U (Set.Ico 0 w)).toReal := by
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul]

end MCand

open MCand in
theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n)
    (k sh Sh : ℝ) (hk : 0 < k) (hcan : IsCanonicalOptimum (N.marginal i) (N.F i) k sh Sh)
    (X : ℝ → Measure ℝ) (hX : ∀ w, X w = (renewalMeasure (N.marginal i) (Set.Ico 0 w))⁻¹
      • (renewalMeasure (N.marginal i)).restrict (Set.Ico 0 w))
    (B : ℝ → ℝ)
    (hB : ∀ w, B w = ⨅ z : ℝ, ∫ y, (N.p * max (z - y) 0 + N.h * max (y - z) 0) ∂(X w)) :
    (∀ w, 0 < w → IsProbabilityMeasure (X w) ∧
      B w ≤ N.h * N.p / (N.h + N.p) * w ∧
      B w ≤ N.h * ∫ y, y ∂(X w) ∧ N.h * ∫ y, y ∂(X w) ≤ N.h * w / 2) ∧
    ∃ G : ℝ, 0 < G ∧ N.J i k = ENNReal.ofReal G ∧
      ∀ w υ : ℝ, 0 < w → w ≤ Sh - sh → 0 ≤ υ → υ ≤ Sh - sh - w →
        N.augCost i (Sh - υ - w) (Sh - υ) = ENNReal.ofReal (G
          + (N.K i - ∫ y in Set.Ico 0 w, (G - N.F i (Sh - (υ + y))) ∂(renewalMeasure (N.marginal i)))
            / (renewalMeasure (N.marginal i) (Set.Ico 0 w)).toReal + B w) := by
  obtain ⟨hF0, -, -, -⟩ := F_properties N hN i
  have hFc := F_cont N hN i
  have hρ := marg_pos N hN i
  have hh := hN.h_pos
  have hp := hN.p_pos
  -- the loss `L_z(y) = p (z - y)⁺ + h (y - z)⁺`
  have hLc : ∀ z : ℝ, Continuous fun y : ℝ => N.p * max (z - y) 0 + N.h * max (y - z) 0 :=
    fun z => by fun_prop
  have hL0 : ∀ z y : ℝ, 0 ≤ N.p * max (z - y) 0 + N.h * max (y - z) 0 := fun z y =>
    add_nonneg (mul_nonneg hp.le (le_max_right _ _)) (mul_nonneg hh.le (le_max_right _ _))
  have hwfacts : ∀ w, 0 < w → renewalMeasure (N.marginal i) (Set.Ico 0 w) ≠ ∞ ∧
      1 ≤ (renewalMeasure (N.marginal i) (Set.Ico 0 w)).toReal := fun w hw => by
    have hfin := (renewalMeasure_Ico_lt_top (N.marginal i) hρ w).ne
    refine ⟨hfin, ?_⟩
    have := ENNReal.toReal_mono hfin (one_le_renewal (N.marginal i) w hw)
    simpa using this
  have hBdd : ∀ w, BddBelow (Set.range fun z : ℝ =>
      ∫ y, (N.p * max (z - y) 0 + N.h * max (y - z) 0) ∂(X w)) :=
    fun w => ⟨0, by rintro _ ⟨z, rfl⟩; exact integral_nonneg fun y => hL0 z y⟩
  have hB0 : ∀ w, 0 ≤ B w := fun w => by
    rw [hB w]; exact le_ciInf fun z => integral_nonneg fun y => hL0 z y
  have hXint : ∀ w (φ : ℝ → ℝ), ∫ y, φ y ∂(X w)
      = (∫ y in Set.Ico 0 w, φ y ∂(renewalMeasure (N.marginal i)))
        / (renewalMeasure (N.marginal i) (Set.Ico 0 w)).toReal := fun w φ => by
    rw [hX w]; exact integral_X _ w φ
  constructor
  · intro w hw
    obtain ⟨hfin, hM1⟩ := hwfacts w hw
    have hM0 : 0 < (renewalMeasure (N.marginal i) (Set.Ico 0 w)).toReal := by linarith
    have hne0 : renewalMeasure (N.marginal i) (Set.Ico 0 w) ≠ 0 := by
      intro h0; rw [h0, ENNReal.toReal_zero] at hM1; linarith
    refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
    · rw [hX w, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        smul_eq_mul, ENNReal.inv_mul_cancel hne0 hfin]
    · -- center `z = h w / (h + p)`
      obtain ⟨z, hz⟩ : ∃ z : ℝ, z = N.h * w / (N.h + N.p) := ⟨_, rfl⟩
      have key1 : N.h * (w - z) = N.h * N.p / (N.h + N.p) * w := by
        rw [hz]; field_simp; try ring
      have key2 : N.p * z = N.h * N.p / (N.h + N.p) * w := by
        rw [hz]; field_simp; try ring
      have hpt : ∀ y ∈ Set.Ico 0 w, N.p * max (z - y) 0 + N.h * max (y - z) 0
          ≤ N.h * N.p / (N.h + N.p) * w := by
        intro y hy
        rcases le_total z y with hzy | hyz
        · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
          have := mul_le_mul_of_nonneg_left (sub_le_sub_right hy.2.le z) hh.le
          linarith
        · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
          have := mul_le_mul_of_nonneg_left (by linarith [hy.1] : z - y ≤ z) hp.le
          linarith
      have hint : ∫ y in Set.Ico 0 w, (N.p * max (z - y) 0 + N.h * max (y - z) 0)
            ∂(renewalMeasure (N.marginal i))
          ≤ N.h * N.p / (N.h + N.p) * w * (renewalMeasure (N.marginal i) (Set.Ico 0 w)).toReal := by
        calc _ ≤ ∫ _y in Set.Ico 0 w, N.h * N.p / (N.h + N.p) * w ∂(renewalMeasure (N.marginal i)) :=
              setIntegral_mono_on (intOn_Ico _ hρ _ (hLc z) w) (integrableOn_const hfin)
                measurableSet_Ico hpt
          _ = _ := by rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
      rw [hB w]
      refine (ciInf_le (hBdd w) z).trans ?_
      rw [hXint w, div_le_iff₀ hM0]
      exact hint
    · -- center `z = 0`: the loss is `h y` on the support
      rw [hB w]
      refine (ciInf_le (hBdd w) 0).trans (le_of_eq ?_)
      have e : ∫ y in Set.Ico 0 w, (N.p * max (0 - y) 0 + N.h * max (y - 0) 0)
            ∂(renewalMeasure (N.marginal i))
          = N.h * ∫ y in Set.Ico 0 w, y ∂(renewalMeasure (N.marginal i)) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ico fun y hy => ?_
        rw [max_eq_right (by linarith [hy.1]), max_eq_left (by linarith [hy.1])]
        ring
      rw [hXint w, hXint w, e, mul_div_assoc]
    · -- `𝔼 X_w ≤ w / 2` (Lemma 2)
      have hmean : ∫ y in Set.Ico 0 w, y ∂(renewalMeasure (N.marginal i))
          ≤ w / 2 * (renewalMeasure (N.marginal i) (Set.Ico 0 w)).toReal := by
        have hnn : 0 ≤ᵐ[(renewalMeasure (N.marginal i)).restrict (Set.Ico 0 w)] fun y : ℝ => y :=
          ae_restrict_of_forall_mem measurableSet_Ico fun y hy => hy.1
        rw [integral_eq_lintegral_of_nonneg_ae hnn continuous_id.aestronglyMeasurable]
        have hE := renewal_depletion_mean (N.marginal i) w hw.le
        have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hE
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
      rw [hXint w]
      have h1 : (∫ y in Set.Ico 0 w, y ∂(renewalMeasure (N.marginal i)))
          / (renewalMeasure (N.marginal i) (Set.Ico 0 w)).toReal ≤ w / 2 := by
        rw [div_le_iff₀ hM0]; exact hmean
      have := mul_le_mul_of_nonneg_left h1 hh.le
      linarith
  · -- the canonical value `G = F(ŝ) = J(k) > 0`
    have hsS : sh < Sh := hcan.1
    have hG0 : 0 ≤ N.F i sh := hF0 sh
    have hJ : N.J i k = ENNReal.ofReal (N.F i sh) := hcan.2.2.1.symm
    have hGpos : 0 < N.F i sh := by
      obtain ⟨hfin, hM1⟩ := hwfacts (Sh - sh) (by linarith)
      have hRR := ss_renewal_reward (N.marginal i) hρ (N.F i) hFc.measurable hF0 k sh Sh hk.le hsS
        (bdd_Icc _ hFc sh Sh)
      have hI0 : 0 ≤ ∫ x in Set.Ico 0 (Sh - sh), N.F i (Sh - x) ∂(renewalMeasure (N.marginal i)) :=
        setIntegral_nonneg measurableSet_Ico fun x _ => hF0 _
      have h1 : ENNReal.ofReal (N.F i sh) = ENNReal.ofReal ((k + ∫ x in Set.Ico 0 (Sh - sh),
          N.F i (Sh - x) ∂(renewalMeasure (N.marginal i)))
            / (renewalMeasure (N.marginal i) (Set.Ico 0 (Sh - sh))).toReal) := by
        rw [← hRR, hcan.2.1, ← hcan.2.2.1]
      have h2 := (ENNReal.ofReal_eq_ofReal_iff hG0 (div_nonneg (by linarith) (by linarith))).1 h1
      rw [h2]; exact div_pos (by linarith) (by linarith)
    refine ⟨N.F i sh, hGpos, hJ, fun w υ hw _ _ _ => ?_⟩
    obtain ⟨hfin, hM1⟩ := hwfacts w hw
    have hM0 : 0 < (renewalMeasure (N.marginal i) (Set.Ico 0 w)).toReal := by linarith
    obtain ⟨S, hS⟩ : ∃ S, S = Sh - υ := ⟨_, rfl⟩
    rw [← hS]
    have hsS' : S - w < S := by linarith
    unfold Network.augCost
    -- setup, holding and backlog: renewal reward
    have hss := ss_renewal_reward (N.marginal i) hρ (N.F i) hFc.measurable hF0 (N.K i) (S - w) S
      (hN.K_nonneg i) hsS' (bdd_Icc _ hFc _ _)
    rw [sub_sub_cancel] at hss
    -- the mirror cost is `B_w`
    have hfz : ∀ z : ℝ, mirrorAvg (N.marginal i) N.h N.p (S - w) S (S - z)
        = ENNReal.ofReal (∫ y, (N.p * max (z - y) 0 + N.h * max (y - z) 0) ∂(X w)) := by
      intro z
      have hφc : Continuous fun y => whLoss N.h N.p ((S - z) - y) := by unfold whLoss; fun_prop
      have hφ0 : ∀ y, 0 ≤ whLoss N.h N.p ((S - z) - y) := fun y =>
        add_nonneg (mul_nonneg hh.le (le_max_right _ _)) (mul_nonneg hp.le (le_max_right _ _))
      have e : ∀ y, whLoss N.h N.p ((S - z) - (S - y))
          = N.p * max (z - y) 0 + N.h * max (y - z) 0 := by
        intro y
        unfold whLoss
        rw [show S - z - (S - y) = y - z by ring, show -(y - z) = z - y by ring]
        ring
      rw [mirrorAvg_eq, ss_renewal_reward (N.marginal i) hρ _ hφc.measurable hφ0 0 _ S le_rfl hsS'
        (bdd_Icc _ hφc _ _), sub_sub_cancel, zero_add, hXint w]
      simp_rw [e]
    have hmir : mirrorCost (N.marginal i) N.h N.p (S - w) S = ENNReal.ofReal (B w) := by
      unfold mirrorCost
      rw [hB w, Monotone.map_ciInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
        (fun a b hab => ENNReal.ofReal_le_ofReal hab) (hBdd w)]
      exact (Function.Surjective.iInf_congr (fun z : ℝ => S - z)
        (fun a => ⟨S - a, sub_sub_cancel S a⟩) hfz).symm
    have hInn : 0 ≤ ∫ x in Set.Ico 0 w, N.F i (S - x) ∂(renewalMeasure (N.marginal i)) :=
      setIntegral_nonneg measurableSet_Ico fun x _ => hF0 _
    rw [hss, hmir, ← ENNReal.ofReal_add (div_nonneg (add_nonneg (hN.K_nonneg i) hInn) hM0.le)
      (hB0 w)]
    congr 1
    have hFint : IntegrableOn (fun y => N.F i (Sh - (υ + y))) (Set.Ico 0 w)
        (renewalMeasure (N.marginal i)) :=
      intOn_Ico _ hρ _ (hFc.comp (continuous_const.sub (continuous_const.add continuous_id))) w
    have hci : IntegrableOn (fun _ : ℝ => N.F i sh) (Set.Ico 0 w) (renewalMeasure (N.marginal i)) :=
      integrableOn_const (C := N.F i sh) hfin
    rw [integral_sub hci hFint, setIntegral_const, smul_eq_mul, measureReal_def]
    have e2 : ∫ x in Set.Ico 0 w, N.F i (S - x) ∂(renewalMeasure (N.marginal i))
        = ∫ y in Set.Ico 0 w, N.F i (Sh - (υ + y)) ∂(renewalMeasure (N.marginal i)) := by
      congr 1; funext y; rw [hS]; ring_nf
    rw [e2]
    field_simp
    ring
