-- Prove2me | solution 1 for XMX.nonstationary_expected_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:38:27.80266+00:00
-- url     : https://prove2.me/submissions/b1d8f779-9843-4327-b4fc-0eaa52779adf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_XMX_nonstationary_period_expected_ge_bound
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_XMX_NonstationaryInventory

open MeasureTheory
open scoped BigOperators
open XMX
set_option maxHeartbeats 250000

private lemma inventory_continuous (T L k : ℕ) (U : ℝ) :
    Continuous (fun z : Levels T L U × Demand T L U => inventory T L U z.1 z.2 k) := by
  dsimp only [inventory]
  apply Continuous.finset_sup'_apply
  intro j hj
  apply Continuous.sub
  · split_ifs with h
    · exact (continuous_apply (⟨j, h⟩ : Fin (T + L))).comp continuous_fst |>.subtype_val
    · exact continuous_const
  · apply continuous_finsetSum
    intro r hr
    split_ifs with h
    · exact (continuous_apply (⟨r, h⟩ : Fin (T + L))).comp continuous_snd |>.subtype_val
    · exact continuous_const

private lemma loss_continuous (T L : ℕ) (U h b : ℝ) :
    Continuous (fun z : Levels T L U × Demand T L U => loss T L U h b z.1 z.2) := by
  unfold loss cost
  apply Continuous.div_const
  apply continuous_finsetSum
  intro k hk
  have hc := (inventory_continuous T L k U).sub
    (((continuous_apply (⟨L + k, by omega⟩ : Fin (T + L))).comp continuous_snd).subtype_val)
  exact (continuous_const.mul (hc.max continuous_const)).add
    (continuous_const.mul (hc.neg.max continuous_const))

private lemma empirical_continuous {P X : Type*} [TopologicalSpace X]
    (N : ℕ) (f : P → X → ℝ) (hf : ∀ p, Continuous (f p)) (p : P) :
    Continuous (fun data : Fin N → X => empiricalRisk N f data p) := by
  unfold empiricalRisk
  exact (continuous_finsetSum _ fun i _ => (hf p).comp (continuous_apply i)).div_const _

private lemma bounded_empirical {P X : Type*} (N : ℕ) (hN : 0 < N)
    (f : P → X → ℝ) (K : ℝ) (hK : ∀ p x, ‖f p x‖ ≤ K) (data : Fin N → X) (p : P) :
    ‖empiricalRisk N f data p‖ ≤ K := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold empiricalRisk
  rw [norm_div, Real.norm_natCast, div_le_iff₀ hn]
  calc
    ‖∑ i : Fin N, f p (data i)‖ ≤ ∑ i : Fin N, ‖f p (data i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, K := Finset.sum_le_sum fun i _ => hK p (data i)
    _ = K * N := by simp [mul_comm]

private lemma bounded_statistics {P X : Type*} [Nonempty P]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (N : ℕ) (hN : 0 < N) (μ : Measure X) [IsProbabilityMeasure μ]
    (f : P → X → ℝ) (hf : ∀ p, Continuous (f p))
    (K : ℝ) (hK : ∀ p x, ‖f p x‖ ≤ K) :
    (∀ p, Integrable (f p) μ) ∧
    (∀ data : Fin N → X,
      BddAbove (Set.range (fun p => risk μ f p - empiricalRisk N f data p))) ∧
    Integrable (generalizationError N μ f) (Measure.pi (fun _ : Fin N => μ)) := by
  classical
  let pstar : P := Classical.choice inferInstance
  let ν := Measure.pi (fun _ : Fin N => μ)
  have hint (p : P) : Integrable (f p) μ :=
    Integrable.of_bound (hf p).aestronglyMeasurable K (Filter.Eventually.of_forall (hK p))
  have hrisk (p : P) : ‖risk μ f p‖ ≤ K := by
    simpa [risk] using (norm_integral_le_of_norm_le_const (μ := μ) (f := f p)
      (Filter.Eventually.of_forall (hK p)))
  have hdiff (data : Fin N → X) (p : P) :
      ‖risk μ f p - empiricalRisk N f data p‖ ≤ 2 * K := by
    calc
      _ ≤ ‖risk μ f p‖ + ‖empiricalRisk N f data p‖ := norm_sub_le _ _
      _ ≤ K + K := add_le_add (hrisk p) (bounded_empirical N hN f K hK data p)
      _ = 2 * K := by ring
  have hbdd (data : Fin N → X) :
      BddAbove (Set.range (fun p => risk μ f p - empiricalRisk N f data p)) := by
    refine ⟨2 * K, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact le_trans (le_abs_self _) (hdiff data p)
  have hGEmeas : Measurable (generalizationError N μ f) := by
    apply LowerSemicontinuous.measurable
    exact lowerSemicontinuous_ciSup hbdd (fun p =>
      (continuous_const.sub (empirical_continuous N f hf p)).lowerSemicontinuous)
  have hGEbound (data : Fin N → X) : ‖generalizationError N μ f data‖ ≤ 2 * K := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have hs := le_ciSup (hbdd data) pstar
      have hd := (abs_le.mp (hdiff data pstar)).1
      exact hd.trans hs
    · exact ciSup_le fun p => (le_abs_self _).trans (hdiff data p)
  have hGE : Integrable (generalizationError N μ f) ν :=
    Integrable.of_bound hGEmeas.aestronglyMeasurable (2 * K)
      (Filter.Eventually.of_forall hGEbound)
  exact ⟨hint, hbdd, hGE⟩

private lemma erm_expected_le_generalization {P X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (N : ℕ) (hN : 0 < N) (μ : Measure X) [IsProbabilityMeasure μ]
    (f : P → X → ℝ) (hf : ∀ p, Continuous (f p))
    (K : ℝ) (hK : ∀ p x, ‖f p x‖ ≤ K)
    (select : (Fin N → X) → P) (pstar : P)
    (hselect : ∀ data p, empiricalRisk N f data (select data) ≤ empiricalRisk N f data p)
    (hselected : Integrable (fun data => risk μ f (select data))
      (Measure.pi (fun _ : Fin N => μ))) :
    expectedEE N μ f select pstar ≤ expectedGE N μ f := by
  classical
  let : Nonempty P := ⟨pstar⟩
  let ν := Measure.pi (fun _ : Fin N => μ)
  obtain ⟨hint, hbdd, hGE⟩ := bounded_statistics N hN μ f hf K hK
  have heach (i : Fin N) : Integrable (fun data : Fin N → X => f pstar (data i)) ν :=
    integrable_comp_eval (hint pstar)
  have hemp : Integrable (fun data : Fin N → X => empiricalRisk N f data pstar) ν := by
    exact (integrable_finsetSum _ fun i _ => heach i).div_const _
  have hunbiased : (∫ data, empiricalRisk N f data pstar ∂ν) = risk μ f pstar := by
    unfold empiricalRisk risk
    rw [integral_div, integral_finsetSum _ fun i _ => heach i]
    change (∑ i : Fin N, ∫ data : Fin N → X, f pstar (data i) ∂Measure.pi (fun _ => μ)) /
      (N : ℝ) = ∫ x, f pstar x ∂μ
    simp_rw [integral_comp_eval (μ := fun _ : Fin N => μ) (hint pstar).aestronglyMeasurable]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.ne_of_gt hN))
  have hpoint (data : Fin N → X) :
      risk μ f (select data) - risk μ f pstar ≤ generalizationError N μ f data +
        (empiricalRisk N f data pstar - risk μ f pstar) := by
    have hsup := le_ciSup (hbdd data) (select data)
    have hmin := hselect data pstar
    change _ ≤ (⨆ p, risk μ f p - empiricalRisk N f data p) + _
    linarith
  have hle := integral_mono (hselected.sub (integrable_const _))
    (hGE.add (hemp.sub (integrable_const _))) hpoint
  change (∫ data, risk μ f (select data) - risk μ f pstar ∂ν) ≤
    ∫ data, generalizationError N μ f data +
      (empiricalRisk N f data pstar - risk μ f pstar) ∂ν at hle
  have hradd := integral_add hGE (hemp.sub (integrable_const (risk μ f pstar)))
  have hrsub := integral_sub hemp (integrable_const (risk μ f pstar))
  simp only [Pi.sub_apply] at hradd hrsub
  rw [hrsub, hunbiased] at hradd
  have hrconst : (∫ _data : Fin N → X, risk μ f pstar ∂ν) = risk μ f pstar := by
    simp [ν]
  rw [hrconst, sub_self, add_zero] at hradd
  rw [hradd] at hle
  exact hle

private lemma inventory_erm_le (T L N : ℕ) (hN : 0 < N) (U h b : ℝ)
    (μ : Measure (Demand T L U)) [IsProbabilityMeasure μ]
    (select : (Fin N → Demand T L U) → Levels T L U) (pstar : Levels T L U)
    (hselect : ∀ data p, empiricalRisk N (loss T L U h b) data (select data) ≤
      empiricalRisk N (loss T L U h b) data p)
    (hselected : Integrable (fun data => risk μ (loss T L U h b) (select data))
      (Measure.pi (fun _ : Fin N => μ))) :
    expectedEE N μ (loss T L U h b) select pstar ≤
      expectedGE N μ (loss T L U h b) := by
  have hc := loss_continuous T L U h b
  have hbdd : BddAbove (Set.range (fun z : Levels T L U × Demand T L U =>
      ‖loss T L U h b z.1 z.2‖)) := (isCompact_range hc.norm).bddAbove
  obtain ⟨K, hK⟩ := hbdd
  have hfc (p : Levels T L U) : Continuous (loss T L U h b p) := by
    have hpair : Continuous (fun d : Demand T L U => (p, d)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using hc.comp hpair
  have hkc : ∀ (p : Levels T L U) (d : Demand T L U), ‖loss T L U h b p d‖ ≤ K :=
    fun p d => hK ⟨(p, d), rfl⟩
  exact erm_expected_le_generalization N hN μ (loss T L U h b)
    hfc K hkc select pstar hselect hselected


private lemma average_expected_ge_le {P X : Type*} [Nonempty P]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (T N : ℕ) (hT : 0 < T) (hN : 0 < N) (μ : Measure X) [IsProbabilityMeasure μ]
    (f : Fin T → P → X → ℝ) (hf : ∀ k p, Continuous (f k p))
    (K : Fin T → ℝ) (hK : ∀ k p x, ‖f k p x‖ ≤ K k) :
    expectedGE N μ (fun p x => (∑ k, f k p x) / (T : ℝ)) ≤
      (∑ k, expectedGE N μ (f k)) / (T : ℝ) := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let avg : P → X → ℝ := fun p x => (∑ k, f k p x) / (T : ℝ)
  have hs k := bounded_statistics N hN μ (f k) (hf k) (K k) (hK k)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hbound (p : P) (x : X) : ‖avg p x‖ ≤ (∑ k, K k) / (T : ℝ) := by
    simp only [avg, norm_div, Real.norm_natCast]
    apply div_le_div_of_nonneg_right _ hT0.le
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => hK k p x))
  have hcont (p : P) : Continuous (avg p) :=
    (continuous_finsetSum _ (fun k _ => hf k p)).div_const _
  have hsa := bounded_statistics N hN μ avg hcont _ hbound
  have hr (p : P) : risk μ avg p = (∑ k, risk μ (f k) p) / (T : ℝ) := by
    unfold risk avg
    rw [integral_div, integral_finsetSum _ (fun k _ => (hs k).1 p)]
  have he (data : Fin N → X) (p : P) : empiricalRisk N avg data p =
      (∑ k, empiricalRisk N (f k) data p) / (T : ℝ) := by
    simp only [empiricalRisk, avg, Finset.sum_div, div_div]
    simp_rw [mul_comm (T : ℝ) (N : ℝ)]
    exact Finset.sum_comm
  have hp (data : Fin N → X) : generalizationError N μ avg data ≤
      (∑ k, generalizationError N μ (f k) data) / (T : ℝ) := by
    apply ciSup_le
    intro p
    rw [hr, he, ← sub_div, ← Finset.sum_sub_distrib]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun k _ =>
      le_ciSup ((hs k).2.1 data) p) hT0.le
  have hsum : Integrable (fun data => (∑ k, generalizationError N μ (f k) data) /
      (T : ℝ)) ν :=
    (integrable_finsetSum _ (fun k _ => (hs k).2.2)).div_const _
  have hi := integral_mono hsa.2.2 hsum hp
  change expectedGE N μ avg ≤ _ at hi
  calc
    expectedGE N μ avg ≤ _ := hi
    _ = (∑ k, expectedGE N μ (f k)) / (T : ℝ) := by
      rw [integral_div, integral_finsetSum _ (fun k _ => (hs k).2.2)]
      rfl

private lemma period_continuous (T L : ℕ) (U h b : ℝ) (k : Fin T) :
    Continuous (fun z : Levels T L U × Demand T L U =>
      cost h b (inventory T L U z.1 z.2 k - (z.2 ⟨L + k, by omega⟩ : ℝ))) := by
  have hc := (inventory_continuous T L k U).sub
    (((continuous_apply (⟨L + k, by omega⟩ : Fin (T + L))).comp continuous_snd).subtype_val)
  unfold cost
  exact (continuous_const.mul (hc.max continuous_const)).add
    (continuous_const.mul (hc.neg.max continuous_const))

private lemma inventory_average_ge_le (T L N : ℕ) (hT : 0 < T) (hN : 0 < N)
    (U h b : ℝ) (hU : 0 < U) (μ : Measure (Demand T L U)) [IsProbabilityMeasure μ] :
    expectedGE N μ (loss T L U h b) ≤
      (∑ k : Fin T, expectedGE N μ (fun (S : Levels T L U) (d : Demand T L U) =>
        cost h b (inventory T L U S d k - (d ⟨L + k, by omega⟩ : ℝ)))) / (T : ℝ) := by
  classical
  let : Nonempty (Levels T L U) := ⟨fun _ => ⟨0, le_rfl,
    mul_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) + 1) hU.le⟩⟩
  let f : Fin T → Levels T L U → Demand T L U → ℝ := fun k S d =>
    cost h b (inventory T L U S d k - (d ⟨L + k, by omega⟩ : ℝ))
  have hc (k : Fin T) : Continuous (fun z : Levels T L U × Demand T L U => f k z.1 z.2) :=
    period_continuous T L U h b k
  have hbound (k : Fin T) : ∃ K : ℝ, ∀ p x, ‖f k p x‖ ≤ K := by
    obtain ⟨K, hK⟩ := (isCompact_range (hc k).norm).bddAbove
    exact ⟨K, fun p x => hK ⟨(p, x), rfl⟩⟩
  choose K hK using hbound
  have hfc (k : Fin T) (p : Levels T L U) : Continuous (f k p) := by
    have hpair : Continuous (fun d : Demand T L U => (p, d)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using (hc k).comp hpair
  exact average_expected_ge_le T N hT hN μ f hfc K hK

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (T L N : ℕ), 0 < T → 0 < N →
      ∀ (U h b : ℝ), 0 < U → h ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (μ : Measure (Demand T L U)) [IsProbabilityMeasure μ],
      expectedGE N μ (loss T L U h b) ≤ C * (((L : ℝ) + 1) * U) / Real.sqrt N ∧
      ∀ (select : (Fin N → Demand T L U) → Levels T L U)
        (pstar : Levels T L U),
        (∀ data p, empiricalRisk N (loss T L U h b) data (select data) ≤
          empiricalRisk N (loss T L U h b) data p) →
        (∀ p, risk μ (loss T L U h b) pstar ≤ risk μ (loss T L U h b) p) →
        Integrable (fun data => risk μ (loss T L U h b) (select data))
          (Measure.pi (fun _ : Fin N => μ)) →
        expectedEE N μ (loss T L U h b) select pstar ≤
          expectedGE N μ (loss T L U h b) := by
  obtain ⟨C, hC, hperiod⟩ := XMX.nonstationary_period_expected_ge_bound
  refine ⟨C, hC, ?_⟩
  intro T L N hT hN U h b hU hh hb μ hμ
  constructor
  · have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    calc
      expectedGE N μ (loss T L U h b) ≤ _ :=
        inventory_average_ge_le T L N hT hN U h b hU μ
      _ ≤ (∑ _k : Fin T, C * (((L : ℝ) + 1) * U) / Real.sqrt N) / (T : ℝ) :=
        div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun k _ => hperiod T L N hT hN U h b hU hh hb μ k)) hT0.le
      _ = C * (((L : ℝ) + 1) * U) / Real.sqrt N := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_div_cancel_left₀ _ hT0.ne'
  · intro select pstar hselect _hstar hint
    exact inventory_erm_le T L N hN U h b μ select pstar hselect hint

#print axioms solution
