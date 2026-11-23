-- Prove2me | solution 1 for PhysReaudit.expected_tau_le
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T09:46:10.130547+00:00
-- url     : https://prove2.me/submissions/21d6ce92-4ea4-4541-b65b-101a11dc3f4e

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_sprtS
import Theorems.Thm_PhysReaudit_increment_mean

open MeasureTheory ProbabilityTheory
open LimitedPriceChanges.LowerBound (klBer)

namespace PRExpTau
open PhysReaudit

/-- The event `{τ > k}`: no boundary crossed at times `1, …, k`. -/
def Ev (q₀ t δ : ℝ) (k : ℕ) : Set (ℕ → Bool) :=
  {y | ∀ j, 1 ≤ j → j ≤ k →
    -Real.log (1 / δ) < sprtS q₀ t y j ∧ sprtS q₀ t y j < Real.log (1 / δ)}

lemma lt_tau_iff (q₀ t δ : ℝ) (y : ℕ → Bool) (k : ℕ) :
    (k : ℕ∞) < sprtTau q₀ t δ y ↔ y ∈ Ev q₀ t δ k := by
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top k)]
  simp only [sprtTau, le_iInf_iff, Ev, Set.mem_ofPred_eq]
  constructor
  · intro h j hj1 hjk
    by_contra hc
    have := h j ⟨hj1, by
      rcases not_and_or.mp hc with h' | h'
      · right; linarith [not_lt.mp h']
      · left; linarith [not_lt.mp h']⟩
    have : (k : ℕ∞) + 1 ≤ (j : ℕ∞) := this
    norm_cast at this
    omega
  · intro h n hn
    by_contra hc
    have hc' : n ≤ k := by
      have : ¬ ((k + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hc
      norm_cast at this; omega
    obtain ⟨a, b⟩ := h n hn.1 hc'
    rcases hn.2 with h' | h' <;> linarith

lemma enat_eq_tsum (e : ℕ∞) :
    (e : ENNReal) = ∑' k : ℕ, if (k : ℕ∞) < e then (1 : ENNReal) else 0 := by
  induction e using ENat.recTopCoe with
  | top =>
    simp only [ENat.natCast_lt_top, if_true, ENat.toENNReal_top]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe n =>
    rw [tsum_eq_sum (s := Finset.range n)]
    · simp only [Nat.cast_lt]
      rw [Finset.sum_ite_of_true (fun k hk => Finset.mem_range.mp hk)]
      simp
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp only [Nat.cast_lt]
      rw [if_neg (by omega)]

lemma tau_eq_tsum (q₀ t δ : ℝ) (y : ℕ → Bool) :
    (sprtTau q₀ t δ y : ENNReal) = ∑' k, (Ev q₀ t δ k).indicator 1 y := by
  rw [enat_eq_tsum]
  refine tsum_congr fun k => ?_
  by_cases h : y ∈ Ev q₀ t δ k <;> simp [h, lt_tau_iff]

lemma measurable_S_past (q₀ t : ℝ) {j k : ℕ} (hjk : j ≤ k) :
    Measurable[pastFiltration k] (fun y => sprtS q₀ t y j) := by
  unfold sprtS
  refine Finset.measurable_sum _ fun i hi => ?_
  have hik : i ∈ Finset.range k := Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hi) hjk)
  have h1 : Measurable[MeasurableSpace.comap (fun y : ℕ → Bool => y i) inferInstance]
      (fun y : ℕ → Bool => sprtIncr q₀ t (y i)) :=
    (measurable_of_countable (sprtIncr q₀ t)).comp (comap_measurable _)
  refine h1.mono ?_ le_rfl
  exact le_iSup₂ (f := fun j (_ : j ∈ Finset.range k) =>
      MeasurableSpace.comap (fun y : ℕ → Bool => y j) inferInstance) i hik

lemma measurableSet_Ev (q₀ t δ : ℝ) (k : ℕ) :
    MeasurableSet[pastFiltration k] (Ev q₀ t δ k) := by
  have : Ev q₀ t δ k = ⋂ j ∈ Finset.Icc 1 k,
      ({y | -Real.log (1 / δ) < sprtS q₀ t y j} ∩ {y | sprtS q₀ t y j < Real.log (1 / δ)}) := by
    ext y; simp [Ev, Finset.mem_Icc]
  rw [this]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hm := measurable_S_past q₀ t (k := k) hjk
  exact (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const)

lemma Ev_succ_subset (q₀ t δ : ℝ) (k : ℕ) : Ev q₀ t δ (k + 1) ⊆ Ev q₀ t δ k :=
  fun _ hy j h1 h2 => hy j h1 (by omega)

/-- Pointwise bound on the stopped sum. -/
lemma stopped_le (q₀ t δ : ℝ) (hA : 0 < Real.log (1 / δ)) (hz : 0 ≤ zPlus q₀ t)
    (hinc : ∀ b, sprtIncr q₀ t b ≤ zPlus q₀ t) (y : ℕ → Bool) (n : ℕ) :
    (y ∈ Ev q₀ t δ n → ∑ k ∈ Finset.range n,
        (Ev q₀ t δ k).indicator (fun y => sprtIncr q₀ t (y k)) y = sprtS q₀ t y n) ∧
    ∑ k ∈ Finset.range n, (Ev q₀ t δ k).indicator (fun y => sprtIncr q₀ t (y k)) y
      ≤ Real.log (1 / δ) + zPlus q₀ t := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact ⟨fun _ => by simp [sprtS], by linarith⟩
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hy : y ∈ Ev q₀ t δ n
    · rw [Set.indicator_of_mem hy, ih.1 hy]
      have hS : sprtS q₀ t y n < Real.log (1 / δ) := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp only [sprtS, Finset.range_zero, Finset.sum_empty]; exact hA
        · exact (hy n hn le_rfl).2
      refine ⟨fun _ => by simp [sprtS, Finset.sum_range_succ], ?_⟩
      linarith [hinc (y n)]
    · rw [Set.indicator_of_notMem hy, add_zero]
      exact ⟨fun h => absurd (Ev_succ_subset q₀ t δ n h) hy, ih.2⟩

end PRExpTau

open PhysReaudit in
theorem solution {q₀ t δ : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1 / 2) {q : ℝ} (hq : q ∈ Set.Icc 0 q₀) :
    ∫⁻ y, (sprtTau q₀ t δ y : ENNReal) ∂(Measure.infinitePi fun _ : ℕ => bern q)
      ≤ ENNReal.ofReal ((Real.log (1 / δ) + zPlus q₀ t) / klBer q₀ t) := by
  obtain ⟨hq0, hqq⟩ := hq
  have ht0 : 0 < t := h0.trans h1
  have hA : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hzp : 0 < zPlus q₀ t :=
    Real.log_pos ((one_lt_div (by linarith)).mpr (by linarith))
  have hzm : zMinus q₀ t < 0 := Real.log_neg (div_pos h0 ht0) ((div_lt_one ht0).mpr h1)
  have hinc : ∀ b, sprtIncr q₀ t b ≤ zPlus q₀ t := by
    intro b; cases b <;> simp [sprtIncr] <;> linarith
  obtain ⟨_, hmono, heq, hD⟩ := increment_mean h0 h1 h2
  set m := q * zMinus q₀ t + (1 - q) * zPlus q₀ t with hm
  have hmD : klBer q₀ t ≤ m := heq ▸ hmono q hqq
  have hb : IsProbabilityMeasure (bern q) := by
    constructor
    simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hq0 (by linarith)]; simp
  set μ := Measure.infinitePi fun _ : ℕ => bern q with hμ
  set g : Bool → ℝ := fun b => sprtIncr q₀ t b with hg
  have hgint : ∀ k, Integrable (fun y : ℕ → Bool => g (y k)) μ := by
    intro k
    refine Integrable.of_bound ((measurable_of_countable g).comp (measurable_pi_apply k)).aestronglyMeasurable
      (|zMinus q₀ t| + |zPlus q₀ t|) (ae_of_all _ fun y => ?_)
    cases y k <;> simp [hg, sprtIncr, Real.norm_eq_abs] <;>
      linarith [abs_nonneg (zMinus q₀ t), abs_nonneg (zPlus q₀ t)]
  have hce : ∀ k, μ[fun y => g (y k) | pastFiltration k] =ᵐ[μ] (fun _ => m) := by
    intro n
    have hind : iIndepFun (fun i (ω : ℕ → Bool) => ω i) μ :=
      iIndepFun_infinitePi (P := fun _ : ℕ => bern q) (X := fun _ b => b) (fun _ => measurable_id)
    have hI : Indep (⨆ i ∈ ({n} : Set ℕ), MeasurableSpace.comap (fun ω : ℕ → Bool => ω i) inferInstance)
        (⨆ i ∈ ((Finset.range n : Finset ℕ) : Set ℕ),
          MeasurableSpace.comap (fun ω : ℕ → Bool => ω i) inferInstance) μ :=
      indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind
        (by simp)
    simp only [iSup_singleton] at hI
    have hle1 : MeasurableSpace.comap (fun ω : ℕ → Bool => ω n) inferInstance ≤ MeasurableSpace.pi :=
      (measurable_pi_apply n).comap_le
    have hfm : StronglyMeasurable[MeasurableSpace.comap (fun ω : ℕ → Bool => ω n) inferInstance]
        (fun y : ℕ → Bool => g (y n)) :=
      ((measurable_of_countable g).comp (comap_measurable _)).stronglyMeasurable
    have hce := condExp_indep_eq hle1 ((pastFiltration).le n) hfm hI
    refine hce.trans (Filter.Eventually.of_forall (fun _ => ?_))
    have hmap : ∫ y, g (y n) ∂μ = ∫ b, g b ∂(bern q) := by
      rw [← (measurePreserving_eval_infinitePi (fun _ : ℕ => bern q) n).map_eq,
        integral_map (measurable_pi_apply n).aemeasurable (measurable_of_countable g).aestronglyMeasurable]
    show ∫ y, g (y n) ∂μ = _
    rw [hmap]
    have i1 : Integrable g (Measure.dirac true) := integrable_dirac (by simp)
    have i0 : Integrable g (Measure.dirac false) := integrable_dirac (by simp)
    rw [bern, integral_add_measure (i1.smul_measure ENNReal.ofReal_ne_top)
      (i0.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, ENNReal.toReal_ofReal hq0, ENNReal.toReal_ofReal (by linarith)]
    simp only [hg, sprtIncr, if_true, Bool.false_eq_true, if_false, smul_eq_mul, hm]
  have hmeas : ∀ k, MeasurableSet (PRExpTau.Ev q₀ t δ k) :=
    fun k => (pastFiltration).le k _ (PRExpTau.measurableSet_Ev q₀ t δ k)
  have hint : ∀ k, ∫ y, (PRExpTau.Ev q₀ t δ k).indicator (fun y => g (y k)) y ∂μ
      = μ.real (PRExpTau.Ev q₀ t δ k) * m := by
    intro k
    rw [integral_indicator (hmeas k),
      ← setIntegral_condExp ((pastFiltration).le k) (hgint k) (PRExpTau.measurableSet_Ev q₀ t δ k),
      setIntegral_congr_ae (hmeas k) ((hce k).mono fun y hy _ => hy), setIntegral_const, smul_eq_mul]
  have hsum : ∀ n, (∑ k ∈ Finset.range n, μ.real (PRExpTau.Ev q₀ t δ k)) * m
      ≤ Real.log (1 / δ) + zPlus q₀ t := by
    intro n
    rw [Finset.sum_mul]
    simp_rw [← hint]
    rw [← integral_finsetSum _ (fun k _ => (hgint k).indicator (hmeas k))]
    calc _ ≤ ∫ _y, (Real.log (1 / δ) + zPlus q₀ t) ∂μ :=
          integral_mono (integrable_finsetSum _ (fun k _ => (hgint k).indicator (hmeas k)))
            (integrable_const _)
            (fun y => (PRExpTau.stopped_le q₀ t δ hA hzp.le hinc y n).2)
      _ = _ := by simp
  calc ∫⁻ y, (sprtTau q₀ t δ y : ENNReal) ∂μ
      = ∫⁻ y, ∑' k, (PRExpTau.Ev q₀ t δ k).indicator 1 y ∂μ := by
        simp_rw [PRExpTau.tau_eq_tsum]
    _ = ∑' k, μ (PRExpTau.Ev q₀ t δ k) := by
        rw [lintegral_tsum fun k => (measurable_one.indicator (hmeas k)).aemeasurable]
        exact tsum_congr fun k => lintegral_indicator_one (hmeas k)
    _ ≤ _ := by
        refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
        have : ∑ k ∈ Finset.range n, μ (PRExpTau.Ev q₀ t δ k)
            = ENNReal.ofReal (∑ k ∈ Finset.range n, μ.real (PRExpTau.Ev q₀ t δ k)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        rw [this]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ hD]
        have hnn : 0 ≤ ∑ k ∈ Finset.range n, μ.real (PRExpTau.Ev q₀ t δ k) :=
          Finset.sum_nonneg fun _ _ => measureReal_nonneg
        exact (mul_le_mul_of_nonneg_left hmD hnn).trans (hsum n)
