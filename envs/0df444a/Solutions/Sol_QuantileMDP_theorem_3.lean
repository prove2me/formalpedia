-- Prove2me | solution 1 for QuantileMDP.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-14T01:39:36.843469+00:00
-- url     : https://prove2.me/submissions/1954c1b1-56a1-4165-82db-5a34c3afcc00

import Definitions.Def_QuantileMDP_augmentedPolicy
import Definitions.Def_QuantileMDP_dpValue
import Theorems.Thm_QuantileMDP_eq_6
import Theorems.Thm_QuantileMDP_eq_7
import Theorems.Thm_QuantileMDP_theorem_1

open MeasureTheory Set QuantileMDP
open scoped ENNReal

namespace QuantileMDP

private theorem level_mem {S : Type*} (next : ℕ → S → ℝ → S → ℝ)
    (hnext : ∀ t s τ, τ ∈ Icc (0 : ℝ) 1 → ∀ i, next t s τ i ∈ Icc (0 : ℝ) 1)
    (k t : ℕ) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) (h : Fin (k + 1) → S) :
    policyLevel next k t τ h ∈ Icc (0 : ℝ) 1 := by
  induction k generalizing t τ with
  | zero => exact hτ
  | succ k ih =>
    exact ih (t + 1) _ (hnext t (h 0) τ hτ (h 1)) (Fin.tail h)

private theorem augmented_admissible {S A : Type*} (M : Model S A)
    (act : ℕ → S → ℝ → A) (next : ℕ → S → ℝ → S → ℝ)
    (hact : ∀ t s τ, τ ∈ Icc (0 : ℝ) 1 → act t s τ ∈ M.adm t s)
    (hnext : ∀ t s τ, τ ∈ Icc (0 : ℝ) 1 → ∀ i, next t s τ i ∈ Icc (0 : ℝ) 1)
    (t : ℕ) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    (M.shift t).Admissible (augmentedPolicy act next t τ) := by
  intro k h
  exact hact _ _ _ (level_mem next hnext k t τ hτ h)

private theorem augmented_first {S A : Type*} (act : ℕ → S → ℝ → A)
    (next : ℕ → S → ℝ → S → ℝ) (t : ℕ) (τ : ℝ) (s : S) :
    augmentedPolicy act next t τ 0 (fun _ => s) = act t s τ := by
  simp [augmentedPolicy, policyLevel]

private theorem augmented_tail {S A : Type*} (act : ℕ → S → ℝ → A)
    (next : ℕ → S → ℝ → S → ℝ) (t : ℕ) (τ : ℝ) (s : S)
    (k : ℕ) (h : Fin (k + 1) → S) :
    (augmentedPolicy act next t τ).tail s k h =
      augmentedPolicy act next (t + 1) (next t s τ (h 0)) k h := by
  simp [Policy.tail, augmentedPolicy, policyLevel, Fin.cons_last,
    Nat.add_left_comm, Nat.add_comm]

/-- On paths beginning at `s`, only the policy's actions on histories that
begin at `s) enter the finite path sum. -/
private theorem rewardLaw_congr_start {S A : Type*} [Fintype S] (M : Model S A)
    (n : ℕ) (π ρ : Policy S A) (s : S)
    (h : ∀ k (g : Fin (k + 1) → S), g 0 = s → π k g = ρ k g) :
    rewardLaw M n π s = rewardLaw M n ρ s := by
  have hp (g : Fin n → S) (i : Fin n) : pathPrefix (Fin.cons s g) i 0 = s := by
    rfl
  unfold rewardLaw
  apply Finset.sum_congr rfl
  intro g _
  have hw : pathWeight M π (Fin.cons s g) = pathWeight M ρ (Fin.cons s g) := by
    unfold pathWeight
    exact Finset.prod_congr rfl fun i _ => by rw [h _ _ (hp g i)]
  have hr : pathReward M π (Fin.cons s g) = pathReward M ρ (Fin.cons s g) := by
    unfold pathReward
    exact Finset.sum_congr rfl fun i _ => by rw [h _ _ (hp g i)]
  rw [hw, hr]

private theorem augmented_tail_law {S A : Type*} [Fintype S] (M : Model S A)
    (act : ℕ → S → ℝ → A) (next : ℕ → S → ℝ → S → ℝ)
    (t n : ℕ) (τ : ℝ) (s i : S) :
    rewardLaw (M.shift (t + 1)) n ((augmentedPolicy act next t τ).tail s) i =
      rewardLaw (M.shift (t + 1)) n (augmentedPolicy act next (t + 1) (next t s τ i)) i := by
  apply rewardLaw_congr_start
  intro k h hh
  rw [augmented_tail, hh]

/-- A strict lower tail of mass below the requested level certifies a lower
bound on the quantile. A null lower tail also works at level zero. -/
private theorem le_quantile_of_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (h : (μ (Iio x)).toReal < τ ∨ μ (Iio x) = 0) :
    (x : EReal) ≤ quantile μ τ := by
  by_cases h0 : τ = 0
  · have hz := h.resolve_left (fun hlt => (not_lt_of_ge ENNReal.toReal_nonneg) (h0 ▸ hlt))
    have hc := prob_add_prob_compl (μ := μ) (measurableSet_Iio (a := x))
    rw [compl_Iio, hz, zero_add] at hc
    rw [quantile, if_pos h0]
    exact le_sSup ⟨x, hc, rfl⟩
  · have hp : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm h0)
    have hlt : μ (Iio x) < ENNReal.ofReal τ := by
      rcases h with h | h
      · exact (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top μ _)).mpr h
      · rw [h]
        exact ENNReal.ofReal_pos.mpr hp
    rw [quantile, if_neg h0]
    split_ifs with h1
    · subst τ
      rw [ENNReal.ofReal_one] at hlt
      apply le_sInf
      rintro _ ⟨z, hz, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (le_of_not_gt fun hzx =>
        hlt.not_ge (hz ▸ measure_mono (Iic_subset_Iio.mpr hzx)))
    · apply le_sInf
      rintro _ ⟨z, hz, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (le_of_not_gt fun hzx =>
        hlt.not_ge (hz.trans (measure_mono (Iic_subset_Iio.mpr hzx))))

private theorem tail_le_of_lt_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (q x : ℝ) (h : (x : EReal) < quantile μ q) (hq : q ∈ Icc (0 : ℝ) 1) :
    (μ (Iio x)).toReal ≤ q := by
  by_cases h0 : q = 0
  · subst q
    rw [quantile, if_pos rfl, lt_sSup_iff] at h
    obtain ⟨_, ⟨d, hd, rfl⟩, hxd⟩ := h
    have hc := prob_add_prob_compl (μ := μ) (measurableSet_Iio (a := d))
    rw [compl_Iio, hd] at hc
    have hz : μ (Iio d) = 0 :=
      (ENNReal.add_left_inj (by simp : (1 : ℝ≥0∞) ≠ ⊤)).mp (hc.trans (zero_add _).symm)
    rw [measure_mono_null (Iio_subset_Iio (EReal.coe_lt_coe_iff.mp hxd).le) hz,
      ENNReal.toReal_zero]
  · by_cases h1 : q = 1
    · subst q
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one :
        μ (Iio x) ≤ 1))
    · rw [quantile, if_neg h0, if_neg h1] at h
      have hx : ¬ ENNReal.ofReal q ≤ μ (Iic x) := fun hx =>
        h.not_ge (sInf_le ⟨x, hx, rfl⟩)
      exact ENNReal.toReal_le_of_le_ofReal hq.1
        ((measure_mono Iio_subset_Iic_self).trans (lt_of_not_ge hx).le)

/-- Every feasible allocation lower-bounds the mixture quantile by its
minimum retained branch quantile. -/
private theorem allocated_le_quantile {ι : Type*} [Fintype ι] (p : PMF ι)
    (ν : ι → Measure ℝ) (hν : ∀ i, IsProbabilityMeasure (ν i))
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) (q : ι → ℝ)
    (hq : q ∈ Feasible (fun i => (p i).toReal) τ) :
    (⨅ i, ⨅ (_ : q i ≠ 1), quantile (ν i) (q i)) ≤
      quantile (∑ i, p i • ν i) τ := by
  let μ : Measure ℝ := ∑ i, p i • ν i
  let : IsProbabilityMeasure μ := ⟨by
    unfold μ
    rw [Measure.finsetSum_apply _ _ _]
    simp only [Measure.smul_apply, smul_eq_mul, fun i => (hν i).measure_univ, mul_one]
    exact (tsum_fintype (fun i => p i)).symm.trans p.tsum_coe⟩
  by_contra! hn
  obtain ⟨x, hx, hxmin⟩ := EReal.exists_between_coe_real hn
  have hmass : (μ (Iio x)).toReal ≤ ∑ i, (p i).toReal * q i := by
    unfold μ
    rw [Measure.finsetSum_apply _ _ _]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_sum (fun i _ =>
      ENNReal.mul_ne_top (p.apply_ne_top i) (let := hν i; measure_ne_top _ _))]
    simp only [ENNReal.toReal_mul]
    apply Finset.sum_le_sum
    intro i _
    let := hν i
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    by_cases hi : q i = 1
    · rw [hi]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one :
        ν i (Iio x) ≤ 1))
    · exact tail_le_of_lt_quantile (ν i) (q i) x
        (hxmin.trans_le (iInf_le_of_le i (iInf_le _ hi))) (hq.1 i)
  apply hx.not_ge (le_quantile_of_tail μ τ x hτ ?_)
  rcases hq.2 with h | h
  · exact Or.inl (hmass.trans_lt h)
  · have hz : (μ (Iio x)).toReal = 0 :=
      le_antisymm (hmass.trans h.le) ENNReal.toReal_nonneg
    exact Or.inr ((ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top _ _))

private theorem rewardLaw_prob {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n t : ℕ) (π : Policy S A) (s : S)
    (hπ : (M.shift t).Admissible π) : IsProbabilityMeasure (rewardLaw (M.shift t) n π s) := by
  induction n generalizing t π s with
  | zero =>
    have hzero : rewardLaw (M.shift t) 0 π s = Measure.dirac 0 := by
      simp [rewardLaw, pathWeight, pathReward]
    rw [hzero]
    infer_instance
  | succ n ih =>
    have ht : t < t + (n + 1) := by omega
    have he := (eq_7 M (t + (n + 1)) t ht s (π 0 (fun _ => s))).1 π hπ rfl
    have hn : t + (n + 1) - t = n + 1 := by omega
    have hn' : t + (n + 1) - (t + 1) = n := by omega
    rw [hn, hn'] at he
    have htail : (M.shift (t + 1)).Admissible (π.tail s) := by
      intro k h
      simpa [Model.shift, Policy.tail, Fin.cons_last, Nat.add_left_comm, Nat.add_comm] using
        hπ (k + 1) (Fin.cons s h)
    constructor
    rw [he, Measure.finsetSum_apply _ _ _]
    have hp : ∑ i, M.P t s (π 0 (fun _ => s)) i = 1 :=
      (tsum_fintype (fun i => M.P t s (π 0 (fun _ => s)) i)).symm.trans (PMF.tsum_coe _)
    rw [← hp]
    apply Finset.sum_congr rfl
    intro i _
    have hm : Measurable (fun x : ℝ => x + M.r t s (π 0 (fun _ => s)) i) :=
      measurable_id.add_const _
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm MeasurableSet.univ,
      preimage_univ, (ih (t + 1) (π.tail s) i htail).measure_univ, mul_one]

private theorem quantile_map_add (μ : Measure ℝ) (c τ : ℝ) :
    quantile (μ.map (fun x => x + c)) τ = quantile μ τ + (c : EReal) := by
  let e : EReal ≃o EReal :=
    { toFun := fun x => x + (c : EReal)
      invFun := fun x => x - (c : EReal)
      left_inv := fun _ => EReal.add_sub_cancel_right
      right_inv := fun _ => EReal.sub_add_cancel
      map_rel_iff' := (EReal.addLECancellable_coe c).add_le_add_iff_right }
  have hm : Measurable (fun y : ℝ => y + c) := measurable_id.add_const c
  have h₁ (x : ℝ) : (μ.map (fun y => y + c)) (Ici x) = μ (Ici (x - c)) := by
    rw [Measure.map_apply hm measurableSet_Ici]
    congr 1
    ext y
    change (x ≤ y + c) ↔ (x - c ≤ y)
    exact sub_le_iff_le_add.symm
  have h₂ (x : ℝ) : (μ.map (fun y => y + c)) (Iic x) = μ (Iic (x - c)) := by
    rw [Measure.map_apply hm measurableSet_Iic]
    congr 1
    ext y
    change (y + c ≤ x) ↔ (y ≤ x - c)
    exact le_sub_iff_add_le.symm
  have himage (p : ℝ → Prop) :
      (fun x : ℝ => (x : EReal)) '' {x | p (x - c)} =
        e '' ((fun x : ℝ => (x : EReal)) '' {x | p x}) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨((x - c : ℝ) : EReal), ⟨x - c, hx, rfl⟩,
        by change ((x - c : ℝ) : EReal) + (c : EReal) = (x : EReal); rw [← EReal.coe_add, sub_add_cancel]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x + c, by simpa using hx, EReal.coe_add _ _⟩
  change _ = e (quantile μ τ)
  simp only [quantile, h₁, h₂]
  split_ifs
  · rw [himage (fun x => μ (Ici x) = 1)]
    rw [sSup_image, ← e.map_sSup]
  · rw [himage (fun x => μ (Iic x) = 1)]
    rw [sInf_image, ← e.map_sInf]
  · rw [himage (fun x => ENNReal.ofReal τ ≤ μ (Iic x))]
    rw [sInf_image, ← e.map_sInf]

private theorem quantile_dirac_zero (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    quantile (Measure.dirac (0 : ℝ)) τ = 0 := by
  have hl (x : ℝ) : Measure.dirac (0 : ℝ) (Ici x) = 1 ↔ x ≤ 0 := by
    rw [Measure.dirac_apply]
    by_cases hx : x ≤ 0 <;> simp [Set.indicator, hx]
  have hr (x : ℝ) : Measure.dirac (0 : ℝ) (Iic x) = 1 ↔ 0 ≤ x := by
    rw [Measure.dirac_apply]
    by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx]
  rw [quantile]
  split_ifs with hz h1
  · apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact EReal.coe_nonpos.mpr ((hl x).mp hx)
    · exact le_sSup ⟨0, (hl 0).mpr le_rfl, EReal.coe_zero⟩
  · apply le_antisymm
    · exact sInf_le ⟨0, (hr 0).mpr le_rfl, EReal.coe_zero⟩
    · refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      exact EReal.coe_nonneg.mpr ((hr x).mp hx)
  · have htpos : 0 < ENNReal.ofReal τ := ENNReal.ofReal_pos.mpr (lt_of_le_of_ne hτ.1 (Ne.symm hz))
    have htle : ENNReal.ofReal τ ≤ 1 := ENNReal.ofReal_le_one.mpr hτ.2
    apply le_antisymm
    · refine sInf_le ⟨0, ?_, EReal.coe_zero⟩
      change ENNReal.ofReal τ ≤ Measure.dirac (0 : ℝ) (Iic 0)
      rw [(hr 0).mpr le_rfl]
      exact htle
    · refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      apply EReal.coe_nonneg.mpr
      by_contra! h
      have hzero : Measure.dirac (0 : ℝ) (Iic x) = 0 := by
        simp [Set.indicator, not_le_of_gt h]
      exact (not_le_of_gt htpos) (hzero ▸ hx)

private theorem optValue_zero {S A : Type*} [Fintype S] (M : Model S A)
    (T t : ℕ) (ht : T - t = 0) (s : S) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    optValue M T t s τ = 0 := by
  have hlaw (π : Policy S A) : rewardLaw (M.shift t) (T - t) π s = Measure.dirac 0 := by
    rw [ht]
    simp [rewardLaw, pathWeight, pathReward]
  have hval (π : Policy S A) : quantile (rewardLaw (M.shift t) (T - t) π s) τ = 0 := by
    rw [hlaw, quantile_dirac_zero τ hτ]
  let π : Policy S A := fun k h => ((M.shift t).adm_nonempty k (h (Fin.last k))).choose
  have hπ : (M.shift t).Admissible π := fun k h =>
    ((M.shift t).adm_nonempty k (h (Fin.last k))).choose_spec
  exact le_antisymm (iSup_le fun ρ => iSup_le fun _ => (hval ρ).le)
    ((hval π).ge.trans (le_iSup_of_le π (le_iSup_of_le hπ le_rfl)))

private theorem dpAux_eq_value {S A : Type*} [Fintype S] [Fintype A] (M : Model S A)
    (T n t : ℕ) (hn : T - t = n) (s : S) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    dpAux M n t s τ = optValue M T t s τ := by
  induction n generalizing t s τ with
  | zero => exact (optValue_zero M T t hn s τ hτ).symm
  | succ n ih =>
    have ht : t < T := by omega
    have hn' : T - (t + 1) = n := by omega
    rw [(eq_6 M T t s τ).1, dpAux]
    congr 1
    funext a
    congr 1
    funext ha
    rw [(theorem_1 M T t ht s a ha τ hτ).1]
    unfold opt
    congr 1
    funext q
    congr 1
    funext hq
    simp_rw [fun i => ih (t + 1) hn' i (q i) (hq.1 i)]

private theorem shift_zero {S A : Type*} (M : Model S A) : M.shift 0 = M := by
  cases M
  simp [Model.shift]

private theorem augmented_optimal {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (T : ℕ) (act : ℕ → S → ℝ → A) (next : ℕ → S → ℝ → S → ℝ)
    (ha : ∀ t s τ, τ ∈ Icc (0 : ℝ) 1 → act t s τ ∈ M.adm t s)
    (hq : ∀ t s τ, τ ∈ Icc (0 : ℝ) 1 → ∀ i, next t s τ i ∈ Icc (0 : ℝ) 1)
    (hg : ∀ t < T, ∀ s τ, τ ∈ Icc (0 : ℝ) 1 →
      let a := act t s τ
      let q := next t s τ
      q ∈ Feasible (fun i => (M.P t s a i).toReal) τ ∧
      (⨅ i, ⨅ (_ : q i ≠ 1), optValue M T (t + 1) i (q i) + (M.r t s a i : EReal)) =
        optValue M T t s τ)
    (n t : ℕ) (hn : T - t = n) (s : S) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    quantile (rewardLaw (M.shift t) n (augmentedPolicy act next t τ) s) τ =
      optValue M T t s τ := by
  induction n generalizing t s τ with
  | zero =>
    rw [optValue_zero M T t hn s τ hτ]
    have hzero : rewardLaw (M.shift t) 0 (augmentedPolicy act next t τ) s = Measure.dirac 0 := by
      simp [rewardLaw, pathWeight, pathReward]
    rw [hzero, quantile_dirac_zero τ hτ]
  | succ n ih =>
    let π := augmentedPolicy act next t τ
    have hπ := augmented_admissible M act next ha hq t τ hτ
    have ht : t < T := by omega
    have hn' : T - (t + 1) = n := by omega
    obtain ⟨hfeas, hbest⟩ := hg t ht s τ hτ
    apply le_antisymm
    · rw [← hn]
      exact le_iSup_of_le π (le_iSup_of_le hπ le_rfl)
    · let a := act t s τ
      let q := next t s τ
      let ν : S → Measure ℝ := fun i =>
        (rewardLaw (M.shift (t + 1)) n (augmentedPolicy act next (t + 1) (q i)) i).map
          (fun x => x + M.r t s a i)
      have hν (i : S) : IsProbabilityMeasure (ν i) := by
        let := rewardLaw_prob M n (t + 1) (augmentedPolicy act next (t + 1) (q i)) i
          (augmented_admissible M act next ha hq _ _ (hq t s τ hτ i))
        exact Measure.isProbabilityMeasure_map (measurable_id.add_const _).aemeasurable
      have hlaw : rewardLaw (M.shift t) (n + 1) π s = ∑ i, M.P t s a i • ν i := by
        have he := (eq_7 M T t ht s a).1 π hπ (augmented_first act next t τ s)
        rw [hn, hn'] at he
        dsimp only [π] at he
        simp_rw [augmented_tail_law M act next t n τ s] at he
        exact he
      rw [hlaw, ← hbest]
      have hbranch (i : S) : quantile (ν i) (q i) =
          optValue M T (t + 1) i (q i) + (M.r t s a i : EReal) := by
        unfold ν
        rw [quantile_map_add, ih (t + 1) hn' i (q i) (hq t s τ hτ i)]
      simpa only [hbranch] using allocated_le_quantile (M.P t s a) ν hν τ hτ q hfeas

end QuantileMDP

/-- Finite-horizon optimal policy on the augmented state of Theorem 3. -/
theorem solution {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T : ℕ) :
    ∃ (act : ℕ → S → ℝ → A) (next : ℕ → S → ℝ → S → ℝ),
      (∀ t s τ, τ ∈ Set.Icc (0 : ℝ) 1 → act t s τ ∈ M.adm t s) ∧
      (∀ t < T, ∀ s τ, τ ∈ Set.Icc (0 : ℝ) 1 →
        let a := act t s τ
        let q := next t s τ
        let p := fun i => (M.P t s a i).toReal
        let g := fun i u => dpValue M T (t + 1) i u + (M.r t s a i : EReal)
        q ∈ Feasible p τ ∧
          (⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)) = opt p g τ ∧
          opt p g τ = dpValue M T t s τ) ∧
      ∀ t s τ, τ ∈ Set.Icc (0 : ℝ) 1 →
        (M.shift t).Admissible (augmentedPolicy act next t τ) ∧
          quantile (rewardLaw (M.shift t) (T - t) (augmentedPolicy act next t τ) s) τ =
            dpValue M T t s τ := by
  classical
  have hdp (t : ℕ) (s : S) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
      dpValue M T t s τ = optValue M T t s τ :=
    dpAux_eq_value M T (T - t) t rfl s τ hτ
  have hchoice (t : ℕ) (s : S) (τ : ℝ) :
      ∃ (a : A) (q : S → ℝ),
        a ∈ M.adm t s ∧ (∀ i, q i ∈ Icc (0 : ℝ) 1) ∧
        (t < T → τ ∈ Icc (0 : ℝ) 1 →
          let p := fun i => (M.P t s a i).toReal
          let g := fun i u => optValue M T (t + 1) i u + (M.r t s a i : EReal)
          q ∈ Feasible p τ ∧ (⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)) = opt p g τ ∧
            opt p g τ = optValue M T t s τ) := by
    by_cases h : t < T ∧ τ ∈ Icc (0 : ℝ) 1
    · obtain ⟨a, ha, hva⟩ := (eq_6 M T t s τ).2
      obtain ⟨hact, ⟨q, hq, hqopt⟩, _⟩ := theorem_1 M T t h.1 s a ha τ h.2
      exact ⟨a, q, ha, hq.1, fun _ _ => ⟨hq, hqopt, hact.symm.trans hva⟩⟩
    · obtain ⟨a, ha⟩ := M.adm_nonempty t s
      exact ⟨a, fun _ => 0, ha, fun _ => ⟨le_rfl, zero_le_one⟩,
        fun ht hτ => (h ⟨ht, hτ⟩).elim⟩
  choose act next ha hq hbest using hchoice
  have hg (t : ℕ) (ht : t < T) (s : S) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
      let a := act t s τ
      let q := next t s τ
      q ∈ Feasible (fun i => (M.P t s a i).toReal) τ ∧
      (⨅ i, ⨅ (_ : q i ≠ 1), optValue M T (t + 1) i (q i) + (M.r t s a i : EReal)) =
        optValue M T t s τ := by
    obtain ⟨hf, hopt, hv⟩ := hbest t s τ ht hτ
    exact ⟨hf, hopt.trans hv⟩
  refine ⟨act, next, fun t s τ _ => ha t s τ, ?_, ?_⟩
  · intro t ht s τ hτ
    dsimp only
    let p := fun i => (M.P t s (act t s τ) i).toReal
    let g := fun i u => optValue M T (t + 1) i u + (M.r t s (act t s τ) i : EReal)
    let gdp := fun i u => dpValue M T (t + 1) i u + (M.r t s (act t s τ) i : EReal)
    obtain ⟨hf, ho, hv⟩ := hbest t s τ ht hτ
    have hbranch (q : S → ℝ) (hq' : q ∈ Feasible p τ) :
        (⨅ i, ⨅ (_ : q i ≠ 1), gdp i (q i)) = ⨅ i, ⨅ (_ : q i ≠ 1), g i (q i) := by
      simp only [gdp, g, fun i => hdp (t + 1) i (q i) (hq'.1 i)]
    have he : opt p gdp τ = opt p g τ := by
      unfold opt
      congr 1
      funext q
      congr 1
      funext h
      exact hbranch q h
    exact ⟨hf, (hbranch _ hf).trans (ho.trans he.symm),
      he.trans (hv.trans (hdp t s τ hτ).symm)⟩
  · intro t s τ hτ
    have hact (k : ℕ) (x : S) (u : ℝ) (_ : u ∈ Icc (0 : ℝ) 1) :=
      ha k x u
    have hnext (k : ℕ) (x : S) (u : ℝ) (_ : u ∈ Icc (0 : ℝ) 1) (i : S) :=
      hq k x u i
    exact ⟨augmented_admissible M act next hact hnext t τ hτ,
      (augmented_optimal M T act next hact hnext hg (T - t) t rfl s τ hτ).trans
        (hdp t s τ hτ).symm⟩
