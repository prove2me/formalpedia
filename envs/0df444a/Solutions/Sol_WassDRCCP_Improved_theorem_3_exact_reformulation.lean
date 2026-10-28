-- Prove2me | solution 1 for WassDRCCP.Improved.theorem_3_exact_reformulation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T07:00:25.148683+00:00
-- url     : https://prove2.me/submissions/e3670899-c35f-4808-ae1e-56bf1e23b97e

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WDRCCP3Aux

open WassDRCCP.Improved

/-! ### Order statistics -/

theorem os_facts {N : ℕ} (v : Fin N → ℝ) (k : ℕ) (hk : k < N) :
    (Finset.univ.filter (fun i => v i < kthSmallest v k)).card ≤ k ∧
    k + 1 ≤ (Finset.univ.filter (fun i => v i ≤ kthSmallest v k)).card := by
  classical
  set m : Multiset ℝ := Finset.univ.val.map v with hm
  set l : List ℝ := m.sort (· ≤ ·) with hl
  have hsorted : l.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hlm : (l : Multiset ℝ) = m := Multiset.sort_eq _ _
  have hlen : l.length = N := by
    rw [hl, Multiset.length_sort, hm, Multiset.card_map]; simp
  have hkl : k < l.length := hlen ▸ hk
  have hs : kthSmallest v k = l[k] := by
    show l.getD k 0 = l[k]
    exact List.getD_eq_getElem _ _ hkl
  have hcount : ∀ (q : ℝ → Prop) [DecidablePred q],
      (Finset.univ.filter (fun i => q (v i))).card = l.countP (fun y => decide (q y)) := by
    intro q _
    have h1 : (l : Multiset ℝ).countP q = l.countP (fun y => decide (q y)) :=
      Multiset.coe_countP _ _
    rw [← h1, hlm, hm, Multiset.countP_map]
    rfl
  have hsortedij : ∀ i j (hi : i < l.length) (hj : j < l.length), i ≤ j → l[i] ≤ l[j] := by
    intro i j hi hj hij
    rcases hij.lt_or_eq with h | h
    · exact List.pairwise_iff_getElem.1 hsorted i j hi hj h
    · subst h; exact le_rfl
  have hsplit : ∀ (p : ℝ → Bool) (n : ℕ),
      l.countP p = (l.take n).countP p + (l.drop n).countP p := by
    intro p n
    rw [← List.countP_append, List.take_append_drop]
  rw [hs, hcount (fun y => y < l[k]), hcount (fun y => y ≤ l[k])]
  constructor
  · have h0 : (l.drop k).countP (fun y => decide (y < l[k])) = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      rw [List.getElem_drop]
      simp only [decide_eq_true_eq, not_lt]
      exact hsortedij _ _ hkl _ (Nat.le_add_right _ _)
    rw [hsplit _ k, h0, add_zero]
    calc _ ≤ (l.take k).length := List.countP_le_length
      _ ≤ k := by simp
  · have h0 : (l.take (k + 1)).countP (fun y => decide (y ≤ l[k])) = k + 1 := by
      rw [List.countP_eq_length.2]
      · simp only [List.length_take]; omega
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      rw [List.getElem_take]
      simp only [decide_eq_true_eq]
      simp only [List.length_take] at hj
      exact hsortedij _ _ _ hkl (by omega)
    rw [hsplit _ (k + 1), h0]
    exact Nat.le_add_right _ _

/-! ### Distance to the unsafe set -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_compl_safety {L P : ℕ} (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E)
    (d : Fin P → ℝ) (x : Fin L → ℝ) (y : E) :
    y ∈ (safetySet a b d x)ᶜ ↔ ∃ p, b p y + d p - a p ⬝ᵥ x ≤ 0 := by
  simp [safetySet]

theorem dist_lower {L P : ℕ} (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E)
    (d : Fin P → ℝ) (hb : ∀ p, b p ≠ 0) (x : Fin L → ℝ) (u : E) (s : ℝ)
    (hne : (safetySet a b d x)ᶜ.Nonempty)
    (hs : ∀ p, s ≤ (b p u + d p - a p ⬝ᵥ x) / ‖b p‖) :
    s ≤ Metric.infDist u (safetySet a b d x)ᶜ := by
  rw [Metric.le_infDist hne]
  intro y hy
  obtain ⟨p, hp⟩ := (mem_compl_safety a b d x y).1 hy
  have hbp : 0 < ‖b p‖ := norm_pos_iff.2 (hb p)
  have h1 := hs p
  rw [le_div_iff₀ hbp] at h1
  have h2 : b p (u - y) ≤ ‖b p‖ * ‖u - y‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (b p).le_opNorm (u - y))
  rw [map_sub] at h2
  rw [dist_eq_norm]
  refine le_of_mul_le_mul_right ?_ hbp
  nlinarith

theorem dist_upper {L P : ℕ} (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E)
    (d : Fin P → ℝ) (hb : ∀ p, b p ≠ 0) (x : Fin L → ℝ) (u : E) (p : Fin P) :
    Metric.infDist u (safetySet a b d x)ᶜ ≤ max 0 ((b p u + d p - a p ⬝ᵥ x) / ‖b p‖) := by
  set c := b p u + d p - a p ⬝ᵥ x with hc
  have hbp : 0 < ‖b p‖ := norm_pos_iff.2 (hb p)
  by_cases hc0 : c ≤ 0
  · have : u ∈ (safetySet a b d x)ᶜ := (mem_compl_safety a b d x u).2 ⟨p, hc0⟩
    rw [Metric.infDist_zero_of_mem this]; exact le_max_left _ _
  push_neg at hc0
  refine le_max_of_le_right ?_
  by_contra hlt
  push_neg at hlt
  set D := Metric.infDist u (safetySet a b d x)ᶜ with hD
  have hDpos : 0 < D := lt_trans (div_pos hc0 hbp) hlt
  have hr : c / D < ‖b p‖ := by
    rw [div_lt_iff₀ hDpos]; rw [div_lt_iff₀ hbp] at hlt; linarith
  obtain ⟨w, hw1, hw2⟩ := (b p).exists_lt_apply_of_lt_opNorm hr
  rw [Real.norm_eq_abs] at hw2
  obtain ⟨w', hw1', hw2'⟩ : ∃ w' : E, ‖w'‖ < 1 ∧ c / D < b p w' := by
    rcases le_or_gt 0 (b p w) with h | h
    · exact ⟨w, hw1, by rwa [abs_of_nonneg h] at hw2⟩
    · refine ⟨-w, by rwa [norm_neg], ?_⟩
      rw [map_neg]; rwa [abs_of_neg h] at hw2
  have hcD : 0 < c / D := div_pos hc0 hDpos
  have hbw : 0 < b p w' := hcD.trans hw2'
  set sc := c / b p w' with hsc
  have hsc0 : 0 < sc := div_pos hc0 hbw
  have hmem : u - sc • w' ∈ (safetySet a b d x)ᶜ := by
    refine (mem_compl_safety a b d x _).2 ⟨p, ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, hsc, div_mul_cancel₀ _ hbw.ne']
    linarith
  have h1 : D ≤ dist u (u - sc • w') := Metric.infDist_le_dist_of_mem hmem
  rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos hsc0] at h1
  have h2 : sc * ‖w'‖ < sc := mul_lt_of_lt_one_right hsc0 hw1'
  have h3 : sc < D := by
    rw [hsc, div_lt_iff₀ hbw]
    have := (div_lt_iff₀ hDpos).1 hw2'
    linarith
  linarith

theorem isOpen_safety {L P : ℕ} (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E)
    (d : Fin P → ℝ) (x : Fin L → ℝ) : IsOpen (safetySet a b d x : Set E) := by
  have : (safetySet a b d x : Set E) = ⋂ p, {u | 0 < b p u + d p - a p ⬝ᵥ x} := by
    ext u; simp [safetySet]
  rw [this]
  exact isOpen_iInter_of_finite fun p => isOpen_lt continuous_const (by fun_prop)

theorem compl_safety_nonempty {L P : ℕ} (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E)
    (d : Fin P → ℝ) (hP : 0 < P) (hb : ∀ p, b p ≠ 0) (x : Fin L → ℝ) :
    ((safetySet a b d x : Set E)ᶜ).Nonempty := by
  obtain ⟨w, hw⟩ : ∃ w, b ⟨0, hP⟩ w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hb ⟨0, hP⟩ (ContinuousLinearMap.ext fun w => by simpa using h w)
  refine ⟨((a ⟨0, hP⟩ ⬝ᵥ x - d ⟨0, hP⟩) / b ⟨0, hP⟩ w) • w,
    (mem_compl_safety a b d x _).2 ⟨⟨0, hP⟩, ?_⟩⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hw]
  linarith

/-! ### Averages in `ℝ≥0∞` -/

theorem ofReal_avg {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (N : ℝ≥0∞)⁻¹ * ∑ i, ENNReal.ofReal (f i) = ENNReal.ofReal ((1 / (N : ℝ)) * ∑ i, f i) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => hf i), one_div,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast]

/-! ### Weak duality -/

theorem weak_duality {N : ℕ} [MeasurableSpace E] [BorelSpace E] (A : Set E) (hA : IsClosed A)
    (ξ : Fin N → E) (ϵ θ t : ℝ) (r : Fin N → ℝ)
    (hN : 0 < N) (ht : 0 < t) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, Metric.infDist (ξ i) A ≥ t - r i)
    (hc : ϵ * t ≥ θ + (1 / (N : ℝ)) * ∑ i, r i) (hθ : 0 ≤ θ) (hϵ : 0 ≤ ϵ) :
    ModelRiskOT.WorstProb.worstProb (fun u v : E => ‖u - v‖)
      (WassersteinDRO.Duality.empiricalDistribution ξ) θ A ≤ ENNReal.ofReal ϵ := by
  set μN := WassersteinDRO.Duality.empiricalDistribution ξ with hμN
  set f : E → ℝ := fun u => max 0 (t - Metric.infDist u A) with hf
  have hfc : Continuous f := continuous_const.max (continuous_const.sub (Metric.continuous_infDist_pt A))
  have hfm : Measurable f := hfc.measurable
  have hAm : MeasurableSet A := hA.measurableSet
  have hr' : 0 ≤ (1 / (N : ℝ)) * ∑ i, r i :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hr i)
  set C : ℝ≥0∞ := ENNReal.ofReal ((1 / (N : ℝ)) * ∑ i, r i) with hC
  have hint : ∫⁻ u, ENNReal.ofReal (f u) ∂μN ≤ C := by
    simp only [hμN, WassersteinDRO.Duality.empiricalDistribution, lintegral_smul_measure,
      lintegral_finsetSum_measure, lintegral_dirac, smul_eq_mul]
    rw [hC, ← ofReal_avg hN r hr]
    gcongr with i
    exact max_le (hr i) (by linarith [hd i])
  unfold ModelRiskOT.WorstProb.worstProb
  refine iSup₂_le fun P hP => ?_
  obtain ⟨-, hPcost⟩ := hP
  have key : ∀ π : Measure (E × E), ModelRiskOT.WorstProb.IsCoupling μN P π →
      ENNReal.ofReal t * P A ≤ (∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖) ∂π) + C := by
    rintro π ⟨-, hπ1, hπ2⟩
    have hPA : P A = π (Prod.snd ⁻¹' A) := by rw [← hπ2, Measure.map_apply measurable_snd hAm]
    rw [hPA, ← lintegral_indicator_const (measurable_snd hAm)]
    calc ∫⁻ p, (Prod.snd ⁻¹' A).indicator (fun _ => ENNReal.ofReal t) p ∂π
        ≤ ∫⁻ p, (ENNReal.ofReal ‖p.1 - p.2‖ + ENNReal.ofReal (f p.1)) ∂π := by
          refine lintegral_mono fun p => ?_
          by_cases hp : p.2 ∈ A
          · rw [Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' A from hp),
              ← ENNReal.ofReal_add (norm_nonneg _) (le_max_left _ _)]
            apply ENNReal.ofReal_le_ofReal
            have h1 : Metric.infDist p.1 A ≤ ‖p.1 - p.2‖ := by
              rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hp
            have h2 : t - Metric.infDist p.1 A ≤ f p.1 := le_max_right _ _
            linarith
          · rw [Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' A from hp)]
            exact bot_le
      _ = (∫⁻ p, ENNReal.ofReal ‖p.1 - p.2‖ ∂π) + ∫⁻ p, ENNReal.ofReal (f p.1) ∂π :=
          lintegral_add_right _ ((hfm.comp measurable_fst).ennreal_ofReal)
      _ = (∫⁻ p, ENNReal.ofReal ‖p.1 - p.2‖ ∂π) + ∫⁻ u, ENNReal.ofReal (f u) ∂μN := by
          rw [← hπ1, lintegral_map hfm.ennreal_ofReal measurable_fst]
      _ ≤ _ := by gcongr
  have h2 : ENNReal.ofReal t * P A ≤
      ModelRiskOT.WorstProb.transportCost (fun u v : E => ‖u - v‖) μN P + C := by
    unfold ModelRiskOT.WorstProb.transportCost
    rw [ENNReal.iInf_add]
    refine le_iInf fun π => ?_
    rw [ENNReal.iInf_add]
    exact le_iInf fun hπ => key π hπ
  have h3 : ENNReal.ofReal t * P A ≤ ENNReal.ofReal t * ENNReal.ofReal ϵ := by
    calc _ ≤ _ := h2
      _ ≤ ENNReal.ofReal θ + C := by gcongr
      _ = ENNReal.ofReal (θ + (1 / (N : ℝ)) * ∑ i, r i) := (ENNReal.ofReal_add hθ hr').symm
      _ ≤ ENNReal.ofReal (ϵ * t) := ENNReal.ofReal_le_ofReal hc
      _ = _ := by rw [ENNReal.ofReal_mul hϵ, mul_comm]
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top).1 h3


/-! ### The adversarial distribution -/

theorem adversary {N : ℕ} [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (A : Set E) (hA : IsClosed A) (hne : A.Nonempty) (ξ : Fin N → E) (ϵ θ : ℝ) (hN : 0 < N)
    (hϵ : 0 ≤ ϵ)
    (hwp : ModelRiskOT.WorstProb.worstProb (fun u v : E => ‖u - v‖)
      (WassersteinDRO.Duality.empiricalDistribution ξ) θ A ≤ ENNReal.ofReal ϵ)
    (α : Fin N → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    (hcost : (1 / (N : ℝ)) * ∑ i, α i * Metric.infDist (ξ i) A ≤ θ) :
    (1 / (N : ℝ)) * ∑ i, α i ≤ ϵ := by
  have : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  set μN := WassersteinDRO.Duality.empiricalDistribution ξ with hμN
  choose y hyA hy using fun i => hA.exists_infDist_eq_dist hne (ξ i)
  have hAm : MeasurableSet A := hA.measurableSet
  set π : Measure (E × E) := (N : ℝ≥0∞)⁻¹ • ∑ i, (ENNReal.ofReal (1 - α i) •
      Measure.dirac (ξ i, ξ i) + ENNReal.ofReal (α i) • Measure.dirac (ξ i, y i)) with hπ
  have hfst : π.map Prod.fst = μN := by
    ext s hs
    rw [Measure.map_apply measurable_fst hs]
    simp only [hπ, hμN, WassersteinDRO.Duality.empiricalDistribution, Measure.smul_apply,
      Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply,
      Measure.dirac_apply' _ (measurable_fst hs), Measure.dirac_apply' _ hs, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : ENNReal.ofReal (1 - α i) + ENNReal.ofReal (α i) = 1 := by
      rw [← ENNReal.ofReal_add (by linarith [hα1 i]) (hα0 i), sub_add_cancel, ENNReal.ofReal_one]
    by_cases h : ξ i ∈ s
    · simp [h, e]
    · simp [h]
  have hμprob : μN Set.univ = 1 := by
    simp only [hμN, WassersteinDRO.Duality.empiricalDistribution, Measure.smul_apply,
      Measure.coe_finsetSum, Finset.sum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)
  have hπprob : IsProbabilityMeasure π := by
    constructor
    have h := Measure.map_apply (μ := π) measurable_fst MeasurableSet.univ
    rw [Set.preimage_univ, hfst, hμprob] at h
    exact h.symm
  set P := π.map Prod.snd with hP
  have hPprob : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hcostπ : ∫⁻ p, ENNReal.ofReal ‖p.1 - p.2‖ ∂π =
      ENNReal.ofReal ((1 / (N : ℝ)) * ∑ i, α i * Metric.infDist (ξ i) A) := by
    simp only [hπ, lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_add_measure,
      lintegral_dirac, sub_self, norm_zero, ENNReal.ofReal_zero, mul_zero, zero_add, smul_eq_mul]
    rw [← ofReal_avg hN _ (fun i => mul_nonneg (hα0 i) Metric.infDist_nonneg)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hy i, dist_eq_norm, ENNReal.ofReal_mul (hα0 i)]
  have hTC : ModelRiskOT.WorstProb.transportCost (fun u v : E => ‖u - v‖) μN P ≤
      ENNReal.ofReal θ := by
    calc _ ≤ ∫⁻ p, ENNReal.ofReal ‖p.1 - p.2‖ ∂π := iInf₂_le π ⟨hπprob, hfst, rfl⟩
      _ ≤ _ := by rw [hcostπ]; exact ENNReal.ofReal_le_ofReal hcost
  have hPA : ENNReal.ofReal ((1 / (N : ℝ)) * ∑ i, α i) ≤ P A := by
    rw [hP, Measure.map_apply measurable_snd hAm]
    simp only [hπ, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.add_apply, Measure.dirac_apply' _ (measurable_snd hAm), smul_eq_mul]
    rw [← ofReal_avg hN α hα0]
    gcongr with i
    have : (Prod.snd ⁻¹' A).indicator (1 : E × E → ℝ≥0∞) (ξ i, y i) = 1 :=
      Set.indicator_of_mem (show (ξ i, y i) ∈ Prod.snd ⁻¹' A from hyA i) _
    rw [this, mul_one]
    exact le_add_self
  have hle : P A ≤ ENNReal.ofReal ϵ := by
    refine le_trans ?_ hwp
    unfold ModelRiskOT.WorstProb.worstProb
    exact le_iSup₂_of_le (f := fun (Q : Measure E) (_ : IsProbabilityMeasure Q ∧
      ModelRiskOT.WorstProb.transportCost (fun u v : E => ‖u - v‖) μN Q ≤ ENNReal.ofReal θ) =>
        Q A) P ⟨hPprob, hTC⟩ le_rfl
  exact (ENNReal.ofReal_le_ofReal_iff hϵ).1 (hPA.trans hle)

/-! ### The fractional knapsack bound for `t = d_(k+1)` -/

theorem kOf_lt {N : ℕ} {ϵ : ℝ} (hN : 0 < N) (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) : kOf ϵ N < N :=
  (Nat.floor_lt (by positivity)).2 (mul_lt_of_lt_one_left (by exact_mod_cast hN) hϵ1)

theorem knapsack {N : ℕ} (hN : 0 < N) (D : Fin N → ℝ) (hD : ∀ i, 0 ≤ D i) (ϵ θ : ℝ)
    (hθ : 0 < θ) (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hadv : ∀ α : Fin N → ℝ, (∀ i, 0 ≤ α i) → (∀ i, α i ≤ 1) →
      (1 / (N : ℝ)) * ∑ i, α i * D i ≤ θ → (1 / (N : ℝ)) * ∑ i, α i ≤ ϵ) :
    ϵ * kthSmallest D (kOf ϵ N) ≥
      θ + (1 / (N : ℝ)) * ∑ i, max 0 (kthSmallest D (kOf ϵ N) - D i) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hkN : kOf ϵ N < N := kOf_lt hN hϵ hϵ1
  obtain ⟨h1, h2⟩ := os_facts D (kOf ϵ N) hkN
  have hk1 : ((kOf ϵ N : ℕ) : ℝ) ≤ ϵ * N := Nat.floor_le (by positivity)
  have hk2 : ϵ * N < (kOf ϵ N : ℝ) + 1 := Nat.lt_floor_add_one _
  set k := kOf ϵ N with hk
  set t := kthSmallest D k with ht
  set S1 : ℝ := ∑ i, if D i < t then (1 : ℝ) else 0 with hS1
  set S2 : ℝ := ∑ i, if D i ≤ t then (1 : ℝ) else 0 with hS2
  set SD : ℝ := ∑ i, if D i < t then D i else 0 with hSD
  have hS1k : S1 ≤ k := by
    rw [hS1, Finset.sum_boole]; exact_mod_cast h1
  have hS2k : (k : ℝ) + 1 ≤ S2 := by
    rw [hS2, Finset.sum_boole]; exact_mod_cast h2
  have ht0 : 0 ≤ t := by
    by_contra hneg
    push_neg at hneg
    have : (Finset.univ.filter (fun i => D i ≤ t)) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun i _ => not_le.2 (by linarith [hD i])
    rw [this] at h2
    simp at h2
  have hsr : ∑ i, max 0 (t - D i) = t * S1 - SD := by
    rw [hS1, hSD, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_left (by linarith)]; ring
  rw [hsr]
  by_contra hcon
  push_neg at hcon
  have hcon' : (ϵ * t - θ) * N < t * S1 - SD := by
    have e : (1 / (N : ℝ)) * (t * S1 - SD) = (t * S1 - SD) / N := by ring
    rw [e] at hcon
    exact (lt_div_iff₀ hNpos).1 (by linarith)
  have hcostf : ∀ γ : ℝ, (∑ i, (if D i < t then (1 : ℝ) else if D i ≤ t then γ else 0) * D i)
      = SD + γ * t * (S2 - S1) := by
    intro γ
    rw [hSD, hS1, hS2, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with ha hb'
    all_goals first
      | ring1
      | (exfalso; linarith)
      | (have e : D i = t := by linarith
         rw [e]; ring1)
  have hα : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 →
      (∑ i, (if D i < t then (1 : ℝ) else if D i ≤ t then γ else 0) * D i) ≤ N * θ →
      S1 + γ * (S2 - S1) ≤ N * ϵ := by
    intro γ hγ0 hγ1 hcost
    have hsum : ∑ i, (if D i < t then (1 : ℝ) else if D i ≤ t then γ else 0)
        = S1 + γ * (S2 - S1) := by
      rw [hS1, hS2, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with ha hb'
      all_goals first
        | ring1
        | (exfalso; linarith)
    have := hadv (fun i => if D i < t then (1 : ℝ) else if D i ≤ t then γ else 0)
      (fun i => by split_ifs <;> linarith)
      (fun i => by split_ifs <;> linarith)
      (by rw [one_div, inv_mul_le_iff₀ hNpos]; exact hcost)
    rw [one_div, inv_mul_le_iff₀ hNpos, hsum] at this
    exact this
  have hG : 1 ≤ S2 - S1 := by linarith
  rcases eq_or_lt_of_le ht0 with ht00 | htpos
  · have hSD' : SD = 0 := by
      rw [hSD]
      refine Finset.sum_eq_zero fun i _ => ?_
      exact if_neg (not_lt.2 (by linarith [hD i]))
    have := hα 1 zero_le_one le_rfl (by rw [hcostf, hSD', ← ht00]; simp; positivity)
    linarith
  · have hts : t * S1 ≤ t * (ϵ * N) := mul_le_mul_of_nonneg_left (by linarith) ht0
    have hSDlt : SD < N * θ := by linarith
    by_cases hcase : t * (S2 - S1) ≤ N * θ - SD
    · have := hα 1 zero_le_one le_rfl (by rw [hcostf]; linarith)
      linarith
    · push_neg at hcase
      have hpos : 0 < t * (S2 - S1) := mul_pos htpos (by linarith)
      set γ := (N * θ - SD) / (t * (S2 - S1)) with hγ
      have hγt : γ * (t * (S2 - S1)) = N * θ - SD := div_mul_cancel₀ _ hpos.ne'
      have hγ0 : 0 ≤ γ := div_nonneg (by linarith) hpos.le
      have hγ1 : γ ≤ 1 := (div_le_one hpos).2 hcase.le
      have := hα γ hγ0 hγ1 (by
        rw [hcostf]
        have : γ * t * (S2 - S1) = γ * (t * (S2 - S1)) := by ring
        linarith)
      have hm := mul_le_mul_of_nonneg_left this ht0
      nlinarith

end WDRCCP3Aux

open WassDRCCP.Improved in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ)
    (ξ : Fin N → E) (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hb : ∀ p, b p ≠ 0)
    (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) (hθ : 0 < θ)
    (hM : ∀ x ∈ X, ∀ (i : Fin N) (p : Fin P), |b p (ξ i) + d p - a p ⬝ᵥ x| / ‖b p‖ ≤ M) :
    XDR (safetySet a b d) X ξ ϵ θ =
      {x | x ∈ X ∧ ∃ (z r : Fin N → ℝ) (t : ℝ), sys20 a b d ξ X ϵ θ M x z r t} := by
  classical
  have hkN : kOf ϵ N < N := WDRCCP3Aux.kOf_lt hN hϵ hϵ1
  have hbp : ∀ p, 0 < ‖b p‖ := fun p => norm_pos_iff.2 (hb p)
  ext x
  simp only [XDR, Set.mem_setOf_eq]
  have hAc : IsClosed (safetySet a b d x)ᶜ := (WDRCCP3Aux.isOpen_safety a b d x).isClosed_compl
  have hAne : ((safetySet a b d x)ᶜ).Nonempty := WDRCCP3Aux.compl_safety_nonempty a b d hP hb x
  constructor
  · rintro ⟨hxX, hwp⟩
    set A := (safetySet a b d x)ᶜ with hA
    set D : Fin N → ℝ := fun i => Metric.infDist (ξ i) A with hD
    have hD0 : ∀ i, 0 ≤ D i := fun i => Metric.infDist_nonneg
    have hc := WDRCCP3Aux.knapsack hN D hD0 ϵ θ hθ hϵ hϵ1
      (fun α h0 h1 hcost => WDRCCP3Aux.adversary A hAc hAne ξ ϵ θ hN hϵ.le hwp α h0 h1 hcost)
    set k := kOf ϵ N with hk
    set t := kthSmallest D k with ht
    have hsumr : 0 ≤ (1 / (N : ℝ)) * ∑ i, max 0 (t - D i) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => le_max_left _ _)
    have htpos : 0 < t := by
      by_contra h
      push_neg at h
      nlinarith
    obtain ⟨h1, -⟩ := WDRCCP3Aux.os_facts D k hkN
    rw [← ht] at h1
    have hin : ∀ i, ξ i ∈ A → D i = 0 := fun i hi => Metric.infDist_zero_of_mem hi
    have hout : ∀ i p, ξ i ∉ A → 0 < gip a b d ξ x i p := by
      intro i p hi
      have : ξ i ∈ safetySet a b d x := by simpa [hA] using hi
      exact div_pos (this p) (hbp p)
    have hup : ∀ i p, D i ≤ max 0 (gip a b d ξ x i p) :=
      fun i p => WDRCCP3Aux.dist_upper a b d hb x (ξ i) p
    have hgstar : ∀ p, gstar a b d ξ k x p ≥ t := by
      intro p
      obtain ⟨-, hq⟩ := WDRCCP3Aux.os_facts (fun i => -(-(b p (ξ i)))) k hkN
      obtain ⟨i, hi1, hi2⟩ : ∃ i, -(-(b p (ξ i))) ≤
          kthSmallest (fun i => -(-(b p (ξ i)))) k ∧ t ≤ D i := by
        by_contra hcon
        push_neg at hcon
        have : (Finset.univ.filter (fun i => -(-(b p (ξ i))) ≤
            kthSmallest (fun i => -(-(b p (ξ i)))) k)).card ≤
            (Finset.univ.filter (fun i => D i < t)).card :=
          Finset.card_le_card fun i hi => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hcon i hi
        omega
      have hq' : qp b ξ k p = -kthSmallest (fun i => -(-(b p (ξ i)))) k := rfl
      have hgi : gip a b d ξ x i p ≤ gstar a b d ξ k x p := by
        show (b p (ξ i) + d p - a p ⬝ᵥ x) / ‖b p‖ ≤ (-(qp b ξ k p) + d p - a p ⬝ᵥ x) / ‖b p‖
        rw [hq']
        exact (div_le_div_iff_of_pos_right (hbp p)).2 (by linarith)
      have := (hi2.trans (hup i p)).trans (max_le_max le_rfl hgi)
      rcases le_max_iff.1 this with h | h
      · linarith
      · exact h
    refine ⟨hxX, fun i => if ξ i ∈ A then 1 else 0, fun i => max 0 (t - D i), t, ?_⟩
    refine ⟨⟨fun i => ?_, htpos.le, fun i => le_max_left _ _, hxX⟩, hc, fun i => ?_, ?_,
      fun p i _ => ?_, hgstar⟩
    · by_cases h : ξ i ∈ A <;> simp [h]
    · by_cases h : ξ i ∈ A
      · simp only [h, if_true, sub_self, mul_zero, hin i h, sub_zero, max_eq_right htpos.le]
        linarith
      · simp only [h, if_false, sub_zero, mul_one]
        have h1 := hup i ⟨0, hP⟩
        have h2 : gip a b d ξ x i ⟨0, hP⟩ ≤ M :=
          ((div_le_div_iff_of_pos_right (hbp _)).2 (le_abs_self _)).trans (hM x hxX i ⟨0, hP⟩)
        rw [max_eq_right (hout i ⟨0, hP⟩ h).le] at h1
        linarith [le_max_right 0 (t - D i)]
    · show ∑ i, (if ξ i ∈ A then (1 : ℝ) else 0) ≤ (kOf ϵ N : ℝ)
      calc ∑ i, (if ξ i ∈ A then (1 : ℝ) else 0)
          ≤ ∑ i, (if D i < t then (1 : ℝ) else 0) :=
            Finset.sum_le_sum fun i _ => by
              by_cases h : ξ i ∈ A
              · rw [if_pos h, if_pos (by rw [hin i h]; exact htpos)]
              · rw [if_neg h]; split_ifs <;> norm_num
        _ = _ := by rw [Finset.sum_boole]
        _ ≤ _ := by exact_mod_cast h1
    · by_cases h : ξ i ∈ A
      · simp only [h, if_true, mul_one, hin i h, sub_zero, max_eq_right htpos.le, sub_self]
        have e : gip a b d ξ x i p + hip b ξ k i p = gstar a b d ξ k x p := by
          simp only [gip, hip, gstar]
          rw [← add_div]
          congr 1
          ring
        rw [e]
        linarith [hgstar p]
      · simp only [h, if_false, mul_zero, add_zero]
        have h1 := hup i p
        rw [max_eq_right (hout i p h).le] at h1
        linarith [le_max_right 0 (t - D i)]
  · rintro ⟨hxX, z, r, t, ⟨hz, ht0, hr0, -⟩, hc5c, hc5d, -, hc20c, hc20d⟩
    refine ⟨hxX, ?_⟩
    have hsumr : 0 ≤ (1 / (N : ℝ)) * ∑ i, r i :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hr0 i)
    have htpos : 0 < t := by
      rcases eq_or_lt_of_le ht0 with h | h
      · exfalso
        unfold c5c at hc5c
        rw [← h, mul_zero] at hc5c
        linarith
      · exact h
    refine WDRCCP3Aux.weak_duality _ hAc ξ ϵ θ t r hN htpos hr0 (fun i => ?_) hc5c hθ.le hϵ.le
    rcases hz i with h | h
    · apply WDRCCP3Aux.dist_lower a b d hb x (ξ i) (t - r i) hAne
      intro p
      by_cases hiN : i ∈ Np b ξ (kOf ϵ N) p
      · have := hc20c p i hiN
        rw [h, mul_zero, add_zero] at this
        exact this
      · have hle : -(b p (ξ i)) ≤ qp b ξ (kOf ϵ N) p :=
          not_lt.1 fun h' => hiN (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩)
        have h1 := hc20d p
        have h2 : gstar a b d ξ (kOf ϵ N) x p ≤ (b p (ξ i) + d p - a p ⬝ᵥ x) / ‖b p‖ :=
          (div_le_div_iff_of_pos_right (hbp p)).2 (by linarith)
        linarith [hr0 i]
    · have := hc5d i
      rw [h, sub_self, mul_zero] at this
      linarith [Metric.infDist_nonneg (x := ξ i) (s := (safetySet a b d x)ᶜ)]
