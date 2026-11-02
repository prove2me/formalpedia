-- Prove2me | solution 1 for SpatialDemandEq.Optimal.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:43:23.697626+00:00
-- url     : https://prove2.me/submissions/54fd9342-8035-4efc-9d89-a283cc0a2ac9

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Theorems.Thm_SpatialDemandEq_Optimal_theorem_4
import Theorems.Thm_SpatialDemandEq_Optimal_mu_step
import Theorems.Thm_SpatialDemandEq_Optimal_cells_partition

open MeasureTheory
open SpatialDemandEq.Optimal

lemma sde5_inv_convex (c x y t : ℝ) (hc : 0 ≤ c) (hx : 0 < x) (hy : 0 < y) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : c / ((1 - t) * x + t * y) ≤ (1 - t) * (c / x) + t * (c / y) := by
  have h1t : 0 ≤ 1 - t := by linarith
  have hm : 0 < min x y := lt_min hx hy
  have hz : 0 < (1 - t) * x + t * y := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left x y) h1t,
      mul_le_mul_of_nonneg_left (min_le_right x y) ht0]
  rw [div_le_iff₀ hz]
  have key : ((1 - t) * (c / x) + t * (c / y)) * ((1 - t) * x + t * y) - c =
      t * (1 - t) * c * (x - y) ^ 2 / (x * y) := by
    field_simp
    ring
  have : 0 ≤ t * (1 - t) * c * (x - y) ^ 2 / (x * y) := by
    apply div_nonneg _ (by positivity)
    have : 0 ≤ 1 - t := by linarith
    positivity
  linarith

theorem solution {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam B : ℝ) (hS : Standing S ν dst xs c lam) (hB : lam < B)
    (μ : Fin K → ℝ) (A : Fin K → Set (E n))
    (hopt : IsLocalOpt ν S (distFn dst xs) c lam B μ A)
    (hpos : ∀ k, 0 < area ν (A k)) :
    (∀ k, A k =ᵐ[ν] cell S (distFn dst xs) (optWeights c lam B (areas ν A)) k) ∧
      μ = optRates lam B (areas ν A) := by
  have hprob := hS.prob
  have hne : Nonempty (Fin K) := ⟨⟨0, hS.K_pos⟩⟩
  set d := distFn dst xs with hd
  set a := areas ν A with ha_def
  have ha : ∀ k, 0 < a k := hpos
  obtain ⟨⟨hApart, hμsum, hstab⟩, ε0, hε0, hloc⟩ := hopt
  -- every partition has total area one
  have hsum1 : ∀ A' : Fin K → Set (E n), IsPartition ν S A' → ∑ k, area ν (A' k) = 1 := by
    rintro A' ⟨hm, -, hU, hN⟩
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν) A') := fun j k hjk => hN j k hjk
    have hUn := measure_iUnion₀ hdisj (fun k => (hm k).nullMeasurableSet)
    rw [hU, tsum_fintype] at hUn
    have hSone : ν S = 1 := by
      rw [measure_congr (ae_eq_univ.mpr hS.supp), measure_univ]
    unfold area
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top _ _), ← hUn, hSone]
    simp
  have hasum : ∑ k, a k = 1 := hsum1 A hApart
  obtain ⟨⟨hpsum, hpstab⟩, hpval, hpmin⟩ :=
    mu_step c lam B hS.c_pos hS.lam_pos hB a ha hasum
  set p := optRates lam B a with hp_def
  ------------------------------------------------------------------
  -- Part (a): the rates are the optimal rates (17)
  ------------------------------------------------------------------
  have hμ : μ = p := by
    by_contra hne'
    have hlt := hpmin μ hμsum hstab hne'
    set M := ∑ k, |p k - μ k| with hM_def
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
    set t := min (1 / 2 : ℝ) (ε0 / (2 * (M + 1))) with ht_def
    have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t ≤ 1 / 2 := min_le_left _ _
    have htε : t * M < ε0 := by
      have h1 : t * M ≤ ε0 / (2 * (M + 1)) * M :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hM
      have h2 : ε0 / (2 * (M + 1)) * M < ε0 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    set μt : Fin K → ℝ := fun k => μ k + t * (p k - μ k) with hμt
    have hfeas : Feasible ν S lam B μt A := by
      refine ⟨hApart, ?_, ?_⟩
      · simp only [μt, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
        rw [hpsum, hμsum]; ring
      · intro k
        have h1 : lam * a k < μ k := hstab k
        have h2 := hpstab k
        change lam * a k < μ k + t * (p k - μ k)
        have h1t : 0 ≤ 1 - t := by linarith
        nlinarith [mul_nonneg h1t (sub_pos.mpr h1).le, mul_pos ht0 (sub_pos.mpr h2)]
    have hclose : ∀ k, |μt k - μ k| < ε0 := by
      intro k
      simp only [μt, add_sub_cancel_left, abs_mul, abs_of_pos ht0]
      have : |p k - μ k| ≤ M :=
        Finset.single_le_sum (f := fun k => |p k - μ k|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ k)
      nlinarith
    have hsd : ∀ k, ν (symmDiff (A k) (A k)) < ENNReal.ofReal ε0 := by
      intro k
      rw [symmDiff_self, Set.bot_eq_empty, measure_empty]
      exact ENNReal.ofReal_pos.mpr hε0
    have hle := hloc μt A hfeas hclose hsd
    have hR : rateCost c lam μ a ≤ rateCost c lam μt a := by
      unfold socialCost at hle
      linarith
    have hconv : rateCost c lam μt a ≤ (1 - t) * rateCost c lam μ a + t * rateCost c lam p a := by
      unfold rateCost
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k _
      have hx : 0 < μ k - lam * a k := sub_pos.mpr (hstab k)
      have hy : 0 < p k - lam * a k := sub_pos.mpr (hpstab k)
      have heq : μt k - lam * a k = (1 - t) * (μ k - lam * a k) + t * (p k - lam * a k) := by
        simp only [μt]; ring
      rw [heq]
      have := sde5_inv_convex c _ _ t hS.c_pos.le hx hy ht0.le (by linarith)
      have hak := (ha k).le
      calc a k * (c / ((1 - t) * (μ k - lam * a k) + t * (p k - lam * a k)))
          ≤ a k * ((1 - t) * (c / (μ k - lam * a k)) + t * (c / (p k - lam * a k))) :=
            mul_le_mul_of_nonneg_left this hak
        _ = (1 - t) * (a k * (c / (μ k - lam * a k))) + t * (a k * (c / (p k - lam * a k))) := by
            ring
    nlinarith [mul_lt_mul_of_pos_left hlt ht0]
  subst hμ
  ------------------------------------------------------------------
  -- Part (b): the optimal partition is a local optimum of (9) with
  -- G(b) = c/(B-λ) (∑ √b_j)²; apply Theorem 4.
  ------------------------------------------------------------------
  set G : (Fin K → ℝ) → ℝ := fun b => c / (B - lam) * ((∑ j, Real.sqrt (b j)) *
    (∑ j, Real.sqrt (b j))) with hG_def
  have hGval : ∀ b, G b = c / (B - lam) * (∑ j, Real.sqrt (b j)) ^ 2 := by
    intro b; simp only [G]; ring
  have hSpos : 0 < ∑ j, Real.sqrt (a j) :=
    Finset.sum_pos (fun j _ => Real.sqrt_pos.mpr (ha j)) Finset.univ_nonempty
  -- continuity of the optimal rates in the areas
  have hcontR : ContinuousAt (optRates lam B) a := by
    apply continuousAt_pi.mpr
    intro k
    have hs : ContinuousAt (fun b : Fin K → ℝ => ∑ j, Real.sqrt (b j)) a :=
      (continuous_finsetSum _ fun j _ =>
        Real.continuous_sqrt.comp (continuous_apply j)).continuousAt
    show ContinuousAt (fun b : Fin K → ℝ =>
      lam * b k + (B - lam) * Real.sqrt (b k) / ∑ j, Real.sqrt (b j)) a
    exact ((continuous_const.mul (continuous_apply k)).continuousAt).add
      (((continuous_const.mul (Real.continuous_sqrt.comp (continuous_apply k))).continuousAt).div
        hs hSpos.ne')
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hcontR ε0 hε0
  obtain ⟨k0, hk0⟩ := Finite.exists_min a
  have hset : GeneralSetting S ν d := by
    refine ⟨hS.closed, hS.convex, hS.prob, hS.ac, hS.supp, ?_, hS.integrable, hS.regular⟩
    intro k
    exact hS.metric.1.comp (Continuous.prodMk continuous_id continuous_const)
  have hlocP : IsLocalOptPartition ν S G d A := by
    refine ⟨hApart, min (min ε0 δ) (a k0), lt_min (lt_min hε0 hδ) (ha k0), ?_⟩
    intro A' hA' hsd
    set b := areas ν A' with hb_def
    have hbclose : ∀ k, |b k - a k| < min (min ε0 δ) (a k0) := by
      intro k
      have h1 : |ν.real (A' k) - ν.real (A k)| ≤ ν.real (symmDiff (A' k) (A k)) :=
        abs_measureReal_sub_le_measureReal_symmDiff (hA'.1 k).nullMeasurableSet
          (hApart.1 k).nullMeasurableSet
      have h2 : ν.real (symmDiff (A' k) (A k)) < min (min ε0 δ) (a k0) :=
        ENNReal.toReal_lt_of_lt_ofReal (hsd k)
      exact lt_of_le_of_lt h1 h2
    have hbpos : ∀ k, 0 < b k := by
      intro k
      have h1 := hbclose k
      have h2 : min (min ε0 δ) (a k0) ≤ a k0 := min_le_right _ _
      have h3 := hk0 k
      rw [abs_lt] at h1
      linarith
    have hbsum : ∑ k, b k = 1 := hsum1 A' hA'
    obtain ⟨⟨hqsum, hqstab⟩, hqval, -⟩ := mu_step c lam B hS.c_pos hS.lam_pos hB b hbpos hbsum
    have hqclose : ∀ k, |optRates lam B b k - p k| < ε0 := by
      have hdist : dist b a < δ := by
        rw [dist_pi_lt_iff hδ]
        intro k
        rw [Real.dist_eq]
        exact lt_of_lt_of_le (hbclose k) ((min_le_left _ _).trans (min_le_right _ _))
      have h := hδc hdist
      rw [dist_pi_lt_iff hε0] at h
      intro k
      have := h k
      rwa [Real.dist_eq] at this
    have hsd' : ∀ k, ν (symmDiff (A' k) (A k)) < ENNReal.ofReal ε0 := by
      intro k
      exact lt_of_lt_of_le (hsd k)
        (ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (min_le_left _ _)))
    have hle := hloc (optRates lam B b) A' ⟨hA', hqsum, hqstab⟩ hqclose hsd'
    unfold socialCost at hle
    unfold partitionObj
    rw [hGval, hGval]
    rw [hpval] at hle
    rw [hqval] at hle
    exact hle
  -- differentiability of G and its partial derivatives
  have hsq : ∀ j, HasFDerivAt (fun b : Fin K → ℝ => Real.sqrt (b j))
      ((1 / (2 * Real.sqrt (a j))) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) j)) a := by
    intro j
    have h0 : HasFDerivAt (fun b : Fin K → ℝ => b j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) j) a := hasFDerivAt_apply j a
    have h1 := (Real.hasDerivAt_sqrt (ha j).ne').comp_hasFDerivAt a h0
    exact h1
  have hsum' : HasFDerivAt (fun b : Fin K → ℝ => ∑ j, Real.sqrt (b j))
      (∑ j, (1 / (2 * Real.sqrt (a j))) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) j)) a :=
    HasFDerivAt.fun_sum fun j _ => hsq j
  have hGd : HasFDerivAt G _ a := (hsum'.mul hsum').const_mul (c / (B - lam))
  have hGdiff : DifferentiableAt ℝ G a := hGd.differentiableAt
  have hderiv : ∀ k, fderiv ℝ G a (Pi.single k (1 : ℝ)) = optWeights c lam B a k := by
    intro k
    rw [hGd.fderiv]
    have hsk : 0 < Real.sqrt (a k) := Real.sqrt_pos.mpr (ha k)
    simp [Pi.single_apply, optWeights]
    field_simp
    ring
  have h4 := theorem_4 S ν d G hset A hlocP hGdiff
  set w := optWeights c lam B a with hw_def
  have hAle : ∀ k, A k ≤ᵐ[ν] cell S d w k := by
    intro k
    filter_upwards [h4 k] with x hx hxA
    refine ⟨hApart.2.1 k hxA, fun j hj => ?_⟩
    have := hx hxA j hj
    rwa [hderiv k, hderiv j] at this
  obtain ⟨⟨_, _, _, hnull⟩, _⟩ := cells_partition S ν dst xs c lam hS w
  have hdiff : ∀ k, ν (cell S d w k \ A k) = 0 := by
    intro k
    have hsub : cell S d w k \ A k ⊆
        (⋃ j, ⋃ (_ : j ≠ k), (cell S d w j ∩ cell S d w k)) ∪ ⋃ j, (A j \ cell S d w j) := by
      rintro x ⟨hxc, hxA⟩
      have hxS : x ∈ (⋃ j, A j) := by rw [hApart.2.2.1]; exact hxc.1
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxS
      have hjk : j ≠ k := by rintro rfl; exact hxA hj
      by_cases hxj : x ∈ cell S d w j
      · exact Or.inl (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjk, hxj, hxc⟩⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨j, hj, hxj⟩)
    apply measure_mono_null hsub
    apply measure_union_null
    · exact measure_iUnion_null fun j => measure_iUnion_null fun hjk => hnull j k hjk
    · exact measure_iUnion_null fun j => ae_le_set.mp (hAle j)
  exact ⟨fun k => (hAle k).antisymm (ae_le_set.mpr (hdiff k)), rfl⟩
