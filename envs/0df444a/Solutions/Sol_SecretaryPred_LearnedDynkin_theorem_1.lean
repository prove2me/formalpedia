-- Prove2me | solution 1 for SecretaryPred.LearnedDynkin.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:15:56.014452+00:00
-- url     : https://prove2.me/submissions/02123fb3-1842-44ab-9421-ea3740ec0e04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SecretaryPred_LearnedDynkin_Setting
import Theorems.Thm_SecretaryPred_LearnedDynkin_case_M_empty
import Theorems.Thm_SecretaryPred_LearnedDynkin_case_i
import Theorems.Thm_SecretaryPred_LearnedDynkin_case_ii
import Theorems.Thm_SecretaryPred_LearnedDynkin_case_iii
import Theorems.Thm_SecretaryPred_LearnedDynkin_case_iv
import Theorems.Thm_SecretaryPred_LearnedDynkin_case_v
import Theorems.Thm_SecretaryPred_LearnedDynkin_case_vi
import Theorems.Thm_SecretaryPred_LearnedDynkin_numerical_bounds
import Theorems.Thm_SecretaryPred_LearnedDynkin_window_single_deviator

set_option autoImplicit false

namespace TheoremOneAssembly
open MeasureTheory SecretaryPred.LearnedDynkin
open scoped BigOperators

noncomputable def altSum (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, (m.choose k:ℝ)*(-1:ℝ)^(k-1)*(1-t^k)/(k:ℝ)

noncomputable def positiveSum (m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, (1-t)^(j+1)/(j+1:ℕ)

theorem sum_Icc_shift (m : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 m, f k = ∑ j ∈ Finset.range m, f (j+1) := by
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

theorem binomial_integrand (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    ∑ j ∈ Finset.range m, (m.choose (j+1):ℝ)*(-x)^j =
      ∑ j ∈ Finset.range m, (1-x)^j := by
  have hb := add_pow (-x) (1:ℝ) m
  rw [Finset.sum_range_succ'] at hb
  simp only [one_pow,mul_one,pow_zero,Nat.choose_zero_right,Nat.cast_one,one_mul] at hb
  have hs : (∑ j ∈ Finset.range m, (m.choose (j+1):ℝ)*(-x)^j)*(-x) =
      ∑ j ∈ Finset.range m, (-x)^(j+1)*(m.choose (j+1):ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    ring
  have hg := geom_sum_mul_neg (1-x) m
  have hm : (∑ j ∈ Finset.range m, (m.choose (j+1):ℝ)*(-x)^j)*x =
      (∑ j ∈ Finset.range m, (1-x)^j)*x := by
    have hp : (-x+1)^m=(1-x)^m := by congr 1; ring
    rw [hp] at hb
    nlinarith
  exact mul_right_cancel₀ hx hm

theorem altSum_eq_positiveSum (m : ℕ) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    altSum m t = positiveSum m t := by
  have hleft : (∫ x in t..1, ∑ j ∈ Finset.range m, (m.choose (j+1):ℝ)*(-x)^j) = altSum m t := by
    rw [intervalIntegral.integral_finsetSum (f := fun j (x : ℝ) => (m.choose (j+1):ℝ)*(-x)^j) (fun j _ =>
      (by fun_prop : Continuous (fun x : ℝ => (m.choose (j+1):ℝ)*(-x)^j)).intervalIntegrable _ _)]
    rw [altSum, sum_Icc_shift]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (fun x : ℝ => (m.choose (j+1):ℝ)*(-x)^j) =
        (fun x => ((m.choose (j+1):ℝ)*(-1:ℝ)^j)*x^j) by funext x; rw [neg_pow]; ring]
    rw [intervalIntegral.integral_const_mul,integral_pow]
    simp only [one_pow,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    ring
  have hright : (∫ x in t..1, ∑ j ∈ Finset.range m, (1-x)^j) = positiveSum m t := by
    rw [intervalIntegral.integral_finsetSum (f := fun j (x : ℝ) => (1-x)^j) (fun j _ =>
      (by fun_prop : Continuous (fun x : ℝ => (1-x)^j)).intervalIntegrable _ _)]
    unfold positiveSum
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^j) 1,integral_pow]
    simp
  rw [← hleft,← hright]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le ht1] at hx
  exact binomial_integrand m x (ne_of_gt (ht0.trans_le hx.1))

theorem positiveSum_nonneg (m : ℕ) (t : ℝ) (ht : t ≤ 1) : 0 ≤ positiveSum m t := by
  apply Finset.sum_nonneg
  intro j hj
  positivity

theorem positiveSum_mono (t : ℝ) (ht : t ≤ 1) : Monotone (fun m => positiveSum m t) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun j _ _ => by positivity)

theorem altSum_nonneg (m : ℕ) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ altSum m t := by rw [altSum_eq_positiveSum m t ht0 ht1]; exact positiveSum_nonneg m t ht1

theorem altSum_mono (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) : Monotone (fun m => altSum m t) := by
  simpa only [altSum_eq_positiveSum _ t ht0 ht1] using positiveSum_mono t ht1

theorem negative_sum (m : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.Icc 1 m, (m.choose k:ℝ)*(-1:ℝ)^k*(1-t^k)/(k:ℝ)) = -altSum m t := by
  rw [altSum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have h1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hp : (-1:ℝ)^k = -(-1:ℝ)^(k-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel h1]
    rw [pow_succ]
    ring
  rw [hp]
  ring

theorem large_m_bound (m : ℕ) (hm : 6 ≤ m) :
    (0.24:ℝ) ≤ 0.313*positiveSum m 0.313 - 0.687/(m:ℝ) := by
  have hs := positiveSum_mono (0.313:ℝ) (by norm_num) hm
  norm_num [positiveSum,Finset.sum_range_succ] at hs ⊢
  have hd : (0.687:ℝ)/(m:ℝ) ≤ 0.687/6 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact_mod_cast hm
  linarith

/-! ### Numerical bounds against `c₀ = (1 - θ)/(1 + θ)` -/

theorem c0_iv (m : ℕ) (hm : 2 ≤ m) :
    (1 - 0.646 : ℝ) / (1 + 0.646) ≤ 0.313 * altSum m 0.313 := by
  rw [altSum_eq_positiveSum _ _ (by norm_num) (by norm_num)]
  have h := positiveSum_mono (0.313:ℝ) (by norm_num) hm
  norm_num [positiveSum, Finset.sum_range_succ] at h ⊢
  linarith

theorem c0_v (m : ℕ) (hm : 1 ≤ m) :
    (1 - 0.646 : ℝ) / (1 + 0.646) ≤ (1-0.313)^(m+1)/((m:ℝ)+1) + 0.313*altSum m 0.313
      - (1-0.313)/(m:ℝ)*(1-(1-0.313)^m) := by
  rw [altSum_eq_positiveSum _ _ (by norm_num) (by norm_num)]
  by_cases h6 : 6 ≤ m
  · have hlarge := large_m_bound m h6
    norm_num at hlarge ⊢
    have hb : 0 ≤ (687/1000/(m:ℝ))*(687/1000:ℝ)^m := by positivity
    have hp : 0 ≤ (687/1000:ℝ)^(m+1)/((m:ℝ)+1) := by positivity
    nlinarith
  · have h5 : m ≤ 5 := by omega
    interval_cases m <;> norm_num [positiveSum, Finset.sum_range_succ]

theorem c0_vi (m : ℕ) (hm : 2 ≤ m) :
    (1 - 0.646 : ℝ) / (1 + 0.646) ≤ 1/((m:ℝ)+1)*((1-0.646)/(1+0.646)) + 0.313*altSum (m+1) 0.313
      - (1-0.313)/((m:ℝ)+1)*(1-(1-0.313)^(m+1)) := by
  rw [altSum_eq_positiveSum _ _ (by norm_num) (by norm_num)]
  by_cases h5 : 5 ≤ m
  · have hlarge := large_m_bound (m+1) (by omega)
    norm_num at hlarge ⊢
    have hb : 0 ≤ (687/1000/((m:ℝ)+1))*(687/1000:ℝ)^(m+1) := by positivity
    have hp : 0 ≤ ((m:ℝ)+1)⁻¹*(177/823:ℝ) := by positivity
    nlinarith
  · have h4 : m ≤ 4 := by omega
    interval_cases m <;> norm_num [positiveSum, Finset.sum_range_succ]

/-! ### Measurability and the expectation lower bound -/

theorem measurable_secretaryAt {n : ℕ} (theta : ℝ) (v vhat : Fin n → ℝ) (k : Fin n) :
    Measurable (fun t : Fin n → ℝ => SecretaryAt theta v vhat t k) := by
  unfold SecretaryAt
  refine Measurable.exists fun j => Measurable.and ?_ measurable_const
  exact measurableSet_setOfPred.mp (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply k))

theorem measurable_bestSoFar {n : ℕ} (v : Fin n → ℝ) (k : Fin n) :
    Measurable (fun t : Fin n → ℝ => BestSoFar v t k) := by
  unfold BestSoFar
  refine Measurable.forall fun j => Measurable.imp ?_ measurable_const
  exact measurableSet_setOfPred.mp (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply k))

theorem measurable_stops {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n) (k : Fin n) :
    Measurable (fun t : Fin n → ℝ => Stops theta tau v vhat ihat t k) := by
  unfold Stops
  refine Measurable.or ((measurable_secretaryAt theta v vhat k).not.and measurable_const)
    ((measurable_secretaryAt theta v vhat k).and (Measurable.and ?_ (measurable_bestSoFar v k)))
  exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const (measurable_pi_apply k))

theorem measurableSet_hired {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n) (k : Fin n) :
    MeasurableSet {t : Fin n → ℝ | Hired theta tau v vhat ihat t k} := by
  apply measurableSet_setOfPred.mpr
  unfold Hired
  refine (measurable_stops theta tau v vhat ihat k).and (Measurable.forall fun j => Measurable.imp ?_
    (measurable_stops theta tau v vhat ihat j).not)
  exact measurableSet_setOfPred.mp (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply k))

instance arrival_finite (n : ℕ) : IsFiniteMeasure (arrivalLaw n) := by
  unfold arrivalLaw
  exact isFiniteMeasure_restrict.mpr
    (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).measure_lt_top.ne

theorem algValue_nonneg {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hv : ∀ i, 0 ≤ v i) (t : Fin n → ℝ) : 0 ≤ algValue theta tau v vhat ihat t := by
  unfold algValue
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact hv k
  · exact le_refl 0

theorem algValue_le {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hv : ∀ i, 0 ≤ v i) (t : Fin n → ℝ) : algValue theta tau v vhat ihat t ≤ ∑ i, v i := by
  unfold algValue
  apply Finset.sum_le_sum
  intro k _
  split_ifs
  · exact le_refl _
  · exact hv k

theorem integrable_algValue {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hv : ∀ i, 0 ≤ v i) : Integrable (algValue theta tau v vhat ihat) (arrivalLaw n) := by
  have hmeas : Measurable (algValue theta tau v vhat ihat) := by
    unfold algValue
    apply Finset.measurable_sum
    intro k _
    exact Measurable.ite (measurableSet_hired theta tau v vhat ihat k) measurable_const
      measurable_const
  refine Integrable.of_bound hmeas.aestronglyMeasurable (∑ i, v i) (Filter.Eventually.of_forall ?_)
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (algValue_nonneg theta tau v vhat ihat hv t)]
  exact algValue_le theta tau v vhat ihat hv t

theorem expectedValue_nonneg {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hv : ∀ i, 0 ≤ v i) : 0 ≤ expectedValue theta tau v vhat ihat :=
  integral_nonneg (algValue_nonneg theta tau v vhat ihat hv)

theorem expectedValue_ge_hire {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hv : ∀ i, 0 ≤ v i) (k : Fin n) :
    v k * (arrivalLaw n).real {t | Hired theta tau v vhat ihat t k}
      ≤ expectedValue theta tau v vhat ihat := by
  have hS := measurableSet_hired theta tau v vhat ihat k
  have hint : ∫ t, Set.indicator {t | Hired theta tau v vhat ihat t k} (fun _ => v k) t
      ∂(arrivalLaw n) = (arrivalLaw n).real {t | Hired theta tau v vhat ihat t k} • v k :=
    integral_indicator_const (v k) hS
  rw [smul_eq_mul] at hint
  rw [mul_comm, ← hint]
  unfold expectedValue
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun t => Set.indicator_nonneg (fun _ _ => hv k) t
  · exact integrable_algValue theta tau v vhat ihat hv
  · refine Filter.Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ {t | Hired theta tau v vhat ihat t k}
    · rw [Set.indicator_of_mem ht]
      classical
      unfold algValue
      have hk := Finset.single_le_sum (f := fun i =>
          (if Hired theta tau v vhat ihat t i then v i else 0))
        (fun i _ => by
          show 0 ≤ (if Hired theta tau v vhat ihat t i then v i else 0)
          split_ifs
          · exact hv i
          · exact le_refl 0) (Finset.mem_univ k)
      have h2 : (if Hired theta tau v vhat ihat t k then v k else 0) = v k := if_pos ht
      calc v k = (if Hired theta tau v vhat ihat t k then v k else 0) := h2.symm
        _ ≤ _ := hk
        _ = _ := by congr
    · rw [Set.indicator_of_notMem ht]
      exact algValue_nonneg theta tau v vhat ihat hv t

/-! ### The top candidate -/

theorem exists_top {n : ℕ} (v : Fin n → ℝ) (i0 : Fin n) :
    ∃ istar : Fin n, ∀ j, j ≠ istar → Beats v istar j := by
  classical
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ v ⟨i0, Finset.mem_univ i0⟩
  set s := Finset.univ.filter (fun j => ∀ k, v k ≤ v j) with hs
  have hne : s.Nonempty := ⟨a, by simp [hs]; exact fun k => ha k (Finset.mem_univ k)⟩
  refine ⟨s.min' hne, fun j hj => ?_⟩
  have hmem : s.min' hne ∈ s := Finset.min'_mem s hne
  have hmax : ∀ k, v k ≤ v (s.min' hne) := by
    simpa [hs] using hmem
  rcases lt_or_eq_of_le (hmax j) with h | h
  · exact Or.inl h
  · right
    refine ⟨h, ?_⟩
    have hjs : j ∈ s := by
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
      intro k; rw [h]; exact hmax k
    exact lt_of_le_of_ne (Finset.min'_le s j hjs) (Ne.symm hj)

theorem mem_Mset {n : ℕ} (theta : ℝ) (v vhat : Fin n → ℝ) (i : Fin n) :
    i ∈ Mset theta v vhat ↔ Deviates theta v vhat i := by
  classical
  unfold Mset
  simp

end TheoremOneAssembly

open MeasureTheory SecretaryPred.LearnedDynkin TheoremOneAssembly

theorem solution (n : ℕ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat) :
    (∀ j, 0.215 * v j ≤ expectedValue 0.646 0.313 v vhat ihat) ∧
      ∀ eps : ℝ, 0 ≤ eps → (∀ i, |v i - vhat i| ≤ eps * v i) →
        ∀ j, (1 - eps) / (1 + eps) * v j ≤ expectedValue 0.646 0.313 v vhat ihat := by
  obtain ⟨istar, histar⟩ := exists_top v ihat
  set E := expectedValue 0.646 0.313 v vhat ihat with hE
  set P := (arrivalLaw n).real {t | Hired 0.646 0.313 v vhat ihat t istar} with hPdef
  have hvmax : ∀ j, v j ≤ v istar := by
    intro j
    by_cases hj : j = istar
    · rw [hj]
    · rcases histar j hj with h | h
      · exact h.le
      · exact h.1.le
  have hE0 : 0 ≤ E := expectedValue_nonneg _ _ v vhat ihat hv
  have hred : ∀ c : ℝ, c * v istar ≤ E → ∀ j, c * v j ≤ E := by
    intro c hc j
    by_cases h : 0 ≤ c
    · exact le_trans (mul_le_mul_of_nonneg_left (hvmax j) h) hc
    · push Not at h
      nlinarith [hv j]
  have hP : ∀ c : ℝ, 0 ≤ c → c ≤ P → c * v istar ≤ E := by
    intro c hc hcP
    have h1 : v istar * P ≤ E := expectedValue_ge_hire 0.646 0.313 v vhat ihat hv istar
    have h2 : c * v istar ≤ v istar * P := by nlinarith [hv istar]
    linarith
  obtain ⟨hN0, hNlog, hNii, hNiv, hNv, hNvi⟩ := numerical_bounds
  have hc0 : (0:ℝ) ≤ (1 - 0.646) / (1 + 0.646) := by norm_num
  -- the six cases with `M` nonempty, for a bound `c`
  set M := Mset 0.646 v vhat with hMdef
  have hθ : (0:ℝ) ≤ 0.646 := by norm_num
  have hτ0 : (0:ℝ) < 0.313 := by norm_num
  have hτ1 : (0.313:ℝ) < 1 := by norm_num
  -- the case `M = ∅`
  have hempty : M = ∅ → (∀ j, (1 - 0.646) / (1 + 0.646) * v j ≤ E) ∧
      ∀ eps : ℝ, 0 ≤ eps → (∀ i, |v i - vhat i| ≤ eps * v i) →
        ∀ j, (1 - eps) / (1 + eps) * v j ≤ E := by
    intro hM
    obtain ⟨-, hEv, hcl⟩ := case_M_empty n 0.646 0.313 v vhat ihat hv hvhat hihat hM
    refine ⟨?_, ?_⟩
    · have herr : ∀ i, |v i - vhat i| ≤ 0.646 * v i := by
        intro i
        have hi : i ∉ M := by rw [hM]; exact Finset.notMem_empty i
        rw [hMdef, mem_Mset] at hi
        unfold Deviates at hi
        exact not_lt.mp hi
      intro j
      rw [hE, hEv]
      exact hcl 0.646 hθ herr j
    · intro eps heps herr j
      rw [hE, hEv]
      exact hcl eps heps herr j
  -- general facts about the size of `M`
  have hcard_pos : M.Nonempty → 1 ≤ M.card := fun h => Finset.card_pos.mpr h
  refine ⟨?_, ?_⟩
  · -- the robustness clause: `0.215 · v(j) ≤ E`
    by_cases hM : M = ∅
    · intro j
      have h := (hempty hM).1 j
      have : (0.215:ℝ) * v j ≤ (1 - 0.646) / (1 + 0.646) * v j :=
        mul_le_mul_of_nonneg_right hN0 (hv j)
      linarith
    have hMne : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr hM
    apply hred
    have hm1 := hcard_pos hMne
    by_cases hhs : ihat = istar
    · by_cases hds : Deviates 0.646 v vhat istar
      · exact hP _ (by norm_num) (le_trans (by linarith)
          (case_i n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs hds))
      · exact hP _ (by norm_num) (le_trans (hNii M.card hm1)
          (case_ii n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs hds
            hMne M.card rfl))
    · by_cases hdh : Deviates 0.646 v vhat ihat
      · by_cases hds : Deviates 0.646 v vhat istar
        · exact hP _ (by norm_num) (le_trans (by linarith)
            (case_iii n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs hdh hds))
        · exact hP _ (by norm_num) (le_trans (hNiv M.card hm1)
            (case_iv n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs hdh hds
              M.card rfl))
      · by_cases hds : Deviates 0.646 v vhat istar
        · exact hP _ (by norm_num) (le_trans (hNv M.card hm1)
            (case_v n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs hdh hds
              M.card rfl))
        · have h := case_vi n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs
            hdh hds hMne M.card rfl
          have h2 := mul_le_mul_of_nonneg_right (hNvi M.card hm1) (hv istar)
          linarith
  · -- the consistency clause
    intro eps heps herr
    by_cases hM : M = ∅
    · exact (hempty hM).2 eps heps herr
    have hMne : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr hM
    have hm1 := hcard_pos hMne
    -- some candidate deviates, hence `θ < ε`
    obtain ⟨i, hi⟩ := hMne
    have hdi : Deviates 0.646 v vhat i := (mem_Mset _ _ _ _).mp hi
    have hθε : (0.646:ℝ) < eps := by
      by_contra hle
      push Not at hle
      unfold Deviates at hdi
      have := mul_le_mul_of_nonneg_right hle (hv i)
      linarith [herr i]
    have hMne : M.Nonempty := ⟨i, hi⟩
    apply hred
    by_cases hW : M.card = 1 ∧ ¬ Deviates 0.646 v vhat istar
    · exact window_single_deviator n v vhat ihat istar hv hvhat hihat histar hW.2 hW.1 eps hθε herr
    -- otherwise the bounds of cases (i)–(vi) all exceed `c₀ = (1-θ)/(1+θ) ≥ (1-ε)/(1+ε)`
    have hcε : (1 - eps) / (1 + eps) ≤ (1 - 0.646) / (1 + 0.646) := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    suffices hc0E : (1 - 0.646) / (1 + 0.646) * v istar ≤ E by
      have := mul_le_mul_of_nonneg_right hcε (hv istar)
      linarith
    have hlog : (1 - 0.646 : ℝ) / (1 + 0.646) ≤ 0.313 * Real.log (1 / 0.313) := by
      have : (1 - 0.646 : ℝ) / (1 + 0.646) ≤ 0.363 := by norm_num
      linarith
    by_cases hds : Deviates 0.646 v vhat istar
    · by_cases hhs : ihat = istar
      · exact hP _ hc0 (le_trans hlog
          (case_i n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs hds))
      · by_cases hdh : Deviates 0.646 v vhat ihat
        · exact hP _ hc0 (le_trans hlog
            (case_iii n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs hdh hds))
        · have h := case_v n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs hdh
            hds M.card rfl
          have hn := c0_v M.card hm1
          rw [negative_sum] at h
          exact hP _ hc0 (by linarith)
    · have hm2 : 2 ≤ M.card := by
        by_contra h2
        exact hW ⟨by omega, hds⟩
      have hiv := c0_iv M.card hm2
      by_cases hhs : ihat = istar
      · have h := case_ii n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs hds
          hMne M.card rfl
        have hpos : (0:ℝ) ≤ 1 / ((M.card : ℝ) + 1) := by positivity
        change _ + 0.313 * altSum M.card 0.313 ≤ P at h
        exact hP _ hc0 (by linarith)
      · by_cases hdh : Deviates 0.646 v vhat ihat
        · have h := case_iv n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs
            hdh hds M.card rfl
          change 0.313 * altSum M.card 0.313 ≤ P at h
          exact hP _ hc0 (by linarith)
        · have h := case_vi n 0.646 0.313 v vhat ihat istar hv hvhat hihat histar hθ hτ0 hτ1 hhs
            hdh hds hMne M.card rfl
          have hn := c0_vi M.card hm2
          rw [negative_sum] at h
          have h2 := mul_le_mul_of_nonneg_right hn (hv istar)
          linarith
