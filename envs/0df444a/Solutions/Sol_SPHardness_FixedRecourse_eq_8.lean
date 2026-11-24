-- Prove2me | solution 1 for SPHardness.FixedRecourse.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:39:50.886168+00:00
-- url     : https://prove2.me/submissions/819bc087-d395-4375-a801-382aa918b625

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

open SPHardness.FixedRecourse

namespace Eq8Aux

/-- Truncated power: x ^ n on [0, ∞) and 0 elsewhere (for n = 0 the indicator of [0, ∞)). -/
def P (n : ℕ) (x : ℝ) : ℝ := if 0 ≤ x then x ^ n else 0

lemma cube_vol (m : ℕ) : volume (cube m) = 1 := by
  rw [cube, volume_pi_pi]
  simp

lemma cube_meas (m : ℕ) : MeasurableSet (cube m) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma cube_compact (m : ℕ) : IsCompact (cube m) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

lemma P_succ_eq (n : ℕ) (x : ℝ) : P (n + 1) x = (max 0 x) ^ (n + 1) := by
  unfold P
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_not_ge h), zero_pow (Nat.succ_ne_zero n)]

lemma oneD (n : ℕ) (a c : ℝ) (ha : 0 < a) :
    ∫ x in Set.Icc (0 : ℝ) 1, P n (c - a * x) =
      (P (n + 1) c - P (n + 1) (c - a)) / (a * ((n : ℝ) + 1)) := by
  rw [integral_Icc_eq_integral_Ioc]
  rcases le_or_gt c 0 with hc | hc
  · have h0 : ∀ x ∈ Set.Ioc (0 : ℝ) 1, P n (c - a * x) = 0 := by
      intro x hx
      unfold P
      rw [if_neg]
      have := mul_pos ha hx.1
      exact not_le.mpr (by linarith)
    rw [setIntegral_congr_fun measurableSet_Ioc h0]
    have h1 : P (n + 1) c = 0 := by
      rw [P_succ_eq, max_eq_left hc, zero_pow (Nat.succ_ne_zero n)]
    have h2 : P (n + 1) (c - a) = 0 := by
      rw [P_succ_eq, max_eq_left (by linarith), zero_pow (Nat.succ_ne_zero n)]
    rw [h1, h2]
    simp
  · set m := min 1 (c / a) with hm
    have hca : 0 < c / a := div_pos hc ha
    have hm0 : 0 ≤ m := le_min zero_le_one hca.le
    have hfun : (fun x => P n (c - a * x)) =
        (Set.Iic (c / a)).indicator (fun x => (c - a * x) ^ n) := by
      funext x
      unfold P
      by_cases hx : x ≤ c / a
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx), if_pos]
        have := (le_div_iff₀ ha).mp hx
        linarith
      · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Iic.mp h)), if_neg]
        intro h
        exact hx ((le_div_iff₀ ha).mpr (by linarith))
    have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iic (c / a) = Set.Ioc 0 m := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, hm, le_min_iff]
      tauto
    have key : ∫ x in (0 : ℝ)..m, (c - a * x) ^ n =
        a⁻¹ • ∫ x in (c - a * m)..(c - a * 0), x ^ n :=
      intervalIntegral.integral_comp_sub_mul (fun x => x ^ n) ha.ne' c
    rw [hfun, setIntegral_indicator measurableSet_Iic, hset,
      ← intervalIntegral.integral_of_le hm0, key, integral_pow, smul_eq_mul, mul_zero, sub_zero]
    have h1 : P (n + 1) c = c ^ (n + 1) := by
      unfold P
      rw [if_pos hc.le]
    rw [h1]
    rcases le_total a c with hac | hac
    · have hm1 : m = 1 := min_eq_left ((one_le_div ha).mpr hac)
      have h2 : P (n + 1) (c - a) = (c - a) ^ (n + 1) := by
        unfold P
        rw [if_pos (by linarith)]
      rw [hm1, h2, mul_one, inv_mul_eq_div, div_div, mul_comm ((n : ℝ) + 1) a]
    · have hm1 : m = c / a := min_eq_right ((div_le_one ha).mpr hac)
      have h2 : P (n + 1) (c - a) = 0 := by
        rw [P_succ_eq, max_eq_left (by linarith), zero_pow (Nat.succ_ne_zero n)]
      have h3 : c - a * (c / a) = 0 := by
        field_simp
        ring
      rw [hm1, h2, h3, zero_pow (Nat.succ_ne_zero n), inv_mul_eq_div, div_div,
        mul_comm ((n : ℝ) + 1) a]

lemma slice {k : ℕ} (n : ℕ) (α : Fin (k + 1) → ℝ) (β : ℝ) :
    ∫ ξ in cube (k + 1), P n (β - ∑ j, α j * ξ j) =
      ∫ y in cube k, ∫ x in Set.Icc (0 : ℝ) 1,
        P n (β - ∑ j : Fin k, α j.succ * y j - α 0 * x) := by
  let h : ℝ × (Fin k → ℝ) → ℝ := fun p => β - ∑ j : Fin k, α j.succ * p.2 j - α 0 * p.1
  let G : ℝ × (Fin k → ℝ) → ℝ := fun p => P n (h p)
  have hh : Continuous h := by
    show Continuous (fun p : ℝ × (Fin k → ℝ) => β - ∑ j : Fin k, α j.succ * p.2 j - α 0 * p.1)
    fun_prop
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have hpre : e ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ cube k) = cube (k + 1) := by
    ext ξ
    show (ξ 0 ∈ Set.Icc (0 : ℝ) 1 ∧ (fun j => ξ ((0 : Fin (k + 1)).succAbove j)) ∈ cube k) ↔
      ξ ∈ cube (k + 1)
    simp only [cube, Set.mem_pi, Set.mem_univ, true_imp_iff, Fin.forall_fin_succ,
      Fin.succAbove_zero]
  have hG : ∀ ξ, G (e ξ) = P n (β - ∑ j, α j * ξ j) := by
    intro ξ
    show P n (β - ∑ j : Fin k, α j.succ * ξ ((0 : Fin (k + 1)).succAbove j) - α 0 * ξ 0) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.succAbove_zero]
    congr 1
    ring
  have hint : IntegrableOn G (Set.Icc (0 : ℝ) 1 ×ˢ cube k) volume := by
    have hfun : G = {p | 0 ≤ h p}.indicator (fun p => h p ^ n) := by
      funext p
      show P n (h p) = _
      unfold P
      by_cases hp : 0 ≤ h p
      · rw [if_pos hp, Set.indicator_of_mem (show p ∈ {p | 0 ≤ h p} from hp)]
      · rw [if_neg hp, Set.indicator_of_notMem (show p ∉ {p | 0 ≤ h p} from hp)]
    rw [hfun]
    exact ((hh.pow n).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (cube_compact k))).indicator
      (measurableSet_le measurable_const hh.measurable)
  have hint' : Integrable (Function.uncurry fun (x : ℝ) (y : Fin k → ℝ) => G (x, y))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (cube k))) := by
    rw [Measure.prod_restrict]
    exact hint
  calc ∫ ξ in cube (k + 1), P n (β - ∑ j, α j * ξ j)
      = ∫ ξ in e ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ cube k), G (e ξ) := by
        rw [hpre]
        exact setIntegral_congr_fun (cube_meas _) (fun ξ _ => (hG ξ).symm)
    _ = ∫ p in Set.Icc (0 : ℝ) 1 ×ˢ cube k, G p :=
        hmp.setIntegral_preimage_emb e.measurableEmbedding G _
    _ = ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in cube k, G (x, y) := by
        rw [Measure.volume_eq_prod]
        exact setIntegral_prod G hint
    _ = ∫ y in cube k, ∫ x in Set.Icc (0 : ℝ) 1, G (x, y) := integral_integral_swap hint'

lemma sum_finset_succ {k : ℕ} (f : Finset (Fin (k + 1)) → ℝ) :
    ∑ s : Finset (Fin (k + 1)), f s =
      ∑ u : Finset (Fin k), f (u.map (Fin.succEmb k)) +
        ∑ u : Finset (Fin k), f (insert 0 (u.map (Fin.succEmb k))) := by
  have h0 : (0 : Fin (k + 1)) ∉ (Finset.univ : Finset (Fin k)).map (Fin.succEmb k) := by
    simp [Fin.succ_ne_zero]
  have hu : (Finset.univ : Finset (Fin (k + 1))) =
      insert 0 ((Finset.univ : Finset (Fin k)).map (Fin.succEmb k)) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  have hp : ((Finset.univ : Finset (Fin k)).map (Fin.succEmb k)).powerset =
      (Finset.univ : Finset (Finset (Fin k))).map
        (Finset.mapEmbedding (Fin.succEmb k)).toEmbedding := by
    ext t
    rw [Finset.mem_powerset, Finset.subset_map_iff, Finset.mem_map]
    constructor
    · rintro ⟨u, -, rfl⟩
      exact ⟨u, Finset.mem_univ _, rfl⟩
    · rintro ⟨u, -, rfl⟩
      exact ⟨u, Finset.subset_univ _, rfl⟩
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert h0, hp, Finset.sum_map,
    Finset.sum_map]
  rfl

lemma main : ∀ (k n : ℕ) (α : Fin k → ℝ) (β : ℝ), (∀ j, 0 < α j) →
    ∫ ξ in cube k, P n (β - ∑ j, α j * ξ j) =
      (n.factorial : ℝ) / ((n + k).factorial : ℝ) *
        (∑ s : Finset (Fin k), (-1 : ℝ) ^ s.card * P (n + k) (β - ∑ j ∈ s, α j)) /
          ∏ j, α j := by
  intro k
  induction k with
  | zero =>
    intro n α β _
    have hs : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
      ext s
      rw [Finset.eq_empty_of_isEmpty s]
      simp only [Finset.mem_univ, Finset.mem_singleton]
    have hc : volume.real (cube 0) = 1 := by
      rw [measureReal_def, cube_vol, ENNReal.toReal_one]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [hs, Finset.sum_singleton]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, sub_zero,
      Finset.card_empty, pow_zero, one_mul, add_zero, div_one]
    rw [setIntegral_const, hc, one_smul, div_self hf, one_mul]
  | succ k ih =>
    intro n α β hα
    have ha : 0 < α 0 := hα 0
    have hN : n + (k + 1) = n + 1 + k := by omega
    rw [hN, slice n α β]
    have inner : ∀ y : Fin k → ℝ,
        ∫ x in Set.Icc (0 : ℝ) 1, P n (β - ∑ j : Fin k, α j.succ * y j - α 0 * x) =
          (P (n + 1) (β - ∑ j : Fin k, α j.succ * y j) -
            P (n + 1) (β - α 0 - ∑ j : Fin k, α j.succ * y j)) / (α 0 * ((n : ℝ) + 1)) := by
      intro y
      rw [oneD n (α 0) (β - ∑ j : Fin k, α j.succ * y j) ha,
        show β - ∑ j : Fin k, α j.succ * y j - α 0 = β - α 0 - ∑ j : Fin k, α j.succ * y j by ring]
    have hi1 : ∀ γ : ℝ, IntegrableOn
        (fun y : Fin k → ℝ => P (n + 1) (γ - ∑ j : Fin k, α j.succ * y j)) (cube k) volume := by
      intro γ
      have hfe : (fun y : Fin k → ℝ => P (n + 1) (γ - ∑ j : Fin k, α j.succ * y j)) =
          fun y => (max 0 (γ - ∑ j : Fin k, α j.succ * y j)) ^ (n + 1) :=
        funext fun y => P_succ_eq _ _
      rw [hfe]
      have hcont : Continuous
          (fun y : Fin k → ℝ => (max 0 (γ - ∑ j : Fin k, α j.succ * y j)) ^ (n + 1)) :=
        (continuous_const.max (continuous_const.sub (continuous_finsetSum _
          fun j _ => continuous_const.mul (continuous_apply j)))).pow (n + 1)
      exact hcont.continuousOn.integrableOn_compact (cube_compact k)
    have hQ : ∑ s : Finset (Fin (k + 1)),
          (-1 : ℝ) ^ s.card * P (n + 1 + k) (β - ∑ j ∈ s, α j) =
        (∑ u : Finset (Fin k), (-1 : ℝ) ^ u.card * P (n + 1 + k) (β - ∑ j ∈ u, α j.succ)) -
        ∑ u : Finset (Fin k),
          (-1 : ℝ) ^ u.card * P (n + 1 + k) (β - α 0 - ∑ j ∈ u, α j.succ) := by
      rw [sum_finset_succ, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      have h0 : (0 : Fin (k + 1)) ∉ u.map (Fin.succEmb k) := by
        simp [Fin.succ_ne_zero]
      rw [Finset.card_insert_of_notMem h0, Finset.sum_insert h0, Finset.card_map,
        Finset.sum_map, pow_succ]
      show (-1 : ℝ) ^ u.card * P (n + 1 + k) (β - ∑ x ∈ u, α x.succ) +
          (-1 : ℝ) ^ u.card * -1 * P (n + 1 + k) (β - (α 0 + ∑ x ∈ u, α x.succ)) =
        (-1 : ℝ) ^ u.card * P (n + 1 + k) (β - ∑ j ∈ u, α j.succ) -
          (-1 : ℝ) ^ u.card * P (n + 1 + k) (β - α 0 - ∑ j ∈ u, α j.succ)
      rw [show β - (α 0 + ∑ x ∈ u, α x.succ) = β - α 0 - ∑ x ∈ u, α x.succ by ring]
      ring
    have hD : ((n + 1 + k).factorial : ℝ) ≠ 0 := by positivity
    have hP : (∏ j : Fin k, α j.succ) ≠ 0 := (Finset.prod_pos fun j _ => hα _).ne'
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have ha' : α 0 ≠ 0 := ha.ne'
    simp only [inner]
    rw [integral_div, integral_sub (hi1 β) (hi1 (β - α 0)),
      ih (n + 1) (fun j => α j.succ) β (fun j => hα _),
      ih (n + 1) (fun j => α j.succ) (β - α 0) (fun j => hα _), hQ, Fin.prod_univ_succ,
      Nat.factorial_succ n]
    push_cast
    field_simp

end Eq8Aux

open Eq8Aux

theorem solution {k : ℕ} (α : Fin k → ℝ) (β : ℝ)
    (hα : ∀ j, 0 < α j) (hβ : 0 ≤ β) :
    vol α β =
      (∑ s : Finset (Fin k), (-1 : ℝ) ^ s.card *
        (max 0 (β - ∑ j ∈ s, α j)) ^ k) /
        ((k.factorial : ℝ) * ∏ j, α j) := by
  have hvol : vol α β = ∫ ξ in cube k, P 0 (β - ∑ j, α j * ξ j) := by
    have hm : MeasurableSet {ξ : Fin k → ℝ | ∑ j, α j * ξ j ≤ β} :=
      measurableSet_le (by fun_prop) measurable_const
    have hfun : (fun ξ : Fin k → ℝ => P 0 (β - ∑ j, α j * ξ j)) =
        {ξ : Fin k → ℝ | ∑ j, α j * ξ j ≤ β}.indicator (fun _ => (1 : ℝ)) := by
      funext ξ
      unfold P
      by_cases h : ∑ j, α j * ξ j ≤ β
      · rw [Set.indicator_of_mem (show ξ ∈ {ξ : Fin k → ℝ | ∑ j, α j * ξ j ≤ β} from h),
          if_pos (by linarith), pow_zero]
      · rw [Set.indicator_of_notMem (show ξ ∉ {ξ : Fin k → ℝ | ∑ j, α j * ξ j ≤ β} from h),
          if_neg (fun h' => h (by linarith))]
    rw [hfun, integral_indicator_const _ hm, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply hm]
    unfold vol knapsack
    congr 2
    ext ξ
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩
  have hP : ∀ s : Finset (Fin k), P k (β - ∑ j ∈ s, α j) = (max 0 (β - ∑ j ∈ s, α j)) ^ k := by
    intro s
    rcases k with _ | k
    · rw [Finset.eq_empty_of_isEmpty s]
      unfold P
      simp [hβ]
    · exact P_succ_eq _ _
  rw [hvol, main k 0 α β hα]
  simp only [zero_add, hP, Nat.factorial_zero, Nat.cast_one]
  ring
