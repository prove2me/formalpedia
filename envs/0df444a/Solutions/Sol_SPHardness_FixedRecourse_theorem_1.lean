-- Prove2me | solution 1 for SPHardness.FixedRecourse.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T17:31:14.542988+00:00
-- url     : https://prove2.me/submissions/6fc31ccb-76f0-4e80-8591-726ddbb4c55d

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace FR7568
open SPHardness.FixedRecourse

lemma mem_cube {k : ℕ} (x : Fin k → ℝ) : x ∈ cube k ↔ ∀ j, x j ∈ Set.Icc (0:ℝ) 1 := by
  simp only [cube, Set.mem_univ_pi]

lemma measurableSet_cube (k : ℕ) : MeasurableSet (cube k) := by
  unfold cube
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma isCompact_cube (k : ℕ) : IsCompact (cube k) := by
  unfold cube
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

lemma volume_cube (k : ℕ) : volume (cube k) = 1 := by
  unfold cube
  rw [volume_pi_pi]
  simp

lemma knapsack_eq {k : ℕ} (α : Fin k → ℝ) (t : ℝ) :
    knapsack α t = cube k ∩ {ξ | ∑ j, α j * ξ j ≤ t} := rfl

lemma measurableSet_knapsack {k : ℕ} (α : Fin k → ℝ) (t : ℝ) :
    MeasurableSet (knapsack α t) := by
  rw [knapsack_eq]
  refine (measurableSet_cube k).inter ?_
  exact measurableSet_le (by fun_prop) measurable_const

lemma volume_knapsack_le {k : ℕ} (α : Fin k → ℝ) (t : ℝ) :
    volume (knapsack α t) ≤ 1 := by
  rw [← volume_cube k]
  exact measure_mono (fun x hx => hx.1)

lemma vol_nonneg {k : ℕ} (α : Fin k → ℝ) (t : ℝ) : 0 ≤ vol α t := ENNReal.toReal_nonneg

lemma vol_le_one {k : ℕ} (α : Fin k → ℝ) (t : ℝ) : vol α t ≤ 1 := by
  unfold vol
  have := volume_knapsack_le α t
  calc (volume (knapsack α t)).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top this
    _ = 1 := by simp

lemma vol_mono {k : ℕ} (α : Fin k → ℝ) : Monotone (vol α) := by
  intro s t hst
  unfold vol
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (volume_knapsack_le α t)
  · apply measure_mono
    intro x hx
    exact ⟨hx.1, le_trans hx.2 hst⟩

/-- the second stage value on the cube -/
lemma secondStageValue_eq {k : ℕ} (α : Fin k → ℝ) (hα : ∀ j, 0 ≤ α j) (β : ℝ)
    (ξ : Fin k → ℝ) (hξ : ∀ j, 0 ≤ ξ j) :
    secondStageValue α β ξ = max (∑ j, α j * ξ j - β) 0 := by
  unfold secondStageValue
  apply IsGreatest.csSup_eq
  constructor
  · by_cases h : 0 ≤ ∑ j, α j * ξ j - β
    · refine ⟨α, 1, fun j => hα j, fun j => by simp, zero_le_one, le_rfl, ?_⟩
      rw [max_eq_left h]
      simp [mul_comm]
    · refine ⟨0, 0, fun j => le_rfl, fun j => by simp, le_rfl, zero_le_one, ?_⟩
      rw [max_eq_right (le_of_lt (not_le.mp h))]
      simp
  · rintro v ⟨y, z, hy0, hyz, hz0, hz1, rfl⟩
    have h1 : ∑ j, ξ j * y j ≤ ∑ j, ξ j * (α j * z) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hyz j) (hξ j))
    have h2 : ∑ j, ξ j * (α j * z) = z * ∑ j, α j * ξ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    have h3 : z * (∑ j, α j * ξ j - β) ≤ max (∑ j, α j * ξ j - β) 0 := by
      rcases le_total 0 (∑ j, α j * ξ j - β) with h | h
      · calc z * (∑ j, α j * ξ j - β) ≤ 1 * (∑ j, α j * ξ j - β) :=
              mul_le_mul_of_nonneg_right hz1 h
          _ ≤ _ := by rw [one_mul]; exact le_max_left _ _
      · calc z * (∑ j, α j * ξ j - β) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hz0 h
          _ ≤ _ := le_max_right _ _
    nlinarith [h1, h2, h3]

lemma expRecourse_eq {k : ℕ} (α : Fin k → ℝ) (hα : ∀ j, 0 ≤ α j) (t : ℝ) :
    expRecourse α t = ∫ ξ in cube k, max (∑ j, α j * ξ j - t) 0 := by
  unfold expRecourse
  apply setIntegral_congr_fun (measurableSet_cube k)
  intro ξ hξ
  rw [mem_cube] at hξ
  exact secondStageValue_eq α hα t ξ (fun j => (hξ j).1)

lemma integrableOn_pos {k : ℕ} (α : Fin k → ℝ) (t : ℝ) :
    IntegrableOn (fun ξ : Fin k → ℝ => max (∑ j, α j * ξ j - t) 0) (cube k) := by
  exact ContinuousOn.integrableOn_compact (isCompact_cube k) (by fun_prop)

lemma vol_eq_integral {k : ℕ} (α : Fin k → ℝ) (t : ℝ) :
    vol α t = ∫ ξ in cube k, ({ξ : Fin k → ℝ | ∑ j, α j * ξ j ≤ t}.indicator 1 ξ : ℝ) := by
  have hm : MeasurableSet {ξ : Fin k → ℝ | ∑ j, α j * ξ j ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [integral_indicator_one hm, Measure.real_def, Measure.restrict_apply hm]
  unfold vol
  rw [knapsack_eq, Set.inter_comm]

/-- finite difference sandwich -/
lemma pt_lower (u γ h : ℝ) (hh : 0 < h) :
    (if u ≤ γ then (1:ℝ) else 0) ≤ (max (u - (γ + h)) 0 - max (u - γ) 0) / h + 1 := by
  by_cases hu : u ≤ γ
  · rw [if_pos hu, max_eq_right (by linarith), max_eq_right (by linarith)]
    simp
  · rw [if_neg hu]
    have : max (u - (γ + h)) 0 - max (u - γ) 0 ≥ -h := by
      rcases le_total (u - (γ + h)) 0 with h1 | h1
      · rw [max_eq_right h1, max_eq_left (by linarith)]; linarith
      · rw [max_eq_left h1, max_eq_left (by linarith)]; linarith
    have : (max (u - (γ + h)) 0 - max (u - γ) 0) / h ≥ -1 := by
      rw [ge_iff_le, le_div_iff₀ hh]; linarith
    linarith

lemma pt_upper (u γ h : ℝ) (hh : 0 < h) :
    (max (u - (γ + h)) 0 - max (u - γ) 0) / h + 1 ≤ (if u ≤ γ + h then (1:ℝ) else 0) := by
  by_cases hu : u ≤ γ + h
  · rw [if_pos hu]
    have : max (u - (γ + h)) 0 - max (u - γ) 0 ≤ 0 := by
      rw [max_eq_right (by linarith)]; simp
    have : (max (u - (γ + h)) 0 - max (u - γ) 0) / h ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg this hh.le
    linarith
  · rw [if_neg hu, max_eq_left (by linarith), max_eq_left (by linarith)]
    have : (u - (γ + h) - (u - γ)) / h = -1 := by
      rw [show u - (γ + h) - (u - γ) = -h by ring, neg_div, div_self hh.ne']
    linarith

lemma fd_sandwich {k : ℕ} (α : Fin k → ℝ) (hα : ∀ j, 0 ≤ α j) (γ h : ℝ) (hh : 0 < h) :
    vol α γ ≤ (expRecourse α (γ + h) - expRecourse α γ) / h + 1 ∧
    (expRecourse α (γ + h) - expRecourse α γ) / h + 1 ≤ vol α (γ + h) := by
  haveI : IsFiniteMeasure (volume.restrict (cube k)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, volume_cube]; exact ENNReal.one_lt_top
  have hm : ∀ s : ℝ, MeasurableSet {ξ : Fin k → ℝ | ∑ j, α j * ξ j ≤ s} := fun s =>
    measurableSet_le (by fun_prop) measurable_const
  have hint : ∀ s : ℝ, IntegrableOn
      (fun ξ : Fin k → ℝ => ({ξ : Fin k → ℝ | ∑ j, α j * ξ j ≤ s}.indicator 1 ξ : ℝ))
      (cube k) := by
    intro s
    exact (integrable_const (1:ℝ)).indicator (hm s)
  have hmid : (expRecourse α (γ + h) - expRecourse α γ) / h + 1 =
      ∫ ξ in cube k, ((max (∑ j, α j * ξ j - (γ + h)) 0 - max (∑ j, α j * ξ j - γ) 0) / h
        + 1) := by
    rw [integral_add, integral_div, integral_sub, integral_const, expRecourse_eq α hα,
      expRecourse_eq α hα]
    · simp [Measure.real_def, Measure.restrict_apply MeasurableSet.univ, volume_cube]
    · exact integrableOn_pos α _
    · exact integrableOn_pos α _
    · exact ((integrableOn_pos α _).sub (integrableOn_pos α _)).div_const _
    · exact integrable_const _
  rw [hmid, vol_eq_integral, vol_eq_integral]
  constructor
  · apply setIntegral_mono_on (hint γ) _ (measurableSet_cube k)
    · intro ξ _
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      exact pt_lower _ _ _ hh
    · exact ((integrableOn_pos α _).sub (integrableOn_pos α _)).div_const _ |>.add
        (integrable_const _)
  · apply setIntegral_mono_on _ (hint (γ + h)) (measurableSet_cube k)
    · intro ξ _
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      exact pt_upper _ _ _ hh
    · exact ((integrableOn_pos α _).sub (integrableOn_pos α _)).div_const _ |>.add
        (integrable_const _)


/-! ## Part B: slicing, pp, Lemma 1 -/

lemma vol_succ {k : ℕ} (α : Fin (k + 1) → ℝ) (ha : 0 ≤ α (Fin.last k)) (t : ℝ) :
    vol α t = ∫ u in (0:ℝ)..1,
      vol (fun j => α (Fin.castSucc j)) (t - α (Fin.last k) * u) := by
  set a := α (Fin.last k)
  set α' : Fin k → ℝ := fun j => α (Fin.castSucc j)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
  have he : ∀ x, e x = (x (Fin.last k), fun j => x (Fin.castSucc j)) := by
    intro x
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  let T : Set (ℝ × (Fin k → ℝ)) :=
    {p | p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 ∈ cube k ∧ ∑ j, α' j * p.2 j ≤ t - a * p.1}
  have hTm : MeasurableSet T := by
    refine (measurableSet_Icc.preimage measurable_fst).inter
      (((measurableSet_cube k).preimage measurable_snd).inter ?_)
    exact measurableSet_le (f := fun p : ℝ × (Fin k → ℝ) => ∑ j, α' j * p.2 j)
      (g := fun p : ℝ × (Fin k → ℝ) => t - a * p.1) (by fun_prop) (by fun_prop)
  have hKT : knapsack α t = e ⁻¹' T := by
    ext x
    simp only [Set.mem_preimage, he, T, Set.mem_setOf_eq, knapsack, mem_cube, α']
    rw [Fin.forall_fin_succ', Fin.sum_univ_castSucc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h2, h1, by linarith⟩
    · rintro ⟨h2, h1, h3⟩
      exact ⟨⟨h1, h2⟩, by linarith⟩
  have hfib : ∀ u : ℝ, volume (Prod.mk u ⁻¹' T) =
      (Set.Icc (0:ℝ) 1).indicator (fun u => volume (knapsack α' (t - a * u))) u := by
    intro u
    by_cases hu : u ∈ Set.Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem hu]
      congr 1
      ext y
      simp only [Set.mem_preimage, T, Set.mem_setOf_eq, knapsack]
      exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hu, h.1, h.2⟩⟩
    · rw [Set.indicator_of_notMem hu]
      have : Prod.mk u ⁻¹' T = ∅ := by
        ext y; simp only [Set.mem_preimage, T, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h; exact absurd h hu
      rw [this, measure_empty]
  have hvol : volume (knapsack α t) =
      ∫⁻ u in Set.Icc (0:ℝ) 1, volume (knapsack α' (t - a * u)) := by
    rw [hKT, hmp.measure_preimage hTm.nullMeasurableSet, Measure.prod_apply hTm]
    simp_rw [hfib]
    rw [lintegral_indicator measurableSet_Icc]
  have hanti : Antitone (fun u : ℝ => volume (knapsack α' (t - a * u))) := by
    intro u v huv
    apply measure_mono
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (by nlinarith)⟩
  unfold vol
  rw [hvol, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    integral_toReal]
  · exact hanti.measurable.aemeasurable
  · exact Filter.Eventually.of_forall (fun u =>
      lt_of_le_of_lt (volume_knapsack_le α' _) ENNReal.one_lt_top)

/-- truncated power -/
def pp (n : ℕ) (x : ℝ) : ℝ := if 0 ≤ x then x ^ n else 0

lemma pp_succ (n : ℕ) (x : ℝ) : pp (n + 1) x = (max x 0) ^ (n + 1) := by
  unfold pp
  split_ifs with h
  · rw [max_eq_left h]
  · rw [max_eq_right (le_of_lt (not_le.mp h))]; simp

lemma pp_mono (n : ℕ) : Monotone (pp n) := by
  intro x y hxy
  unfold pp
  split_ifs with h1 h2 h2
  · exact pow_le_pow_left₀ h1 hxy n
  · exact absurd (le_trans h1 hxy) h2
  · exact pow_nonneg h2 n
  · exact le_rfl

lemma pp_continuous (n : ℕ) : Continuous (pp (n + 1)) := by
  have : pp (n + 1) = fun x => (max x 0) ^ (n + 1) := funext (pp_succ n)
  rw [this]; fun_prop

lemma hasDerivAt_pp (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (pp (n + 1)) (((n : ℝ) + 1) * pp n x) x := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hev : (fun _ : ℝ => (0:ℝ)) =ᶠ[nhds x] pp (n + 1) := by
      filter_upwards [Iio_mem_nhds h] with y hy
      unfold pp; rw [if_neg (not_le.mpr hy)]
    have : pp n x = 0 := by unfold pp; rw [if_neg (not_le.mpr h)]
    rw [this, mul_zero]
    exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq hev.symm
  · have hev : (fun y : ℝ => y ^ (n + 1)) =ᶠ[nhds x] pp (n + 1) := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      unfold pp; rw [if_pos (le_of_lt hy)]
    have : pp n x = x ^ n := by unfold pp; rw [if_pos (le_of_lt h)]
    rw [this]
    have := hasDerivAt_pow (n + 1) x
    simp only [Nat.add_sub_cancel] at this
    push_cast at this
    exact this.congr_of_eventuallyEq hev.symm

lemma integral_pp (n : ℕ) (c d : ℝ) (hcd : c ≤ d) :
    ∫ w in c..d, pp n w = (pp (n + 1) d - pp (n + 1) c) / ((n : ℝ) + 1) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [integral_eq_of_hasDerivAt_off_countable_of_le (fun w => pp (n + 1) w / ((n : ℝ) + 1))
    (pp n) hcd (Set.countable_singleton 0)]
  · ring
  · exact ((pp_continuous n).div_const _).continuousOn
  · intro x hx
    have hx0 : x ≠ 0 := fun h => hx.2 (by simp [h])
    have := (hasDerivAt_pp n x hx0).div_const ((n : ℝ) + 1)
    rwa [mul_div_cancel_left₀ _ hn] at this
  · exact (pp_mono n).intervalIntegrable

lemma integral_pp_slice (n : ℕ) (c a : ℝ) (ha : 0 < a) :
    ∫ u in (0:ℝ)..1, pp n (c - a * u) =
      (pp (n + 1) c - pp (n + 1) (c - a)) / (((n : ℝ) + 1) * a) := by
  rw [intervalIntegral.integral_comp_sub_mul (f := pp n) ha.ne' c, mul_one, mul_zero, sub_zero,
    integral_pp n _ _ (by linarith), smul_eq_mul]
  field_simp

lemma sum_finset_fin_succ {k : ℕ} (f : Finset (Fin (k + 1)) → ℝ) :
    ∑ S : Finset (Fin (k + 1)), f S =
      ∑ S : Finset (Fin k), (f (S.map Fin.castSuccEmb) +
        f (insert (Fin.last k) (S.map Fin.castSuccEmb))) := by
  have hnot : Fin.last k ∉ (Finset.univ : Finset (Fin k)).map Fin.castSuccEmb := by
    simp [Finset.mem_map]
  rw [← Finset.powerset_univ, Fin.univ_castSuccEmb, Finset.cons_eq_insert,
    Finset.sum_powerset_insert hnot, ← Finset.sum_add_distrib]
  have himg : ((Finset.univ : Finset (Fin k)).map Fin.castSuccEmb).powerset =
      (Finset.univ : Finset (Finset (Fin k))).image (fun S => S.map Fin.castSuccEmb) := by
    ext T
    simp only [Finset.mem_powerset, Finset.mem_image, Finset.mem_univ, true_and]
    rw [Finset.subset_map_iff]
    constructor
    · rintro ⟨u, _, rfl⟩; exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩; exact ⟨u, Finset.subset_univ _, rfl⟩
  rw [himg, Finset.sum_image (fun S _ T _ h => (Finset.map_inj).1 h)]

lemma lemma1 (k : ℕ) (α : Fin k → ℝ) (hα : ∀ j, 0 < α j) (t : ℝ) :
    (k.factorial : ℝ) * (∏ j, α j) * vol α t =
      ∑ S : Finset (Fin k), (-1 : ℝ) ^ S.card * pp k (t - ∑ j ∈ S, α j) := by
  induction k generalizing t with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one, Finset.univ_eq_empty, Finset.prod_empty,
      one_mul]
    rw [Fintype.sum_unique]
    have hd : (default : Finset (Fin 0)) = ∅ := Subsingleton.elim _ _
    rw [hd]
    simp only [Finset.card_empty, pow_zero, Finset.sum_empty, sub_zero, one_mul]
    unfold vol pp
    by_cases ht : 0 ≤ t
    · rw [if_pos ht, pow_zero]
      have : knapsack α t = cube 0 := by
        ext x; simp [knapsack, ht]
      rw [this, volume_cube]; simp
    · rw [if_neg ht]
      have : knapsack α t = ∅ := by
        ext x; simp [knapsack, ht]
      rw [this]; simp
  | succ k ih =>
    rw [vol_succ α (hα _).le t]
    set a := α (Fin.last k)
    set α' : Fin k → ℝ := fun j => α (Fin.castSucc j)
    have ha : 0 < a := hα _
    have hP : 0 < ∏ j, α' j := Finset.prod_pos (fun j _ => hα _)
    have hF : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hvol' : ∀ s, vol α' s =
        (∑ S : Finset (Fin k), (-1 : ℝ) ^ S.card * pp k (s - ∑ j ∈ S, α' j)) /
          ((k.factorial : ℝ) * ∏ j, α' j) := by
      intro s
      rw [← ih α' (fun j => hα _) s]
      field_simp
    simp_rw [hvol']
    rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul]
      have hsl : ∀ S : Finset (Fin k), ∫ u in (0:ℝ)..1, pp k (t - a * u - ∑ j ∈ S, α' j) =
          (pp (k + 1) (t - ∑ j ∈ S, α' j) - pp (k + 1) (t - ∑ j ∈ S, α' j - a)) /
            (((k : ℝ) + 1) * a) := by
        intro S
        rw [← integral_pp_slice k _ a ha]
        congr 1; ext u; congr 1; ring
      simp_rw [hsl]
      rw [sum_finset_fin_succ]
      rw [Fin.prod_univ_castSucc, Nat.factorial_succ,
        show (∏ i, α (Fin.castSucc i)) * α (Fin.last k) = (∏ j, α' j) * a from rfl]
      push_cast
      rw [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      have hc1 : (S.map Fin.castSuccEmb).card = S.card := Finset.card_map _
      have hc2 : (insert (Fin.last k) (S.map Fin.castSuccEmb)).card = S.card + 1 := by
        rw [Finset.card_insert_of_notMem (by simp [Finset.mem_map]), hc1]
      have hs1 : ∑ j ∈ S.map Fin.castSuccEmb, α j = ∑ j ∈ S, α' j := by
        rw [Finset.sum_map]; rfl
      have hs2 : ∑ j ∈ insert (Fin.last k) (S.map Fin.castSuccEmb), α j =
          a + ∑ j ∈ S, α' j := by
        rw [Finset.sum_insert (by simp [Finset.mem_map]), hs1]
      rw [hc2, hc1, hs1, hs2, pow_succ]
      have e1 : t - (a + ∑ j ∈ S, α' j) = t - ∑ j ∈ S, α' j - a := by ring
      rw [e1]
      field_simp
      ring
    · intro S _
      apply IntervalIntegrable.const_mul
      exact (pp_mono k).comp_antitone (fun u v huv => by nlinarith) |>.intervalIntegrable


/-! ## Part C: Lipschitz bound, forward differences -/

lemma vol_lip {k : ℕ} (α : Fin (k + 1) → ℝ) (ha : 0 < α (Fin.last k)) (t h : ℝ)
    (hh : 0 ≤ h) : vol α (t + h) - vol α t ≤ h / α (Fin.last k) := by
  rw [vol_succ α ha.le, vol_succ α ha.le]
  set a := α (Fin.last k)
  set V := vol (fun j => α (Fin.castSucc j))
  have hV : Monotone V := vol_mono _
  have hii : ∀ c d : ℝ, IntervalIntegrable V volume c d := fun c d => hV.intervalIntegrable
  rw [intervalIntegral.integral_comp_sub_mul (f := V) ha.ne',
    intervalIntegral.integral_comp_sub_mul (f := V) ha.ne']
  simp only [mul_one, mul_zero, sub_zero, smul_eq_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii (t + h - a) t) (hii t (t + h)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii (t - a) (t + h - a))
      (hii (t + h - a) t)]
  have h1 : ∫ x in t..t + h, V x ≤ h := by
    have := intervalIntegral.integral_mono_on (by linarith : t ≤ t + h) (hii t (t + h))
      (intervalIntegrable_const (c := (1:ℝ))) (fun u _ => vol_le_one _ u)
    simpa using this
  have h2 : 0 ≤ ∫ x in t - a..t + h - a, V x :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => vol_nonneg _ u)
  rw [div_eq_inv_mul]
  have hai : 0 < a⁻¹ := inv_pos.mpr ha
  nlinarith

lemma fd_pow (k j : ℕ) (hj : j ≤ k) (b s : ℝ) :
    ∑ i ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * (b + i * s) ^ j =
      if j = k then (k.factorial : ℝ) * s ^ k else 0 := by
  have hf : (fun r : ℝ => (b + r * s) ^ j) = ∑ m ∈ Finset.range (j + 1),
      ((s ^ m * b ^ (j - m) * (j.choose m : ℝ))) • (fun r : ℝ => r ^ m) := by
    funext r
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have h1 : ∑ i ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * (b + i * s) ^ j
      = (fwdDiff (1:ℝ))^[k] (fun r : ℝ => (b + r * s) ^ j) 0 := by
    rw [fwdDiff_iter_eq_sum_shift]
    apply Finset.sum_congr rfl
    intro i _
    simp only [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul]
    push_cast
    ring
  rw [h1, hf, fwdDiff_iter_finsetSum, Finset.sum_apply]
  rcases lt_or_eq_of_le hj with hlt | heq
  · rw [if_neg hlt.ne]
    apply Finset.sum_eq_zero
    intro m hm
    have hm' : m < k := by have := Finset.mem_range.1 hm; omega
    rw [fwdDiff_iter_const_smul, fwdDiff_iter_pow_eq_zero_of_lt hm']
    simp
  · subst heq
    rw [if_pos rfl, Finset.sum_range_succ, Finset.sum_eq_zero]
    · rw [fwdDiff_iter_const_smul, fwdDiff_iter_eq_factorial]
      simp
      ring
    · intro m hm
      rw [fwdDiff_iter_const_smul, fwdDiff_iter_pow_eq_zero_of_lt (Finset.mem_range.1 hm)]
      simp

lemma pp_feas (k σ β : ℕ) (γ : ℝ) (h1 : (β : ℝ) ≤ γ) (h2 : γ < β + 1) :
    pp k (γ - σ) = if σ ≤ β then (γ - σ) ^ k else 0 := by
  unfold pp
  by_cases hs : σ ≤ β
  · have : (σ : ℝ) ≤ β := by exact_mod_cast hs
    rw [if_pos (by linarith), if_pos hs]
  · have : (β : ℝ) + 1 ≤ σ := by exact_mod_cast (show β + 1 ≤ σ by omega)
    rw [if_neg (by linarith), if_neg hs]

lemma parityD_eq {k : ℕ} (α : Fin k → ℕ) (β : ℕ) :
    (parityD α β : ℝ) = ∑ S : Finset (Fin k),
      if (∑ j ∈ S, α j) ≤ β then (-1 : ℝ) ^ S.card else 0 := by
  unfold parityD
  rw [← Finset.sum_filter, Finset.powerset_univ]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun S : Finset (Fin k) => Even S.card)]
  rw [Finset.filter_filter, Finset.filter_filter]
  have e1 : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin k) =>
      (∑ j ∈ S, α j) ≤ β ∧ Even S.card), (-1 : ℝ) ^ S.card = 1 := by
    intro S hS
    exact (Finset.mem_filter.1 hS).2.2.neg_one_pow
  have e2 : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin k) =>
      (∑ j ∈ S, α j) ≤ β ∧ ¬ Even S.card), (-1 : ℝ) ^ S.card = -1 := by
    intro S hS
    exact (Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hS).2.2).neg_one_pow
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have : (Finset.univ.filter (fun S : Finset (Fin k) => (∑ j ∈ S, α j) ≤ β ∧ ¬ Even S.card)) =
      Finset.univ.filter (fun S : Finset (Fin k) => (∑ j ∈ S, α j) ≤ β ∧ Odd S.card) := by
    ext S; simp [Nat.not_even_iff_odd]
  rw [this]
  push_cast
  ring


/-! ## Part D: assembly -/

lemma vol_lip' {k : ℕ} (hk : 0 < k) (α : Fin k → ℝ) (ha : 0 < lastWeight hk α) (t h : ℝ)
    (hh : 0 ≤ h) : vol α (t + h) - vol α t ≤ h / lastWeight hk α := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hl : lastWeight hk α = α (Fin.last n) := by
    unfold lastWeight; congr 1
  rw [hl] at ha ⊢
  exact vol_lip α ha t h hh

lemma final_arith (A a Sα kf K R sd : ℝ) (k : ℕ) (hA : 0 < A) (ha : 1 ≤ a) (hS : 0 ≤ Sα)
    (hkf : 1 ≤ kf) (hK : 2 ≤ K)
    (hR : R = a / (2 * kf * (1 + a) * (Sα + 2) ^ k * K ^ (k + 1) * A))
    (hsd : sd < R) :
    A * 2 ^ k * (1 + 2 / a) * K ^ k * sd < 1 / 2 := by
  have ha0 : 0 < a := by linarith
  have hK0 : 0 < K := by linarith
  have hP : 0 < A * 2 ^ k * (1 + 2 / a) * K ^ k := by positivity
  have hDen : 0 < 2 * kf * (1 + a) * (Sα + 2) ^ k * K ^ (k + 1) * A := by positivity
  calc A * 2 ^ k * (1 + 2 / a) * K ^ k * sd < A * 2 ^ k * (1 + 2 / a) * K ^ k * R :=
        mul_lt_mul_of_pos_left hsd hP
    _ ≤ 1 / 2 := by
      rw [hR, mul_div_assoc', div_le_iff₀ hDen]
      have hrw : A * 2 ^ k * (1 + 2 / a) * K ^ k * a = A * 2 ^ k * K ^ k * (a + 2) := by
        field_simp
      rw [hrw]
      have h2k : (2:ℝ) ^ k ≤ (Sα + 2) ^ k := pow_le_pow_left₀ (by norm_num) (by linarith) k
      have e1 : A * 2 ^ k * K ^ k * (a + 2) ≤ A * (Sα + 2) ^ k * K ^ k * (2 * (1 + a)) := by
        have hKk : 0 ≤ K ^ k := by positivity
        have : A * 2 ^ k * K ^ k ≤ A * (Sα + 2) ^ k * K ^ k := by
          apply mul_le_mul_of_nonneg_right _ hKk
          exact mul_le_mul_of_nonneg_left h2k hA.le
        have h3 : a + 2 ≤ 2 * (1 + a) := by linarith
        have h4 : 0 ≤ A * (Sα + 2) ^ k * K ^ k := by positivity
        calc A * 2 ^ k * K ^ k * (a + 2) ≤ A * (Sα + 2) ^ k * K ^ k * (a + 2) :=
              mul_le_mul_of_nonneg_right this (by linarith)
          _ ≤ A * (Sα + 2) ^ k * K ^ k * (2 * (1 + a)) := mul_le_mul_of_nonneg_left h3 h4
      have hX : 0 ≤ A * (Sα + 2) ^ k * K ^ k * (1 + a) := by positivity
      have h2 : (2:ℝ) ≤ kf * K := by nlinarith
      calc A * 2 ^ k * K ^ k * (a + 2) ≤ A * (Sα + 2) ^ k * K ^ k * (2 * (1 + a)) := e1
        _ = (A * (Sα + 2) ^ k * K ^ k * (1 + a)) * 2 := by ring
        _ ≤ (A * (Sα + 2) ^ k * K ^ k * (1 + a)) * (kf * K) := mul_le_mul_of_nonneg_left h2 hX
        _ = 1 / 2 * (2 * kf * (1 + a) * (Sα + 2) ^ k * K ^ (k + 1) * A) := by ring

lemma main {k : ℕ} (hk : 0 < k) (α : Fin k → ℕ) (hα : ∀ j, 1 ≤ α j) (β : ℕ)
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ < delta7 (fun j => (α j : ℝ)) (lastWeight hk (fun j => (α j : ℝ))))
    (Qδ : ℝ → ℝ)
    (hQ : ∀ t : ℝ, 0 ≤ t → |Qδ t - expRecourse (fun j => (α j : ℝ)) t| ≤ δ)
    (x : Fin (k + 1) → ℝ)
    (hx : (vandermondeF k (β : ℝ)).mulVec x = ((k.factorial : ℝ) * ∏ j, (α j : ℝ)) •
          (fun i => (Qδ (budget k (β : ℝ) i + 2 * Real.sqrt δ) - Qδ (budget k (β : ℝ) i)) /
              (2 * Real.sqrt δ) + 1)) :
    |x 0 - (parityD α β : ℝ)| < (1 / 2 : ℝ) := by
  set αR : Fin k → ℝ := fun j => (α j : ℝ) with hαR
  have hαpos : ∀ j, 0 < αR j := fun j => by
    have := hα j
    simp only [αR]
    exact_mod_cast (show 0 < α j by omega)
  set a := lastWeight hk αR with ha_def
  have ha1 : 1 ≤ a := by
    simp only [a, lastWeight, αR]
    exact_mod_cast hα _
  set A := ∏ j, αR j with hA_def
  have hA : 0 < A := Finset.prod_pos (fun j _ => hαpos j)
  have hkf : (1:ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hK : (0:ℝ) < (k : ℝ) + 1 := by positivity
  set s : ℝ := 1 / ((k : ℝ) + 1) with hs_def
  have hs0 : 0 < s := by positivity
  set sd := Real.sqrt δ with hsd_def
  have hsd : 0 < sd := Real.sqrt_pos.mpr hδ0
  have hh : 0 < 2 * sd := by positivity
  have hγ : ∀ i : Fin (k + 1), budget k (β : ℝ) i = (β : ℝ) + ((i : ℕ) : ℝ) * s := by
    intro i; simp only [budget, s]; ring
  have hγlo : ∀ i : Fin (k + 1), (β : ℝ) ≤ budget k (β : ℝ) i := by
    intro i; rw [hγ]; have : (0:ℝ) ≤ ((i : ℕ) : ℝ) * s := by positivity
    linarith
  have hγhi : ∀ i : Fin (k + 1), budget k (β : ℝ) i < β + 1 := by
    intro i; rw [hγ]
    have hi : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
    have : ((i : ℕ) : ℝ) * s < 1 := by
      rw [hs_def, mul_one_div, div_lt_one hK]; linarith
    linarith
  have hγ0 : ∀ i : Fin (k + 1), 0 ≤ budget k (β : ℝ) i := fun i =>
    le_trans (Nat.cast_nonneg β) (hγlo i)
  -- F1
  have F1 : ∀ c : Fin (k + 1), ∑ i : Fin (k + 1), (-1 : ℝ) ^ (k - (i : ℕ)) *
      (k.choose i : ℝ) * budget k (β : ℝ) i ^ (k - (c : ℕ)) =
      if (c : ℕ) = 0 then (k.factorial : ℝ) * s ^ k else 0 := by
    intro c
    have h1 := fd_pow k (k - c) (Nat.sub_le _ _) β s
    rw [← Fin.sum_univ_eq_sum_range] at h1
    simp_rw [hγ]
    rw [h1]
    have : k - (c : ℕ) = k ↔ (c : ℕ) = 0 := by have := c.isLt; omega
    simp only [this]
  -- F2
  have F2 : ∑ i : Fin (k + 1), (-1 : ℝ) ^ (k - (i : ℕ)) * (k.choose i : ℝ) *
      (vandermondeF k (β : ℝ)).mulVec x i = x 0 * ((k.factorial : ℝ) * s ^ k) := by
    simp only [Matrix.mulVec, dotProduct, vandermondeF]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hc : ∀ c : Fin (k + 1), ∑ i : Fin (k + 1), (-1 : ℝ) ^ (k - (i : ℕ)) *
        (k.choose i : ℝ) * (budget k (β : ℝ) i ^ (k - (c : ℕ)) * x c) =
        x c * (if (c : ℕ) = 0 then (k.factorial : ℝ) * s ^ k else 0) := by
      intro c
      rw [← F1 c, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [Finset.sum_congr rfl (fun c _ => hc c)]
    rw [Finset.sum_eq_single (0 : Fin (k + 1))]
    · simp
    · intro c _ hc0
      have : (c : ℕ) ≠ 0 := fun h => hc0 (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- F3
  have F3 : ∑ i : Fin (k + 1), (-1 : ℝ) ^ (k - (i : ℕ)) * (k.choose i : ℝ) *
      ((k.factorial : ℝ) * A * vol αR (budget k (β : ℝ) i)) =
      (parityD α β : ℝ) * ((k.factorial : ℝ) * s ^ k) := by
    have hv : ∀ i : Fin (k + 1), (k.factorial : ℝ) * A * vol αR (budget k (β : ℝ) i) =
        ∑ S : Finset (Fin k), if (∑ j ∈ S, α j) ≤ β then (-1 : ℝ) ^ S.card *
          (((β : ℝ) - ∑ j ∈ S, (α j : ℝ)) + ((i : ℕ) : ℝ) * s) ^ k else 0 := by
      intro i
      rw [hA_def, lemma1 k αR hαpos]
      apply Finset.sum_congr rfl
      intro S _
      have hσ : ∑ j ∈ S, αR j = ((∑ j ∈ S, α j : ℕ) : ℝ) := by
        simp only [αR]; push_cast; rfl
      rw [hσ, pp_feas k _ β _ (hγlo i) (hγhi i)]
      split_ifs
      · rw [hγ]; push_cast; ring_nf
      · simp
    simp_rw [hv, Finset.mul_sum]
    rw [Finset.sum_comm, parityD_eq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hS
    · have h1 := fd_pow k k le_rfl ((β : ℝ) - ∑ j ∈ S, (α j : ℝ)) s
      rw [if_pos rfl, ← Fin.sum_univ_eq_sum_range] at h1
      calc ∑ i : Fin (k + 1), (-1 : ℝ) ^ (k - (i : ℕ)) * (k.choose i : ℝ) *
            ((-1 : ℝ) ^ S.card * (((β : ℝ) - ∑ j ∈ S, (α j : ℝ)) + ((i : ℕ) : ℝ) * s) ^ k)
          = (-1 : ℝ) ^ S.card * ∑ i : Fin (k + 1), (-1 : ℝ) ^ (k - (i : ℕ)) *
            (k.choose i : ℝ) * (((β : ℝ) - ∑ j ∈ S, (α j : ℝ)) + ((i : ℕ) : ℝ) * s) ^ k := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        _ = _ := by rw [h1]
    · simp
  -- F5
  have F5 : ∀ i : Fin (k + 1), |(Qδ (budget k (β : ℝ) i + 2 * sd) - Qδ (budget k (β : ℝ) i)) /
      (2 * sd) + 1 - vol αR (budget k (β : ℝ) i)| ≤ sd * (1 + 2 / a) := by
    intro i
    set g := budget k (β : ℝ) i
    have hsw := fd_sandwich αR (fun j => (hαpos j).le) g (2 * sd) hh
    have hl := vol_lip' hk αR (by linarith) g (2 * sd) hh.le
    have q1 := hQ (g + 2 * sd) (by linarith [hγ0 i])
    have q2 := hQ g (hγ0 i)
    have hδsd : δ = sd ^ 2 := (Real.sq_sqrt hδ0.le).symm
    have hq : |(Qδ (g + 2 * sd) - Qδ g) / (2 * sd) -
        (expRecourse αR (g + 2 * sd) - expRecourse αR g) / (2 * sd)| ≤ sd := by
      rw [← sub_div, abs_div, abs_of_pos hh, div_le_iff₀ hh]
      have : (Qδ (g + 2 * sd) - Qδ g) - (expRecourse αR (g + 2 * sd) - expRecourse αR g) =
          (Qδ (g + 2 * sd) - expRecourse αR (g + 2 * sd)) - (Qδ g - expRecourse αR g) := by ring
      rw [this]
      calc _ ≤ |Qδ (g + 2 * sd) - expRecourse αR (g + 2 * sd)| + |Qδ g - expRecourse αR g| :=
            abs_sub _ _
        _ ≤ δ + δ := add_le_add q1 q2
        _ = sd * (2 * sd) := by rw [hδsd]; ring
    rw [abs_le] at hq ⊢
    have h2a : 2 * sd / a = sd * (2 / a) := by ring
    constructor <;> nlinarith [hsw.1, hsw.2, hq.1, hq.2, hl, h2a]
  -- assembly
  have hxv : ∀ i, (vandermondeF k (β : ℝ)).mulVec x i = (k.factorial : ℝ) * A *
      ((Qδ (budget k (β : ℝ) i + 2 * sd) - Qδ (budget k (β : ℝ) i)) / (2 * sd) + 1) := by
    intro i; rw [hx]; rfl
  have key : (x 0 - (parityD α β : ℝ)) * ((k.factorial : ℝ) * s ^ k) =
      ∑ i : Fin (k + 1), (-1 : ℝ) ^ (k - (i : ℕ)) * (k.choose i : ℝ) *
        ((k.factorial : ℝ) * A * ((Qδ (budget k (β : ℝ) i + 2 * sd) - Qδ (budget k (β : ℝ) i)) /
          (2 * sd) + 1 - vol αR (budget k (β : ℝ) i))) := by
    rw [sub_mul, ← F2, ← F3, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hxv]; ring
  have hC : 0 < (k.factorial : ℝ) * s ^ k := by positivity
  have hsum2 : ∑ i : Fin (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (k.choose i : ℝ))]
    exact_mod_cast Nat.sum_range_choose k
  have bound : |x 0 - (parityD α β : ℝ)| * ((k.factorial : ℝ) * s ^ k) ≤
      (k.factorial : ℝ) * A * 2 ^ k * (sd * (1 + 2 / a)) := by
    rw [← abs_of_pos hC, ← abs_mul, key]
    calc _ ≤ ∑ i : Fin (k + 1), |(-1 : ℝ) ^ (k - (i : ℕ)) * (k.choose i : ℝ) *
          ((k.factorial : ℝ) * A * ((Qδ (budget k (β : ℝ) i + 2 * sd) -
            Qδ (budget k (β : ℝ) i)) / (2 * sd) + 1 - vol αR (budget k (β : ℝ) i)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (k + 1), (k.choose i : ℝ) * ((k.factorial : ℝ) * A * (sd * (1 + 2 / a))) := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            Nat.abs_cast]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [abs_of_pos (by positivity : (0:ℝ) < (k.factorial : ℝ) * A)]
          exact mul_le_mul_of_nonneg_left (F5 i) (by positivity)
      _ = _ := by rw [← Finset.sum_mul, hsum2]; ring
  have hsdR : sd < a / (2 * (k.factorial : ℝ) * (1 + a) * ((∑ j, |αR j|) + 2) ^ k *
      ((k : ℝ) + 1) ^ (k + 1) * A) := by
    have hR0 : 0 < a / (2 * (k.factorial : ℝ) * (1 + a) * ((∑ j, |αR j|) + 2) ^ k *
        ((k : ℝ) + 1) ^ (k + 1) * A) := by
      have : 0 ≤ ∑ j, |αR j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      have : 0 < a := by linarith
      positivity
    have h7 : δ < (a / (2 * (k.factorial : ℝ) * (1 + a) * ((∑ j, |αR j|) + 2) ^ k *
        ((k : ℝ) + 1) ^ (k + 1) * A)) ^ 2 := by
      have := hδ
      simp only [delta7] at this
      push_cast at this
      exact this
    rw [hsd_def]
    calc Real.sqrt δ < Real.sqrt ((a / (2 * (k.factorial : ℝ) * (1 + a) *
          ((∑ j, |αR j|) + 2) ^ k * ((k : ℝ) + 1) ^ (k + 1) * A)) ^ 2) :=
          Real.sqrt_lt_sqrt hδ0.le h7
      _ = _ := Real.sqrt_sq hR0.le
  have hfin := final_arith A a (∑ j, |αR j|) (k.factorial : ℝ) ((k : ℝ) + 1) _ sd k hA ha1
    (Finset.sum_nonneg (fun j _ => abs_nonneg _)) hkf
    (by have : (1:ℝ) ≤ k := by exact_mod_cast hk
        linarith) rfl hsdR
  -- conclude
  have hsK : s ^ k * ((k : ℝ) + 1) ^ k = 1 := by
    rw [← mul_pow, hs_def, one_div, inv_mul_cancel₀ hK.ne', one_pow]
  have hb2 : |x 0 - (parityD α β : ℝ)| * ((k.factorial : ℝ) * s ^ k) ≤
      ((k.factorial : ℝ) * s ^ k) *
        (A * 2 ^ k * (1 + 2 / a) * ((k : ℝ) + 1) ^ k * sd) := by
    calc _ ≤ (k.factorial : ℝ) * A * 2 ^ k * (sd * (1 + 2 / a)) := bound
      _ = (k.factorial : ℝ) * A * 2 ^ k * (sd * (1 + 2 / a)) * (s ^ k * ((k : ℝ) + 1) ^ k) := by
          rw [hsK, mul_one]
      _ = _ := by ring
  rw [mul_comm] at hb2
  have := le_of_mul_le_mul_left hb2 hC
  linarith

end FR7568

open SPHardness.FixedRecourse in
theorem solution {k : ℕ} (hk : 0 < k) (α : Fin k → ℕ)
    (hα : ∀ j, 1 ≤ α j) (β : ℕ) (hβ : β ≤ ∑ j, α j)
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ < delta7 (fun j => (α j : ℝ))
      (lastWeight hk (fun j => (α j : ℝ))))
    (Qδ : ℝ → ℝ)
    (hQ : ∀ t : ℝ, 0 ≤ t →
      |Qδ t - expRecourse (fun j => (α j : ℝ)) t| ≤ δ) :
    ∀ x : Fin (k + 1) → ℝ,
      (vandermondeF k (β : ℝ)).mulVec x =
        ((k.factorial : ℝ) * ∏ j, (α j : ℝ)) •
          (fun i =>
            (Qδ (budget k (β : ℝ) i + 2 * Real.sqrt δ) -
                Qδ (budget k (β : ℝ) i)) /
              (2 * Real.sqrt δ) + 1) →
        |x 0 - (parityD α β : ℝ)| < (1 / 2 : ℝ) := by
  intro x hx
  exact FR7568.main hk α hα β δ hδ0 hδ Qδ hQ x hx
