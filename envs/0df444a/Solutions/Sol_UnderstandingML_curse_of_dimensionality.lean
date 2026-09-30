-- Prove2me | solution 1 for UnderstandingML.curse_of_dimensionality
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T07:32:28.226538+00:00
-- url     : https://prove2.me/submissions/7dca9d55-c1bf-4885-8d8c-a103abc1351a

import Definitions.Def_UnderstandingML_NearestNeighbor
import Mathlib

open MeasureTheory

namespace CurseAux

open Classical in
/-- The No-Free-Lunch counting core. -/
lemma nfl_count {G : Type*} [Fintype G] [DecidableEq G] (m : ℕ)
    (hm : 2 * m ≤ Fintype.card G) (A : (Fin m → G × Bool) → G → Bool) :
    ∃ f : G → Bool, ((Fintype.card G : ℝ) ^ m * Fintype.card G / 4) ≤
      ∑ gs : Fin m → G, ∑ g : G,
        (if A (fun i ↦ (gs i, f (gs i))) g = f g then (0 : ℝ) else 1) := by
  set N := Fintype.card G
  -- the error indicator
  let err : (G → Bool) → (Fin m → G) → G → ℝ := fun f gs g ↦
    if A (fun i ↦ (gs i, f (gs i))) g = f g then (0 : ℝ) else 1
  have herr_nn : ∀ f gs g, 0 ≤ err f gs g := by intro f gs g; simp only [err]; split_ifs <;> norm_num
  -- for an unseen point, the average over labelings is 1/2
  have hflip : ∀ gs : Fin m → G, ∀ g, g ∉ Set.range gs →
      ∑ f : G → Bool, err f gs g = 2 ^ N / 2 := by
    intro gs g hg
    let σ : (G → Bool) ≃ (G → Bool) :=
      { toFun := fun f ↦ Function.update f g (!f g)
        invFun := fun f ↦ Function.update f g (!f g)
        left_inv := by intro f; ext x; by_cases hx : x = g <;> simp [Function.update, hx]
        right_inv := by intro f; ext x; by_cases hx : x = g <;> simp [Function.update, hx] }
    have hsample : ∀ f, (fun i ↦ (gs i, (σ f) (gs i))) = (fun i ↦ (gs i, f (gs i))) := by
      intro f; funext i
      have : gs i ≠ g := fun h ↦ hg ⟨i, h⟩
      simp [σ, Function.update, this]
    have hpair : ∀ f, err f gs g + err (σ f) gs g = 1 := by
      intro f
      simp only [err, hsample]
      simp only [σ, Equiv.coe_fn_mk, Function.update_self]
      cases f g <;> cases A (fun i ↦ (gs i, f (gs i))) g <;> simp
    have hsum : ∑ f, err (σ f) gs g = ∑ f, err f gs g := Equiv.sum_comp σ (fun f ↦ err f gs g)
    have htot : ∑ f : G → Bool, (err f gs g + err (σ f) gs g) = 2 ^ N := by
      simp [hpair, N]
    rw [Finset.sum_add_distrib, hsum] at htot
    linarith
  -- lower bound on the number of unseen points
  have hunseen : ∀ gs : Fin m → G,
      (N : ℝ) / 2 ≤ ((Finset.univ.filter (fun g ↦ g ∉ Set.range gs)).card : ℝ) := by
    intro gs
    have h1 : (Finset.univ.filter (fun g ↦ g ∈ Set.range gs)).card ≤ m := by
      calc (Finset.univ.filter (fun g ↦ g ∈ Set.range gs)).card
          ≤ (Finset.univ.image gs).card := by
            apply Finset.card_le_card; intro x; simp [eq_comm]
        _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
        _ = m := by simp
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun g ↦ g ∈ Set.range gs)
    simp only [Finset.card_univ] at h2
    have : (N : ℝ) ≤ m + ((Finset.univ.filter (fun g ↦ g ∉ Set.range gs)).card : ℝ) := by
      exact_mod_cast (by omega : N ≤ m + (Finset.univ.filter (fun g ↦ g ∉ Set.range gs)).card)
    have hm' : (2 * m : ℝ) ≤ N := by exact_mod_cast hm
    linarith
  -- total over all labelings
  have htotal : ∑ f : G → Bool, ((N : ℝ) ^ m * N / 4) ≤
      ∑ f : G → Bool, ∑ gs : Fin m → G, ∑ g : G, err f gs g := by
    rw [Finset.sum_comm]
    have : ∀ gs : Fin m → G, (2 : ℝ) ^ N * (N / 4) ≤ ∑ f : G → Bool, ∑ g : G, err f gs g := by
      intro gs
      rw [Finset.sum_comm]
      calc (2 : ℝ) ^ N * (N / 4) ≤ (2 ^ N / 2) *
            ((Finset.univ.filter (fun g ↦ g ∉ Set.range gs)).card : ℝ) := by
            have := hunseen gs
            have h2 : (0 : ℝ) ≤ 2 ^ N / 2 := by positivity
            nlinarith
        _ = ∑ g ∈ Finset.univ.filter (fun g ↦ g ∉ Set.range gs), ∑ f : G → Bool, err f gs g := by
            rw [Finset.sum_congr rfl (fun g hg ↦ hflip gs g (Finset.mem_filter.1 hg).2)]
            simp [mul_comm]
        _ ≤ ∑ g, ∑ f : G → Bool, err f gs g := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro g _ _; exact Finset.sum_nonneg (fun f _ ↦ herr_nn f gs g)
    calc ∑ f : G → Bool, ((N : ℝ) ^ m * N / 4) = ∑ gs : Fin m → G, (2 : ℝ) ^ N * (N / 4) := by
          simp [Finset.card_univ, Fintype.card_bool, N]; ring
      _ ≤ _ := Finset.sum_le_sum (fun gs _ ↦ this gs)
  obtain ⟨f, -, hf⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty htotal
  exact ⟨f, hf⟩


open UnderstandingML

lemma bernoulliLaw_apply (p : ℝ) (A : Set Bool) :
    bernoulliLaw p A = ENNReal.ofReal p * A.indicator 1 true +
      ENNReal.ofReal (1 - p) * A.indicator 1 false := by
  simp [bernoulliLaw, Measure.dirac_apply' _ (MeasurableSet.of_discrete : MeasurableSet A)]

lemma kernel_measurable {X : Type*} [MeasurableSpace X] {η : X → ℝ} (hη : Measurable η) :
    Measurable (fun x ↦ (bernoulliLaw (η x)).map (fun y ↦ (x, y))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have : (fun x ↦ ((bernoulliLaw (η x)).map (fun y ↦ (x, y))) s) = fun x ↦
      ENNReal.ofReal (η x) * {x | (x, true) ∈ s}.indicator 1 x +
      ENNReal.ofReal (1 - η x) * {x | (x, false) ∈ s}.indicator 1 x := by
    funext x
    rw [Measure.map_apply measurable_prodMk_left hs, bernoulliLaw_apply]
    simp [Set.indicator]; rfl
  rw [this]
  refine Measurable.add ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp hη).mul
      (measurable_one.indicator (measurable_prodMk_right hs))
  · exact (ENNReal.measurable_ofReal.comp (measurable_const.sub hη)).mul
      (measurable_one.indicator (measurable_prodMk_right hs))

variable {d c : ℕ}

/-- grid point with coordinates `g j / c`. -/
noncomputable def gridPt (c : ℕ) (g : Fin d → Fin (c + 1)) : cube d :=
  ⟨WithLp.toLp 2 (fun j ↦ ((g j : ℕ) : ℝ) / c), by
    intro j
    have h1 : ((g j : ℕ) : ℝ) ≤ c := by exact_mod_cast Nat.lt_succ_iff.mp (g j).isLt
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc; simp
    · have hc' : (0 : ℝ) < c := by exact_mod_cast hc
      simp only [Set.mem_Icc]
      exact ⟨by positivity, by rw [div_le_one hc']; exact h1⟩⟩

lemma gridPt_dist (hc : 2 ≤ c) {g g' : Fin d → Fin (c + 1)} (hne : g ≠ g') :
    1 / (c : ℝ) ≤ dist (gridPt c g) (gridPt c g') := by
  obtain ⟨j, hj⟩ : ∃ j, g j ≠ g' j := by
    by_contra h; push Not at h; exact hne (funext h)
  have hc' : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  rw [Subtype.dist_eq]
  refine le_trans ?_ (PiLp.dist_apply_le _ _ j)
  simp only [gridPt, Real.dist_eq]
  have hint : (1 : ℝ) ≤ |((g j : ℕ) : ℝ) - ((g' j : ℕ) : ℝ)| := by
    have : (g j : ℕ) ≠ (g' j : ℕ) := fun h ↦ hj (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne this with h | h
    · have : ((g j : ℕ) : ℝ) + 1 ≤ ((g' j : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_sub_comm]; linarith [le_abs_self (((g' j : ℕ) : ℝ) - ((g j : ℕ) : ℝ))]
    · have : ((g' j : ℕ) : ℝ) + 1 ≤ ((g j : ℕ) : ℝ) := by exact_mod_cast h
      linarith [le_abs_self (((g j : ℕ) : ℝ) - ((g' j : ℕ) : ℝ))]
  rw [← sub_div, abs_div, abs_of_pos hc']
  exact div_le_div_of_nonneg_right hint hc'.le

/-- The Lipschitz extension of the labeling `f` off the grid. -/
noncomputable def gridEta (c : ℕ) (f : (Fin d → Fin (c + 1)) → Bool) (x : cube d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun g ↦ if f g then max 0 (1 - c * dist x (gridPt c g)) else 0)

lemma gridEta_lipschitz (f : (Fin d → Fin (c + 1)) → Bool) :
    LipschitzWith c (gridEta c f) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  obtain ⟨g0, -, hg0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin d → Fin (c + 1)))
    (fun g ↦ if f g then max 0 (1 - c * dist x (gridPt c g)) else 0)
  have hle : (if f g0 then max 0 (1 - c * dist y (gridPt c g0)) else 0) ≤ gridEta c f y :=
    Finset.le_sup' (fun g ↦ if f g then max 0 (1 - c * dist y (gridPt c g)) else 0)
      (Finset.mem_univ g0)
  unfold gridEta; rw [hg0]
  have htri : dist y (gridPt c g0) ≤ dist x y + dist x (gridPt c g0) := by
    have := dist_triangle y x (gridPt c g0); rw [dist_comm y x] at this; linarith
  have hc0 : (0 : ℝ) ≤ c := by positivity
  simp only [NNReal.coe_natCast]
  split_ifs at hle ⊢ with hf
  · have : 1 - c * dist x (gridPt c g0) ≤ (1 - c * dist y (gridPt c g0)) + c * dist x y := by
      nlinarith
    have hmax : max 0 (1 - c * dist x (gridPt c g0)) ≤
        max 0 (1 - c * dist y (gridPt c g0)) + c * dist x y := by
      apply max_le
      · have := le_max_left 0 (1 - c * dist y (gridPt c g0)); positivity
      · have := le_max_right 0 (1 - c * dist y (gridPt c g0)); linarith
    unfold gridEta at hle; linarith
  · have := dist_nonneg (x := x) (y := y)
    unfold gridEta at hle
    have h0 : (0 : ℝ) ≤ gridEta c f y := le_trans (le_refl 0) hle
    unfold gridEta at h0; nlinarith

lemma gridEta_mem (f : (Fin d → Fin (c + 1)) → Bool) (x : cube d) :
    gridEta c f x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · refine le_trans ?_ (Finset.le_sup' (fun g ↦ if f g then max 0 (1 - c * dist x (gridPt c g))
      else 0) (Finset.mem_univ (fun _ ↦ 0)))
    split_ifs <;> simp
  · apply Finset.sup'_le
    intro g _
    split_ifs
    · apply max_le (by norm_num)
      have : 0 ≤ (c : ℝ) * dist x (gridPt c g) := by positivity
      linarith
    · norm_num

lemma gridEta_grid (hc : 2 ≤ c) (f : (Fin d → Fin (c + 1)) → Bool) (g : Fin d → Fin (c + 1)) :
    gridEta c f (gridPt c g) = if f g then 1 else 0 := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  cases hfg : f g
  · simp only [Bool.false_eq_true, if_false]
    apply le_antisymm
    · apply Finset.sup'_le
      intro g' _
      split_ifs with hf'
      · apply max_le (le_refl 0)
        have hne : g' ≠ g := by rintro rfl; rw [hfg] at hf'; exact absurd hf' (by simp)
        have := gridPt_dist hc hne.symm
        have : 1 ≤ (c : ℝ) * dist (gridPt c g) (gridPt c g') := by
          rw [div_le_iff₀ hc'] at this; linarith
        linarith
      · exact le_refl 0
    · exact (gridEta_mem f _).1
  · simp only [if_true]
    apply le_antisymm (gridEta_mem f _).2
    refine le_trans ?_ (Finset.le_sup' (fun g' ↦ if f g' then max 0
      (1 - c * dist (gridPt c g) (gridPt c g')) else 0) (Finset.mem_univ g))
    simp [hfg]

end CurseAux

namespace CurseAux

open UnderstandingML

variable {d c : ℕ}

local notation "G" => (Fin d → Fin (c + 1))

lemma gridPt_injective (hc : 2 ≤ c) : Function.Injective (gridPt (d := d) c) := by
  intro g g' h
  by_contra hne
  have := gridPt_dist hc hne
  rw [h, dist_self] at this
  have hc' : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have : 0 < 1 / (c : ℝ) := by positivity
  linarith

/-- uniform law on the grid -/
noncomputable def U (d c : ℕ) : Measure (Fin d → Fin (c + 1)) :=
  (PMF.uniformOfFintype (Fin d → Fin (c + 1))).toMeasure

instance : IsProbabilityMeasure (U d c) := by unfold U; infer_instance

lemma U_real_singleton (g : G) : (U d c).real {g} = 1 / (Fintype.card G : ℝ) := by
  rw [measureReal_def, U, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton g),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

lemma measurableEmbedding_of_finite {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] {f : α → β}
    (hf : Function.Injective f) : MeasurableEmbedding f where
  injective := hf
  measurable := measurable_of_countable f
  measurableSet_image' := fun s _ ↦ (s.toFinite.image f).measurableSet

open Classical in
lemma condLaw_grid (hc : 2 ≤ c) (f : G → Bool) :
    condLaw ((U d c).map (gridPt c)) (gridEta c f) = (U d c).map (fun g ↦ (gridPt c g, f g)) := by
  have hηm : Measurable (gridEta c f) := (gridEta_lipschitz f).continuous.measurable
  ext s hs
  rw [condLaw, Measure.bind_apply hs (kernel_measurable hηm).aemeasurable,
    lintegral_map (show Measurable (fun a ↦ ((bernoulliLaw (gridEta c f a)).map
      (fun y ↦ (a, y))) s) from (Measure.measurable_coe hs).comp (kernel_measurable hηm))
      (measurable_of_countable _),
    Measure.map_apply (measurable_of_countable _) hs, ← lintegral_indicator_one
      (MeasurableSet.of_discrete)]
  apply lintegral_congr
  intro g
  rw [Measure.map_apply measurable_prodMk_left hs, bernoulliLaw_apply, gridEta_grid hc]
  cases hfg : f g
  · simp only [Set.indicator, ENNReal.ofReal_zero, ENNReal.ofReal_one, zero_mul, zero_add,
      sub_zero, one_mul, if_false, Bool.false_eq_true]
    change (if (gridPt c g, false) ∈ s then (1 : ENNReal) else 0) =
      if (gridPt c g, f g) ∈ s then 1 else 0
    rw [hfg]
  · simp only [Set.indicator, ENNReal.ofReal_zero, ENNReal.ofReal_one, zero_mul, add_zero,
      sub_self, one_mul, if_true]
    change (if (gridPt c g, true) ∈ s then (1 : ENNReal) else 0) =
      if (gridPt c g, f g) ∈ s then 1 else 0
    rw [hfg]

lemma risk_grid (hc : 2 ≤ c) (f : G → Bool) (h : cube d → Bool) :
    risk loss01 (condLaw ((U d c).map (gridPt c)) (gridEta c f)) h =
      ∑ g : G, 1 / (Fintype.card G : ℝ) * loss01 h (gridPt c g, f g) := by
  have hinj : Function.Injective (fun g : G ↦ (gridPt c g, f g)) :=
    fun g g' hgg ↦ gridPt_injective hc (congrArg Prod.fst hgg)
  rw [risk, condLaw_grid hc, (measurableEmbedding_of_finite hinj).integral_map,
    integral_fintype Integrable.of_finite]
  simp [U_real_singleton]

end CurseAux

open UnderstandingML CurseAux in
theorem solution (d c : ℕ) (hc : 2 ≤ c)
    (L : Learner (cube d × Bool) (cube d → Bool)) (m : ℕ) (hm : 2 * m ≤ (c + 1) ^ d) :
    ∃ (DX : Measure (cube d)) (η : cube d → ℝ), IsProbabilityMeasure DX ∧
      LipschitzWith c η ∧ (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) ∧
      risk loss01 (condLaw DX η) (bayesRule η) = 0 ∧
      1 / 4 ≤ ∫ S, risk loss01 (condLaw DX η) (L m S) ∂(iidLaw (condLaw DX η) m) := by
  classical
  have hcard : Fintype.card (Fin d → Fin (c + 1)) = (c + 1) ^ d := by simp
  obtain ⟨f, hf⟩ := nfl_count m (G := Fin d → Fin (c + 1)) (by rw [hcard]; exact hm)
    (fun S' g ↦ L m (fun i ↦ (gridPt c (S' i).1, (S' i).2)) (gridPt c g))
  refine ⟨(U d c).map (gridPt c), gridEta c f,
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable,
    gridEta_lipschitz f, gridEta_mem f, ?_, ?_⟩
  · rw [risk_grid hc]
    apply Finset.sum_eq_zero
    intro g _
    simp [loss01, bayesRule, gridEta_grid hc]
    cases f g <;> norm_num
  · set N := Fintype.card (Fin d → Fin (c + 1))
    have hN : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
    have hinj : Function.Injective (fun gs : Fin m → (Fin d → Fin (c + 1)) ↦
        fun i ↦ (gridPt c (gs i), f (gs i))) := by
      intro gs gs' h; funext i
      exact gridPt_injective hc (congrArg Prod.fst (congrFun h i))
    have hiid : iidLaw (condLaw ((U d c).map (gridPt c)) (gridEta c f)) m =
        (Measure.pi (fun _ : Fin m ↦ U d c)).map
          (fun gs i ↦ (gridPt c (gs i), f (gs i))) := by
      rw [iidLaw, condLaw_grid hc]
      have : ∀ _ : Fin m, SigmaFinite ((U d c).map (fun g ↦ (gridPt c g, f g))) := fun _ ↦ by
        have := Measure.isProbabilityMeasure_map (μ := U d c)
          (measurable_of_countable (fun g ↦ (gridPt c g, f g))).aemeasurable
        infer_instance
      exact (Measure.pi_map_pi (fun _ ↦ (measurable_of_countable _).aemeasurable)).symm
    rw [hiid, (measurableEmbedding_of_finite hinj).integral_map,
      integral_fintype Integrable.of_finite]
    have hpi : ∀ gs : Fin m → (Fin d → Fin (c + 1)),
        (Measure.pi (fun _ : Fin m ↦ U d c)).real {gs} = (1 / (N : ℝ)) ^ m := by
      intro gs
      rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
      have h1 := fun i ↦ U_real_singleton (d := d) (c := c) (gs i)
      simp only [measureReal_def] at h1
      simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, N]
    simp_rw [hpi, risk_grid hc, smul_eq_mul]
    have hf' : ((N : ℝ) ^ m * N / 4) ≤ ∑ gs : Fin m → (Fin d → Fin (c + 1)), ∑ g,
        loss01 (L m (fun i ↦ (gridPt c (gs i), f (gs i)))) (gridPt c g, f g) := by
      convert hf using 3
      simp [loss01]
    have hre : ∑ gs : Fin m → (Fin d → Fin (c + 1)), (1 / (N : ℝ)) ^ m * ∑ g : Fin d → Fin (c + 1),
        1 / (N : ℝ) * loss01 (L m (fun i ↦ (gridPt c (gs i), f (gs i)))) (gridPt c g, f g) =
        (1 / (N : ℝ)) ^ m * (1 / N * ∑ gs : Fin m → (Fin d → Fin (c + 1)), ∑ g,
          loss01 (L m (fun i ↦ (gridPt c (gs i), f (gs i)))) (gridPt c g, f g)) := by
      simp only [Finset.mul_sum]
    rw [hre]
    calc (1 : ℝ) / 4 = (1 / (N : ℝ)) ^ m * (1 / N * ((N : ℝ) ^ m * N / 4)) := by
          have hNm : (N : ℝ) ^ m ≠ 0 := pow_ne_zero _ hN.ne'
          rw [div_pow, one_pow]; field_simp
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left hf' (by positivity)
