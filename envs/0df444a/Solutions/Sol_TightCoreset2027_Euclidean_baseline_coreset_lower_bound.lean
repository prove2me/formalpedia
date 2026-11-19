-- Prove2me | solution 1 for TightCoreset2027.Euclidean.baseline_coreset_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:08:37.567216+00:00
-- url     : https://prove2.me/submissions/b84b0be5-5225-44eb-bbdc-0fb84e295c53

import Definitions.Def_TightCoreset2027_Euclidean_queryConstruction
open scoped BigOperators Classical
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000
namespace TightCoreset2027.Euclidean
noncomputable def errorCoeff {E : Type*} (S : Finset E) (w : E → NNReal) (p : E) : ℝ := by
  classical
  exact (if p ∈ S then (w p : ℝ) else 0) - 1

lemma signValue_sq (b : Bool) : signValue b ^ 2 = 1 := by cases b <;> norm_num [signValue]
lemma signValue_abs (b : Bool) : |signValue b| = 1 := by cases b <;> norm_num [signValue]

lemma nearestDistance_eq_of_min {E : Type*} [PseudoMetricSpace E]
    (p : E) (C : Finset E) (c : E) (hc : c ∈ C)
    (hmin : ∀ c' ∈ C, dist p c ≤ dist p c') : nearestDistance p C = dist p c := by
  classical
  have hC : C.Nonempty := ⟨c, hc⟩
  unfold nearestDistance
  rw [dif_pos hC]
  exact le_antisymm (Finset.inf'_le _ hc) (Finset.le_inf' _ _ hmin)

lemma nearestDistance_eq_of_unique {E : Type*} [PseudoMetricSpace E]
    (p : E) (C : Finset E) (c : E) (hc : IsUniqueNearest p C c) :
    nearestDistance p C = dist p c := by
  apply nearestDistance_eq_of_min p C c hc.1
  intro c' hc'
  by_cases hh : c' = c
  · simp [hh]
  · exact (hc.2 c' hc' hh).le

lemma nearestDistance_nonneg {E : Type*} [PseudoMetricSpace E] (p : E) (C : Finset E) :
    0 ≤ nearestDistance p C := by
  classical
  unfold nearestDistance
  split_ifs with hC
  · exact Finset.le_inf' hC _ (fun c hc => dist_nonneg)
  · rfl

lemma distance_power_via_square (x z : ℝ) (hx : 0 ≤ x) :
    x ^ z = (x ^ (2 : ℕ)) ^ (z / 2) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  congr 1
  ring

lemma signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> norm_num [signValue]

lemma signValue_decide_mul (x : ℝ) : signValue (decide (0 ≤ x)) * x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [hx, signValue, abs_of_nonneg hx]
  · simp [hx, signValue, abs_of_neg (lt_of_not_ge hx)]

lemma error_as_sum_power {E : Type*} [PseudoMetricSpace E] (z : ℝ) (X S : Finset E) (w : E → NNReal)
    (hsubset : S ⊆ X) (C : Finset E) :
    weightedCost z S w C - cost z X C = ∑ p ∈ X, errorCoeff S w p * (nearestDistance p C) ^ z := by
  classical
  have hw : (∑ p ∈ X, (if p ∈ S then (w p : ℝ) else 0) * (nearestDistance p C) ^ z) =
      ∑ p ∈ S, (w p : ℝ) * (nearestDistance p C) ^ z := by
    calc
      _ = ∑ p ∈ S, (if p ∈ S then (w p : ℝ) else 0) * (nearestDistance p C) ^ z := by
        symm
        apply Finset.sum_subset hsubset
        intro p hp hpS
        simp [hpS]
      _ = _ := by apply Finset.sum_congr rfl; intro p hp; simp [hp]
  unfold weightedCost cost
  simp only [Real.rpow_eq_pow]
  symm
  unfold errorCoeff
  simp_rw [sub_mul, one_mul]
  rw [Finset.sum_sub_distrib, hw]


end TightCoreset2027.Euclidean

set_option autoImplicit false
set_option linter.all false
open scoped BigOperators Classical
namespace TightCoreset2027.Euclidean

lemma nearestDistance_image {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F] [DecidableEq E] [DecidableEq F]
    (e : E ≃ᵢ F) (p : E) (C : Finset E) :
    nearestDistance (e p) (C.image e) = nearestDistance p C := by
  unfold nearestDistance
  by_cases hC : C.Nonempty
  · rw [dif_pos (hC.image e), dif_pos hC, Finset.inf'_image]
    congr 1
    funext c
    exact e.isometry.dist_eq p c
  · have hz : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp [hz]

lemma cost_image {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F] [DecidableEq E] [DecidableEq F]
    (e : E ≃ᵢ F) (z : ℝ) (X C : Finset E) :
    cost z (X.image e) (C.image e) = cost z X C := by
  unfold cost
  rw [Finset.sum_image e.injective.injOn]
  simp only [nearestDistance_image]

lemma weightedCost_image {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F] [DecidableEq E] [DecidableEq F]
    (e : E ≃ᵢ F) (z : ℝ) (S C : Finset E) (w : F → NNReal) :
    weightedCost z (S.image e) w (C.image e) = weightedCost z S (fun p => w (e p)) C := by
  unfold weightedCost
  rw [Finset.sum_image e.injective.injOn]
  simp only [nearestDistance_image]

lemma coreset_pullback {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F] [DecidableEq E] [DecidableEq F]
    (e : E ≃ᵢ F) (z ε : ℝ) (k : ℕ) (X S : Finset E) (w : F → NNReal)
    (h : IsStrongCoreset z ε k (X.image e) (S.image e) w) :
    IsStrongCoreset z ε k X S (fun p => w (e p)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hh := h.1 (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    obtain ⟨p', hp', heq⟩ := Finset.mem_image.mp hh
    exact e.injective heq ▸ hp'
  · intro C hC
    have hh := h.2 (C.image e) (by rw [Finset.card_image_of_injective _ e.injective, hC])
    simpa only [weightedCost_image, cost_image] using hh

lemma image_symm_image {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F] [DecidableEq E] [DecidableEq F]
    (e : E ≃ᵢ F) (S : Finset F) : (S.image e.symm).image e = S := by
  rw [Finset.image_image]
  have hh : (e ∘ e.symm) = id := by funext x; exact e.apply_symm_apply x
  rw [hh, Finset.image_id]

end TightCoreset2027.Euclidean
open scoped BigOperators Classical
open Set
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000
namespace TightCoreset2027.Euclidean

abbrev SimplexSpace (k q : ℕ) := EuclideanSpace ℝ (Fin k ⊕ Fin q)

noncomputable def simplexPoint {k q : ℕ} (i : Fin k) (s : Fin q) : SimplexSpace k q :=
  WithLp.toLp 2 (fun a => match a with
    | Sum.inl j => if j = i then 10 else 0
    | Sum.inr t => if t = s then 1 else 0)

noncomputable def simplexCenter {k q : ℕ} (σ : SignArray k q) (i : Fin k) : SimplexSpace k q :=
  WithLp.toLp 2 (fun a => match a with
    | Sum.inl j => if j = i then 10 else 0
    | Sum.inr t => signValue (σ i t) / Real.sqrt (q : ℝ))

noncomputable def simplexDataset (k q : ℕ) : Finset (SimplexSpace k q) :=
  Finset.univ.image (fun a : Fin k × Fin q => simplexPoint a.1 a.2)

noncomputable def simplexQuery {k q : ℕ} (σ : SignArray k q) : Finset (SimplexSpace k q) :=
  Finset.univ.image (simplexCenter σ)

lemma simplexPoint_norm_sq {k q : ℕ} (i : Fin k) (s : Fin q) : ‖simplexPoint i s‖ ^ 2 = 101 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [simplexPoint, Fintype.sum_sum_type]
  norm_num

lemma simplexCenter_norm_sq {k q : ℕ} (hq : 1 ≤ q) (σ : SignArray k q) (i : Fin k) :
    ‖simplexCenter σ i‖ ^ 2 = 101 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  simp [simplexCenter, Fintype.sum_sum_type, div_pow, signValue_sq,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)]
  field_simp
  norm_num

lemma simplex_inner {k q : ℕ} (σ : SignArray k q) (i i' : Fin k) (s : Fin q) :
    inner ℝ (simplexPoint i s) (simplexCenter σ i') =
      (if i = i' then 100 else 0) + signValue (σ i' s) / Real.sqrt (q : ℝ) := by
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, simplexPoint, simplexCenter, Fintype.sum_sum_type, ite_mul, mul_ite]
  split_ifs <;> norm_num

lemma simplex_dist_sq {k q : ℕ} (hq : 1 ≤ q) (σ : SignArray k q)
    (i i' : Fin k) (s : Fin q) :
    dist (simplexPoint i s) (simplexCenter σ i') ^ 2 =
      (if i = i' then 2 else 202) - 2 * signValue (σ i' s) / Real.sqrt (q : ℝ) := by
  rw [dist_eq_norm, norm_sub_sq_real, simplexPoint_norm_sq,
    simplexCenter_norm_sq hq, simplex_inner]
  split_ifs <;> ring

lemma simplexPoint_injective {k q : ℕ} :
    Function.Injective (fun a : Fin k × Fin q => simplexPoint a.1 a.2) := by
  intro a a' heq
  have hi := congrArg (fun x : SimplexSpace k q => x (Sum.inl a.1)) heq
  have hs := congrArg (fun x : SimplexSpace k q => x (Sum.inr a.2)) heq
  change (if a.1 = a.1 then (10 : ℝ) else 0) = (if a.1 = a'.1 then 10 else 0) at hi
  change (if a.2 = a.2 then (1 : ℝ) else 0) = (if a.2 = a'.2 then 1 else 0) at hs
  have hii : a.1 = a'.1 := by by_contra h; simp [h] at hi
  have hss : a.2 = a'.2 := by by_contra h; simp [h] at hs
  exact Prod.ext hii hss

lemma simplexCenter_injective {k q : ℕ} (σ : SignArray k q) : Function.Injective (simplexCenter σ) := by
  intro i i' heq
  have hh := congrArg (fun x : SimplexSpace k q => x (Sum.inl i)) heq
  change (if i = i then (10 : ℝ) else 0) = (if i = i' then 10 else 0) at hh
  by_contra h
  simp [h] at hh

lemma simplexDataset_card (k q : ℕ) : (simplexDataset k q).card = k * q := by
  rw [simplexDataset, Finset.card_image_of_injective _ simplexPoint_injective]
  simp

lemma simplexQuery_card {k q : ℕ} (σ : SignArray k q) : (simplexQuery σ).card = k := by
  rw [simplexQuery, Finset.card_image_of_injective _ (simplexCenter_injective σ)]
  simp

lemma sign_div_sqrt_le_one {q : ℕ} (hq : 1 ≤ q) (b : Bool) :
    |signValue b / Real.sqrt (q : ℝ)| ≤ 1 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 1 ≤ Real.sqrt (q : ℝ) := by simpa using Real.sqrt_le_sqrt hq1
  rw [abs_div, signValue_abs, abs_of_nonneg (Real.sqrt_nonneg (q : ℝ))]
  exact (div_le_one₀ (by positivity : 0 < Real.sqrt (q : ℝ))).mpr hs

lemma simplex_nearest_sq {k q : ℕ} (hq : 1 ≤ q) (σ : SignArray k q)
    (i : Fin k) (s : Fin q) :
    nearestDistance (simplexPoint i s) (simplexQuery σ) ^ 2 =
      2 - 2 * signValue (σ i s) / Real.sqrt (q : ℝ) := by
  have heq : nearestDistance (simplexPoint i s) (simplexQuery σ) =
      dist (simplexPoint i s) (simplexCenter σ i) := by
    apply nearestDistance_eq_of_min _ _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    intro c hc
    obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hc
    by_cases hh : i = i'
    · simp [hh]
    · have h1 := simplex_dist_sq hq σ i i s
      have h2 := simplex_dist_sq hq σ i i' s
      simp only [if_true, if_neg hh] at h1 h2
      obtain ⟨hl1, hh1⟩ := abs_le.mp (sign_div_sqrt_le_one hq (σ i s))
      obtain ⟨hl2, hh2⟩ := abs_le.mp (sign_div_sqrt_le_one hq (σ i' s))
      have he1 : 2 * signValue (σ i s) / Real.sqrt (q : ℝ) = 2 * (signValue (σ i s) / Real.sqrt (q : ℝ)) := by ring
      have he2 : 2 * signValue (σ i' s) / Real.sqrt (q : ℝ) = 2 * (signValue (σ i' s) / Real.sqrt (q : ℝ)) := by ring
      rw [he1] at h1
      rw [he2] at h2
      nlinarith [dist_nonneg (x := simplexPoint i s) (y := simplexCenter σ i),
        dist_nonneg (x := simplexPoint i s) (y := simplexCenter σ i')]
  rw [heq, simplex_dist_sq hq]
  simp
lemma power_derivative_lower_window (z N u : ℝ) (hz : 1 ≤ z) (hN : 1 ≤ N)
    (hu : N ≤ u ∧ u ≤ 9 * N) :
    N ^ (z / 2 - 1) / 6 ≤ (z / 2) * u ^ (z / 2 - 1) := by
  have hNp : 0 < N := by linarith
  have hup : 0 < u := by linarith [hu.1]
  have hnval : 0 < N ^ (z / 2 - 1) := Real.rpow_pos_of_pos hNp _
  have huval : 0 < u ^ (z / 2 - 1) := Real.rpow_pos_of_pos hup _
  by_cases hβ : 0 ≤ z / 2 - 1
  · have hbase : N ^ (z / 2 - 1) ≤ u ^ (z / 2 - 1) := Real.rpow_le_rpow hNp.le (by linarith [hu.1]) hβ
    have hmul : (1 / 2 : ℝ) * u ^ (z / 2 - 1) ≤ (z / 2) * u ^ (z / 2 - 1) := by nlinarith
    nlinarith
  · have hβ0 : z / 2 - 1 ≤ 0 := le_of_not_ge hβ
    have hbase := Real.rpow_le_rpow_of_nonpos hup hu.2 hβ0
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) hNp.le] at hbase
    have hconstant : (1 / 3 : ℝ) ≤ (9 : ℝ) ^ (z / 2 - 1) := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9)
        (show -(1 / 2 : ℝ) ≤ z / 2 - 1 by linarith)
      have heq : (9 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 3 := by
        rw [Real.rpow_neg, ← Real.sqrt_eq_rpow] <;> norm_num
      rwa [heq] at hh
    have hprod := mul_le_mul_of_nonneg_right hconstant hnval.le
    have hmul : (1 / 2 : ℝ) * u ^ (z / 2 - 1) ≤ (z / 2) * u ^ (z / 2 - 1) := by nlinarith
    nlinarith


lemma simplex_power_gap_lower (z : ℝ) (hz : 1 ≤ z) (q : ℕ) (hq : 4 ≤ q) :
    2 / (3 * Real.sqrt (q : ℝ)) ≤
      ((2 : ℝ) + 2 / Real.sqrt (q : ℝ)) ^ (z / 2) -
        ((2 : ℝ) - 2 / Real.sqrt (q : ℝ)) ^ (z / 2) := by
  have hq4 : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hs2 : 2 ≤ Real.sqrt (q : ℝ) := by simpa only [show Real.sqrt (4 : ℝ) = 2 by norm_num] using Real.sqrt_le_sqrt hq4
  have hsp : 0 < Real.sqrt (q : ℝ) := by positivity
  have hh : 0 < 2 / Real.sqrt (q : ℝ) := by positivity
  have hh1 : 2 / Real.sqrt (q : ℝ) ≤ 1 := (div_le_one₀ hsp).mpr hs2
  have hα : 0 ≤ z / 2 := by linarith
  have hd : DifferentiableOn ℝ (fun u : ℝ => u ^ (z / 2)) (interior (Set.Icc (1 : ℝ) 9)) := by
    intro u hu
    have hu' : u ∈ Set.Icc (1 : ℝ) 9 := interior_subset hu
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hu'.1] : u ≠ 0))).differentiableAt.differentiableWithinAt
  have hder : ∀ u ∈ interior (Set.Icc (1 : ℝ) 9), (1 / 6 : ℝ) ≤ deriv (fun u : ℝ => u ^ (z / 2)) u := by
    intro u hu
    have hu' : u ∈ Set.Icc (1 : ℝ) 9 := interior_subset hu
    rw [Real.deriv_rpow_const]
    have hh := power_derivative_lower_window z 1 u hz (by norm_num) (by simpa using hu')
    simpa using hh
  have hg := (convex_Icc (1 : ℝ) 9).mul_sub_le_image_sub_of_le_deriv
    (Real.continuous_rpow_const hα).continuousOn hd hder
    (2 - 2 / Real.sqrt (q : ℝ)) ⟨by linarith, by linarith⟩
    (2 + 2 / Real.sqrt (q : ℝ)) ⟨by linarith, by linarith⟩ (by linarith)
  convert hg using 1 <;> ring

lemma signed_power_gap (D h α η : ℝ) (hη : η ^ 2 = 1) :
    (D + h * η) ^ α - (D - h * η) ^ α = ((D + h) ^ α - (D - h) ^ α) * η := by
  rcases sq_eq_one_iff.mp hη with hη|hη
  · simp [hη]
  · simp only [hη, mul_neg_one, sub_neg_eq_add, mul_neg_one]
    ring

lemma simplex_paired_power {k q : ℕ} (hq : 1 ≤ q) (z : ℝ) (σ : SignArray k q)
    (i : Fin k) (s : Fin q) :
    (nearestDistance (simplexPoint i s) (simplexQuery (fun i s => !(σ i s)))) ^ z -
      (nearestDistance (simplexPoint i s) (simplexQuery σ)) ^ z =
      (((2 : ℝ) + 2 / Real.sqrt (q : ℝ)) ^ (z / 2) -
        ((2 : ℝ) - 2 / Real.sqrt (q : ℝ)) ^ (z / 2)) * signValue (σ i s) := by
  rw [distance_power_via_square _ z (nearestDistance_nonneg _ _),
    distance_power_via_square _ z (nearestDistance_nonneg _ _),
    simplex_nearest_sq hq, simplex_nearest_sq hq, signValue_not]
  convert signed_power_gap 2 (2 / Real.sqrt (q : ℝ)) (z / 2) (signValue (σ i s)) (signValue_sq _) using 1 <;> congr 2 <;> ring

lemma simplex_total_cost {k q : ℕ} (hq : 1 ≤ q) (z : ℝ) (hz : 1 ≤ z) (σ : SignArray k q) :
    cost z (simplexDataset k q) (simplexQuery σ) ≤ (4 : ℝ) ^ (z / 2) * (simplexDataset k q).card := by
  unfold cost
  simp only [Real.rpow_eq_pow]
  have hp (p : SimplexSpace k q) (hp : p ∈ simplexDataset k q) :
      (nearestDistance p (simplexQuery σ)) ^ z ≤ (4 : ℝ) ^ (z / 2) := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    rw [distance_power_via_square _ z (nearestDistance_nonneg _ _), simplex_nearest_sq hq]
    have hbase : 0 ≤ 2 - 2 * signValue (σ a.1 a.2) / Real.sqrt (q : ℝ) := by
      rw [← simplex_nearest_sq hq σ a.1 a.2]
      exact sq_nonneg _
    apply Real.rpow_le_rpow hbase _ (by linarith)
    have hh := (abs_le.mp (sign_div_sqrt_le_one hq (σ a.1 a.2))).1
    nlinarith [show 2 * signValue (σ a.1 a.2) / Real.sqrt (q : ℝ) = 2 * (signValue (σ a.1 a.2) / Real.sqrt (q : ℝ)) by ring]
  have hh := Finset.sum_le_card_nsmul (simplexDataset k q)
    (fun p => (nearestDistance p (simplexQuery σ)) ^ z) ((4 : ℝ) ^ (z / 2)) hp
  simpa [nsmul_eq_mul, mul_comm] using hh

lemma half_support_abs_error_lower {E : Type*} (X S : Finset E) (w : E → NNReal)
    (hS : S ⊆ X) (hhalf : 2 * S.card ≤ X.card) :
    (X.card : ℝ) / 2 ≤ ∑ p ∈ X, |errorCoeff S w p| := by
  classical
  have hset : X.filter (fun p => p ∉ S) = X \ S := by ext p; simp
  have hboole : (∑ p ∈ X, if p ∉ S then (1 : ℝ) else 0) = ((X \ S).card : ℝ) := by
    rw [Finset.sum_boole, hset]
  have hcard := Finset.card_sdiff_add_card_inter X S
  rw [Finset.inter_eq_right.mpr hS] at hcard
  have hhalfR : 2 * (S.card : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hhalf
  have hcardR : ((X \ S).card : ℝ) + (S.card : ℝ) = (X.card : ℝ) := by exact_mod_cast hcard
  have hsum : ((X \ S).card : ℝ) ≤ ∑ p ∈ X, |errorCoeff S w p| := by
    rw [← hboole]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hpS : p ∈ S
    · simp [hpS, abs_nonneg]
    · simp [errorCoeff, hpS]
  linarith

lemma simplex_not_half_coreset {k q : ℕ} (hk : 1 ≤ k) (hq : 4 ≤ q)
    (z : ℝ) (hz : 1 ≤ z) (ε : ℝ) (hε : 0 < ε)
    (herr : ε * Real.sqrt (q : ℝ) < 1 / (12 * (4 : ℝ) ^ (z / 2)))
    (S : Finset (SimplexSpace k q)) (w : SimplexSpace k q → NNReal)
    (hhalf : 2 * S.card ≤ (simplexDataset k q).card) :
    ¬ IsStrongCoreset z ε k (simplexDataset k q) S w := by
  classical
  intro hco
  let X := simplexDataset k q
  let N : ℝ := X.card
  let g : ℝ := ((2 : ℝ) + 2 / Real.sqrt (q : ℝ)) ^ (z / 2) -
    ((2 : ℝ) - 2 / Real.sqrt (q : ℝ)) ^ (z / 2)
  let C : ℝ := (4 : ℝ) ^ (z / 2)
  let σ : SignArray k q := fun i s => decide (0 ≤ errorCoeff S w (simplexPoint i s))
  let Cplus := simplexQuery σ
  let Cminus := simplexQuery (fun i s => !(σ i s))
  let ΔP := weightedCost z S w Cplus - cost z X Cplus
  let ΔM := weightedCost z S w Cminus - cost z X Cminus
  have hq1 : 1 ≤ q := by omega
  have hN : 0 < N := by dsimp [N, X]; rw [simplexDataset_card]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hsq : 0 < Real.sqrt (q : ℝ) := by positivity
  have hglower : 2 / (3 * Real.sqrt (q : ℝ)) ≤ g := simplex_power_gap_lower z hz q hq
  have hg : 0 < g := lt_of_lt_of_le (by positivity) hglower
  have hid : ΔM - ΔP = g * (∑ p ∈ X, |errorCoeff S w p|) := by
    dsimp [ΔM, ΔP]
    rw [error_as_sum_power z _ _ _ hco.1, error_as_sum_power z _ _ _ hco.1,
      ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    rw [simplex_paired_power hq1]
    change errorCoeff S w (simplexPoint a.1 a.2) *
      (g * signValue (decide (0 ≤ errorCoeff S w (simplexPoint a.1 a.2)))) = _
    rw [show errorCoeff S w (simplexPoint a.1 a.2) *
      (g * signValue (decide (0 ≤ errorCoeff S w (simplexPoint a.1 a.2)))) =
        g * (signValue (decide (0 ≤ errorCoeff S w (simplexPoint a.1 a.2))) * errorCoeff S w (simplexPoint a.1 a.2)) by ring,
      signValue_decide_mul]
  have hp := hco.2 Cplus (simplexQuery_card σ)
  have hm := hco.2 Cminus (simplexQuery_card _)
  have hbP : |ΔP| ≤ ε * (C * N) := hp.trans (mul_le_mul_of_nonneg_left (simplex_total_cost hq1 z hz σ) hε.le)
  have hbM : |ΔM| ≤ ε * (C * N) := hm.trans (mul_le_mul_of_nonneg_left (simplex_total_cost hq1 z hz _) hε.le)
  have hgap : ΔM - ΔP ≤ 2 * ε * C * N := by nlinarith [le_abs_self ΔM, neg_le_abs ΔP]
  have homit := half_support_abs_error_lower X S w hco.1 hhalf
  have hmul := mul_le_mul_of_nonneg_left homit hg.le
  rw [← hid] at hmul
  have hcancel : N * (g / 2) ≤ N * (2 * ε * C) := by nlinarith
  have hgb : g / 2 ≤ 2 * ε * C := le_of_mul_le_mul_left hcancel hN
  have hscalar : 2 ≤ 12 * ε * C * Real.sqrt (q : ℝ) := by
    have hh : 2 / (3 * Real.sqrt (q : ℝ)) ≤ 4 * ε * C := by linarith
    have hh' := (div_le_iff₀ (by positivity : 0 < 3 * Real.sqrt (q : ℝ))).mp hh
    nlinarith
  have hsmall : (ε * Real.sqrt (q : ℝ)) * (12 * C) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 12 * C)).mp herr
  nlinarith

end TightCoreset2027.Euclidean
open scoped BigOperators Classical
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000
namespace TightCoreset2027.Euclidean

lemma exact_k_query_avoiding {E : Type*} [Infinite E] (X S : Finset E) (hS : S ⊆ X)
    (k : ℕ) (hcard : X.card ≤ k) :
    ∃ C : Finset E, C.card = k ∧ S ⊆ C ∧ ∀ p ∈ X, p ∉ S → p ∉ C := by
  classical
  obtain ⟨T, hTX, hTcard⟩ := X.finite_toSet.infinite_compl.exists_subset_card_eq (k - S.card)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro p hp hpT
    exact hTX hpT (hS hp)
  refine ⟨S ∪ T, ?_, Finset.subset_union_left, ?_⟩
  · rw [Finset.card_union_of_disjoint hST, hTcard]
    have := Finset.card_le_card hS
    omega
  · intro p hp hpS hpC
    rcases Finset.mem_union.mp hpC with hpS'|hpT
    · exact hpS hpS'
    · exact hTX hpT hp

lemma nearestDistance_eq_zero_of_mem {E : Type*} [PseudoMetricSpace E] (p : E)
    (C : Finset E) (hp : p ∈ C) : nearestDistance p C = 0 := by
  rw [nearestDistance_eq_of_min p C p hp (fun c hc => by simp), dist_self]

lemma nearestDistance_pos_of_notMem {E : Type*} [MetricSpace E] (p : E)
    (C : Finset E) (hC : C.Nonempty) (hp : p ∉ C) : 0 < nearestDistance p C := by
  classical
  unfold nearestDistance
  rw [dif_pos hC]
  apply (Finset.lt_inf'_iff (f := fun c => dist p c) hC).mpr
  intro c hc
  exact dist_pos.mpr (fun heq => hp (heq ▸ hc))

lemma coreset_full_support_of_card_le_k {E : Type*} [MetricSpace E] [Infinite E]
    (z ε : ℝ) (hz : 0 < z) (hε : ε < 1) (k : ℕ) (hk : 1 ≤ k)
    (X S : Finset E) (w : E → NNReal) (hcard : X.card ≤ k)
    (hco : IsStrongCoreset z ε k X S w) : S = X := by
  classical
  apply Finset.Subset.antisymm hco.1
  intro p hp
  by_contra hpS
  obtain ⟨C, hCcard, hSC, havoid⟩ := exact_k_query_avoiding X S hco.1 k hcard
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
  have hpC : p ∉ C := havoid p hp hpS
  have hw0 : weightedCost z S w C = 0 := by
    unfold weightedCost
    apply Finset.sum_eq_zero
    intro x hx
    rw [nearestDistance_eq_zero_of_mem x C (hSC hx)]
    simp [Real.rpow_eq_pow, Real.zero_rpow hz.ne']
  have hcost : 0 < cost z X C := by
    unfold cost
    apply Finset.sum_pos'
    · intro x hx
      exact Real.rpow_nonneg (nearestDistance_nonneg x C) z
    · exact ⟨p, hp, Real.rpow_pos_of_pos (nearestDistance_pos_of_notMem p C hCne hpC) z⟩
  have hh := hco.2 C hCcard
  rw [hw0, zero_sub, abs_neg, abs_of_pos hcost] at hh
  nlinarith

lemma k_point_lower_bound (z : ℝ) (hz : 1 ≤ z) (k : ℕ) (hk : 1 ≤ k)
    (ε : ℝ) (hε : ε < 1) :
    ∃ X : Finset (Point 1), X.card = k ∧
      ∀ (S : Finset (Point 1)) (w : Point 1 → NNReal), IsStrongCoreset z ε k X S w →
        k ≤ S.card := by
  obtain ⟨X, hX⟩ := Finset.exists_card_eq (α := Point 1) k
  refine ⟨X, hX, ?_⟩
  intro S w hco
  rw [coreset_full_support_of_card_le_k z ε (by linarith) hε k hk X S w (by omega) hco, hX]

end TightCoreset2027.Euclidean
open scoped BigOperators Classical
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000
namespace TightCoreset2027.Euclidean

 theorem baseline_lower_bound_proof (z : ℝ) (hz : 1 ≤ z) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ d : ℕ, 1 ≤ d ∧ ∃ X : Finset (Point d),
        ∀ (S : Finset (Point d)) (w : Point d → NNReal),
          IsStrongCoreset z ε k X S w → c * (k : ℝ) * Real.rpow ε (-2) ≤ (S.card : ℝ) := by
  classical
  let a : ℝ := 1 / (12 * (4 : ℝ) ^ (z / 2))
  let c : ℝ := a ^ 2 / 32
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro k hk ε hε hε1
  have hpower : Real.rpow ε (-2) = 1 / ε ^ 2 := by
    rw [Real.rpow_eq_pow, Real.rpow_neg hε.le, Real.rpow_two]
    simp [one_div]
  by_cases hsmall : ε < a / 4
  · let t : ℝ := (a / (2 * ε)) ^ 2
    let q : ℕ := ⌊t⌋₊
    have ht4 : (4 : ℝ) < t := by
      have hquot : 2 < a / (2 * ε) := (lt_div_iff₀ (by positivity : 0 < 2 * ε)).mpr (by linarith)
      dsimp [t]
      nlinarith
    have hq4 : 4 ≤ q := Nat.le_floor ht4.le
    have hqle : (q : ℝ) ≤ t := Nat.floor_le (by dsimp [t]; positivity)
    have hqt : t / 2 ≤ (q : ℝ) := by
      have hlt := Nat.lt_floor_add_one t
      change t < (q : ℝ) + 1 at hlt
      linarith
    have herror : ε * Real.sqrt (q : ℝ) < a := by
      have hh := Real.sqrt_le_sqrt hqle
      change Real.sqrt (q : ℝ) ≤ Real.sqrt ((a / (2 * ε)) ^ 2) at hh
      rw [Real.sqrt_sq (by positivity : 0 ≤ a / (2 * ε))] at hh
      have hm := mul_le_mul_of_nonneg_left hh hε.le
      have heq : ε * (a / (2 * ε)) = a / 2 := by field_simp
      rw [heq] at hm
      linarith
    let I := Fin k ⊕ Fin q
    let d := Fintype.card I
    letI : Nonempty I := ⟨Sum.inl ⟨0, by omega⟩⟩
    let e : SimplexSpace k q ≃ᵢ Point d :=
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin I)).toIsometryEquiv
    let Y := simplexDataset k q
    let X := Y.image e
    have hd : 1 ≤ d := by dsimp [d]; exact Nat.succ_le_of_lt Fintype.card_pos
    have hXY : X.card = Y.card := Finset.card_image_of_injective _ e.injective
    have hcard : X.card = k * q := hXY.trans (simplexDataset_card k q)
    have hscalar : c * (1 / ε ^ 2) ≤ (q : ℝ) / 2 := by
      calc
        _ = t / 8 := by dsimp [c, t]; ring
        _ ≤ t / 4 := by linarith
        _ ≤ _ := by linarith
    have hnumeric : c * (k : ℝ) * Real.rpow ε (-2) ≤ (X.card : ℝ) / 2 := by
      rw [hpower, hcard, Nat.cast_mul]
      have hh := mul_le_mul_of_nonneg_right hscalar (show (0 : ℝ) ≤ k by positivity)
      nlinarith
    refine ⟨d, hd, X, ?_⟩
    intro S w hco
    have hsize : (X.card : ℝ) / 2 < (S.card : ℝ) := by
      let S' := S.image e.symm
      have hSS : S'.image e = S := by simpa only [S'] using image_symm_image e S
      have hpull : IsStrongCoreset z ε k Y S' (fun p => w (e p)) := by
        apply coreset_pullback e z ε k Y S' w
        rw [hSS]
        exact hco
      have hScard : S'.card = S.card := Finset.card_image_of_injective _ e.symm.injective
      by_contra! hsize
      have hhalfR : 2 * (S.card : ℝ) ≤ (Y.card : ℝ) := by rw [← hXY]; nlinarith
      have hhalf : 2 * S'.card ≤ Y.card := by rw [hScard]; exact_mod_cast hhalfR
      exact simplex_not_half_coreset hk hq4 z hz ε hε herror S' (fun p => w (e p)) hhalf hpull
    exact hnumeric.trans hsize.le
  · obtain ⟨X, hcard, hX⟩ := k_point_lower_bound z hz k hk ε hε1
    refine ⟨1, by norm_num, X, ?_⟩
    intro S w hco
    have hεa : a / 4 ≤ ε := le_of_not_gt hsmall
    have hscalar : c / ε ^ 2 ≤ 1 := by
      apply (div_le_one₀ (sq_pos_of_pos hε)).mpr
      dsimp [c]
      nlinarith
    have hsize : (k : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hX S w hco
    rw [hpower]
    have hh := mul_le_mul_of_nonneg_right hscalar (show (0 : ℝ) ≤ k by positivity)
    calc
      _ = (c / ε ^ 2) * (k : ℝ) := by ring
      _ ≤ 1 * (k : ℝ) := hh
      _ ≤ (S.card : ℝ) := by simpa using hsize

end TightCoreset2027.Euclidean
open TightCoreset2027.Euclidean

 theorem solution (z : ℝ) (hz : 1 ≤ z) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ d : ℕ, 1 ≤ d ∧ ∃ X : Finset (Point d),
        ∀ (S : Finset (Point d)) (w : Point d → NNReal),
          IsStrongCoreset z ε k X S w →
            c * (k : ℝ) * Real.rpow ε (-2) ≤ (S.card : ℝ) := by
  exact TightCoreset2027.Euclidean.baseline_lower_bound_proof z hz
