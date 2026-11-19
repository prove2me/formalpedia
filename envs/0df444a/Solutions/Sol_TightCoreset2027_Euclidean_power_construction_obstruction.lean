-- Prove2me | solution 1 for TightCoreset2027.Euclidean.power_construction_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:56:18.088201+00:00
-- url     : https://prove2.me/submissions/295cc9d4-bfe2-4686-8c68-2627287544c6

import Definitions.Def_TightCoreset2027_Euclidean_generalPowers
import Theorems.Thm_TightCoreset2027_Euclidean_discrete_projections_discrepancy
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
open scoped BigOperators
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000
namespace TightCoreset2027.Euclidean

lemma localPoint_norm_sq {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (j : Fin n) (i : Fin m) (s : Fin q) :
    ‖localPoint G j i s‖ ^ 2 = (n : ℝ) + 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hx : ∑ a, G.x s a ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hG.2.1 s]
    norm_num
  simp [localPoint, sphereAxis, labelAxis, embedProjection, EuclideanSpace.single_apply,
    Fintype.sum_sum_type, hx, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
  norm_num

lemma signValue_sq (b : Bool) : signValue b ^ 2 = 1 := by cases b <;> norm_num [signValue]
lemma signValue_abs (b : Bool) : |signValue b| = 1 := by cases b <;> norm_num [signValue]

lemma localPoint_inner_localCenter {n m L q : ℕ} (G : ProjectionFamily L q)
    (j : Fin n) (i i' : Fin m) (s : Fin q)
    (δ : Fin (L + 1) → ℝ) (v : ProjectionSpace L) (σ : SignArray n m)
    (ℓ : Fin (L + 1)) :
    inner ℝ (localPoint G j i s) (localCenter δ v σ i' ℓ) =
      (if i = i' then 2 * Real.sqrt (n : ℝ) else 0) +
        Real.sqrt (n : ℝ) * gridValue L ℓ * inner ℝ (G.x s) v -
          Real.sqrt (n : ℝ) * (-1 : ℝ) ^ ℓ.val * δ ℓ * signValue (σ j i') := by
  simp [PiLp.inner_apply, RCLike.inner_apply, localPoint, localCenter, sphereAxis, labelAxis,
    embedProjection, extraAxis, EuclideanSpace.single_apply, Fintype.sum_sum_type,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  simp only [Pi.single_apply, Sum.inl.injEq]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, mul_one, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [mul_assoc]
  ring

lemma gridValue_bounds {L : ℕ} (hL : 1 ≤ L) (ℓ : Fin (L + 1)) :
    -1 ≤ gridValue L ℓ ∧ gridValue L ℓ ≤ 1 := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (Nat.zero_lt_of_lt hL)
  have hℓ : (ℓ.val : ℝ) ≤ L := by exact_mod_cast (Nat.le_of_lt_succ ℓ.isLt)
  have h0 : 0 ≤ 2 * (ℓ.val : ℝ) / (L : ℝ) := by positivity
  have h2 : 2 * (ℓ.val : ℝ) / (L : ℝ) ≤ 2 := (div_le_iff₀ hLp).mpr (by linarith)
  dsimp [gridValue]
  constructor <;> linarith

lemma gridValue_sq_le_one {L : ℕ} (hL : 1 ≤ L) (ℓ : Fin (L + 1)) :
    gridValue L ℓ ^ 2 ≤ 1 := by
  obtain ⟨h1, h2⟩ := gridValue_bounds hL ℓ
  nlinarith

lemma sqrt_nat_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ Real.sqrt (n : ℝ) ∧ Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · simpa using Real.sqrt_le_sqrt hn1
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith

lemma center_radicand_bounds {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (ℓ : Fin (L + 1)) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    0 ≤ 4 * (n : ℝ) + (Real.sqrt (n : ℝ) - 2 * (n : ℝ)) * (gridValue L ℓ) ^ 2 - (n : ℝ) * δ ^ 2 ∧
    4 * (n : ℝ) + (Real.sqrt (n : ℝ) - 2 * (n : ℝ)) * (gridValue L ℓ) ^ 2 - (n : ℝ) * δ ^ 2 ≤ 4 * (n : ℝ) := by
  obtain ⟨hs1, hsn⟩ := sqrt_nat_bounds hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have ht := gridValue_sq_le_one hL ℓ
  have hcoef : Real.sqrt (n : ℝ) - 2 * (n : ℝ) ≤ 0 := by nlinarith
  have hp := mul_le_mul_of_nonpos_left ht hcoef
  have hp0 := mul_nonpos_of_nonpos_of_nonneg hcoef (sq_nonneg (gridValue L ℓ))
  have hd : δ ^ 2 ≤ 1 := by nlinarith
  have hnd := mul_le_mul_of_nonneg_left hd hn0
  have hnd0 := mul_nonneg hn0 (sq_nonneg δ)
  constructor <;> nlinarith

lemma localCenter_norm_sq {n m L : ℕ} (δ : Fin (L + 1) → ℝ)
    (v : ProjectionSpace L) (hv : ‖v‖ ^ 2 = 2) (σ : SignArray n m)
    (i : Fin m) (ℓ : Fin (L + 1))
    (hR : 0 ≤ 4 * (n : ℝ) + (Real.sqrt (n : ℝ) - 2 * (n : ℝ)) *
      (gridValue L ℓ) ^ 2 - (n : ℝ) * (δ ℓ) ^ 2) :
    ‖localCenter δ v σ i ℓ‖ ^ 2 = 8 * (n : ℝ) + Real.sqrt (n : ℝ) * gridValue L ℓ ^ 2 := by
  have hvs : ∑ a, v a ^ 2 = 2 := by rwa [← EuclideanSpace.real_norm_sq_eq]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [localCenter, labelAxis, embedProjection, sphereAxis, extraAxis,
    EuclideanSpace.single_apply, Pi.single_apply, Fintype.sum_sum_type,
    mul_pow, signValue_sq, Real.sq_sqrt hR, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n),
    Finset.sum_mul, Finset.mul_sum, hvs]
  have hsign : ((-1 : ℝ) ^ ℓ.val) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [← Finset.mul_sum, hvs, hsign]
  ring

lemma localPoint_dist_sq_localCenter {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (j : Fin n) (i i' : Fin m) (s : Fin q)
    (δ : Fin (L + 1) → ℝ) (v : ProjectionSpace L) (hv : v ∈ G.directions)
    (σ : SignArray n m) (ℓ ℓ' : Fin (L + 1)) (hℓ : G.level s v = ℓ)
    (hR : 0 ≤ 4 * (n : ℝ) + (Real.sqrt (n : ℝ) - 2 * (n : ℝ)) *
      (gridValue L ℓ') ^ 2 - (n : ℝ) * (δ ℓ') ^ 2) :
    dist (localPoint G j i s) (localCenter δ v σ i' ℓ') ^ 2 =
      baseline n L ℓ + Real.sqrt (n : ℝ) * (gridValue L ℓ' - gridValue L ℓ) ^ 2 +
        (if i = i' then 0 else 4 * Real.sqrt (n : ℝ)) +
        2 * Real.sqrt (n : ℝ) * (-1 : ℝ) ^ ℓ'.val * δ ℓ' * signValue (σ j i') := by
  have hinner := hG.2.2.2.2 s v hv
  rw [hℓ] at hinner
  rw [dist_eq_norm, norm_sub_sq_real, localPoint_norm_sq G hG,
    localCenter_norm_sq δ v (hG.2.2.2.1 v hv) σ i' ℓ' hR,
    localPoint_inner_localCenter, hinner]
  dsimp [baseline]
  split_ifs <;> ring

lemma displacement2_bounds {L : ℕ} (hL : 1 ≤ L) (ℓ : Fin (L + 1)) :
    0 < displacement2 L ℓ ∧ displacement2 L ℓ ≤ 1 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  dsimp [displacement2]
  constructor
  · positivity
  · apply (div_le_one₀ (by positivity : (0 : ℝ) < 16 * (L : ℝ) ^ 2)).mpr
    nlinarith

lemma distance_sq_prescribed {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (j : Fin n) (i i' : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m)
    (ℓ ℓ' : Fin (L + 1)) (hℓ : G.level s v = ℓ) :
    dist (localPoint G j i s) (localCenter (displacement2 L) v σ i' ℓ') ^ 2 =
      baseline n L ℓ + Real.sqrt (n : ℝ) * (gridValue L ℓ' - gridValue L ℓ) ^ 2 +
        (if i = i' then 0 else 4 * Real.sqrt (n : ℝ)) +
        Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) * (-1 : ℝ) ^ ℓ'.val * signValue (σ j i') := by
  have hδ := displacement2_bounds hL ℓ'
  rw [localPoint_dist_sq_localCenter G hG j i i' s (displacement2 L) v hv σ ℓ ℓ' hℓ
    (center_radicand_bounds hn hL ℓ' _ hδ.1.le hδ.2).1]
  simp only [displacement2]
  ring

lemma localPoint_norm_le {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (j : Fin n) (i : Fin m) (s : Fin q) :
    ‖localPoint G j i s‖ ≤ 3 * Real.sqrt (n : ℝ) := by
  have hh := localPoint_norm_sq G hG j i s
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn := Real.sqrt_nonneg (n : ℝ)
  nlinarith [norm_nonneg (localPoint G j i s)]

lemma localCenter_norm_le {n m L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (v : ProjectionSpace L) (hv : ‖v‖ ^ 2 = 2) (σ : SignArray n m)
    (i : Fin m) (ℓ : Fin (L + 1)) :
    ‖localCenter (displacement2 L) v σ i ℓ‖ ≤ 3 * Real.sqrt (n : ℝ) := by
  have hδ := displacement2_bounds hL ℓ
  have hh := localCenter_norm_sq (displacement2 L) v hv σ i ℓ
    (center_radicand_bounds hn hL ℓ _ hδ.1.le hδ.2).1
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
  obtain ⟨hs1, hsn⟩ := sqrt_nat_bounds hn
  have ht := gridValue_sq_le_one hL ℓ
  have hp := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg (n : ℝ))
  nlinarith [norm_nonneg (localCenter (displacement2 L) v σ i ℓ)]

lemma extraAxis_norm (n m L : ℕ) : ‖extraAxis n m L‖ = 1 := by
  simp [extraAxis, EuclideanSpace.norm_single]

lemma sphereAxis_norm {n m L : ℕ} (j : Fin n) : ‖sphereAxis (m := m) (L := L) j‖ = 1 := by
  simp [sphereAxis, EuclideanSpace.norm_single]

lemma translation_dist_lower (n m L b b' : ℕ) (hbb : b ≠ b') :
    20 * Real.sqrt (n : ℝ) ≤ dist (copyTranslation n m L b) (copyTranslation n m L b') := by
  rw [dist_eq_norm, copyTranslation, copyTranslation, ← sub_smul, norm_smul,
    extraAxis_norm, mul_one, Real.norm_eq_abs]
  have hgap : (1 : ℝ) ≤ |(b : ℝ) - b'| := by
    rcases lt_or_gt_of_ne hbb with h|h
    · have hh : (b : ℝ) + 1 ≤ b' := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (b' : ℝ) + 1 ≤ b := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [show 20 * Real.sqrt (n : ℝ) * (b : ℝ) - 20 * Real.sqrt (n : ℝ) * (b' : ℝ) =
    (20 * Real.sqrt (n : ℝ)) * ((b : ℝ) - b') by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 20 * Real.sqrt (n : ℝ))]
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

lemma cross_copy_distance {n m L : ℕ} (b b' : ℕ) (hbb : b ≠ b')
    (u v : ConstructionSpace n m L)
    (hu : ‖u‖ ≤ 3 * Real.sqrt (n : ℝ)) (hv : ‖v‖ ≤ 3 * Real.sqrt (n : ℝ)) :
    14 * Real.sqrt (n : ℝ) ≤ dist (copyTranslation n m L b + u) (copyTranslation n m L b' + v) := by
  have ht := translation_dist_lower n m L b b' hbb
  have htri := dist_triangle4 (copyTranslation n m L b)
    (copyTranslation n m L b + u) (copyTranslation n m L b' + v) (copyTranslation n m L b')
  have hl : dist (copyTranslation n m L b) (copyTranslation n m L b + u) = ‖u‖ := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
  have hr : dist (copyTranslation n m L b' + v) (copyTranslation n m L b') = ‖v‖ := by
    rw [dist_eq_norm, add_sub_cancel_left]
  rw [hl, hr] at htri
  linarith

lemma signed_perturbation_bound {n L : ℕ} (hL : 1 ≤ L) (ℓ : Fin (L + 1)) (b : Bool) :
    |Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) * (-1 : ℝ) ^ ℓ.val * signValue b| ≤
      Real.sqrt (n : ℝ) / 8 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  rw [abs_mul, signValue_abs, mul_one, abs_mul, abs_pow]
  norm_num
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2))]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (L : ℝ) ^ 2)).mpr
  nlinarith [mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (show 0 ≤ (L : ℝ) ^ 2 - 1 by nlinarith)]

lemma prescribed_cost_bounds {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (j : Fin n) (i : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) (ℓ : Fin (L + 1))
    (hℓ : G.level s v = ℓ) :
    5 * (n : ℝ) ≤ dist (localPoint G j i s) (localCenter (displacement2 L) v σ i ℓ) ^ 2 ∧
    dist (localPoint G j i s) (localCenter (displacement2 L) v σ i ℓ) ^ 2 ≤ 9 * (n : ℝ) := by
  rw [distance_sq_prescribed G hG hn hL j i i s v hv σ ℓ ℓ hℓ]
  simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, if_true, add_zero]
  have hp := signed_perturbation_bound (n := n) hL ℓ (σ j i)
  have hp' := abs_le.mp hp
  obtain ⟨hs1, hsn⟩ := sqrt_nat_bounds hn
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht := gridValue_sq_le_one hL ℓ
  have hpgrid := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg (n : ℝ))
  have hpgrid0 := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (sq_nonneg (gridValue L ℓ))
  dsimp [baseline]
  constructor <;> nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 1)]

lemma gridValue_difference_lower {L : ℕ} (hL : 1 ≤ L) (ℓ ℓ' : Fin (L + 1))
    (hℓ : ℓ' ≠ ℓ) : 4 / (L : ℝ) ^ 2 ≤ (gridValue L ℓ' - gridValue L ℓ) ^ 2 := by
  have hgap : (1 : ℝ) ≤ |(ℓ'.val : ℝ) - ℓ.val| := by
    have hv : ℓ'.val ≠ ℓ.val := fun h => hℓ (Fin.ext h)
    rcases lt_or_gt_of_ne hv with h|h
    · have hh : (ℓ'.val : ℝ) + 1 ≤ ℓ.val := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
    · have hh : (ℓ.val : ℝ) + 1 ≤ ℓ'.val := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have hsq : (1 : ℝ) ≤ ((ℓ'.val : ℝ) - ℓ.val) ^ 2 := by
    nlinarith [sq_abs ((ℓ'.val : ℝ) - ℓ.val)]
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  unfold gridValue
  have heq : (1 - 2 * (ℓ'.val : ℝ) / (L : ℝ) - (1 - 2 * (ℓ.val : ℝ) / (L : ℝ))) ^ 2 =
      4 * ((ℓ'.val : ℝ) - ℓ.val) ^ 2 / (L : ℝ) ^ 2 := by ring
  rw [heq]
  exact div_le_div_of_nonneg_right (by nlinarith : (4 : ℝ) ≤ 4 * ((ℓ'.val : ℝ) - ℓ.val) ^ 2) (by positivity)

lemma active_center_strict {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (j : Fin n) (i i' : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) (ℓ ℓ' : Fin (L + 1))
    (hℓ : G.level s v = ℓ) (hdiff : (i', ℓ') ≠ (i, ℓ)) :
    dist (localPoint G j i s) (localCenter (displacement2 L) v σ i ℓ) <
      dist (localPoint G j i s) (localCenter (displacement2 L) v σ i' ℓ') := by
  have h1 := distance_sq_prescribed G hG hn hL j i i s v hv σ ℓ ℓ hℓ
  have h2 := distance_sq_prescribed G hG hn hL j i i' s v hv σ ℓ ℓ' hℓ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsn : 0 < Real.sqrt (n : ℝ) := by positivity
  have hLp : 0 < (L : ℝ) ^ 2 := by positivity
  have hnoise1 : |Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) * (-1 : ℝ) ^ ℓ.val * signValue (σ j i)| ≤
      Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) := by
    simp [abs_mul, abs_pow, signValue_abs, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2))]
  have hnoise2 : |Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) * (-1 : ℝ) ^ ℓ'.val * signValue (σ j i')| ≤
      Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) := by
    simp [abs_mul, abs_pow, signValue_abs, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2))]
  obtain ⟨hn1lo, hn1hi⟩ := abs_le.mp hnoise1
  obtain ⟨hn2lo, hn2hi⟩ := abs_le.mp hnoise2
  have hpenalty : 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 ≤
      Real.sqrt (n : ℝ) * (gridValue L ℓ' - gridValue L ℓ) ^ 2 +
        (if i = i' then 0 else 4 * Real.sqrt (n : ℝ)) := by
    by_cases hi : i = i'
    · have hne : ℓ' ≠ ℓ := by intro heq; exact hdiff (Prod.ext hi.symm heq)
      have hh := mul_le_mul_of_nonneg_left (gridValue_difference_lower hL ℓ ℓ' hne) hsn.le
      have hhh : 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 ≤
          Real.sqrt (n : ℝ) * (gridValue L ℓ' - gridValue L ℓ) ^ 2 := by
        calc
          _ = Real.sqrt (n : ℝ) * (4 / (L : ℝ) ^ 2) := by ring
          _ ≤ _ := hh
      simpa [hi] using hhh
    · rw [if_neg hi]
      have hh : 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 ≤ 4 * Real.sqrt (n : ℝ) := by
        apply (div_le_iff₀ hLp).mpr
        nlinarith [mul_nonneg hsn.le (show 0 ≤ (L : ℝ) ^ 2 - 1 by nlinarith)]
      nlinarith [mul_nonneg hsn.le (sq_nonneg (gridValue L ℓ' - gridValue L ℓ))]
  have hpos : 0 < 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 -
      2 * (Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2)) := by
    have : 0 < Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 := div_pos hsn hLp
    rw [show 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 -
      2 * (Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2)) =
        (15 / 4 : ℝ) * (Real.sqrt (n : ℝ) / (L : ℝ) ^ 2) by ring]
    positivity
  have hsq : dist (localPoint G j i s) (localCenter (displacement2 L) v σ i ℓ) ^ 2 <
      dist (localPoint G j i s) (localCenter (displacement2 L) v σ i' ℓ') ^ 2 := by
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, if_true, add_zero] at h1
    linarith
  nlinarith [dist_nonneg (x := localPoint G j i s) (y := localCenter (displacement2 L) v σ i ℓ),
    dist_nonneg (x := localPoint G j i s) (y := localCenter (displacement2 L) v σ i' ℓ')]

lemma dataPoint_extra {n m L q : ℕ} (G : ProjectionFamily L q)
    (b : ℕ) (j : Fin n) (i : Fin m) (s : Fin q) :
    dataPoint G b j i s (Sum.inr (Sum.inr (Sum.inr ()))) =
      20 * Real.sqrt (n : ℝ) * (b : ℝ) := by
  simp [dataPoint, copyTranslation, localPoint, extraAxis, sphereAxis, labelAxis,
    embedProjection, EuclideanSpace.single_apply]

lemma dataPoint_sphere {n m L q : ℕ} (G : ProjectionFamily L q)
    (b : ℕ) (j h : Fin n) (i : Fin m) (s : Fin q) :
    dataPoint G b j i s (Sum.inl h) =
      if h = j then Real.sqrt (n : ℝ) else 0 := by
  simp [dataPoint, copyTranslation, localPoint, extraAxis, sphereAxis, labelAxis,
    embedProjection, EuclideanSpace.single_apply, Pi.single_apply, mul_ite]

lemma dataPoint_label {n m L q : ℕ} (G : ProjectionFamily L q)
    (b : ℕ) (j : Fin n) (i h : Fin m) (s : Fin q) :
    dataPoint G b j i s (Sum.inr (Sum.inl h)) = if h = i then 1 else 0 := by
  simp [dataPoint, copyTranslation, localPoint, extraAxis, sphereAxis, labelAxis,
    embedProjection, EuclideanSpace.single_apply, Pi.single_apply]

lemma dataPoint_projection {n m L q : ℕ} (G : ProjectionFamily L q)
    (b : ℕ) (j : Fin n) (i : Fin m) (s : Fin q) (a : Fin (2 * L)) :
    dataPoint G b j i s (Sum.inr (Sum.inr (Sum.inl a))) = G.x s a := by
  simp [dataPoint, copyTranslation, localPoint, extraAxis, sphereAxis, labelAxis,
    embedProjection, EuclideanSpace.single_apply]

lemma dataPoint_inj {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n)
    {b b' : ℕ} {j j' : Fin n} {i i' : Fin m} {s s' : Fin q}
    (heq : dataPoint G b j i s = dataPoint G b' j' i' s') :
    b = b' ∧ j = j' ∧ i = i' ∧ s = s' := by
  have hspos : 0 < Real.sqrt (n : ℝ) := by positivity
  have hb := congrArg (fun p : ConstructionSpace n m L => p (Sum.inr (Sum.inr (Sum.inr ())))) heq
  simp only [dataPoint_extra] at hb
  have hbb : b = b' := by
    have hb' : (b : ℝ) = b' := by nlinarith
    exact_mod_cast hb'
  have hj := congrArg (fun p : ConstructionSpace n m L => p (Sum.inl j)) heq
  simp only [dataPoint_sphere, if_true] at hj
  have hjj : j = j' := by
    by_contra h
    rw [if_neg h] at hj
    linarith
  have hi := congrArg (fun p : ConstructionSpace n m L => p (Sum.inr (Sum.inl i))) heq
  simp only [dataPoint_label, if_true] at hi
  have hii : i = i' := by
    by_contra h
    rw [if_neg h] at hi
    norm_num at hi
  have hss : s = s' := by
    apply hG.1
    ext a
    have hh := congrArg (fun p : ConstructionSpace n m L => p (Sum.inr (Sum.inr (Sum.inl a)))) heq
    simpa only [dataPoint_projection] using hh
  exact ⟨hbb, hjj, hii, hss⟩

lemma dataCopy_card {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (b : ℕ) :
    (dataCopy n m G b).card = n * m * q := by
  classical
  unfold dataCopy
  rw [Finset.card_image_of_injective]
  · simp [Nat.mul_assoc]
  · intro a a' heq
    obtain ⟨_, hj, hi, hs⟩ := dataPoint_inj G hG hn heq
    exact Prod.ext hj (Prod.ext hi hs)

lemma dataCopy_disjoint {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) {b b' : ℕ} (hbb : b ≠ b') :
    Disjoint (dataCopy n m G b) (dataCopy n m G b') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨a', _, hh⟩ := Finset.mem_image.mp hp'
  exact hbb (dataPoint_inj G hG hn hh.symm).1

lemma dataset_card {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (B : ℕ) :
    (dataset B n m G).card = B * n * m * q := by
  classical
  unfold dataset
  rw [Finset.card_biUnion]
  · simp [dataCopy_card G hG hn, Nat.mul_assoc]
  · intro b hb b' hb' hbb
    exact dataCopy_disjoint G hG hn hbb

lemma localPoint_inner_sphere {n m L q : ℕ} (G : ProjectionFamily L q)
    (j j' : Fin n) (i : Fin m) (s : Fin q) :
    inner ℝ (localPoint G j i s) (Real.sqrt (n : ℝ) • sphereAxis (m := m) (L := L) j') =
      if j = j' then (n : ℝ) else 0 := by
  simp [PiLp.inner_apply, RCLike.inner_apply, localPoint, sphereAxis, labelAxis,
    embedProjection, EuclideanSpace.single_apply, Pi.single_apply, Fintype.sum_sum_type,
    Finset.sum_ite_irrel, ite_mul, mul_ite]
  split_ifs <;> simp_all [← sq, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]

lemma localPoint_dist_sphere_sq {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (j j' : Fin n) (i : Fin m) (s : Fin q) :
    dist (localPoint G j i s) (Real.sqrt (n : ℝ) • sphereAxis (m := m) (L := L) j') ^ 2 =
      2 + (if j = j' then 0 else 2 * (n : ℝ)) := by
  rw [dist_eq_norm, norm_sub_sq_real, localPoint_norm_sq G hG,
    localPoint_inner_sphere, norm_smul, sphereAxis_norm]
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ)), mul_one,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
  split_ifs <;> ring

lemma activeCenter_label {n m L : ℕ} (b : ℕ) (δ : Fin (L + 1) → ℝ)
    (v : ProjectionSpace L) (σ : SignArray n m) (i h : Fin m) (ℓ : Fin (L + 1)) :
    activeCenter b δ v σ i ℓ (Sum.inr (Sum.inl h)) =
      if h = i then 2 * Real.sqrt (n : ℝ) else 0 := by
  simp [activeCenter, copyTranslation, localCenter, extraAxis, sphereAxis, labelAxis,
    embedProjection, EuclideanSpace.single_apply, Pi.single_apply, mul_ite]

lemma activeCenter_projection {n m L : ℕ} (b : ℕ) (δ : Fin (L + 1) → ℝ)
    (v : ProjectionSpace L) (σ : SignArray n m) (i : Fin m) (ℓ : Fin (L + 1))
    (a : Fin (2 * L)) :
    activeCenter b δ v σ i ℓ (Sum.inr (Sum.inr (Sum.inl a))) =
      Real.sqrt (n : ℝ) * gridValue L ℓ * v a := by
  simp [activeCenter, copyTranslation, localCenter, extraAxis, sphereAxis, labelAxis,
    embedProjection, EuclideanSpace.single_apply]

lemma inactiveCenter_label (n m L b : ℕ) (j : Fin n) (i : Fin m) :
    inactiveCenter n m L b j (Sum.inr (Sum.inl i)) = 0 := by
  simp [inactiveCenter, copyTranslation, sphereAxis, extraAxis, EuclideanSpace.single_apply]

lemma inactiveCenter_sphere (n m L b : ℕ) (j h : Fin n) :
    inactiveCenter n m L b j (Sum.inl h) = if h = j then Real.sqrt (n : ℝ) else 0 := by
  simp [inactiveCenter, copyTranslation, sphereAxis, extraAxis, EuclideanSpace.single_apply,
    Pi.single_apply, mul_ite]

lemma inactiveCenter_extra (n m L b : ℕ) (j : Fin n) :
    inactiveCenter n m L b j (Sum.inr (Sum.inr (Sum.inr ()))) =
      20 * Real.sqrt (n : ℝ) * (b : ℝ) := by
  simp [inactiveCenter, copyTranslation, sphereAxis, extraAxis, EuclideanSpace.single_apply]

lemma paddingPoint_label (B n m L r : ℕ) (i : Fin m) :
    paddingPoint B n m L r (Sum.inr (Sum.inl i)) = 0 := by
  simp [paddingPoint, extraAxis, EuclideanSpace.single_apply]

lemma paddingPoint_sphere (B n m L r : ℕ) (j : Fin n) :
    paddingPoint B n m L r (Sum.inl j) = 0 := by
  simp [paddingPoint, extraAxis, EuclideanSpace.single_apply]

lemma paddingPoint_extra (B n m L r : ℕ) :
    paddingPoint B n m L r (Sum.inr (Sum.inr (Sum.inr ()))) =
      20 * Real.sqrt (n : ℝ) * ((B + 1 + r : ℕ) : ℝ) := by
  simp [paddingPoint, extraAxis, EuclideanSpace.single_apply]

lemma gridValue_injective {L : ℕ} (hL : 1 ≤ L) : Function.Injective (gridValue L) := by
  intro ℓ ℓ' heq
  unfold gridValue at heq
  have hn : (L : ℝ) ≠ 0 := by positivity
  have hh : (ℓ.val : ℝ) = ℓ'.val := by
    field_simp at heq
    linarith
  apply Fin.ext
  exact_mod_cast hh

lemma activeCenter_injective {n m L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (b : ℕ) (δ : Fin (L + 1) → ℝ) (v : ProjectionSpace L) (hv : ‖v‖ ^ 2 = 2)
    (σ : SignArray n m) :
    Function.Injective (fun a : Fin m × Fin (L + 1) => activeCenter b δ v σ a.1 a.2) := by
  intro a a' heq
  have hsp : 0 < Real.sqrt (n : ℝ) := by positivity
  have hi := congrArg (fun p : ConstructionSpace n m L => p (Sum.inr (Sum.inl a.1))) heq
  simp only [activeCenter_label, if_true] at hi
  have hii : a.1 = a'.1 := by
    by_contra h
    rw [if_neg h] at hi
    linarith
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
    by_contra! h
    apply hv0
    ext x
    exact h x
  have hp := congrArg (fun p : ConstructionSpace n m L => p (Sum.inr (Sum.inr (Sum.inl x)))) heq
  simp only [activeCenter_projection] at hp
  have ht : gridValue L a.2 = gridValue L a'.2 := by
    have hh := mul_right_cancel₀ hx hp
    exact mul_left_cancel₀ hsp.ne' hh
  exact Prod.ext hii (gridValue_injective hL ht)

lemma inactiveCenter_injective {B n m L : ℕ} (hn : 1 ≤ n) :
    Function.Injective (fun a : Fin B × Fin n => inactiveCenter n m L a.1.val a.2) := by
  intro a a' heq
  have hsp : 0 < Real.sqrt (n : ℝ) := by positivity
  have hb := congrArg (fun p : ConstructionSpace n m L => p (Sum.inr (Sum.inr (Sum.inr ())))) heq
  simp only [inactiveCenter_extra] at hb
  have hbb : a.1 = a'.1 := by
    apply Fin.ext
    have hh : (a.1.val : ℝ) = a'.1.val := by nlinarith
    exact_mod_cast hh
  have hj := congrArg (fun p : ConstructionSpace n m L => p (Sum.inl a.2)) heq
  simp only [inactiveCenter_sphere, if_true] at hj
  have hjj : a.2 = a'.2 := by
    by_contra h
    rw [if_neg h] at hj
    linarith
  exact Prod.ext hbb hjj

lemma paddingPoint_injective (B n m L : ℕ) (hn : 1 ≤ n) :
    Function.Injective (paddingPoint B n m L) := by
  intro r r' heq
  have hsp : 0 < Real.sqrt (n : ℝ) := by positivity
  have hb := congrArg (fun p : ConstructionSpace n m L => p (Sum.inr (Sum.inr (Sum.inr ())))) heq
  simp only [paddingPoint_extra, Nat.cast_add, Nat.cast_one] at hb
  have hh : (r : ℝ) = r' := by nlinarith
  exact_mod_cast hh

lemma queryCenters_card {B n m L k : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (b : Fin B) (δ : Fin (L + 1) → ℝ) (v : ProjectionSpace L) (hv : ‖v‖ ^ 2 = 2)
    (σ : SignArray n m) (hbudget : n * (B - 1) + m * (L + 1) ≤ k) :
    (queryCenters B n m L k b δ v σ).card = k := by
  classical
  let A := Finset.univ.image (fun a : Fin m × Fin (L + 1) => activeCenter b.val δ v σ a.1 a.2)
  let I := (Finset.univ.filter (fun a : Fin B × Fin n => a.1 ≠ b)).image
    (fun a => inactiveCenter n m L a.1.val a.2)
  let P := (Finset.range (k - (n * (B - 1) + m * (L + 1)))).image (paddingPoint B n m L)
  have hsp : 0 < Real.sqrt (n : ℝ) := by positivity
  have hA : A.card = m * (L + 1) := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ (activeCenter_injective hn hL b.val δ v hv σ)]
    simp
  have hI : I.card = (B - 1) * n := by
    dsimp [I]
    rw [Finset.card_image_of_injective _ (inactiveCenter_injective hn)]
    have hf : (Finset.univ.filter (fun a : Fin B × Fin n => a.1 ≠ b)) =
        (Finset.univ.erase b) ×ˢ (Finset.univ : Finset (Fin n)) := by ext a; simp
    rw [hf, Finset.card_product]
    simp
  have hP : P.card = k - (n * (B - 1) + m * (L + 1)) := by
    dsimp [P]
    rw [Finset.card_image_of_injective _ (paddingPoint_injective B n m L hn)]
    simp
  have hAI : Disjoint A I := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨a', _, heq⟩ := Finset.mem_image.mp hp'
    have hh := congrArg (fun p : ConstructionSpace n m L => p (Sum.inr (Sum.inl a.1))) heq
    simp only [activeCenter_label, inactiveCenter_label, if_true] at hh
    linarith
  have hAP : Disjoint A P := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨r, _, heq⟩ := Finset.mem_image.mp hp'
    have hh := congrArg (fun p : ConstructionSpace n m L => p (Sum.inr (Sum.inl a.1))) heq
    simp only [activeCenter_label, paddingPoint_label, if_true] at hh
    linarith
  have hIP : Disjoint I P := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨r, _, heq⟩ := Finset.mem_image.mp hp'
    have hh := congrArg (fun p : ConstructionSpace n m L => p (Sum.inl a.2)) heq
    simp only [inactiveCenter_sphere, paddingPoint_sphere, if_true] at hh
    linarith
  change (A ∪ I ∪ P).card = k
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAP, hIP⟩),
    Finset.card_union_of_disjoint hAI, hA, hI, hP]
  nlinarith [Nat.sub_add_cancel hbudget]

lemma sphereCenter_norm_le {n m L : ℕ} (j : Fin n) :
    ‖Real.sqrt (n : ℝ) • sphereAxis (m := m) (L := L) j‖ ≤ 3 * Real.sqrt (n : ℝ) := by
  rw [norm_smul, sphereAxis_norm, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

lemma within_cross_lt {n m L : ℕ} (hn : 1 ≤ n) (b b' : ℕ) (hbb : b ≠ b')
    (u v w : ConstructionSpace n m L)
    (hu : ‖u‖ ≤ 3 * Real.sqrt (n : ℝ))
    (hv : ‖v‖ ≤ 3 * Real.sqrt (n : ℝ))
    (hw : ‖w‖ ≤ 3 * Real.sqrt (n : ℝ)) :
    dist (copyTranslation n m L b + u) (copyTranslation n m L b + v) <
      dist (copyTranslation n m L b + u) (copyTranslation n m L b' + w) := by
  have hc := cross_copy_distance b b' hbb u w hu hw
  have hwithin : dist (copyTranslation n m L b + u) (copyTranslation n m L b + v) ≤
      6 * Real.sqrt (n : ℝ) := by
    rw [dist_add_left]
    have := dist_le_norm_add_norm u v
    linarith
  have hs : 0 < Real.sqrt (n : ℝ) := by positivity
  linarith

lemma activeCenter_mem_query {B n m L k : ℕ} (b : Fin B) (δ : Fin (L + 1) → ℝ)
    (v : ProjectionSpace L) (σ : SignArray n m) (i : Fin m) (ℓ : Fin (L + 1)) :
    activeCenter b.val δ v σ i ℓ ∈ queryCenters B n m L k b δ v σ := by
  classical
  unfold queryCenters
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(i, ℓ), Finset.mem_univ _, rfl⟩))

lemma inactiveCenter_mem_query {B n m L k : ℕ} (b b' : Fin B) (hbb : b' ≠ b)
    (δ : Fin (L + 1) → ℝ) (v : ProjectionSpace L) (σ : SignArray n m) (j : Fin n) :
    inactiveCenter n m L b'.val j ∈ queryCenters B n m L k b δ v σ := by
  classical
  unfold queryCenters
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨(b', j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbb⟩, rfl⟩))

lemma active_unique_nearest {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (b : Fin B) (j : Fin n) (i : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) (ℓ : Fin (L + 1))
    (hℓ : G.level s v = ℓ) :
    IsUniqueNearest (dataPoint G b.val j i s)
      (queryCenters B n m L k b (displacement2 L) v σ)
      (activeCenter b.val (displacement2 L) v σ i ℓ) := by
  classical
  refine ⟨activeCenter_mem_query b _ v σ i ℓ, ?_⟩
  intro c hc hne
  change c ∈ _ ∪ _ ∪ _ at hc
  rcases Finset.mem_union.mp hc with hac|hpc
  · rcases Finset.mem_union.mp hac with hac|hic
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hac
      have ha : a ≠ (i, ℓ) := by intro h; subst a; exact hne rfl
      simpa only [dataPoint, activeCenter, dist_add_left] using
        active_center_strict G hG hn hL j i a.1 s v hv σ ℓ a.2 hℓ ha
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hic
      have hbb : b.val ≠ a.1.val := by
        intro h
        exact (Finset.mem_filter.mp ha).2 (Fin.ext h.symm)
      exact within_cross_lt hn b.val a.1.val hbb _ _ _
        (localPoint_norm_le G hG hn j i s)
        (localCenter_norm_le hn hL v (hG.2.2.2.1 v hv) σ i ℓ)
        (sphereCenter_norm_le a.2)
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hpc
    have hbb : b.val ≠ B + 1 + r := by have := b.isLt; omega
    have hh := within_cross_lt hn b.val (B + 1 + r) hbb
      (localPoint G j i s) (localCenter (displacement2 L) v σ i ℓ) 0
      (localPoint_norm_le G hG hn j i s)
      (localCenter_norm_le hn hL v (hG.2.2.2.1 v hv) σ i ℓ)
      (by simp)
    simpa only [add_zero, dataPoint, activeCenter, paddingPoint, copyTranslation] using hh

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

lemma inactive_query_distance_sq {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (b b' : Fin B) (hbb : b' ≠ b) (j : Fin n) (i : Fin m) (s : Fin q)
    (v : ProjectionSpace L) (hv : v ∈ G.directions) (σ : SignArray n m) :
    nearestDistance (dataPoint G b'.val j i s) (queryCenters B n m L k b (displacement2 L) v σ) ^ 2 = 2 := by
  classical
  have heq : nearestDistance (dataPoint G b'.val j i s) (queryCenters B n m L k b (displacement2 L) v σ) =
      dist (dataPoint G b'.val j i s) (inactiveCenter n m L b'.val j) := by
    apply nearestDistance_eq_of_min _ _ _ (inactiveCenter_mem_query b b' hbb _ v σ j)
    intro c hc
    change c ∈ _ ∪ _ ∪ _ at hc
    rcases Finset.mem_union.mp hc with hac|hpc
    · rcases Finset.mem_union.mp hac with hac|hic
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hac
        have hneq : b'.val ≠ b.val := fun h => hbb (Fin.ext h)
        exact (within_cross_lt hn b'.val b.val hneq _ _ _
          (localPoint_norm_le G hG hn j i s) (sphereCenter_norm_le j)
          (localCenter_norm_le hn hL v (hG.2.2.2.1 v hv) σ a.1 a.2)).le
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hic
        by_cases hh : a.1 = b'
        · have h1 := localPoint_dist_sphere_sq G hG j j i s
          have h2 := localPoint_dist_sphere_sq G hG j a.2 i s
          simp only [if_true, add_zero] at h1
          simp only [dataPoint, inactiveCenter, hh, dist_add_left]
          have hle : (0 : ℝ) ≤ if j = a.2 then 0 else 2 * (n : ℝ) := by split_ifs <;> positivity
          nlinarith [dist_nonneg (x := localPoint G j i s)
            (y := Real.sqrt (n : ℝ) • sphereAxis (m := m) (L := L) j),
            dist_nonneg (x := localPoint G j i s)
            (y := Real.sqrt (n : ℝ) • sphereAxis (m := m) (L := L) a.2)]
        · have hneq : b'.val ≠ a.1.val := fun h => hh (Fin.ext h.symm)
          exact (within_cross_lt hn b'.val a.1.val hneq _ _ _
            (localPoint_norm_le G hG hn j i s) (sphereCenter_norm_le j)
            (sphereCenter_norm_le a.2)).le
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hpc
      have hneq : b'.val ≠ B + 1 + r := by have := b'.isLt; omega
      have hh := within_cross_lt hn b'.val (B + 1 + r) hneq (localPoint G j i s)
        (Real.sqrt (n : ℝ) • sphereAxis (m := m) (L := L) j) 0
        (localPoint_norm_le G hG hn j i s) (sphereCenter_norm_le j) (by simp)
      exact (by simpa only [add_zero, dataPoint, inactiveCenter, paddingPoint, copyTranslation] using hh.le)
  rw [heq]
  simpa only [dataPoint, inactiveCenter, dist_add_left, if_true, add_zero] using
    localPoint_dist_sphere_sq G hG j j i s

lemma active_query_costs {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (b : Fin B) (j : Fin n) (i : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) (ℓ : Fin (L + 1))
    (hℓ : G.level s v = ℓ) :
    IsUniqueNearest (dataPoint G b.val j i s) (queryCenters B n m L k b (displacement2 L) v σ)
        (activeCenter b.val (displacement2 L) v σ i ℓ) ∧
      nearestDistance (dataPoint G b.val j i s) (queryCenters B n m L k b (displacement2 L) v σ) ^ 2 =
        baseline n L ℓ + Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) * signValue (σ j i) * (-1 : ℝ) ^ ℓ.val ∧
      5 * (n : ℝ) ≤ nearestDistance (dataPoint G b.val j i s) (queryCenters B n m L k b (displacement2 L) v σ) ^ 2 ∧
      nearestDistance (dataPoint G b.val j i s) (queryCenters B n m L k b (displacement2 L) v σ) ^ 2 ≤ 9 * (n : ℝ) := by
  have hu := active_unique_nearest (k := k) G hG hn hL b j i s v hv σ ℓ hℓ
  refine ⟨hu, ?_⟩
  rw [nearestDistance_eq_of_unique _ _ _ hu]
  simp only [dataPoint, activeCenter, dist_add_left]
  refine ⟨?_, prescribed_cost_bounds G hG hn hL j i s v hv σ ℓ hℓ⟩
  rw [distance_sq_prescribed G hG hn hL j i i s v hv σ ℓ ℓ hℓ]
  simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, if_true, add_zero]
  ring

lemma query_total_cost {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (b : Fin B) (v : ProjectionSpace L) (hv : v ∈ G.directions) (σ : SignArray n m) :
    cost 2 (dataset B n m G) (queryCenters B n m L k b (displacement2 L) v σ) ≤
      (2 * (B : ℝ) + 9 * (n : ℝ)) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) := by
  classical
  let C := queryCenters B n m L k b (displacement2 L) v σ
  have hcopy (r : ℕ) (hr : r ∈ Finset.range B) :
      (∑ p ∈ dataCopy n m G r, nearestDistance p C ^ 2) ≤
        2 * ((n : ℝ) * (m : ℝ) * (q : ℝ)) +
          if r = b.val then 9 * (n : ℝ) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) else 0 := by
    have hp (p : ConstructionSpace n m L) (hp : p ∈ dataCopy n m G r) :
        nearestDistance p C ^ 2 ≤ if r = b.val then 9 * (n : ℝ) else 2 := by
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      by_cases hh : r = b.val
      · rw [if_pos hh, hh]
        exact (active_query_costs (k := k) G hG hn hL b a.1 a.2.1 a.2.2 v hv σ
          (G.level a.2.2 v) rfl).2.2.2
      · rw [if_neg hh]
        let b' : Fin B := ⟨r, Finset.mem_range.mp hr⟩
        have hb' : b' ≠ b := fun h => hh (congrArg Fin.val h)
        exact (inactive_query_distance_sq (k := k) G hG hn hL b b' hb' a.1 a.2.1 a.2.2 v hv σ).le
    have hh := Finset.sum_le_card_nsmul (dataCopy n m G r) (fun p => nearestDistance p C ^ 2)
      (if r = b.val then 9 * (n : ℝ) else 2) hp
    rw [nsmul_eq_mul, dataCopy_card G hG hn, Nat.cast_mul, Nat.cast_mul] at hh
    by_cases hrb : r = b.val
    · simp only [hrb, if_true] at hh ⊢
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) * (m : ℝ) * (q : ℝ) by positivity]
    · simpa [hrb, mul_comm] using hh
  unfold cost dataset
  simp only [Real.rpow_eq_pow, Real.rpow_two]
  rw [Finset.sum_biUnion]
  · have hh := Finset.sum_le_sum hcopy
    have heq : (∑ r ∈ Finset.range B,
        (2 * ((n : ℝ) * (m : ℝ) * (q : ℝ)) +
          (if r = b.val then 9 * (n : ℝ) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) else 0))) =
        (2 * (B : ℝ) + 9 * (n : ℝ)) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr b.isLt)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hh.trans_eq heq
  · intro r hr r' hr' hrr
    exact dataCopy_disjoint G hG hn hrr

end TightCoreset2027.Euclidean

open scoped BigOperators
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000
namespace TightCoreset2027.Euclidean

lemma card_filter_eq_sum_ones {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ a, if p a then (1 : ℕ) else 0 := by
  simpa using (Finset.sum_boole (R := ℕ) p Finset.univ).symm

noncomputable def errorCoeff {E : Type*} (S : Finset E) (w : E → NNReal) (p : E) : ℝ := by
  classical
  exact (if p ∈ S then (w p : ℝ) else 0) - 1

noncomputable def omissionCount {n m L q : ℕ} (G : ProjectionFamily L q)
    (S : Finset (ConstructionSpace n m L)) (b : ℕ) (j : Fin n) (i : Fin m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : Fin q => dataPoint G b j i s ∉ S)).card

noncomputable def errorVector {n m L q : ℕ} (G : ProjectionFamily L q)
    (S : Finset (ConstructionSpace n m L)) (w : ConstructionSpace n m L → NNReal)
    (b : ℕ) (j : Fin n) (i : Fin m) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 (fun s => errorCoeff S w (dataPoint G b j i s))

lemma omissionCount_le {n m L q : ℕ} (G : ProjectionFamily L q)
    (S : Finset (ConstructionSpace n m L)) (b : ℕ) (j : Fin n) (i : Fin m) :
    omissionCount G S b j i ≤ q := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin q)

lemma omissionCount_le_sq_norm {n m L q : ℕ} (G : ProjectionFamily L q)
    (S : Finset (ConstructionSpace n m L)) (w : ConstructionSpace n m L → NNReal)
    (b : ℕ) (j : Fin n) (i : Fin m) :
    (omissionCount G S b j i : ℝ) ≤ ‖errorVector G S w b j i‖ ^ 2 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  change (Finset.univ.filter (fun s : Fin q => dataPoint G b j i s ∉ S)).card ≤
    ∑ s, errorCoeff S w (dataPoint G b j i s) ^ 2
  rw [← Finset.sum_boole]
  apply Finset.sum_le_sum
  intro s hs
  by_cases h : dataPoint G b j i s ∈ S
  · simp [h, sq_nonneg]
  · simp [errorCoeff, h]

lemma omissionCount_le_sqrt_mul_norm {n m L q : ℕ} (G : ProjectionFamily L q)
    (S : Finset (ConstructionSpace n m L)) (w : ConstructionSpace n m L → NNReal)
    (b : ℕ) (j : Fin n) (i : Fin m) :
    (omissionCount G S b j i : ℝ) ≤ Real.sqrt (q : ℝ) * ‖errorVector G S w b j i‖ := by
  have hM0 : (0 : ℝ) ≤ omissionCount G S b j i := by positivity
  have hMq : (omissionCount G S b j i : ℝ) ≤ q := by exact_mod_cast omissionCount_le G S b j i
  have hMn := omissionCount_le_sq_norm G S w b j i
  apply (sq_le_sq₀ hM0 (mul_nonneg (Real.sqrt_nonneg (q : ℝ)) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)]
  calc
    _ ≤ (q : ℝ) * (omissionCount G S b j i : ℝ) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hMn (by positivity)

lemma sum_omissionCount {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n)
    (S : Finset (ConstructionSpace n m L)) (b : ℕ) :
    ∑ j, ∑ i, omissionCount G S b j i = (dataCopy n m G b \ S).card := by
  classical
  have hinj : Function.Injective (fun a : Fin n × Fin m × Fin q => dataPoint G b a.1 a.2.1 a.2.2) := by
    intro a a' h
    obtain ⟨_, hj, hi, hs⟩ := dataPoint_inj G hG hn h
    exact Prod.ext hj (Prod.ext hi hs)
  have hset : dataCopy n m G b \ S =
      (Finset.univ.filter (fun a : Fin n × Fin m × Fin q => dataPoint G b a.1 a.2.1 a.2.2 ∉ S)).image
        (fun a => dataPoint G b a.1 a.2.1 a.2.2) := by
    ext p
    simp only [Finset.mem_sdiff, dataCopy, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  rw [hset, Finset.card_image_of_injective _ hinj, card_filter_eq_sum_ones]
  simp only [Fintype.sum_prod_type, omissionCount, card_filter_eq_sum_ones]

lemma omitted_copy_norm_bound {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n)
    (S : Finset (ConstructionSpace n m L)) (w : ConstructionSpace n m L → NNReal)
    (b : ℕ) (hhalf : 2 * (S ∩ dataCopy n m G b).card ≤ (dataCopy n m G b).card) :
    ((n : ℝ) * (m : ℝ) * (q : ℝ)) / 2 ≤
      Real.sqrt (q : ℝ) * (∑ j, ∑ i, ‖errorVector G S w b j i‖) := by
  classical
  have hc := Finset.card_sdiff_add_card_inter (dataCopy n m G b) S
  rw [Finset.inter_comm] at hc
  have hmiss : (dataCopy n m G b).card ≤ 2 * (dataCopy n m G b \ S).card := by omega
  have hmissR : ((n : ℝ) * (m : ℝ) * (q : ℝ)) / 2 ≤ ((dataCopy n m G b \ S).card : ℝ) := by
    rw [dataCopy_card G hG hn] at hmiss
    have hh : (n * m * q : ℝ) ≤ 2 * ((dataCopy n m G b \ S).card : ℝ) := by exact_mod_cast hmiss
    linarith
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => omissionCount_le_sqrt_mul_norm G S w b j i))
  have heq : (∑ j, ∑ i, (omissionCount G S b j i : ℝ)) = ((dataCopy n m G b \ S).card : ℝ) := by
    exact_mod_cast sum_omissionCount G hG hn S b
  rw [heq] at hs
  simp_rw [← Finset.mul_sum] at hs
  exact hmissR.trans hs

lemma small_copy_exists {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n)
    (S : Finset (ConstructionSpace n m L)) (hsubset : S ⊆ dataset n n m G)
    (hhalf : 2 * S.card ≤ (dataset n n m G).card) :
    ∃ b : Fin n, 2 * (S ∩ dataCopy n m G b.val).card ≤ (dataCopy n m G b.val).card := by
  classical
  have hdisj : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint (fun r => S ∩ dataCopy n m G r) := by
    intro r hr r' hr' hrr
    exact (dataCopy_disjoint G hG hn hrr).mono Finset.inter_subset_right Finset.inter_subset_right
  have hparts : (Finset.range n).biUnion (fun r => S ∩ dataCopy n m G r) = S := by
    rw [← Finset.inter_biUnion]
    exact Finset.inter_eq_left.mpr hsubset
  have hcard : (∑ r ∈ Finset.range n, (S ∩ dataCopy n m G r).card) = S.card := by
    rw [← Finset.card_biUnion hdisj, hparts]
  by_contra! hbad
  have hslt : (∑ r ∈ Finset.range n, (dataCopy n m G r).card) <
      ∑ r ∈ Finset.range n, 2 * (S ∩ dataCopy n m G r).card := Finset.sum_lt_sum_of_nonempty
    (Finset.nonempty_range_iff.mpr (show n ≠ 0 by omega))
    (fun r (hr : r ∈ Finset.range n) => hbad (⟨r, Finset.mem_range.mp hr⟩ : Fin n))
  simp only [dataCopy_card G hG hn, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum, hcard] at hslt
  rw [dataset_card G hG hn n] at hhalf
  norm_cast at hslt
  simp only [Nat.mul_assoc] at hslt hhalf
  omega

lemma discrepancy_for_groups {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionSpecification G) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (A : Fin n → Fin m → EuclideanSpace ℝ (Fin q)) :
    ∃ v ∈ G.directions,
      (1 / Real.sqrt 3) * (∑ j, ∑ i, ‖A j i‖) ≤
        ∑ j, ∑ i, |∑ s, A j i s * (-1 : ℝ) ^ (G.level s v).val| := by
  classical
  let e : Fin (n * m) ≃ Fin n × Fin m :=
    Fintype.equivOfCardEq (by simp)
  obtain ⟨v, hv, hh⟩ := hG.2 (n * m) (by nlinarith) (fun r => A (e r).1 (e r).2)
  refine ⟨v, hv, ?_⟩
  have hleft := e.sum_comp (fun a : Fin n × Fin m => ‖A a.1 a.2‖)
  have hright := e.sum_comp (fun a : Fin n × Fin m =>
    |∑ s, A a.1 a.2 s * (-1 : ℝ) ^ (G.level s v).val|)
  rw [Fintype.sum_prod_type] at hleft hright
  simpa only [hleft, hright] using hh

lemma omission_discrepancy_direction {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionSpecification G) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (S : Finset (ConstructionSpace n m L)) (w : ConstructionSpace n m L → NNReal)
    (b : ℕ) (hhalf : 2 * (S ∩ dataCopy n m G b).card ≤ (dataCopy n m G b).card) :
    ∃ v ∈ G.directions,
      ((n : ℝ) * (m : ℝ) * (q : ℝ)) / 2 ≤
        Real.sqrt 3 * Real.sqrt (q : ℝ) *
          (∑ j, ∑ i, |∑ s, errorCoeff S w (dataPoint G b j i s) * (-1 : ℝ) ^ (G.level s v).val|) := by
  obtain ⟨v, hv, hh⟩ := discrepancy_for_groups G hG hn hm (errorVector G S w b)
  have hnrm := omitted_copy_norm_bound G hG.1 hn S w b hhalf
  have h3 : 0 < Real.sqrt 3 := by positivity
  have hcoeff : ∑ j, ∑ i, ‖errorVector G S w b j i‖ ≤
      Real.sqrt 3 * (∑ j, ∑ i, |∑ s, errorCoeff S w (dataPoint G b j i s) * (-1 : ℝ) ^ (G.level s v).val|) := by
    have hh' : (∑ j, ∑ i, ‖errorVector G S w b j i‖) / Real.sqrt 3 ≤
        ∑ j, ∑ i, |∑ s, errorCoeff S w (dataPoint G b j i s) * (-1 : ℝ) ^ (G.level s v).val| := by
      simpa [errorVector, div_eq_mul_inv, mul_comm] using hh
    have := (div_le_iff₀ h3).mp hh'
    linarith
  refine ⟨v, hv, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hcoeff (Real.sqrt_nonneg (q : ℝ))
  nlinarith

lemma error_as_sum {E : Type*} [PseudoMetricSpace E] (X S : Finset E) (w : E → NNReal)
    (hsubset : S ⊆ X) (C : Finset E) :
    weightedCost 2 S w C - cost 2 X C =
      ∑ p ∈ X, errorCoeff S w p * nearestDistance p C ^ 2 := by
  classical
  have hw : (∑ p ∈ X, (if p ∈ S then (w p : ℝ) else 0) * nearestDistance p C ^ 2) =
      ∑ p ∈ S, (w p : ℝ) * nearestDistance p C ^ 2 := by
    calc
      _ = ∑ p ∈ S, (if p ∈ S then (w p : ℝ) else 0) * nearestDistance p C ^ 2 := by
        symm
        apply Finset.sum_subset hsubset
        intro p hp hpS
        simp [hpS]
      _ = _ := by apply Finset.sum_congr rfl; intro p hp; simp [hp]
  unfold weightedCost cost
  simp only [Real.rpow_eq_pow, Real.rpow_two]
  symm
  unfold errorCoeff
  simp_rw [sub_mul, one_mul]
  rw [Finset.sum_sub_distrib, hw]

lemma signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> norm_num [signValue]

lemma active_paired_difference {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (b : Fin B) (j : Fin n) (i : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) :
    nearestDistance (dataPoint G b.val j i s) (queryCenters B n m L k b (displacement2 L) v σ) ^ 2 -
      nearestDistance (dataPoint G b.val j i s)
        (queryCenters B n m L k b (displacement2 L) v (fun j i => !(σ j i))) ^ 2 =
      Real.sqrt (n : ℝ) / (4 * (L : ℝ) ^ 2) * signValue (σ j i) *
        (-1 : ℝ) ^ (G.level s v).val := by
  rw [(active_query_costs G hG hn hL b j i s v hv σ _ rfl).2.1,
    (active_query_costs G hG hn hL b j i s v hv (fun j i => !(σ j i)) _ rfl).2.1]
  rw [signValue_not]
  ring

lemma paired_error_identity {n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (S : Finset (ConstructionSpace n m L)) (w : ConstructionSpace n m L → NNReal)
    (hsubset : S ⊆ dataset n n m G) (b : Fin n)
    (v : ProjectionSpace L) (hv : v ∈ G.directions) (σ : SignArray n m) :
    (weightedCost 2 S w (queryCenters n n m L k b (displacement2 L) v σ) -
      cost 2 (dataset n n m G) (queryCenters n n m L k b (displacement2 L) v σ)) -
    (weightedCost 2 S w (queryCenters n n m L k b (displacement2 L) v (fun j i => !(σ j i))) -
      cost 2 (dataset n n m G) (queryCenters n n m L k b (displacement2 L) v (fun j i => !(σ j i)))) =
      Real.sqrt (n : ℝ) / (4 * (L : ℝ) ^ 2) *
        (∑ j, ∑ i, signValue (σ j i) *
          (∑ s, errorCoeff S w (dataPoint G b.val j i s) * (-1 : ℝ) ^ (G.level s v).val)) := by
  classical
  let Cplus := queryCenters n n m L k b (displacement2 L) v σ
  let Cminus := queryCenters n n m L k b (displacement2 L) v (fun j i => !(σ j i))
  rw [error_as_sum _ _ _ hsubset, error_as_sum _ _ _ hsubset, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hcopy (r : ℕ) (hr : r ∈ Finset.range n) :
      (∑ p ∈ dataCopy n m G r, errorCoeff S w p *
        (nearestDistance p Cplus ^ 2 - nearestDistance p Cminus ^ 2)) =
      if r = b.val then
        Real.sqrt (n : ℝ) / (4 * (L : ℝ) ^ 2) *
          (∑ j, ∑ i, signValue (σ j i) *
            (∑ s, errorCoeff S w (dataPoint G b.val j i s) * (-1 : ℝ) ^ (G.level s v).val))
      else 0 := by
    by_cases hrb : r = b.val
    · rw [if_pos hrb, hrb]
      unfold dataCopy
      rw [Finset.sum_image]
      · dsimp only [Cplus, Cminus]
        simp only [Fintype.sum_prod_type]
        simp_rw [active_paired_difference G hG hn hL b _ _ _ v hv σ]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro s hs
        ring
      · intro a ha a' ha' heq
        obtain ⟨_, hj, hi, hs⟩ := dataPoint_inj G hG hn heq
        exact Prod.ext hj (Prod.ext hi hs)
    · rw [if_neg hrb]
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      let b' : Fin n := ⟨r, Finset.mem_range.mp hr⟩
      have hb' : b' ≠ b := fun h => hrb (congrArg Fin.val h)
      have hplus := inactive_query_distance_sq (k := k) G hG hn hL b b' hb' a.1 a.2.1 a.2.2 v hv σ
      have hminus := inactive_query_distance_sq (k := k) G hG hn hL b b' hb' a.1 a.2.1 a.2.2 v hv (fun j i => !(σ j i))
      change errorCoeff S w _ * (_ - _) = 0
      rw [show nearestDistance (dataPoint G r a.1 a.2.1 a.2.2) Cplus ^ 2 = 2 from hplus,
        show nearestDistance (dataPoint G r a.1 a.2.1 a.2.2) Cminus ^ 2 = 2 from hminus]
      ring
  unfold dataset
  rw [Finset.sum_biUnion]
  · change (∑ r ∈ Finset.range n, ∑ p ∈ dataCopy n m G r, errorCoeff S w p *
      (nearestDistance p Cplus ^ 2 - nearestDistance p Cminus ^ 2)) = _
    apply Eq.trans (Finset.sum_congr rfl (fun r hr => hcopy r hr))
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr b.isLt)]
  · intro r hr r' hr' hrr
    exact dataCopy_disjoint G hG hn hrr

lemma query_cost_pos {n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hm : 1 ≤ m) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (b : Fin n) (v : ProjectionSpace L) (hv : v ∈ G.directions) (σ : SignArray n m) :
    0 < cost 2 (dataset n n m G) (queryCenters n n m L k b (displacement2 L) v σ) := by
  classical
  unfold cost
  simp only [Real.rpow_eq_pow, Real.rpow_two]
  apply Finset.sum_pos'
  · intro p hp; positivity
  · let j : Fin n := ⟨0, by omega⟩
    let i : Fin m := ⟨0, by omega⟩
    let s : Fin q := ⟨0, by omega⟩
    refine ⟨dataPoint G b.val j i s, ?_, ?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨b.val, Finset.mem_range.mpr b.isLt, ?_⟩
      exact Finset.mem_image.mpr ⟨(j, i, s), Finset.mem_univ _, rfl⟩
    · have hh := (active_query_costs (k := k) G hG hn hL b j i s v hv σ _ rfl).2.2.1
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith

lemma signValue_decide_mul (x : ℝ) : signValue (decide (0 ≤ x)) * x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [hx, signValue, abs_of_nonneg hx]
  · simp [hx, signValue, abs_of_neg (lt_of_not_ge hx)]

lemma paired_large_absolute_error {n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionSpecification G) (hn : 1 ≤ n) (hm : 1 ≤ m) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (S : Finset (ConstructionSpace n m L)) (w : ConstructionSpace n m L → NNReal)
    (hsubset : S ⊆ dataset n n m G) (b : Fin n)
    (hhalf : 2 * (S ∩ dataCopy n m G b.val).card ≤ (dataCopy n m G b.val).card) :
    ∃ v ∈ G.directions, ∃ σ : SignArray n m,
      0 < cost 2 (dataset n n m G) (queryCenters n n m L k b (displacement2 L) v σ) ∧
      1 / (176 * Real.sqrt 3 * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2) ≤
        |weightedCost 2 S w (queryCenters n n m L k b (displacement2 L) v σ) -
            cost 2 (dataset n n m G) (queryCenters n n m L k b (displacement2 L) v σ)| /
          cost 2 (dataset n n m G) (queryCenters n n m L k b (displacement2 L) v σ) := by
  classical
  obtain ⟨v, hv, hdisc⟩ := omission_discrepancy_direction G hG hn hm S w b.val hhalf
  let H : Fin n → Fin m → ℝ := fun j i =>
    ∑ s, errorCoeff S w (dataPoint G b.val j i s) * (-1 : ℝ) ^ (G.level s v).val
  let σ : SignArray n m := fun j i => decide (0 ≤ H j i)
  let σminus : SignArray n m := fun j i => !(σ j i)
  let Cplus := queryCenters n n m L k b (displacement2 L) v σ
  let Cminus := queryCenters n n m L k b (displacement2 L) v σminus
  let costP := cost 2 (dataset n n m G) Cplus
  let costM := cost 2 (dataset n n m G) Cminus
  let ΔP := weightedCost 2 S w Cplus - costP
  let ΔM := weightedCost 2 S w Cminus - costM
  let T := 1 / (176 * Real.sqrt 3 * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2)
  have hPpos : 0 < costP := query_cost_pos G hG.1 hn hm hL hq b v hv σ
  have hMpos : 0 < costM := query_cost_pos G hG.1 hn hm hL hq b v hv σminus
  have hPbound : costP ≤ 11 * ((n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) := by
    have hh := query_total_cost (k := k) G hG.1 hn hL b v hv σ
    dsimp [costP, Cplus]
    convert hh using 1 <;> ring
  have hMbound : costM ≤ 11 * ((n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) := by
    have hh := query_total_cost (k := k) G hG.1 hn hL b v hv σminus
    dsimp [costM, Cminus]
    convert hh using 1 <;> ring
  have hidentity : ΔP - ΔM = Real.sqrt (n : ℝ) / (4 * (L : ℝ) ^ 2) * (∑ j, ∑ i, |H j i|) := by
    have hh := paired_error_identity (k := k) G hG.1 hn hL S w hsubset b v hv σ
    dsimp [ΔP, ΔM, costP, costM, Cplus, Cminus, σminus]
    rw [hh]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    exact signValue_decide_mul (H j i)
  have hsn : 0 < Real.sqrt (n : ℝ) := by positivity
  have hsq : 0 < Real.sqrt (q : ℝ) := by positivity
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hLsq : 0 < (L : ℝ) ^ 2 := by positivity
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hsqrtN := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
  have hsum0 : 0 ≤ ∑ j, ∑ i, |H j i| := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hdisc' : ((n : ℝ) * (m : ℝ) * (q : ℝ)) / 2 ≤ Real.sqrt 3 * Real.sqrt (q : ℝ) * (∑ j, ∑ i, |H j i|) := hdisc
  have hcoef : 22 * T * (n : ℝ) =
      Real.sqrt (n : ℝ) / (8 * Real.sqrt 3 * Real.sqrt (q : ℝ) * (L : ℝ) ^ 2) := by
    dsimp [T]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ n)]
    field_simp
    nlinarith only [hsqrtN]
  have hgap : 22 * T * ((n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) ≤ ΔP - ΔM := by
    rw [hidentity]
    have hmul := mul_le_mul_of_nonneg_left hdisc'
      (show 0 ≤ (Real.sqrt (n : ℝ) / (4 * (L : ℝ) ^ 2)) / (Real.sqrt 3 * Real.sqrt (q : ℝ)) by positivity)
    calc
      _ = (22 * T * (n : ℝ)) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) := by ring
      _ = ((Real.sqrt (n : ℝ) / (4 * (L : ℝ) ^ 2)) / (Real.sqrt 3 * Real.sqrt (q : ℝ))) *
          (((n : ℝ) * (m : ℝ) * (q : ℝ)) / 2) := by rw [hcoef]; ring
      _ ≤ _ := hmul
      _ = _ := by field_simp
  by_cases hP : T ≤ |ΔP| / costP
  · exact ⟨v, hv, σ, hPpos, hP⟩
  · refine ⟨v, hv, σminus, hMpos, ?_⟩
    change T ≤ |ΔM| / costM
    by_contra! hM
    have hPP : |ΔP| < T * costP := (div_lt_iff₀ hPpos).mp (lt_of_not_ge hP)
    have hMM : |ΔM| < T * costM := (div_lt_iff₀ hMpos).mp hM
    have hPb := mul_le_mul_of_nonneg_left hPbound hTpos.le
    have hMb := mul_le_mul_of_nonneg_left hMbound hTpos.le
    nlinarith [le_abs_self ΔP, neg_le_abs ΔM]

end TightCoreset2027.Euclidean

open scoped BigOperators
open Set
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000
namespace TightCoreset2027.Euclidean

lemma power_derivative_lower (z N u : ℝ) (hz : 1 ≤ z) (hN : 1 ≤ N)
    (hu : 5 * N ≤ u ∧ u ≤ 9 * N) :
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

lemma baseline_window {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (ℓ : Fin (L + 1)) :
    5 * (n : ℝ) ≤ baseline n L ℓ - Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) ∧
    baseline n L ℓ + Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) ≤ 9 * (n : ℝ) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hp : Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) ≤ Real.sqrt (n : ℝ) / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * (L : ℝ) ^ 2)).mpr
    nlinarith [mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (show 0 ≤ (L : ℝ) ^ 2 - 1 by nlinarith)]
  obtain ⟨hs1, hsn⟩ := sqrt_nat_bounds hn
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht := gridValue_sq_le_one hL ℓ
  have hgrid := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg (n : ℝ))
  have hgrid0 := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (sq_nonneg (gridValue L ℓ))
  dsimp [baseline]
  constructor <;> nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 1)]

lemma calibration_exists_unique (z : ℝ) (hz : 1 ≤ z) (n L : ℕ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (ℓ : Fin (L + 1)) :
    ∃! δ : ℝ, CalibratesPower z n L ℓ δ := by
  let D := baseline n L ℓ
  let sn := Real.sqrt (n : ℝ)
  let h := sn / (8 * (L : ℝ) ^ 2)
  let δmax := 1 / (16 * (L : ℝ) ^ 2)
  let target := (n : ℝ) ^ ((z - 1) / 2) / (32 * (L : ℝ) ^ 2)
  let F : ℝ → ℝ := fun δ => (D + 2 * sn * δ) ^ (z / 2) - (D - 2 * sn * δ) ^ (z / 2)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNp : (0 : ℝ) < n := by positivity
  have hsn : 0 < sn := by dsimp [sn]; positivity
  have hLs : 0 < (L : ℝ) ^ 2 := by positivity
  have hδmax : 0 < δmax := by dsimp [δmax]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hstep : 2 * sn * δmax = h := by dsimp [δmax, h]; ring
  have hwindow : 5 * (n : ℝ) ≤ D - h ∧ D + h ≤ 9 * (n : ℝ) := baseline_window hn hL ℓ
  have hα : 0 < z / 2 := by linarith
  have htarget : 0 < target := by dsimp [target]; positivity
  have hF : Continuous F := by
    apply Continuous.sub
    · exact (Real.continuous_rpow_const hα.le).comp (by fun_prop)
    · exact (Real.continuous_rpow_const hα.le).comp (by fun_prop)
  have hF0 : F 0 = 0 := by simp [F]
  have hmono : StrictMonoOn F (Icc 0 δmax) := by
    intro x hx y hy hxy
    have hxb : 0 ≤ D + 2 * sn * x := by nlinarith [hwindow.1, mul_nonneg hsn.le hx.1]
    have hyb : 0 ≤ D - 2 * sn * y := by
      have hmul := mul_le_mul_of_nonneg_left hy.2 (by positivity : 0 ≤ 2 * sn)
      rw [hstep] at hmul
      nlinarith [hwindow.1]
    have hp := Real.rpow_lt_rpow hxb (show D + 2 * sn * x < D + 2 * sn * y by nlinarith) hα
    have hm := Real.rpow_lt_rpow hyb (show D - 2 * sn * y < D - 2 * sn * x by nlinarith) hα
    dsimp [F]
    linarith
  have hderiv : ∀ u ∈ interior (Icc (5 * (n : ℝ)) (9 * (n : ℝ))),
      (n : ℝ) ^ (z / 2 - 1) / 6 ≤ deriv (fun u : ℝ => u ^ (z / 2)) u := by
    intro u hu
    rw [Real.deriv_rpow_const]
    have hu' : u ∈ Icc (5 * (n : ℝ)) (9 * (n : ℝ)) := interior_subset hu
    exact power_derivative_lower z n u hz hnR ⟨hu'.1, hu'.2⟩
  have hdiff : DifferentiableOn ℝ (fun u : ℝ => u ^ (z / 2))
      (interior (Icc (5 * (n : ℝ)) (9 * (n : ℝ)))) := by
    intro u hu
    have hu' : u ∈ Icc (5 * (n : ℝ)) (9 * (n : ℝ)) := interior_subset hu
    have hup : 0 < u := by nlinarith [hu'.1]
    exact (Real.hasDerivAt_rpow_const (Or.inl hup.ne')).differentiableAt.differentiableWithinAt
  have hgrowth := (convex_Icc (5 * (n : ℝ)) (9 * (n : ℝ))).mul_sub_le_image_sub_of_le_deriv
    (Real.continuous_rpow_const hα.le).continuousOn hdiff hderiv
    (D - h) ⟨hwindow.1, by nlinarith [hwindow.2]⟩
    (D + h) ⟨by nlinarith [hwindow.1], hwindow.2⟩ (by linarith)
  have hpower : (n : ℝ) ^ (z / 2 - 1) * sn = (n : ℝ) ^ ((z - 1) / 2) := by
    rw [show sn = (n : ℝ) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow (n : ℝ), ← Real.rpow_add hNp]
    congr 1
    ring
  have hfull : target < F δmax := by
    have heq : (n : ℝ) ^ (z / 2 - 1) / 6 * (D + h - (D - h)) =
        (n : ℝ) ^ ((z - 1) / 2) / (24 * (L : ℝ) ^ 2) := by
      dsimp [h]
      rw [show (n : ℝ) ^ (z / 2 - 1) / 6 * (D + sn / (8 * (L : ℝ) ^ 2) - (D - sn / (8 * (L : ℝ) ^ 2))) =
        ((n : ℝ) ^ (z / 2 - 1) * sn) / (24 * (L : ℝ) ^ 2) by ring, hpower]
    rw [heq] at hgrowth
    change target < (D + 2 * sn * δmax) ^ (z / 2) - (D - 2 * sn * δmax) ^ (z / 2)
    rw [hstep]
    have hstrict : target < (n : ℝ) ^ ((z - 1) / 2) / (24 * (L : ℝ) ^ 2) := by
      dsimp [target]
      have hp : 0 < (n : ℝ) ^ ((z - 1) / 2) / (L : ℝ) ^ 2 := by positivity
      have heq : (n : ℝ) ^ ((z - 1) / 2) / (32 * (L : ℝ) ^ 2) =
          (1 / 32 : ℝ) * ((n : ℝ) ^ ((z - 1) / 2) / (L : ℝ) ^ 2) := by ring
      rw [heq]
      rw [show (n : ℝ) ^ ((z - 1) / 2) / (24 * (L : ℝ) ^ 2) =
          (1 / 24 : ℝ) * ((n : ℝ) ^ ((z - 1) / 2) / (L : ℝ) ^ 2) by ring]
      nlinarith
    exact hstrict.trans_le hgrowth
  obtain ⟨δ, hδ, heq⟩ := intermediate_value_Icc hδmax.le hF.continuousOn
    (show target ∈ Icc (F 0) (F δmax) by rw [hF0]; exact ⟨htarget.le, hfull.le⟩)
  have hδp : 0 < δ := by
    by_contra! hh
    have hzδ : δ = 0 := by linarith [hδ.1]
    rw [hzδ, hF0] at heq
    linarith
  have hcal : CalibratesPower z n L ℓ δ := by
    refine ⟨hδp, hδ.2, ?_⟩
    simpa only [Real.rpow_eq_pow] using heq
  refine ⟨δ, hcal, ?_⟩
  intro δ' hδ'
  apply hmono.injOn ⟨hδ'.1.le, hδ'.2.1⟩ hδ
  have hδ'eq : F δ' = target := by simpa only [Real.rpow_eq_pow] using hδ'.2.2
  exact hδ'eq.trans heq.symm

end TightCoreset2027.Euclidean

open scoped BigOperators
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000
namespace TightCoreset2027.Euclidean

lemma generalCenter_norm_le {n m L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (v : ProjectionSpace L) (hv : ‖v‖ ^ 2 = 2) (σ : SignArray n m)
    (i : Fin m) (ℓ : Fin (L + 1)) :
    ‖localCenter δ v σ i ℓ‖ ≤ 3 * Real.sqrt (n : ℝ) := by
  have hδ1 := (hδ ℓ).2.trans (displacement2_bounds hL ℓ).2
  have hh := localCenter_norm_sq δ v hv σ i ℓ
    (center_radicand_bounds hn hL ℓ _ (hδ ℓ).1.le hδ1).1
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
  obtain ⟨hs1, hsn⟩ := sqrt_nat_bounds hn
  have ht := gridValue_sq_le_one hL ℓ
  have hp := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg (n : ℝ))
  nlinarith [norm_nonneg (localCenter δ v σ i ℓ)]

lemma general_distance_sq {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (j : Fin n) (i i' : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m)
    (ℓ ℓ' : Fin (L + 1)) (hℓ : G.level s v = ℓ) :
    dist (localPoint G j i s) (localCenter δ v σ i' ℓ') ^ 2 =
      baseline n L ℓ + Real.sqrt (n : ℝ) * (gridValue L ℓ' - gridValue L ℓ) ^ 2 +
        (if i = i' then 0 else 4 * Real.sqrt (n : ℝ)) +
        2 * Real.sqrt (n : ℝ) * (-1 : ℝ) ^ ℓ'.val * δ ℓ' * signValue (σ j i') := by
  apply localPoint_dist_sq_localCenter G hG j i i' s δ v hv σ ℓ ℓ' hℓ
  exact (center_radicand_bounds hn hL ℓ' _ (hδ ℓ').1.le
    ((hδ ℓ').2.trans (displacement2_bounds hL ℓ').2)).1

lemma general_perturbation_bound {n L : ℕ} (δ : Fin (L + 1) → ℝ)
    (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (ℓ : Fin (L + 1)) (b : Bool) :
    |2 * Real.sqrt (n : ℝ) * (-1 : ℝ) ^ ℓ.val * δ ℓ * signValue b| ≤
      Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) := by
  rw [abs_mul, signValue_abs, mul_one, abs_mul, abs_of_pos (hδ ℓ).1,
    abs_mul, abs_pow]
  norm_num
  rw [abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
  have hh := mul_le_mul_of_nonneg_left (hδ ℓ).2 (by positivity : 0 ≤ 2 * Real.sqrt (n : ℝ))
  dsimp [displacement2] at hh
  exact hh.trans_eq (by ring)

lemma general_active_center_strict {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (j : Fin n) (i i' : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) (ℓ ℓ' : Fin (L + 1))
    (hℓ : G.level s v = ℓ) (hdiff : (i', ℓ') ≠ (i, ℓ)) :
    dist (localPoint G j i s) (localCenter δ v σ i ℓ) <
      dist (localPoint G j i s) (localCenter δ v σ i' ℓ') := by
  have h1 := general_distance_sq G hG hn hL δ hδ j i i s v hv σ ℓ ℓ hℓ
  have h2 := general_distance_sq G hG hn hL δ hδ j i i' s v hv σ ℓ ℓ' hℓ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsn : 0 < Real.sqrt (n : ℝ) := by positivity
  have hLp : 0 < (L : ℝ) ^ 2 := by positivity
  have hnoise1 := general_perturbation_bound (n := n) δ hδ ℓ (σ j i)
  have hnoise2 := general_perturbation_bound (n := n) δ hδ ℓ' (σ j i')
  obtain ⟨hn1lo, hn1hi⟩ := abs_le.mp hnoise1
  obtain ⟨hn2lo, hn2hi⟩ := abs_le.mp hnoise2
  have hpenalty : 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 ≤
      Real.sqrt (n : ℝ) * (gridValue L ℓ' - gridValue L ℓ) ^ 2 +
        (if i = i' then 0 else 4 * Real.sqrt (n : ℝ)) := by
    by_cases hi : i = i'
    · have hne : ℓ' ≠ ℓ := by intro heq; exact hdiff (Prod.ext hi.symm heq)
      have hh := mul_le_mul_of_nonneg_left (gridValue_difference_lower hL ℓ ℓ' hne) hsn.le
      have hhh : 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 ≤
          Real.sqrt (n : ℝ) * (gridValue L ℓ' - gridValue L ℓ) ^ 2 := by
        calc
          _ = Real.sqrt (n : ℝ) * (4 / (L : ℝ) ^ 2) := by ring
          _ ≤ _ := hh
      simpa [hi] using hhh
    · rw [if_neg hi]
      have hh : 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 ≤ 4 * Real.sqrt (n : ℝ) := by
        apply (div_le_iff₀ hLp).mpr
        nlinarith [mul_nonneg hsn.le (show 0 ≤ (L : ℝ) ^ 2 - 1 by nlinarith)]
      nlinarith [mul_nonneg hsn.le (sq_nonneg (gridValue L ℓ' - gridValue L ℓ))]
  have hpos : 0 < 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 -
      2 * (Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2)) := by
    have : 0 < Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 := div_pos hsn hLp
    rw [show 4 * Real.sqrt (n : ℝ) / (L : ℝ) ^ 2 -
      2 * (Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2)) =
        (15 / 4 : ℝ) * (Real.sqrt (n : ℝ) / (L : ℝ) ^ 2) by ring]
    positivity
  have hsq : dist (localPoint G j i s) (localCenter δ v σ i ℓ) ^ 2 <
      dist (localPoint G j i s) (localCenter δ v σ i' ℓ') ^ 2 := by
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, if_true, add_zero] at h1
    linarith
  nlinarith [dist_nonneg (x := localPoint G j i s) (y := localCenter δ v σ i ℓ),
    dist_nonneg (x := localPoint G j i s) (y := localCenter δ v σ i' ℓ')]

lemma general_active_unique_nearest {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (b : Fin B) (j : Fin n) (i : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) (ℓ : Fin (L + 1))
    (hℓ : G.level s v = ℓ) :
    IsUniqueNearest (dataPoint G b.val j i s)
      (queryCenters B n m L k b δ v σ)
      (activeCenter b.val δ v σ i ℓ) := by
  classical
  refine ⟨activeCenter_mem_query b _ v σ i ℓ, ?_⟩
  intro c hc hne
  change c ∈ _ ∪ _ ∪ _ at hc
  rcases Finset.mem_union.mp hc with hac|hpc
  · rcases Finset.mem_union.mp hac with hac|hic
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hac
      have ha : a ≠ (i, ℓ) := by intro h; subst a; exact hne rfl
      simpa only [dataPoint, activeCenter, dist_add_left] using
        general_active_center_strict G hG hn hL δ hδ j i a.1 s v hv σ ℓ a.2 hℓ ha
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hic
      have hbb : b.val ≠ a.1.val := by
        intro h
        exact (Finset.mem_filter.mp ha).2 (Fin.ext h.symm)
      exact within_cross_lt hn b.val a.1.val hbb _ _ _
        (localPoint_norm_le G hG hn j i s)
        (generalCenter_norm_le hn hL δ hδ v (hG.2.2.2.1 v hv) σ i ℓ)
        (sphereCenter_norm_le a.2)
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hpc
    have hbb : b.val ≠ B + 1 + r := by have := b.isLt; omega
    have hh := within_cross_lt hn b.val (B + 1 + r) hbb
      (localPoint G j i s) (localCenter δ v σ i ℓ) 0
      (localPoint_norm_le G hG hn j i s)
      (generalCenter_norm_le hn hL δ hδ v (hG.2.2.2.1 v hv) σ i ℓ)
      (by simp)
    simpa only [add_zero, dataPoint, activeCenter, paddingPoint, copyTranslation] using hh

lemma general_inactive_query_distance_sq {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (b b' : Fin B) (hbb : b' ≠ b) (j : Fin n) (i : Fin m) (s : Fin q)
    (v : ProjectionSpace L) (hv : v ∈ G.directions) (σ : SignArray n m) :
    nearestDistance (dataPoint G b'.val j i s) (queryCenters B n m L k b δ v σ) ^ 2 = 2 := by
  classical
  have heq : nearestDistance (dataPoint G b'.val j i s) (queryCenters B n m L k b δ v σ) =
      dist (dataPoint G b'.val j i s) (inactiveCenter n m L b'.val j) := by
    apply nearestDistance_eq_of_min _ _ _ (inactiveCenter_mem_query b b' hbb _ v σ j)
    intro c hc
    change c ∈ _ ∪ _ ∪ _ at hc
    rcases Finset.mem_union.mp hc with hac|hpc
    · rcases Finset.mem_union.mp hac with hac|hic
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hac
        have hneq : b'.val ≠ b.val := fun h => hbb (Fin.ext h)
        exact (within_cross_lt hn b'.val b.val hneq _ _ _
          (localPoint_norm_le G hG hn j i s) (sphereCenter_norm_le j)
          (generalCenter_norm_le hn hL δ hδ v (hG.2.2.2.1 v hv) σ a.1 a.2)).le
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hic
        by_cases hh : a.1 = b'
        · have h1 := localPoint_dist_sphere_sq G hG j j i s
          have h2 := localPoint_dist_sphere_sq G hG j a.2 i s
          simp only [if_true, add_zero] at h1
          simp only [dataPoint, inactiveCenter, hh, dist_add_left]
          have hle : (0 : ℝ) ≤ if j = a.2 then 0 else 2 * (n : ℝ) := by split_ifs <;> positivity
          nlinarith [dist_nonneg (x := localPoint G j i s)
            (y := Real.sqrt (n : ℝ) • sphereAxis (m := m) (L := L) j),
            dist_nonneg (x := localPoint G j i s)
            (y := Real.sqrt (n : ℝ) • sphereAxis (m := m) (L := L) a.2)]
        · have hneq : b'.val ≠ a.1.val := fun h => hh (Fin.ext h.symm)
          exact (within_cross_lt hn b'.val a.1.val hneq _ _ _
            (localPoint_norm_le G hG hn j i s) (sphereCenter_norm_le j)
            (sphereCenter_norm_le a.2)).le
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hpc
      have hneq : b'.val ≠ B + 1 + r := by have := b'.isLt; omega
      have hh := within_cross_lt hn b'.val (B + 1 + r) hneq (localPoint G j i s)
        (Real.sqrt (n : ℝ) • sphereAxis (m := m) (L := L) j) 0
        (localPoint_norm_le G hG hn j i s) (sphereCenter_norm_le j) (by simp)
      exact (by simpa only [add_zero, dataPoint, inactiveCenter, paddingPoint, copyTranslation] using hh.le)
  rw [heq]
  simpa only [dataPoint, inactiveCenter, dist_add_left, if_true, add_zero] using
    localPoint_dist_sphere_sq G hG j j i s


lemma general_prescribed_cost_bounds {n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (j : Fin n) (i : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) (ℓ : Fin (L + 1))
    (hℓ : G.level s v = ℓ) :
    5 * (n : ℝ) ≤ dist (localPoint G j i s) (localCenter δ v σ i ℓ) ^ 2 ∧
    dist (localPoint G j i s) (localCenter δ v σ i ℓ) ^ 2 ≤ 9 * (n : ℝ) := by
  rw [general_distance_sq G hG hn hL δ hδ j i i s v hv σ ℓ ℓ hℓ]
  simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, if_true, add_zero]
  obtain ⟨hlo, hhi⟩ := abs_le.mp (general_perturbation_bound (n := n) δ hδ ℓ (σ j i))
  have hw := baseline_window hn hL ℓ
  constructor <;> linarith

lemma general_active_query_costs {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (b : Fin B) (j : Fin n) (i : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) (ℓ : Fin (L + 1))
    (hℓ : G.level s v = ℓ) :
    IsUniqueNearest (dataPoint G b.val j i s) (queryCenters B n m L k b δ v σ)
        (activeCenter b.val δ v σ i ℓ) ∧
      nearestDistance (dataPoint G b.val j i s) (queryCenters B n m L k b δ v σ) ^ 2 =
        baseline n L ℓ + 2 * Real.sqrt (n : ℝ) * (-1 : ℝ) ^ ℓ.val * δ ℓ * signValue (σ j i) ∧
      5 * (n : ℝ) ≤ nearestDistance (dataPoint G b.val j i s) (queryCenters B n m L k b δ v σ) ^ 2 ∧
      nearestDistance (dataPoint G b.val j i s) (queryCenters B n m L k b δ v σ) ^ 2 ≤ 9 * (n : ℝ) := by
  have hu := general_active_unique_nearest (k := k) G hG hn hL δ hδ b j i s v hv σ ℓ hℓ
  refine ⟨hu, ?_⟩
  rw [nearestDistance_eq_of_unique _ _ _ hu]
  simp only [dataPoint, activeCenter, dist_add_left]
  refine ⟨?_, general_prescribed_cost_bounds G hG hn hL δ hδ j i s v hv σ ℓ hℓ⟩
  rw [general_distance_sq G hG hn hL δ hδ j i i s v hv σ ℓ ℓ hℓ]
  simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, if_true, add_zero]

lemma displacementZ_calibrates (z : ℝ) (hz : 1 ≤ z) (n L : ℕ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (ℓ : Fin (L + 1)) :
    CalibratesPower z n L ℓ (displacementZ z n L ℓ) := by
  have hex := (calibration_exists_unique z hz n L hn hL ℓ).exists
  unfold displacementZ
  rw [dif_pos hex]
  exact Classical.choose_spec hex

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

lemma calibrated_paired_difference {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (z : ℝ) (hz : 1 ≤ z) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hcal : ∀ ℓ, CalibratesPower z n L ℓ (δ ℓ))
    (b : Fin B) (j : Fin n) (i : Fin m) (s : Fin q) (v : ProjectionSpace L)
    (hv : v ∈ G.directions) (σ : SignArray n m) :
    (nearestDistance (dataPoint G b.val j i s) (queryCenters B n m L k b δ v σ)) ^ z -
      (nearestDistance (dataPoint G b.val j i s)
        (queryCenters B n m L k b δ v (fun j i => !(σ j i)))) ^ z =
      ((n : ℝ) ^ ((z - 1) / 2) / (32 * (L : ℝ) ^ 2)) * signValue (σ j i) *
        (-1 : ℝ) ^ (G.level s v).val := by
  have hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ := fun ℓ => ⟨(hcal ℓ).1, (hcal ℓ).2.1⟩
  rw [distance_power_via_square _ z (nearestDistance_nonneg _ _),
    distance_power_via_square _ z (nearestDistance_nonneg _ _)]
  rw [(general_active_query_costs G hG hn hL δ hδ b j i s v hv σ _ rfl).2.1,
    (general_active_query_costs G hG hn hL δ hδ b j i s v hv (fun j i => !(σ j i)) _ rfl).2.1]
  rw [signValue_not]
  let η : ℝ := signValue (σ j i) * (-1 : ℝ) ^ (G.level s v).val
  have hsquare : η ^ 2 = 1 := by
    dsimp [η]
    rw [mul_pow, signValue_sq, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have heq := (hcal (G.level s v)).2.2
  simp only [Real.rpow_eq_pow] at heq
  have hleft : 2 * Real.sqrt (n : ℝ) * (-1 : ℝ) ^ (G.level s v).val * δ (G.level s v) * signValue (σ j i) =
      2 * Real.sqrt (n : ℝ) * δ (G.level s v) * η := by dsimp [η]; ring
  have hright : 2 * Real.sqrt (n : ℝ) * (-1 : ℝ) ^ (G.level s v).val * δ (G.level s v) * -signValue (σ j i) =
      -(2 * Real.sqrt (n : ℝ) * δ (G.level s v) * η) := by dsimp [η]; ring
  rw [hleft, hright]
  rw [show ((n : ℝ) ^ ((z - 1) / 2) / (32 * (L : ℝ) ^ 2)) * signValue (σ j i) *
      (-1 : ℝ) ^ (G.level s v).val =
      ((n : ℝ) ^ ((z - 1) / 2) / (32 * (L : ℝ) ^ 2)) * η by dsimp [η]; ring]
  rcases sq_eq_one_iff.mp hsquare with hη|hη
  · simp only [hη, mul_one, ← sub_eq_add_neg]
    exact heq
  · simp only [hη, mul_neg_one, neg_neg, mul_neg_one, ← sub_eq_add_neg]
    linarith

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
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000
namespace TightCoreset2027.Euclidean

lemma small_copy_exists_B {B n m L q : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (hn : 1 ≤ n) (hB : 1 ≤ B)
    (S : Finset (ConstructionSpace n m L)) (hsubset : S ⊆ dataset B n m G)
    (hhalf : 2 * S.card ≤ (dataset B n m G).card) :
    ∃ b : Fin B, 2 * (S ∩ dataCopy n m G b.val).card ≤ (dataCopy n m G b.val).card := by
  classical
  have hdisj : (↑(Finset.range B) : Set ℕ).PairwiseDisjoint (fun r => S ∩ dataCopy n m G r) := by
    intro r hr r' hr' hrr
    exact (dataCopy_disjoint G hG hn hrr).mono Finset.inter_subset_right Finset.inter_subset_right
  have hparts : (Finset.range B).biUnion (fun r => S ∩ dataCopy n m G r) = S := by
    rw [← Finset.inter_biUnion]
    exact Finset.inter_eq_left.mpr hsubset
  have hcard : (∑ r ∈ Finset.range B, (S ∩ dataCopy n m G r).card) = S.card := by
    rw [← Finset.card_biUnion hdisj, hparts]
  by_contra! hbad
  have hslt : (∑ r ∈ Finset.range B, (dataCopy n m G r).card) <
      ∑ r ∈ Finset.range B, 2 * (S ∩ dataCopy n m G r).card := Finset.sum_lt_sum_of_nonempty
    (Finset.nonempty_range_iff.mpr (show B ≠ 0 by omega))
    (fun r (hr : r ∈ Finset.range B) => hbad (⟨r, Finset.mem_range.mp hr⟩ : Fin B))
  simp only [dataCopy_card G hG hn, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum, hcard] at hslt
  rw [dataset_card G hG hn B] at hhalf
  norm_cast at hslt
  simp only [Nat.mul_assoc] at hslt hhalf
  omega


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

lemma inactive_power {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (z : ℝ) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (b b' : Fin B) (hbb : b' ≠ b) (j : Fin n) (i : Fin m) (s : Fin q)
    (v : ProjectionSpace L) (hv : v ∈ G.directions) (σ : SignArray n m) :
    (nearestDistance (dataPoint G b'.val j i s) (queryCenters B n m L k b δ v σ)) ^ z =
      (2 : ℝ) ^ (z / 2) := by
  rw [distance_power_via_square _ z (nearestDistance_nonneg _ _),
    general_inactive_query_distance_sq G hG hn hL δ hδ b b' hbb j i s v hv σ]

lemma calibrated_error_identity {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (z : ℝ) (hz : 1 ≤ z) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hcal : ∀ ℓ, CalibratesPower z n L ℓ (δ ℓ))
    (S : Finset (ConstructionSpace n m L)) (w : ConstructionSpace n m L → NNReal)
    (hsubset : S ⊆ dataset B n m G) (b : Fin B)
    (v : ProjectionSpace L) (hv : v ∈ G.directions) (σ : SignArray n m) :
    (weightedCost z S w (queryCenters B n m L k b δ v σ) -
      cost z (dataset B n m G) (queryCenters B n m L k b δ v σ)) -
    (weightedCost z S w (queryCenters B n m L k b δ v (fun j i => !(σ j i))) -
      cost z (dataset B n m G) (queryCenters B n m L k b δ v (fun j i => !(σ j i)))) =
      ((n : ℝ) ^ ((z - 1) / 2) / (32 * (L : ℝ) ^ 2)) *
        (∑ j, ∑ i, signValue (σ j i) *
          (∑ s, errorCoeff S w (dataPoint G b.val j i s) * (-1 : ℝ) ^ (G.level s v).val)) := by
  classical
  have hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ := fun ℓ => ⟨(hcal ℓ).1, (hcal ℓ).2.1⟩
  let Cplus := queryCenters B n m L k b δ v σ
  let Cminus := queryCenters B n m L k b δ v (fun j i => !(σ j i))
  rw [error_as_sum_power z _ _ _ hsubset, error_as_sum_power z _ _ _ hsubset, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hcopy (r : ℕ) (hr : r ∈ Finset.range B) :
      (∑ p ∈ dataCopy n m G r, errorCoeff S w p *
        (nearestDistance p Cplus ^ z - nearestDistance p Cminus ^ z)) =
      if r = b.val then
        ((n : ℝ) ^ ((z - 1) / 2) / (32 * (L : ℝ) ^ 2)) *
          (∑ j, ∑ i, signValue (σ j i) *
            (∑ s, errorCoeff S w (dataPoint G b.val j i s) * (-1 : ℝ) ^ (G.level s v).val))
      else 0 := by
    by_cases hrb : r = b.val
    · rw [if_pos hrb, hrb]
      unfold dataCopy
      rw [Finset.sum_image]
      · dsimp only [Cplus, Cminus]
        simp only [Fintype.sum_prod_type]
        simp_rw [calibrated_paired_difference G hG z hz hn hL δ hcal b _ _ _ v hv σ]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro s hs
        ring
      · intro a ha a' ha' heq
        obtain ⟨_, hj, hi, hs⟩ := dataPoint_inj G hG hn heq
        exact Prod.ext hj (Prod.ext hi hs)
    · rw [if_neg hrb]
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      let b' : Fin B := ⟨r, Finset.mem_range.mp hr⟩
      have hb' : b' ≠ b := fun h => hrb (congrArg Fin.val h)
      have hplus := inactive_power (k := k) G hG z hn hL δ hδ b b' hb' a.1 a.2.1 a.2.2 v hv σ
      have hminus := inactive_power (k := k) G hG z hn hL δ hδ b b' hb' a.1 a.2.1 a.2.2 v hv (fun j i => !(σ j i))
      change errorCoeff S w _ * (_ - _) = 0
      rw [show nearestDistance (dataPoint G r a.1 a.2.1 a.2.2) Cplus ^ z = (2 : ℝ) ^ (z / 2) from hplus,
        show nearestDistance (dataPoint G r a.1 a.2.1 a.2.2) Cminus ^ z = (2 : ℝ) ^ (z / 2) from hminus]
      ring
  unfold dataset
  rw [Finset.sum_biUnion]
  · change (∑ r ∈ Finset.range B, ∑ p ∈ dataCopy n m G r, errorCoeff S w p *
      (nearestDistance p Cplus ^ z - nearestDistance p Cminus ^ z)) = _
    apply Eq.trans (Finset.sum_congr rfl (fun r hr => hcopy r hr))
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr b.isLt)]
  · intro r hr r' hr' hrr
    exact dataCopy_disjoint G hG hn hrr


lemma copyCountZ_bounds (z : ℝ) (hz : 1 ≤ z) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (z / 2) ≤ (copyCountZ z n : ℝ) ∧
      (copyCountZ z n : ℝ) ≤ 2 * (n : ℝ) ^ (z / 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ (z / 2) := Real.one_le_rpow hnR (by linarith)
  unfold copyCountZ
  simp only [Real.rpow_eq_pow]
  constructor
  · exact Nat.le_ceil _
  · have hh := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ (z / 2) by positivity)
    linarith

lemma copyCountZ_pos (z : ℝ) (hz : 1 ≤ z) (n : ℕ) (hn : 1 ≤ n) : 1 ≤ copyCountZ z n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ (z / 2) := Real.one_le_rpow hnR (by linarith)
  have h := (copyCountZ_bounds z hz n hn).1
  have : (1 : ℝ) ≤ copyCountZ z n := hp.trans h
  exact_mod_cast this

lemma general_query_total_cost {B n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (z : ℝ) (hz : 1 ≤ z) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (δ : Fin (L + 1) → ℝ) (hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ)
    (b : Fin B) (v : ProjectionSpace L) (hv : v ∈ G.directions) (σ : SignArray n m) :
    cost z (dataset B n m G) (queryCenters B n m L k b δ v σ) ≤
      ((B : ℝ) * (2 : ℝ) ^ (z / 2) + (9 * (n : ℝ)) ^ (z / 2)) *
        ((n : ℝ) * (m : ℝ) * (q : ℝ)) := by
  classical
  let C := queryCenters B n m L k b δ v σ
  have hα : 0 ≤ z / 2 := by linarith
  have hcopy (r : ℕ) (hr : r ∈ Finset.range B) :
      (∑ p ∈ dataCopy n m G r, (nearestDistance p C) ^ z) ≤
        (2 : ℝ) ^ (z / 2) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) +
          if r = b.val then (9 * (n : ℝ)) ^ (z / 2) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) else 0 := by
    have hp (p : ConstructionSpace n m L) (hp : p ∈ dataCopy n m G r) :
        (nearestDistance p C) ^ z ≤ if r = b.val then (9 * (n : ℝ)) ^ (z / 2) else (2 : ℝ) ^ (z / 2) := by
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      by_cases hh : r = b.val
      · rw [if_pos hh, hh]
        rw [distance_power_via_square _ z (nearestDistance_nonneg _ _)]
        exact Real.rpow_le_rpow (sq_nonneg _)
          (general_active_query_costs (k := k) G hG hn hL δ hδ b a.1 a.2.1 a.2.2 v hv σ _ rfl).2.2.2 hα
      · rw [if_neg hh]
        let b' : Fin B := ⟨r, Finset.mem_range.mp hr⟩
        have hb' : b' ≠ b := fun h => hh (congrArg Fin.val h)
        exact (inactive_power (k := k) G hG z hn hL δ hδ b b' hb' a.1 a.2.1 a.2.2 v hv σ).le
    have hh := Finset.sum_le_card_nsmul (dataCopy n m G r) (fun p => (nearestDistance p C) ^ z)
      (if r = b.val then (9 * (n : ℝ)) ^ (z / 2) else (2 : ℝ) ^ (z / 2)) hp
    rw [nsmul_eq_mul, dataCopy_card G hG hn, Nat.cast_mul, Nat.cast_mul] at hh
    by_cases hrb : r = b.val
    · simp only [hrb, if_true] at hh ⊢
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ (z / 2) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) by positivity]
    · simpa [hrb, mul_comm] using hh
  unfold cost dataset
  simp only [Real.rpow_eq_pow]
  rw [Finset.sum_biUnion]
  · have hh := Finset.sum_le_sum hcopy
    have heq : (∑ r ∈ Finset.range B,
        ((2 : ℝ) ^ (z / 2) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) +
          (if r = b.val then (9 * (n : ℝ)) ^ (z / 2) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) else 0))) =
        ((B : ℝ) * (2 : ℝ) ^ (z / 2) + (9 * (n : ℝ)) ^ (z / 2)) * ((n : ℝ) * (m : ℝ) * (q : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr b.isLt)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hh.trans_eq heq
  · intro r hr r' hr' hrr
    exact dataCopy_disjoint G hG hn hrr

lemma calibrated_query_total_cost {n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionGeometry G) (z : ℝ) (hz : 1 ≤ z) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (b : Fin (copyCountZ z n)) (v : ProjectionSpace L) (hv : v ∈ G.directions) (σ : SignArray n m) :
    cost z (datasetZ z n m G) (queryCentersZ z n m L k b v σ) ≤
      ((2 : ℝ) ^ (z / 2) + (9 : ℝ) ^ (z / 2)) *
        ((copyCountZ z n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) := by
  have hδ : ∀ ℓ, 0 < displacementZ z n L ℓ ∧ displacementZ z n L ℓ ≤ displacement2 L ℓ :=
    fun ℓ => ⟨(displacementZ_calibrates z hz n L hn hL ℓ).1, (displacementZ_calibrates z hz n L hn hL ℓ).2.1⟩
  have hh := general_query_total_cost (k := k) G hG z hz hn hL _ hδ b v hv σ
  have hb := (copyCountZ_bounds z hz n hn).1
  have h9 : (9 * (n : ℝ)) ^ (z / 2) ≤ (9 : ℝ) ^ (z / 2) * (copyCountZ z n : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) (by positivity : (0 : ℝ) ≤ n)]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hmul := mul_le_mul_of_nonneg_right h9 (show 0 ≤ (n : ℝ) * (m : ℝ) * (q : ℝ) by positivity)
  dsimp [datasetZ, queryCentersZ]
  nlinarith

lemma calibrated_dataset_not_half_coreset {n m L q k : ℕ} (G : ProjectionFamily L q)
    (hG : ProjectionSpecification G) (z : ℝ) (hz : 1 ≤ z)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hbudget : n * (copyCountZ z n - 1) + m * (L + 1) ≤ k)
    (ε : ℝ) (hε : 0 < ε)
    (herror : ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2 <
      1 / (512 * Real.sqrt 3 * ((2 : ℝ) ^ (z / 2) + (9 : ℝ) ^ (z / 2))))
    (S : Finset (ConstructionSpace n m L)) (w : ConstructionSpace n m L → NNReal)
    (hhalf : 2 * S.card ≤ (datasetZ z n m G).card) :
    ¬ IsStrongCoreset z ε k (datasetZ z n m G) S w := by
  classical
  intro hco
  let B := copyCountZ z n
  let R : ℝ := (n : ℝ) * (m : ℝ) * (q : ℝ)
  let P : ℝ := (n : ℝ) ^ ((z - 1) / 2)
  let C : ℝ := (2 : ℝ) ^ (z / 2) + (9 : ℝ) ^ (z / 2)
  let sn := Real.sqrt (n : ℝ)
  let sq := Real.sqrt (q : ℝ)
  let δ := displacementZ z n L
  have hcal : ∀ ℓ, CalibratesPower z n L ℓ (δ ℓ) := displacementZ_calibrates z hz n L hn hL
  have hB : 1 ≤ B := copyCountZ_pos z hz n hn
  have hsn : 0 < sn := by dsimp [sn]; positivity
  have hsq : 0 < sq := by dsimp [sq]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hLs : 0 < (L : ℝ) ^ 2 := by positivity
  obtain ⟨b, hb⟩ := small_copy_exists_B G hG.1 hn hB S hco.1 hhalf
  obtain ⟨v, hv, hdisc⟩ := omission_discrepancy_direction G hG hn hm S w b.val hb
  let H : Fin n → Fin m → ℝ := fun j i =>
    ∑ s, errorCoeff S w (dataPoint G b.val j i s) * (-1 : ℝ) ^ (G.level s v).val
  let σ : SignArray n m := fun j i => decide (0 ≤ H j i)
  let σminus : SignArray n m := fun j i => !(σ j i)
  let Cplus := queryCenters B n m L k b δ v σ
  let Cminus := queryCenters B n m L k b δ v σminus
  let ΔP := weightedCost z S w Cplus - cost z (dataset B n m G) Cplus
  let ΔM := weightedCost z S w Cminus - cost z (dataset B n m G) Cminus
  have hidentity : ΔP - ΔM = P / (32 * (L : ℝ) ^ 2) * (∑ j, ∑ i, |H j i|) := by
    have hh := calibrated_error_identity (k := k) G hG.1 z hz hn hL δ hcal S w hco.1 b v hv σ
    dsimp [ΔP, ΔM, Cplus, Cminus, σminus]
    rw [hh]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    exact signValue_decide_mul (H j i)
  have hδ : ∀ ℓ, 0 < δ ℓ ∧ δ ℓ ≤ displacement2 L ℓ := fun ℓ => ⟨(hcal ℓ).1, (hcal ℓ).2.1⟩
  have hcardP : Cplus.card = k := queryCenters_card hn hL b δ v (hG.1.2.2.2.1 v hv) σ hbudget
  have hcardM : Cminus.card = k := queryCenters_card hn hL b δ v (hG.1.2.2.2.1 v hv) σminus hbudget
  have hcP : cost z (dataset B n m G) Cplus ≤ C * (B : ℝ) * R := by
    have hh := calibrated_query_total_cost (k := k) G hG.1 z hz hn hL b v hv σ
    simpa only [C, R, B, Cplus, Cminus, δ, datasetZ, queryCentersZ, mul_assoc] using hh
  have hcM : cost z (dataset B n m G) Cminus ≤ C * (B : ℝ) * R := by
    have hh := calibrated_query_total_cost (k := k) G hG.1 z hz hn hL b v hv σminus
    simpa only [C, R, B, Cplus, Cminus, δ, datasetZ, queryCentersZ, mul_assoc] using hh
  have habsP : |ΔP| ≤ ε * (C * (B : ℝ) * R) :=
    (hco.2 Cplus hcardP).trans (mul_le_mul_of_nonneg_left hcP hε.le)
  have habsM : |ΔM| ≤ ε * (C * (B : ℝ) * R) :=
    (hco.2 Cminus hcardM).trans (mul_le_mul_of_nonneg_left hcM hε.le)
  have hgap : ΔP - ΔM ≤ 2 * ε * C * (B : ℝ) * R := by
    nlinarith [le_abs_self ΔP, neg_le_abs ΔM]
  have hdisc' : R / 2 ≤ Real.sqrt 3 * sq * (∑ j, ∑ i, |H j i|) := hdisc
  have hmul := mul_le_mul_of_nonneg_left hdisc'
    (show 0 ≤ P / (32 * (L : ℝ) ^ 2) by positivity)
  have hsumgap : (P * R) / (64 * (L : ℝ) ^ 2) ≤ Real.sqrt 3 * sq * (ΔP - ΔM) := by
    rw [hidentity]
    calc
      _ = (P / (32 * (L : ℝ) ^ 2)) * (R / 2) := by ring
      _ ≤ _ := hmul
      _ = _ := by ring
  have hraw : P * R ≤ (Real.sqrt 3 * sq * (2 * ε * C * (B : ℝ) * R)) * (64 * (L : ℝ) ^ 2) := by
    have hh := hsumgap.trans (mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ Real.sqrt 3 * sq))
    exact (div_le_iff₀ (by positivity : 0 < 64 * (L : ℝ) ^ 2)).mp hh
  have hpower : P * sn = (n : ℝ) ^ (z / 2) := by
    dsimp [P, sn]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : (0 : ℝ) < n)]
    congr 1
    ring
  have hBbound : (B : ℝ) ≤ 2 * (P * sn) := by rw [hpower]; exact (copyCountZ_bounds z hz n hn).2
  have hbmul := mul_le_mul_of_nonneg_left hBbound
    (show 0 ≤ Real.sqrt 3 * sq * 2 * ε * C * R * (64 * (L : ℝ) ^ 2) by positivity)
  have hnorm : (P * R) * 1 ≤ (P * R) * (256 * ε * C * sn * Real.sqrt 3 * sq * (L : ℝ) ^ 2) := by
    nlinarith [hraw, hbmul]
  have hbig : 1 ≤ 256 * ε * C * sn * Real.sqrt 3 * sq * (L : ℝ) ^ 2 :=
    le_of_mul_le_mul_left hnorm (mul_pos hP hR)
  have hsmall : (ε * sn * sq * (L : ℝ) ^ 2) * (512 * Real.sqrt 3 * C) < 1 := by
    apply (lt_div_iff₀ (by positivity : 0 < 512 * Real.sqrt 3 * C)).mp
    simpa only [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ n), C, sn, sq, mul_assoc] using herror
  nlinarith

 theorem power_obstruction_proof (z : ℝ) (hz : 1 ≤ z) :
    ∃ A : ℝ, 0 < A ∧ ∀ n m L q k : ℕ,
      1 ≤ n → 1 ≤ m → 1 ≤ L → 1 ≤ q →
      q + Nat.choose q 3 < 2 ^ L →
      n * (copyCountZ z n - 1) + m * (L + 1) ≤ k →
      ∃ d : ℕ, 1 ≤ d ∧ ∃ X : Finset (Point d),
        X.card = copyCountZ z n * n * m * q ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2 < A →
          ∀ (S : Finset (Point d)) (w : Point d → NNReal),
            IsStrongCoreset z ε k X S w → (X.card : ℝ) / 2 < (S.card : ℝ) := by
  classical
  refine ⟨1 / (512 * Real.sqrt 3 * ((2 : ℝ) ^ (z / 2) + (9 : ℝ) ^ (z / 2))), by positivity, ?_⟩
  intro n m L q k hn hm hL hq hcode hbudget
  obtain ⟨G, hG⟩ := discrete_projections_discrepancy L q hL hq hcode
  let I := Fin n ⊕ (Fin m ⊕ (Fin (2 * L) ⊕ Unit))
  let d := Fintype.card I
  let e : ConstructionSpace n m L ≃ᵢ Point d :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin I)).toIsometryEquiv
  let Y := datasetZ z n m G
  let X := Y.image e
  have hd : 1 ≤ d := by dsimp [d]; exact Nat.succ_le_of_lt Fintype.card_pos
  have hXY : X.card = Y.card := Finset.card_image_of_injective _ e.injective
  have hYcard : Y.card = copyCountZ z n * n * m * q := dataset_card G hG.1 hn _
  refine ⟨d, hd, X, hXY.trans hYcard, ?_⟩
  intro ε hε hε1 herror S w hco
  let S' := S.image e.symm
  have hSS : (S'.image e) = S := by simpa only [S'] using image_symm_image e S
  have hpull : IsStrongCoreset z ε k Y S' (fun p => w (e p)) := by
    apply coreset_pullback e z ε k Y S' w
    rw [hSS]
    exact hco
  have hScard : S'.card = S.card := Finset.card_image_of_injective _ e.symm.injective
  by_contra! hsize
  have hsizeR : 2 * (S.card : ℝ) ≤ (Y.card : ℝ) := by rw [← hXY]; nlinarith
  have hhalf : 2 * S'.card ≤ Y.card := by rw [hScard]; exact_mod_cast hsizeR
  exact calibrated_dataset_not_half_coreset G hG z hz hn hm hL hq hbudget ε hε herror S'
    (fun p => w (e p)) hhalf hpull

end TightCoreset2027.Euclidean
open TightCoreset2027.Euclidean

 theorem solution (z : ℝ) (hz : 1 ≤ z) :
    ∃ A : ℝ, 0 < A ∧ ∀ n m L q k : ℕ,
      1 ≤ n → 1 ≤ m → 1 ≤ L → 1 ≤ q →
      q + Nat.choose q 3 < 2 ^ L →
      n * (copyCountZ z n - 1) + m * (L + 1) ≤ k →
      ∃ d : ℕ, 1 ≤ d ∧ ∃ X : Finset (Point d),
        X.card = copyCountZ z n * n * m * q ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2 < A →
          ∀ (S : Finset (Point d)) (w : Point d → NNReal),
            IsStrongCoreset z ε k X S w → (X.card : ℝ) / 2 < (S.card : ℝ) := by
  exact TightCoreset2027.Euclidean.power_obstruction_proof z hz
