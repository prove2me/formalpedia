-- Prove2me | solution 1 for TightCoreset2027.Euclidean.nearest_centers_and_costs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:24:27.511982+00:00
-- url     : https://prove2.me/submissions/96ac18d4-187b-4292-aeaa-1fabb73d09f3

import Definitions.Def_TightCoreset2027_Euclidean_queryConstruction
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

open TightCoreset2027.Euclidean


theorem solution (n m L q k : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hcode : q + Nat.choose q 3 < 2 ^ L)
    (G : ProjectionFamily L q) (hG : ProjectionSpecification G)
    (hbudget : n * (n - 1) + m * (L + 1) ≤ k) :
    ∀ (b : Fin n) (v : ProjectionSpace L), v ∈ G.directions →
      ∀ σ : SignArray n m,
        let C := queryCenters n n m L k b (displacement2 L) v σ
        let X := dataset n n m G
        C.card = k ∧ X.card = n * n * m * q ∧
        (∀ (j : Fin n) (i : Fin m) (ℓ : Fin (L + 1)) (s : Fin q),
          G.level s v = ℓ →
            IsUniqueNearest (dataPoint G b.val j i s) C
              (activeCenter b.val (displacement2 L) v σ i ℓ) ∧
            nearestDistance (dataPoint G b.val j i s) C ^ 2 =
              baseline n L ℓ + Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) *
                signValue (σ j i) * (-1 : ℝ) ^ ℓ.val ∧
            5 * (n : ℝ) ≤ nearestDistance (dataPoint G b.val j i s) C ^ 2 ∧
            nearestDistance (dataPoint G b.val j i s) C ^ 2 ≤ 9 * (n : ℝ)) ∧
        (∀ b' : Fin n, b' ≠ b → ∀ (j : Fin n) (i : Fin m) (s : Fin q),
          nearestDistance (dataPoint G b'.val j i s) C ^ 2 = 2) ∧
        cost 2 X C ≤ 11 * (X.card : ℝ)  := by
  intro b v hv σ
  refine ⟨queryCenters_card hn hL b (displacement2 L) v (hG.1.2.2.2.1 v hv) σ hbudget,
    dataset_card G hG.1 hn n, ?_, ?_, ?_⟩
  · intro j i ℓ s hℓ
    exact active_query_costs G hG.1 hn hL b j i s v hv σ ℓ hℓ
  · intro b' hbb j i s
    exact inactive_query_distance_sq G hG.1 hn hL b b' hbb j i s v hv σ
  · have hh := query_total_cost (k := k) G hG.1 hn hL b v hv σ
    rw [dataset_card G hG.1 hn n]
    convert hh using 1 <;> push_cast <;> ring



