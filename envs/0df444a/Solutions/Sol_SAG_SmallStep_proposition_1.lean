-- Prove2me | solution 1 for SAG.SmallStep.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T01:26:05.296996+00:00
-- url     : https://prove2.me/submissions/e2fc66b6-80de-42b8-a397-c7ead15b4932

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_SmallStep_run
open scoped BigOperators RealInnerProductSpace
open Set Filter

namespace SAGRateProof
end SAGRateProof

open scoped BigOperators RealInnerProductSpace
open Set
namespace SAGRateProof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma line_gradient {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) ⟪g (x + t • d), d⟫ t := by
  convert! (hg (x + t • d)).hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const d).const_add x) using 1
  simp only [one_smul, InnerProductSpace.toDual_apply_apply]

lemma gradient_support {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x) (x y : E) :
    f x + ⟪g x, y - x⟫ ≤ f y := by
  have hcv : ConvexOn ℝ univ (fun t : ℝ => f (x + t • (y - x))) := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ u v hu hv huv
    have h := hc.2 (mem_univ (x + a • (y - x)))
      (mem_univ (x + b • (y - x))) hu hv huv
    have he : x + (u * a + v * b) • (y - x) =
        u • (x + a • (y - x)) + v • (x + b • (y - x)) := by
      calc
        _ = (u + v) • x + (u * a + v * b) • (y - x) := by rw [huv, one_smul]
        _ = _ := by module
    simpa only [smul_eq_mul, he] using h
  have hd := line_gradient hg x (y - x) 0
  simp only [zero_smul, add_zero] at hd
  have h := hcv.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hd
  simp [slope] at h
  linarith

lemma gradient_upper_model {f : E → ℝ} {g : E → E} {L : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let F := fun t : ℝ => f (x + t • d) - f x - t * ⟪g x, d⟫ -
    (L / 2) * t ^ 2 * ‖d‖ ^ 2
  have hd (t : ℝ) : HasDerivAt F
      (⟪g (x + t • d), d⟫ - ⟪g x, d⟫ - L * t * ‖d‖ ^ 2) t := by
    convert! (((line_gradient hg x d t).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const ⟪g x, d⟫)).sub
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖d‖ ^ 2)) using 1
    dsimp [F]
    ring
  have hc : ContinuousOn F (Icc 0 1) := fun t _ => (hd t).continuousAt.continuousWithinAt
  have hn (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      ⟪g (x + t • d), d⟫ - ⟪g x, d⟫ - L * t * ‖d‖ ^ 2 ≤ 0 := by
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hl := hlip (x + t • d) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hl
    have hi := real_inner_le_norm (g (x + t • d) - g x) d
    rw [inner_sub_left] at hi
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg d)
    nlinarith
  have ha := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1) hc
    (fun t _ => (hd t).hasDerivWithinAt) hn
  have h := ha (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1) zero_le_one
  dsimp [F, d] at h
  simp only [zero_smul, add_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),
    one_smul, add_sub_cancel, one_mul, one_pow, mul_one, sub_self] at h
  linarith

lemma bregman_lower {f : E → ℝ} {g : E → E} {L : ℝ} (hL : 0 < L)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖g x - g y‖ ^ 2 / (2 * L) ≤ f x - f y - ⟪g y, x - y⟫ := by
  let v := g x - g y
  have hs := gradient_support hc hg y (x - (1 / L) • v)
  have hu := gradient_upper_model hg hlip x (x - (1 / L) • v)
  have he : x - (1 / L) • v - x = -(1 / L) • v := by module
  have he' : x - (1 / L) • v - y = (x - y) - (1 / L) • v := by abel
  rw [he] at hu
  rw [he', inner_sub_right, inner_smul_right] at hs
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hu
  have hi : ⟪g x, v⟫ - ⟪g y, v⟫ = ‖v‖ ^ 2 := by
    rw [← inner_sub_left]; exact real_inner_self_eq_norm_sq v
  have hsum := add_le_add hs hu
  have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * L)
  field_simp at hm ⊢
  dsimp [v] at hi hm
  nlinarith

lemma cocoercive {f : E → ℝ} {g : E → E} {L : ℝ} (hL : 0 < L)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖g x - g y‖ ^ 2 ≤ L * ⟪g x - g y, x - y⟫ := by
  have h1 := bregman_lower hL hc hg hlip x y
  have h2 := bregman_lower hL hc hg hlip y x
  rw [norm_sub_rev (g y) (g x)] at h2
  have he : y - x = -(x - y) := by abel
  rw [he, inner_neg_right] at h2
  have h := add_le_add h1 h2
  rw [inner_sub_left]
  have hm := mul_le_mul_of_nonneg_left h hL.le
  field_simp at hm
  nlinarith

end SAGRateProof

open scoped BigOperators RealInnerProductSpace
open Set Filter
namespace SAGRateProof
variable {p n : ℕ}

lemma avg_hasGradient
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hg : ∀ i x, HasGradientAt (f i) (g i x) x) (x : EuclideanSpace ℝ (Fin p)) :
    HasGradientAt (SAGA.Convex.fAvg f) (SAGA.Convex.gradAvg g x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! (HasFDerivAt.sum (fun i (_ : i ∈ Finset.univ) => (hg i x).hasFDerivAt)).const_mul
    (1 / (n : ℝ)) using 1
  · funext v; simp [SAGA.Convex.fAvg, Finset.sum_apply]
  · ext v
    simp [SAGA.Convex.gradAvg]

lemma sum_star_zero (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hg : ∀ i x, HasGradientAt (f i) (g i x) x)
    (a : EuclideanSpace ℝ (Fin p)) (hmin : ∀ x, SAGA.Convex.fAvg f a ≤ SAGA.Convex.fAvg f x) :
    ∑ i, g i a = 0 := by
  have hm : IsLocalMin (SAGA.Convex.fAvg f) a := Eventually.of_forall hmin
  have hz := hm.hasFDerivAt_eq_zero (avg_hasGradient f g hg a).hasFDerivAt
  have hz' : SAGA.Convex.gradAvg g a = 0 := by
    apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p))).injective
    simpa using hz
  have hN : (1 / (n : ℝ)) ≠ 0 := by positivity
  exact (smul_eq_zero.mp hz').resolve_left hN

lemma avg_lipschitz (hn : 0 < n)
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (hl : ∀ i x y, ‖g i x - g i y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin p)) :
    ‖SAGA.Convex.gradAvg g x - SAGA.Convex.gradAvg g y‖ ≤ L * ‖x - y‖ := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := norm_sum_le (s := Finset.univ) (f := fun i => g i x - g i y)
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i x y)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ht
  simp only [SAGA.Convex.gradAvg, ← smul_sub, ← Finset.sum_sub_distrib, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))]
  calc
    _ ≤ (1 / (n : ℝ)) * ((n : ℝ) * (L * ‖x - y‖)) :=
      mul_le_mul_of_nonneg_left (hs.trans ht) (by positivity)
    _ = _ := by field_simp

lemma strong_monotone
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (μ : ℝ)
    (hg : ∀ i x, HasGradientAt (f i) (g i x) x)
    (hc : ConvexOn ℝ univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (x y : EuclideanSpace ℝ (Fin p)) :
    μ * ‖x - y‖ ^ 2 ≤ ⟪SAGA.Convex.gradAvg g x - SAGA.Convex.gradAvg g y, x - y⟫ := by
  have hd (z : EuclideanSpace ℝ (Fin p)) :
      HasGradientAt (fun w => SAGA.Convex.fAvg f w - μ / 2 * ‖w‖ ^ 2)
        (SAGA.Convex.gradAvg g z - μ • z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! (avg_hasGradient f g hg z).hasFDerivAt.sub
      ((hasFDerivAt_id z).norm_sq.const_mul (μ / 2)) using 1
    ext v
    simp
    ; ring
  have h1 := gradient_support hc hd x y
  have h2 := gradient_support hc hd y x
  have he : y - x = -(x - y) := by abel
  rw [he, inner_neg_right] at h1
  simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial] at h1 h2 ⊢
  have hid : ⟪x, x - y⟫ - ⟪y, x - y⟫ = ‖x - y‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hm := congrArg (fun t : ℝ => μ * t) hid
  nlinarith

lemma gradient_growth (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (μ : ℝ)
    (hg : ∀ i x, HasGradientAt (f i) (g i x) x)
    (hc : ConvexOn ℝ univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (a : EuclideanSpace ℝ (Fin p)) (hmin : ∀ x, SAGA.Convex.fAvg f a ≤ SAGA.Convex.fAvg f x)
    (x : EuclideanSpace ℝ (Fin p)) :
    μ * ‖x - a‖ ^ 2 ≤ ⟪SAGA.Convex.gradAvg g x, x - a⟫ := by
  have h := strong_monotone f g μ hg hc x a
  simpa [SAGA.Convex.gradAvg, sum_star_zero hn f g hg a hmin] using h

lemma summed_cocoercivity (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (hL : 0 < L) (hg : ∀ i x, HasGradientAt (f i) (g i x) x)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hl : ∀ i x y, ‖g i x - g i y‖ ≤ L * ‖x - y‖)
    (a : EuclideanSpace ℝ (Fin p)) (hmin : ∀ x, SAGA.Convex.fAvg f a ≤ SAGA.Convex.fAvg f x)
    (x : EuclideanSpace ℝ (Fin p)) :
    ∑ i, ‖g i x - g i a‖ ^ 2 ≤ (n : ℝ) * L * ⟪SAGA.Convex.gradAvg g x, x - a⟫ := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    cocoercive hL (hc i) (hg i) (hl i) x a)
  simp only [← Finset.mul_sum, ← sum_inner, Finset.sum_sub_distrib,
    sum_star_zero hn f g hg a hmin, sub_zero] at h
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    _ ≤ L * ⟪(∑ i, g i x), x - a⟫ := h
    _ = _ := by
      simp only [SAGA.Convex.gradAvg, inner_smul_left, starRingEnd_apply, star_trivial]
      field_simp

lemma mu_le_L (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (hg : ∀ i x, HasGradientAt (f i) (g i x) x)
    (hc : ConvexOn ℝ univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (hl : ∀ i x y, ‖g i x - g i y‖ ≤ L * ‖x - y‖) : μ ≤ L := by
  let : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin p))
  have hgrowth := strong_monotone f g μ hg hc v 0
  have hbound := avg_lipschitz hn g L hl v 0
  have hi := real_inner_le_norm (SAGA.Convex.gradAvg g v - SAGA.Convex.gradAvg g 0) v
  simp only [sub_zero] at hgrowth hbound
  have hm := mul_le_mul_of_nonneg_right hbound (norm_nonneg v)
  have hpv : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  nlinarith

end SAGRateProof

open scoped BigOperators RealInnerProductSpace
open Set
namespace SAGRateProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

noncomputable def potential (α : ℝ) (v : Fin n → E) (z : E) : ℝ :=
  3 * (n : ℝ) * α ^ 2 * (∑ i, ‖v i‖ ^ 2) +
    α ^ 2 * (1 / (n : ℝ) ^ 2 - 2 / (n : ℝ)) * ‖∑ i, v i‖ ^ 2 -
    2 * α * (1 - 1 / (n : ℝ)) * ⟪(∑ i, v i), z⟫ + ‖z‖ ^ 2

noncomputable def statePotential {p : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (s : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) : ℝ :=
  potential α (fun i => s.1 i - g i a) (s.2 - a)

omit [InnerProductSpace ℝ E] in
lemma finite_sum_sq_le (v : Fin n → E) :
    ‖∑ i, v i‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
  have h := norm_sum_le (s := Finset.univ) (f := v)
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖v i‖)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans hc

lemma potential_domination (hn : 0 < n) (α : ℝ) (v : Fin n → E) (z : E) :
    ‖z‖ ^ 2 ≤ 3 * potential α v z := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := finite_sum_sq_le v
  have hm := mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hs)
  have hc : 0 ≤ 1 + 2 / (n : ℝ) - 1 / (n : ℝ) ^ 2 := by
    have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
    have hinv1 : 1 / (n : ℝ) ≤ 1 := (div_le_one hN).mpr hN1
    have he : 1 / (n : ℝ) ^ 2 = (1 / (n : ℝ)) ^ 2 := by ring
    rw [he]; simp only [div_eq_mul_inv, one_mul] at *; nlinarith
  have hp := mul_nonneg (mul_nonneg (sq_nonneg α) hc) (sq_nonneg ‖∑ i, v i‖)
  have hsq := sq_nonneg ‖(α * (1 - 1 / (n : ℝ))) • (∑ i, v i) - (1 / 2 : ℝ) • z‖
  rw [norm_sub_sq_real] at hsq
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial] at hsq
  unfold potential
  simp only [div_eq_mul_inv, one_mul, ← inv_pow] at *
  norm_num at hsq
  nlinarith [sq_nonneg ‖z‖]

omit [InnerProductSpace ℝ E] in
lemma update_sum (v : Fin n → E) (u : E) (i : Fin n) :
    ∑ j, Function.update v i u j = (∑ j, v j) + u - v i := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.sum_sdiff (f := v) (by simp : {i} ⊆ Finset.univ)
  simp only [Finset.sum_singleton] at h
  rw [← h]; abel

omit [InnerProductSpace ℝ E] in
lemma update_sq_sum (v : Fin n → E) (u : E) (i : Fin n) :
    ∑ j, ‖Function.update v i u j‖ ^ 2 = (∑ j, ‖v j‖ ^ 2) + ‖u‖ ^ 2 - ‖v i‖ ^ 2 := by
  classical
  have he : (fun j => ‖Function.update v i u j‖ ^ 2) =
      Function.update (fun j => ‖v j‖ ^ 2) i (‖u‖ ^ 2) := by
    funext j; by_cases h : j = i <;> simp [h]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.sum_sdiff (f := fun j => ‖v j‖ ^ 2) (by simp : {i} ⊆ Finset.univ)
  simp only [Finset.sum_singleton] at h
  rw [← h]; ring

lemma potential_after (hn : 0 < n) (α : ℝ) (v : Fin n → E) (z : E) :
    potential α v (z - (α / (n : ℝ)) • (∑ j, v j)) =
      3 * (n : ℝ) * α ^ 2 * (∑ j, ‖v j‖ ^ 2) + ‖z‖ ^ 2 -
        2 * α * ⟪(∑ j, v j), z⟫ := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold potential
  rw [norm_sub_sq_real]
  simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm z (∑ j, v j)]
  field_simp
  ; ring

lemma state_one_step {p : ℕ} (hn : 0 < n)
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : EuclideanSpace ℝ (Fin p)) (hga : ∑ i, g i a = 0) (α : ℝ)
    (s : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i, statePotential g a α (SAG.SmallStep.step g α i s) =
      3 * (n : ℝ) * α ^ 2 * (1 - 1 / (n : ℝ)) * (∑ i, ‖s.1 i - g i a‖ ^ 2) +
      ‖s.2 - a‖ ^ 2 - 2 * α * ⟪SAGA.Convex.gradAvg g s.2, s.2 - a⟫ +
      3 * α ^ 2 * (∑ i, ‖g i s.2 - g i a‖ ^ 2) -
      2 * α * (1 - 1 / (n : ℝ)) * ⟪(∑ i, (s.1 i - g i a)), s.2 - a⟫ := by
  classical
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he (i : Fin n) : statePotential g a α (SAG.SmallStep.step g α i s) =
      3 * (n : ℝ) * α ^ 2 * ((∑ j, ‖s.1 j - g j a‖ ^ 2) +
        ‖g i s.2 - g i a‖ ^ 2 - ‖s.1 i - g i a‖ ^ 2) + ‖s.2 - a‖ ^ 2 -
      2 * α * ⟪((∑ j, (s.1 j - g j a)) + (g i s.2 - g i a) - (s.1 i - g i a)), s.2 - a⟫ := by
    have hv : (fun j => Function.update s.1 i (g i s.2) j - g j a) =
        Function.update (fun j => s.1 j - g j a) i (g i s.2 - g i a) := by
      funext j; by_cases h : j = i <;> simp [h]
    have hz : s.2 - (α / (n : ℝ)) • (∑ j, Function.update s.1 i (g i s.2) j) - a =
        (s.2 - a) - (α / (n : ℝ)) •
          (∑ j, Function.update (fun j => s.1 j - g j a) i (g i s.2 - g i a) j) := by
      rw [← hv, Finset.sum_sub_distrib, hga, sub_zero]; abel
    simp only [statePotential, SAG.SmallStep.step]
    rw [hv, hz, potential_after hn, update_sum, update_sq_sum]
  simp_rw [he, inner_sub_left, inner_add_left]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← sum_inner, Finset.sum_sub_distrib, hga, sub_zero, inner_zero_left]
  simp only [SAGA.Convex.gradAvg, inner_smul_left, starRingEnd_apply, star_trivial]
  field_simp
  ; ring

lemma state_initial {p : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : EuclideanSpace ℝ (Fin p)) (hga : ∑ i, g i a = 0) (α : ℝ)
    (x : EuclideanSpace ℝ (Fin p)) :
    statePotential g a α (fun _ => 0, x) =
      3 * (n : ℝ) * α ^ 2 * (∑ i, ‖g i a‖ ^ 2) + ‖x - a‖ ^ 2 := by
  simp [statePotential, potential, hga]

end SAGRateProof

namespace SAGRateProof

theorem scalar_contraction_core (N L μ a δ V s r c D U : ℝ)
    (hN : 1 ≤ N) (ha : 0 < a) (hδ : 0 ≤ δ) (hδN : N * δ ≤ 1 / 8)
    (haNL : a * N * L = 1 / 2) (haμ : a * μ = 4 * δ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hV : s ^ 2 ≤ N * V)
    (hc : -s * r ≤ c) (hD : μ * r ^ 2 ≤ D) (hU : U ≤ N * L * D) :
    3 * (N - 1) * a ^ 2 * V + 3 * a ^ 2 * U + r ^ 2
        - 2 * a * (1 - 1 / N) * c - 2 * a * D
      ≤ (1 - δ) * (3 * N * a ^ 2 * V + a ^ 2 * (1 / N ^ 2 - 2 / N) * s ^ 2
        - 2 * a * (1 - 1 / N) * c + r ^ 2) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hN0 : N ≠ 0 := ne_of_gt hNp
  have hi : 1 / N ≤ 1 := (div_le_iff₀ hNp).2 (by linarith)
  have hip : 0 ≤ 1 / N := by positivity
  have ht : 0 ≤ 1 - 1 / N := sub_nonneg.2 hi
  have ht1 : 1 - 1 / N ≤ 1 := by linarith
  have hδ1 : δ ≤ 1 := by
    have := mul_nonneg (sub_nonneg.2 hN) hδ
    nlinarith
  have hd : δ - 1 / N ≤ 0 := by
    have : δ ≤ 1 / N := (le_div_iff₀ hNp).2 (by nlinarith)
    linarith
  have hVm : s ^ 2 / N ≤ V := (div_le_iff₀ hNp).2 (by nlinarith [hV])
  have hv := mul_le_mul_of_nonpos_left hVm
    (show 3 * N * a ^ 2 * (δ - 1 / N) ≤ 0 from
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hd)
  have hK : (1 / 2 : ℝ) ≤ 1 - 3 * N * δ + 2 * δ + (1 - δ) / N := by
    have : 0 ≤ (1 - δ) / N := by positivity
    nlinarith
  have htable : 3 * N * a ^ 2 * (δ - 1 / N) * V
      + (1 - δ) * a ^ 2 * (2 / N - 1 / N ^ 2) * s ^ 2
      ≤ -(a ^ 2 / (2 * N)) * s ^ 2 := by
    calc
      _ ≤ 3 * N * a ^ 2 * (δ - 1 / N) * (s ^ 2 / N)
          + (1 - δ) * a ^ 2 * (2 / N - 1 / N ^ 2) * s ^ 2 :=
        add_le_add hv le_rfl
      _ = (-(a ^ 2 / N) * s ^ 2) *
          (1 - 3 * N * δ + 2 * δ + (1 - δ) / N) := by field_simp; ring
      _ ≤ (-(a ^ 2 / N) * s ^ 2) * (1 / 2) :=
        mul_le_mul_of_nonpos_left hK
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg s))
      _ = _ := by ring
  have hcross : -2 * a * δ * (1 - 1 / N) * c ≤ 2 * a * δ * s * r := by
    calc
      _ ≤ -2 * a * δ * (1 - 1 / N) * (-s * r) :=
        mul_le_mul_of_nonpos_left hc (by
          have : 0 ≤ 2 * a * δ * (1 - 1 / N) := by positivity
          nlinarith only [this])
      _ = (2 * a * δ * s * r) * (1 - 1 / N) := by ring
      _ ≤ (2 * a * δ * s * r) * 1 :=
        mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ = _ := mul_one _
  have hyoung : -(a ^ 2 / (2 * N)) * s ^ 2 + 2 * a * δ * s * r
      ≤ 2 * N * δ ^ 2 * r ^ 2 := by
    have he : (2 * N) * (2 * N * δ ^ 2 * r ^ 2 -
        (-(a ^ 2 / (2 * N)) * s ^ 2 + 2 * a * δ * s * r))
        = (a * s - 2 * N * δ * r) ^ 2 := by field_simp; ring
    have hp : 0 ≤ (2 * N) * (2 * N * δ ^ 2 * r ^ 2 -
        (-(a ^ 2 / (2 * N)) * s ^ 2 + 2 * a * δ * s * r)) := by
      rw [he]; exact sq_nonneg _
    have := nonneg_of_mul_nonneg_right hp (show 0 < 2 * N by positivity)
    linarith
  have hu := mul_le_mul_of_nonneg_left hU (show 0 ≤ 3 * a ^ 2 by positivity)
  have hg := mul_le_mul_of_nonneg_left hD (show 0 ≤ a / 2 by positivity)
  have hcoef : 2 * a - 3 * a ^ 2 * N * L = a / 2 := by
    calc
      _ = 2 * a - 3 * a * (a * N * L) := by ring
      _ = _ := by rw [haNL]; ring
  have hstrong : 2 * δ * r ^ 2 ≤ (a / 2) * D := by
    have he : a / 2 * (μ * r ^ 2) = 2 * δ * r ^ 2 := by
      calc
        _ = (a * μ) / 2 * r ^ 2 := by ring
        _ = _ := by rw [haμ]; ring
    rwa [he] at hg
  have hlast : 2 * N * δ ^ 2 * r ^ 2 ≤ δ * r ^ 2 := by
    have : 0 ≤ δ * r ^ 2 := by positivity
    nlinarith only [mul_nonneg this (show 0 ≤ 1 - 2 * N * δ by nlinarith only [hδN])]
  have hsum := add_le_add htable hcross
  have he :
      (3 * (N - 1) * a ^ 2 * V + 3 * a ^ 2 * U + r ^ 2
        - 2 * a * (1 - 1 / N) * c - 2 * a * D)
      - (1 - δ) * (3 * N * a ^ 2 * V + a ^ 2 * (1 / N ^ 2 - 2 / N) * s ^ 2
        - 2 * a * (1 - 1 / N) * c + r ^ 2) =
      (3 * N * a ^ 2 * (δ - 1 / N) * V
        + (1 - δ) * a ^ 2 * (2 / N - 1 / N ^ 2) * s ^ 2)
        + (-2 * a * δ * (1 - 1 / N) * c) + δ * r ^ 2
        - (2 * a - 3 * a ^ 2 * N * L) * D + 3 * a ^ 2 * (U - N * L * D) := by
    field_simp; ring
  rw [hcoef] at he
  linarith only [he, hsum, hyoung, hu, hstrong, hlast]

theorem scalar_contraction (N L μ V s r c D U : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hV : s ^ 2 ≤ N * V)
    (hc : -s * r ≤ c) (hD : μ * r ^ 2 ≤ D) (hU : U ≤ N * L * D) :
    let a := 1 / (2 * N * L)
    let δ := μ / (8 * N * L)
    3 * (N - 1) * a ^ 2 * V + 3 * a ^ 2 * U + r ^ 2
        - 2 * a * (1 - 1 / N) * c - 2 * a * D
      ≤ (1 - δ) * (3 * N * a ^ 2 * V + a ^ 2 * (1 / N ^ 2 - 2 / N) * s ^ 2
        - 2 * a * (1 - 1 / N) * c + r ^ 2) := by
  dsimp only
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  apply scalar_contraction_core N L μ _ _ V s r c D U hN
  · positivity
  · positivity
  · apply (le_div_iff₀ (show 0 < (8 : ℝ) by norm_num)).2
    have he : N * (μ / (8 * N * L)) * 8 = μ / L := by field_simp
    rw [he]
    exact (div_le_one hL).2 hμL
  · field_simp
  · field_simp; ring
  · exact hs
  · exact hr
  · exact hV
  · exact hc
  · exact hD
  · exact hU

theorem rate_nonneg (N L μ : ℝ) (hN : 1 ≤ N) (hL : 0 < L)
    (_hμ : 0 < μ) (hμL : μ ≤ L) : 0 ≤ 1 - μ / (8 * N * L) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have : μ / (8 * N * L) ≤ 1 := (div_le_one (by positivity)).2 (by nlinarith)
  linarith

end SAGRateProof

open scoped BigOperators

namespace SAGRateProof

theorem expect_mono {n k : ℕ} {f g : (Fin k → Fin n) → ℝ}
    (h : ∀ js, f js ≤ g js) :
    SAGA.Convex.expectIdx n k f ≤ SAGA.Convex.expectIdx n k g := by
  unfold SAGA.Convex.expectIdx
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun js _ => h js) (by positivity)

theorem expect_mul (n k : ℕ) (c : ℝ) (f : (Fin k → Fin n) → ℝ) :
    SAGA.Convex.expectIdx n k (fun js => c * f js) =
      c * SAGA.Convex.expectIdx n k f := by
  simp only [SAGA.Convex.expectIdx, ← Finset.mul_sum]
  ring

theorem expect_cons {n k : ℕ} (hn : 0 < n) (f : (Fin (k + 1) → Fin n) → ℝ) :
    SAGA.Convex.expectIdx n (k + 1) f =
      (1 / (n : ℝ)) * ∑ i, SAGA.Convex.expectIdx n k (fun js => f (Fin.cons i js)) := by
  have hs : (∑ js, f js) = ∑ i, ∑ js, f (Fin.cons i js) := by
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)).sum_comp f]
    exact Fintype.sum_prod_type _
  simp only [SAGA.Convex.expectIdx, hs, ← Finset.mul_sum]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [pow_succ]
  field_simp

theorem run_cons {p n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : ℝ) (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p))
    (i : Fin n) (js : Fin k → Fin n) :
    SAG.SmallStep.runFrom f' a θ (Fin.cons i js) =
      SAG.SmallStep.runFrom f' a (SAG.SmallStep.step f' a i θ) js := by
  simp only [SAG.SmallStep.runFrom, List.ofFn_cons, List.foldl_cons]

theorem run_expectation_le {p n : ℕ} (hn : 0 < n)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (a ρ : ℝ)
    (Q : ((Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) → ℝ)
    (hρ : 0 ≤ ρ)
    (hstep : ∀ θ, (1 / (n : ℝ)) * ∑ i, Q (SAG.SmallStep.step f' a i θ) ≤ ρ * Q θ)
    (k : ℕ) (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    SAGA.Convex.expectIdx n k (fun js => Q (SAG.SmallStep.runFrom f' a θ js))
      ≤ ρ ^ k * Q θ := by
  induction k generalizing θ with
  | zero => simp [SAGA.Convex.expectIdx, SAG.SmallStep.runFrom]
  | succ k ih =>
      rw [expect_cons hn]
      simp only [run_cons]
      calc
        _ ≤ (1 / (n : ℝ)) * ∑ i, ρ ^ k * Q (SAG.SmallStep.step f' a i θ) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun i _ => ih (SAG.SmallStep.step f' a i θ)) (by positivity)
        _ = ρ ^ k * ((1 / (n : ℝ)) * ∑ i, Q (SAG.SmallStep.step f' a i θ)) := by
          rw [← Finset.mul_sum]; ring
        _ ≤ ρ ^ k * (ρ * Q θ) := mul_le_mul_of_nonneg_left (hstep θ) (pow_nonneg hρ _)
        _ = _ := by rw [pow_succ]; ring

end SAGRateProof

open scoped BigOperators RealInnerProductSpace

namespace SAGRateProof

theorem state_contraction {p n : ℕ} (hn : 0 < n)
    (g : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (a : EuclideanSpace ℝ (Fin p)) (hga : ∑ i, g i a = 0)
    (hstrong : ∀ x, μ * ‖x - a‖ ^ 2 ≤ ⟪SAGA.Convex.gradAvg g x, x - a⟫)
    (hcoco : ∀ x, (∑ i, ‖g i x - g i a‖ ^ 2) ≤
      (n : ℝ) * L * ⟪SAGA.Convex.gradAvg g x, x - a⟫)
    (s : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i,
      statePotential g a (1 / (2 * (n : ℝ) * L))
        (SAG.SmallStep.step g (1 / (2 * (n : ℝ) * L)) i s)
      ≤ (1 - μ / (8 * (n : ℝ) * L)) * statePotential g a (1 / (2 * (n : ℝ) * L)) s := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hinner : -‖∑ i, (s.1 i - g i a)‖ * ‖s.2 - a‖ ≤
      ⟪(∑ i, (s.1 i - g i a)), s.2 - a⟫ := by
    have h := neg_le_abs ⟪(∑ i, (s.1 i - g i a)), s.2 - a⟫
    have hc := abs_real_inner_le_norm (∑ i, (s.1 i - g i a)) (s.2 - a)
    linarith
  have h := scalar_contraction (n : ℝ) L μ
    (∑ i, ‖s.1 i - g i a‖ ^ 2) ‖∑ i, (s.1 i - g i a)‖ ‖s.2 - a‖
    ⟪(∑ i, (s.1 i - g i a)), s.2 - a⟫ ⟪SAGA.Convex.gradAvg g s.2, s.2 - a⟫
    (∑ i, ‖g i s.2 - g i a‖ ^ 2)
    hN hL hμ hμL (norm_nonneg _) (norm_nonneg _) (finite_sum_sq_le _) hinner
    (hstrong s.2) (hcoco s.2)
  dsimp only at h
  rw [state_one_step hn g a hga]
  unfold statePotential potential
  have he : 3 * (n : ℝ) * (1 / (2 * (n : ℝ) * L)) ^ 2 * (1 - 1 / (n : ℝ)) =
      3 * ((n : ℝ) - 1) * (1 / (2 * (n : ℝ) * L)) ^ 2 := by field_simp
  rw [he]
  linarith only [h]

end SAGRateProof

open scoped BigOperators RealInnerProductSpace

namespace SAG.SmallStep

/-- Proposition 1 (Le Roux–Schmidt–Bach, arXiv:1202.6258v4, p. 5). With the constant step size
`α = 1/(2nL)` and the table initialized to `y⁰ = 0`, the SAG iterates satisfy, for `k ≥ 1`,
`E‖xᵏ − x*‖² ≤ (1 − μ/(8Ln))ᵏ [3‖x⁰ − x*‖² + 9σ²/(4L²)]`, where `σ² = (1/n) ∑ᵢ ‖f'ᵢ(x*)‖²` and the
expectation is over `k` i.i.d. uniform indices. -/
theorem proposition_1 {p n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hsc : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (xstar : EuclideanSpace ℝ (Fin p))
    (hmin : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    SAGA.Convex.expectIdx n k
        (fun js => ‖(runFrom f' (1 / (2 * (n : ℝ) * L)) (fun _ => 0, x0) js).2 - xstar‖ ^ 2)
      ≤ (1 - μ / (8 * L * (n : ℝ))) ^ k
        * (3 * ‖x0 - xstar‖ ^ 2 + 9 * ((1 / (n : ℝ)) * ∑ i, ‖f' i xstar‖ ^ 2) / (4 * L ^ 2)) := by
  classical
  have _ := hk
  by_cases hp : p = 0
  · subst p
    have hz (v : EuclideanSpace ℝ (Fin 0)) : ‖v‖ = 0 := by
      rw [Subsingleton.elim v 0, norm_zero]
    simp [SAGA.Convex.expectIdx, hz]
  · have hpp : 0 < p := Nat.pos_of_ne_zero hp
    have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hN0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hμL := SAGRateProof.mu_le_L hpp hn f f' L μ hgrad hsc hlip
    have hzero := SAGRateProof.sum_star_zero hn f f' hgrad xstar hmin
    have hstrong := SAGRateProof.gradient_growth hn f f' μ hgrad hsc xstar hmin
    have hcoco := SAGRateProof.summed_cocoercivity hn f f' L hL hgrad hconv hlip xstar hmin
    have hrate := SAGRateProof.rate_nonneg (n : ℝ) L μ hN hL hμ hμL
    let a : ℝ := 1 / (2 * (n : ℝ) * L)
    let ρ : ℝ := 1 - μ / (8 * (n : ℝ) * L)
    let Q := SAGRateProof.statePotential f' xstar a
    have hstep (s : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
        (1 / (n : ℝ)) * ∑ i, Q (step f' a i s) ≤ ρ * Q s :=
      SAGRateProof.state_contraction hn f' L μ hL hμ hμL xstar hzero hstrong hcoco s
    have hrun := SAGRateProof.run_expectation_le hn f' a ρ Q hrate hstep k (fun _ => 0, x0)
    have hdom : SAGA.Convex.expectIdx n k
        (fun js => ‖(runFrom f' a (fun _ => 0, x0) js).2 - xstar‖ ^ 2)
        ≤ 3 * SAGA.Convex.expectIdx n k (fun js => Q (runFrom f' a (fun _ => 0, x0) js)) := by
      rw [← SAGRateProof.expect_mul]
      apply SAGRateProof.expect_mono
      intro js
      exact SAGRateProof.potential_domination hn a _ _
    have hinit : 3 * Q (fun _ => 0, x0) =
        3 * ‖x0 - xstar‖ ^ 2 + 9 * ((1 / (n : ℝ)) * ∑ i, ‖f' i xstar‖ ^ 2) / (4 * L ^ 2) := by
      dsimp only [Q]
      rw [SAGRateProof.state_initial f' xstar hzero]
      dsimp only [a]
      field_simp
      ring
    have hrho : ρ = 1 - μ / (8 * L * (n : ℝ)) := by dsimp only [ρ]; ring
    have hfinal := mul_le_mul_of_nonneg_left hrun (show (0 : ℝ) ≤ 3 by norm_num)
    have he : 3 * (ρ ^ k * Q (fun _ => 0, x0)) = ρ ^ k * (3 * Q (fun _ => 0, x0)) := by ring
    rw [he, hinit, hrho] at hfinal
    exact hdom.trans hfinal

end SAG.SmallStep

open SAG.SmallStep
theorem solution {p n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hsc : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (xstar : EuclideanSpace ℝ (Fin p))
    (hmin : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    SAGA.Convex.expectIdx n k
        (fun js => ‖(runFrom f' (1 / (2 * (n : ℝ) * L)) (fun _ => 0, x0) js).2 - xstar‖ ^ 2)
      ≤ (1 - μ / (8 * L * (n : ℝ))) ^ k
        * (3 * ‖x0 - xstar‖ ^ 2 + 9 * ((1 / (n : ℝ)) * ∑ i, ‖f' i xstar‖ ^ 2) / (4 * L ^ 2)) :=
  SAG.SmallStep.proposition_1 hn f f' L μ hL hμ hgrad hconv hlip hsc xstar hmin x0 k hk
