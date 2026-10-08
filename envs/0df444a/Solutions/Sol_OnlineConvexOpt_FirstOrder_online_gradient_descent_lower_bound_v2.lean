-- Prove2me | solution 1 for OnlineConvexOpt.FirstOrder.online_gradient_descent_lower_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T14:09:38.715995+00:00
-- url     : https://prove2.me/submissions/3c636a2f-f55b-477a-be82-9985e6561274

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm

open scoped BigOperators
set_option autoImplicit false

namespace ParentMoments

/-- A finite second/fourth-moment estimate sufficient for a random-walk lower bound. -/
theorem sqrt_le_twice_expect_abs {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (S : Ω → ℝ) (n : ℝ) (hn : 0 < n)
    (h2 : (𝔼 ω, S ω ^ 2) = n)
    (h4 : (𝔼 ω, S ω ^ 4) ≤ 3 * n ^ 2) :
    Real.sqrt n / 2 ≤ 𝔼 ω, |S ω| := by
  let A : ℝ := 𝔼 ω, |S ω|
  let C : ℝ := 𝔼 ω, |S ω| ^ 3
  let D : ℝ := 𝔼 ω, S ω ^ 4
  have hA : 0 ≤ A := Finset.expect_nonneg (fun ω _ => abs_nonneg (S ω))
  have hsqrt (ω : Ω) : (Real.sqrt |S ω|) ^ 2 = |S ω| := Real.sq_sqrt (abs_nonneg _)
  have habs2 (ω : Ω) : |S ω| ^ 2 = S ω ^ 2 := sq_abs _
  have hm (ω : Ω) : Real.sqrt |S ω| * (|S ω| * Real.sqrt |S ω|) = S ω ^ 2 := by
    nlinarith [hsqrt ω, habs2 ω]
  have hq (ω : Ω) : (|S ω| * Real.sqrt |S ω|) ^ 2 = |S ω| ^ 3 := by
    rw [mul_pow, hsqrt]
    ring
  have hcs1 : n ^ 2 ≤ A * C := by
    simpa only [hm, hsqrt, hq, h2] using
      (Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
        (fun ω => Real.sqrt |S ω|) (fun ω => |S ω| * Real.sqrt |S ω|))
  have hm2 (ω : Ω) : |S ω| * |S ω| ^ 2 = |S ω| ^ 3 := by ring
  have hq2 (ω : Ω) : (|S ω| ^ 2) ^ 2 = S ω ^ 4 := by rw [habs2]; ring
  have hcs2 : C ^ 2 ≤ n * D := by
    have hh := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
        (fun ω => |S ω|) (fun ω => |S ω| ^ 2)
    simp_rw [hm2, hq2] at hh
    simpa only [habs2, h2] using hh
  have hcs1sq : (n ^ 2) ^ 2 ≤ (A * C) ^ 2 :=
    (sq_le_sq₀ (sq_nonneg n) ((sq_nonneg n).trans hcs1)).2 hcs1
  have hproduct : n ^ 4 ≤ 3 * A ^ 2 * n ^ 3 := calc
    n ^ 4 = (n ^ 2) ^ 2 := by ring
    _ ≤ (A * C) ^ 2 := hcs1sq
    _ = A ^ 2 * C ^ 2 := by ring
    _ ≤ A ^ 2 * (n * D) := mul_le_mul_of_nonneg_left hcs2 (sq_nonneg A)
    _ ≤ A ^ 2 * (n * (3 * n ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hn.le) (sq_nonneg A)
    _ = 3 * A ^ 2 * n ^ 3 := by ring
  have hscaled : n ^ 3 * n ≤ n ^ 3 * (3 * A ^ 2) := by nlinarith [hproduct]
  have hA2 : n ≤ 3 * A ^ 2 := le_of_mul_le_mul_left hscaled (pow_pos hn 3)
  have hs : Real.sqrt n ≤ 2 * A := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [sq_nonneg A]
  change Real.sqrt n / 2 ≤ A
  linarith

end ParentMoments

#print axioms ParentMoments.sqrt_le_twice_expect_abs

open scoped BigOperators
set_option autoImplicit false

namespace OGDCube

def sign (b : Bool) : ℝ := if b then 1 else -1

def walk {T : ℕ} (σ : Fin T → Bool) : ℝ := ∑ i, sign (σ i)

theorem walk_cons {T : ℕ} (b : Bool) (σ : Fin T → Bool) :
    walk (Fin.cons b σ) = sign b + walk σ := by
  simp [walk, Fin.sum_univ_succ]

theorem expect_bool (f : Bool → ℝ) :
    (𝔼 b, f b) = (f false + f true) / 2 := by
  simp [Finset.expect, NNRat.smul_def, add_comm, div_eq_mul_inv]
  <;> ring

theorem expect_split (T : ℕ) (F : ℝ → ℝ) :
    (𝔼 σ : Fin (T + 1) → Bool, F (walk σ)) =
      𝔼 σ : Fin T → Bool, (F (-1 + walk σ) + F (1 + walk σ)) / 2 := by
  let e : ((Fin T → Bool) × Bool) ≃ (Fin (T + 1) → Bool) :=
    (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => Bool))
  have he : (𝔼 p : ((Fin T → Bool) × Bool), F (sign p.2 + walk p.1)) =
      (𝔼 σ : Fin (T + 1) → Bool, F (walk σ)) := by
    apply Fintype.expect_equiv e
    intro p
    change F (sign p.2 + walk p.1) = F (walk (Fin.cons p.2 p.1))
    rw [walk_cons]
  rw [← he, ← Finset.univ_product_univ, Finset.expect_product]
  apply Finset.expect_congr rfl
  intro σ _
  rw [expect_bool]
  rfl

theorem second_moment (T : ℕ) :
    (𝔼 σ : Fin T → Bool, walk σ ^ 2) = (T : ℝ) := by
  induction T with
  | zero => simp [walk, Finset.expect]
  | succ T ih =>
    rw [expect_split T (fun x => x ^ 2)]
    have hpoly (x : ℝ) : ((-1 + x) ^ 2 + (1 + x) ^ 2) / 2 = x ^ 2 + 1 := by ring
    simp_rw [hpoly]
    rw [Finset.expect_add_distrib, ih, Fintype.expect_const]
    norm_cast

theorem fourth_moment (T : ℕ) :
    (𝔼 σ : Fin T → Bool, walk σ ^ 4) = 3 * (T : ℝ) ^ 2 - 2 * T := by
  induction T with
  | zero => simp [walk, Finset.expect]
  | succ T ih =>
    rw [expect_split T (fun x => x ^ 4)]
    have hpoly (x : ℝ) : ((-1 + x) ^ 4 + (1 + x) ^ 4) / 2 = x ^ 4 + 6 * x ^ 2 + 1 := by ring
    simp_rw [hpoly, Finset.expect_add_distrib]
    rw [ih, Fintype.expect_const]
    have hc : (𝔼 σ : Fin T → Bool, 6 * walk σ ^ 2) = 6 * (T : ℝ) := by
      rw [← Finset.mul_expect, second_moment]
    rw [hc]
    push_cast
    ring

theorem fourth_moment_le (T : ℕ) :
    (𝔼 σ : Fin T → Bool, walk σ ^ 4) ≤ 3 * (T : ℝ) ^ 2 := by
  rw [fourth_moment]
  linarith [Nat.cast_nonneg (α := ℝ) T]

theorem abs_expect_lower (T : ℕ) (hT : 0 < T) :
    Real.sqrt (T : ℝ) / 2 ≤ 𝔼 σ : Fin T → Bool, |walk σ| := by
  exact ParentMoments.sqrt_le_twice_expect_abs walk T (by exact_mod_cast hT)
    (second_moment T) (fourth_moment_le T)

end OGDCube

#print axioms OGDCube.abs_expect_lower


open OnlineConvexOpt.FirstOrder
open Finset
open scoped RealInnerProductSpace

namespace OGDLower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma linear_gradient (v x : E) : HasGradientAt (fun y => ⟪v, y⟫) v x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (InnerProductSpace.toDual ℝ E v).hasFDerivAt

lemma linear_properties (K : Set E) (hK : Convex ℝ K) (v : E) (hv : ‖v‖ ≤ 1) :
    ConvexOn ℝ K (fun x => ⟪v, x⟫) ∧
    (∀ x ∈ K, ∀ y ∈ K, |⟪v, x⟫ - ⟪v, y⟫| ≤ 1 * dist x y) ∧
    (∀ x ∈ K, ∀ w, HasGradientAt (fun y => ⟪v, y⟫) w x → ‖w‖ ≤ 1) := by
  refine ⟨(innerSL ℝ v).toLinearMap.convexOn hK, ?_, ?_⟩
  · intro x _ y _
    rw [← inner_sub_right, dist_eq_norm]
    exact (abs_real_inner_le_norm v (x - y)).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
  · intro x _ w hw
    have he := hw.unique (linear_gradient v x)
    simpa [he] using hv

lemma unit_ball_comparator (e : E) (he : ‖e‖ = 1) (c : ℕ → ℝ) (x : ℕ → E) (T : ℕ) :
    (∑ t ∈ range T, c t * ⟪e, x t⟫) + |∑ t ∈ range T, c t| ≤
      RegretT (Metric.closedBall (0 : E) 1) (fun t y => c t * ⟪e, y⟫) x T := by
  let S : ℝ := ∑ t ∈ range T, c t
  have hsum (y : E) : (∑ t ∈ range T, c t * ⟪e, y⟫) = S * ⟪e, y⟫ := by
    exact (sum_mul ..).symm
  have hnorm (y : E) (hy : y ∈ Metric.closedBall (0 : E) 1) : |⟪e, y⟫| ≤ 1 := by
    have hy' : ‖y‖ ≤ 1 := by simpa using hy
    simpa [he] using (abs_real_inner_le_norm e y).trans
      (mul_le_mul_of_nonneg_left hy' (norm_nonneg e))
  have hb : BddBelow ((fun y => ∑ t ∈ range T, c t * ⟪e, y⟫) ''
      Metric.closedBall (0 : E) 1) := by
    refine ⟨-|S|, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    rw [hsum]
    have h := mul_le_mul_of_nonneg_left (hnorm y hy) (abs_nonneg S)
    have h' := neg_abs_le (S * ⟪e, y⟫)
    rw [abs_mul] at h'
    nlinarith
  have hemem : e ∈ Metric.closedBall (0 : E) 1 := by simpa [he]
  have hnemem : -e ∈ Metric.closedBall (0 : E) 1 := by simpa [he]
  have hii : ⟪e, e⟫ = 1 := by simp [real_inner_self_eq_norm_sq, he]
  unfold RegretT
  change _ + |S| ≤ _
  by_cases hS : 0 ≤ S
  · have h := csInf_le hb (Set.mem_image_of_mem (fun y => ∑ t ∈ range T, c t * ⟪e, y⟫) hnemem)
    rw [hsum, inner_neg_right, hii] at h
    rw [abs_of_nonneg hS]
    linarith
  · have h := csInf_le hb (Set.mem_image_of_mem (fun y => ∑ t ∈ range T, c t * ⟪e, y⟫) hemem)
    rw [hsum, hii] at h
    rw [abs_of_neg (lt_of_not_ge hS)]
    linarith

end OGDLower


open OnlineConvexOpt.FirstOrder Finset
open scoped BigOperators RealInnerProductSpace

namespace OGDLower

def coeff {T : ℕ} (σ : Fin T → Bool) (t : ℕ) : ℝ :=
  if h : t < T then OGDCube.sign (σ ⟨t, h⟩) else 0

def flip {T : ℕ} (i : Fin T) (σ : Fin T → Bool) : Fin T → Bool :=
  Function.update σ i (!(σ i))

lemma flip_involutive {T : ℕ} (i : Fin T) : Function.Involutive (flip i) := by
  intro σ
  funext j
  by_cases hj : j = i
  · subst j; simp [flip]
  · simp [flip, Function.update_of_ne hj]

lemma coeff_abs_le {T : ℕ} (σ : Fin T → Bool) (t : ℕ) : |coeff σ t| ≤ 1 := by
  unfold coeff
  split_ifs with ht
  · cases σ ⟨t, ht⟩ <;> norm_num [OGDCube.sign]
  · norm_num

lemma coeff_sum {T : ℕ} (σ : Fin T → Bool) :
    (∑ t ∈ range T, coeff σ t) = OGDCube.walk σ := by
  rw [OGDCube.walk, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp [coeff]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def loss {T : ℕ} (e : E) (σ : Fin T → Bool) (t : ℕ) (x : E) : ℝ :=
  coeff σ t * ⟪e, x⟫

lemma loss_flip {K : Set E} {T : ℕ} (e : E)
    (A : (ℕ → E → ℝ) → ℕ → E) (hA : IsOnlineAlgorithm K A)
    (t : ℕ) (ht : t < T) (σ : Fin T → Bool) :
    loss e (flip ⟨t, ht⟩ σ) t (A (loss e (flip ⟨t, ht⟩ σ)) t) =
      -loss e σ t (A (loss e σ) t) := by
  have hp : A (loss e σ) t = A (loss e (flip ⟨t, ht⟩ σ)) t := by
    apply hA.2.2
    intro s hs
    have hsT : s < T := hs.trans ht
    have hne : (⟨s, hsT⟩ : Fin T) ≠ ⟨t, ht⟩ := by
      intro h
      have h' : s = t := congrArg (fun j : Fin T => (j : ℕ)) h
      exact (ne_of_lt hs) h'
    funext x
    simp [loss, coeff, hsT, flip, Function.update_of_ne hne]
  rw [← hp]
  have hc : coeff (flip ⟨t, ht⟩ σ) t = -coeff σ t := by
    simp only [coeff, dif_pos ht, flip, Function.update_self]
    cases σ ⟨t, ht⟩ <;> norm_num [OGDCube.sign]
  simp [loss, hc]

lemma expect_play_zero {K : Set E} (T : ℕ) (e : E)
    (A : (ℕ → E → ℝ) → ℕ → E) (hA : IsOnlineAlgorithm K A) (t : ℕ) :
    (𝔼 σ : Fin T → Bool, loss e σ t (A (loss e σ) t)) = 0 := by
  by_cases ht : t < T
  · have h : (𝔼 σ : Fin T → Bool, loss e σ t (A (loss e σ) t)) =
        𝔼 σ : Fin T → Bool, -(loss e σ t (A (loss e σ) t)) := by
      apply Fintype.expect_bijective (flip ⟨t, ht⟩) (flip_involutive ⟨t, ht⟩).bijective
      intro σ
      rw [loss_flip e A hA t ht σ, neg_neg]
    rw [expect_neg_distrib] at h
    linarith
  · simp [loss, coeff, ht]

lemma exists_large_proxy {K : Set E} (T : ℕ) (hT : 0 < T) (e : E)
    (A : (ℕ → E → ℝ) → ℕ → E) (hA : IsOnlineAlgorithm K A) :
    ∃ σ : Fin T → Bool, Real.sqrt T / 2 ≤
      (∑ t ∈ range T, loss e σ t (A (loss e σ) t)) + |OGDCube.walk σ| := by
  have hsum : (𝔼 σ : Fin T → Bool, ∑ t ∈ range T, loss e σ t (A (loss e σ) t)) = 0 := by
    rw [expect_sum_comm]
    simp only [expect_play_zero T e A hA, sum_const_zero]
  have h : Real.sqrt T / 2 ≤ 𝔼 σ : Fin T → Bool,
      ((∑ t ∈ range T, loss e σ t (A (loss e σ) t)) + |OGDCube.walk σ|) := by
    rw [expect_add_distrib, hsum, zero_add]
    exact OGDCube.abs_expect_lower T hT
  obtain ⟨σ, _, hσ⟩ := exists_le_of_le_expect univ_nonempty h
  exact ⟨σ, hσ⟩

end OGDLower

#print axioms OGDLower.exists_large_proxy


open OnlineConvexOpt.FirstOrder OGDLower Finset
open scoped BigOperators RealInnerProductSpace

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (D G : ℝ), 0 < D ∧ 0 < G ∧
        Convex ℝ K ∧ IsComplete K ∧ K.Nonempty ∧ (∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) ∧
        ∀ (A : (ℕ → EuclideanSpace ℝ (Fin n) → ℝ) → ℕ → EuclideanSpace ℝ (Fin n)),
          IsOnlineAlgorithm K A →
          ∀ T : ℕ, 1 ≤ T →
            ∃ f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
              (∀ t, ConvexOn ℝ K (f t)) ∧
              (∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y) ∧
              (∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G) ∧
              c * D * G * Real.sqrt T ≤ RegretT K f (fun t => A f t) T := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro n hn
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  let K : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1
  have hconv : Convex ℝ K := convex_closedBall _ _
  refine ⟨K, 2, 1, by norm_num, by norm_num, hconv,
    Metric.isClosed_closedBall.isComplete, ⟨0, by simp [K]⟩, ?_, ?_⟩
  · intro x hx y hy
    have hx' : dist x 0 ≤ 1 := hx
    have hy' : dist 0 y ≤ 1 := by
      have hy'' : dist y 0 ≤ 1 := hy
      simpa only [dist_comm] using hy''
    have h := dist_triangle x 0 y
    linarith
  · intro A hA T hT
    obtain ⟨σ, hσ⟩ := exists_large_proxy T (by omega) e A hA
    have hp (t : ℕ) : ConvexOn ℝ K (loss e σ t) ∧
        (∀ x ∈ K, ∀ y ∈ K, |loss e σ t x - loss e σ t y| ≤ 1 * dist x y) ∧
        (∀ x ∈ K, ∀ v, HasGradientAt (loss e σ t) v x → ‖v‖ ≤ 1) := by
      have hv : ‖coeff σ t • e‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, he, mul_one]
        exact coeff_abs_le σ t
      have hh := linear_properties K hconv (coeff σ t • e) hv
      have hf : (fun x => ⟪coeff σ t • e, x⟫) = loss e σ t := by
        funext x
        simp [loss, real_inner_smul_left]
      rw [hf] at hh
      simpa only [loss, real_inner_smul_left] using hh
    refine ⟨loss e σ, fun t => (hp t).1, fun t => (hp t).2.1, fun t => (hp t).2.2, ?_⟩
    have hcomp := unit_ball_comparator e he (coeff σ) (fun t => A (loss e σ) t) T
    rw [coeff_sum] at hcomp
    change _ ≤ RegretT K (loss e σ) (fun t => A (loss e σ) t) T at hcomp
    have heq : (1 / 4 : ℝ) * 2 * 1 * Real.sqrt T = Real.sqrt T / 2 := by ring
    rw [heq]
    exact hσ.trans hcomp

#print axioms solution

