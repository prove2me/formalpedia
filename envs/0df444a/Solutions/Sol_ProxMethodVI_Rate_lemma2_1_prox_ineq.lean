-- Prove2me | solution 1 for ProxMethodVI.Rate.lemma2_1_prox_ineq
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:41.092132+00:00
-- url     : https://prove2.me/submissions/b3741d33-3182-48ef-a72a-27a96a07ee26

import Definitions.Def_ProxMethodVI_Rate_Setting
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open ProxMethodVI.Rate

private theorem dgf_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ)
    (α : ℝ) (hω : IsStrongDGF Z ω ω' α) (z v : E) (hz : z ∈ Z) (hv : v ∈ Z) :
    α / 2 * ‖v - z‖ ^ 2 ≤ ω v - ω z - ω' z (v - z) := by
  let d := v - z
  let a : ℝ → E := fun t => z + t • d
  let f : ℝ → ℝ := fun t => ω (a t) - ω z - t * ω' z d - α / 2 * t ^ 2 * ‖d‖ ^ 2
  let fp : ℝ → ℝ := fun t => ω' (a t) d - ω' z d - α * t * ‖d‖ ^ 2
  have hamem : Set.MapsTo a (Set.Icc 0 1) Z := by
    intro t ht
    exact hZc.add_smul_sub_mem hz hv ht
  have had (t : ℝ) : HasDerivAt a d t := by
    simpa only [a, id_eq, one_smul] using ((hasDerivAt_id t).smul_const d).const_add z
  have hfd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt f (fp t) (Set.Icc 0 1) t := by
    have hcomp := (hω.2.1 (a t) (hamem ht)).comp_hasDerivWithinAt t
      (had t).hasDerivWithinAt hamem
    have hder := ((hcomp.sub_const (ω z)).sub
      ((hasDerivAt_id t).mul_const (ω' z d)).hasDerivWithinAt).sub
      ((((hasDerivAt_id t).pow 2).const_mul (α / 2)).mul_const (‖d‖ ^ 2)).hasDerivWithinAt
    convert hder using 1 <;> (first | rfl | (simp only [f, fp, Function.comp, id_eq]; ring))
  have hnonneg (t : ℝ) (ht : t ∈ interior (Set.Icc (0 : ℝ) 1)) : 0 ≤ fp t := by
    rw [interior_Icc] at ht
    have hm := hω.2.2.2 (a t) (hamem ⟨ht.1.le, ht.2.le⟩) z hz
    have hadiff : a t - z = t • d := by simp [a]
    rw [hadiff, norm_smul, Real.norm_of_nonneg ht.1.le] at hm
    simp only [ContinuousLinearMap.sub_apply, map_smul, smul_eq_mul] at hm
    have hlin : α * t * ‖d‖ ^ 2 ≤ ω' (a t) d - ω' z d := by
      by_contra! hcontra
      have hmul := mul_lt_mul_of_pos_right hcontra ht.1
      nlinarith only [hm, hmul]
    dsimp [fp]
    linarith only [hlin]
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hfd t ht).continuousWithinAt)
      (fun t ht => (hfd t (interior_subset ht)).mono interior_subset) hnonneg
  have hest := hmono (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) zero_le_one
  have ha0 : a 0 = z := by simp [a]
  have ha1 : a 1 = v := by simp [a, d]
  dsimp [f] at hest
  rw [ha0, ha1] at hest
  norm_num at hest
  dsimp [d] at hest ⊢
  linarith only [hest]



private theorem prox_vi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z U : Set E) (hUZ : U ⊆ Z) (hUc : Convex ℝ U)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ)
    (hω : ∀ x ∈ Z, HasFDerivWithinAt ω (ω' x) Z x)
    (z v u : E) (ξ : E →L[ℝ] ℝ) (hv : IsProxPt U ω ω' z ξ v) (hu : u ∈ U) :
    0 ≤ (ω' v + (ξ - ω' z)) (u - v) := by
  have hd : HasFDerivWithinAt (fun y => ω y + (ξ - ω' z) y)
      (ω' v + (ξ - ω' z)) U v :=
    ((hω v (hUZ hv.1)).mono hUZ).add (ξ - ω' z).hasFDerivAt.hasFDerivWithinAt
  have hmin : IsMinOn (fun y => ω y + (ξ - ω' z) y) U v := hv.2
  exact hmin.localize.hasFDerivWithinAt_nonneg hd
    (sub_mem_posTangentConeAt_of_segment_subset (hUc.segment_subset hv.1 hu))


private theorem legendre_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ)
    (α : ℝ) (hω : IsStrongDGF Z ω ω' α) (x : E) (hx : x ∈ Z) :
    legendre Z ω (ω' x) = ω' x x - ω x := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro b ⟨y, hy, rfl⟩
  have hD := dgf_bound Z hZc ω ω' α hω x y hx hy
  have h0 : 0 ≤ α / 2 * ‖y - x‖ ^ 2 :=
    mul_nonneg (div_nonneg hω.1.le (by norm_num)) (sq_nonneg _)
  simp only [map_sub] at hD
  linarith


theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (z : E) (hz : z ∈ Z) (ξ : E →L[ℝ] ℝ) (v : E) (hv : IsProxPt Z ω ω' z ξ v)
    (u : E) (hu : u ∈ Z) :
    Hfun Z ω ω' u v - Hfun Z ω ω' u z ≤ ξ (u - v) + (ω z + ω' z (v - z) - ω v) ∧
      ω z + ω' z (v - z) - ω v ≤ 0 := by
  have hzval := legendre_at Z hZc ω ω' α hω z hz
  have hvval := legendre_at Z hZc ω ω' α hω v hv.1
  have hvi := prox_vi Z Z Set.Subset.rfl hZc ω ω' hω.2.1 z v u ξ hv hu
  have hD := dgf_bound Z hZc ω ω' α hω z v hz hv.1
  have hD0 : 0 ≤ α / 2 * ‖v - z‖ ^ 2 :=
    mul_nonneg (div_nonneg hω.1.le (by norm_num)) (sq_nonneg _)
  constructor
  · unfold Hfun
    rw [hzval, hvval]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_sub] at *
    linarith
  · linarith

#print axioms solution



