-- Prove2me | solution 1 for ProxMethodVI.Rate.lemma3_1_d
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:48.192369+00:00
-- url     : https://prove2.me/submissions/52797aab-c14b-4092-b2e9-576767724388

import Definitions.Def_ProxMethodVI_Rate_Setting
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

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

private theorem prox_lip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (U : Set E) (hUZ : U ⊆ Z) (hUne : U.Nonempty) (hUc : Convex ℝ U) (hUcl : IsClosed U)
    (z : E) (hz : z ∈ Z) (ξ η : E →L[ℝ] ℝ) (γ : ℝ) (hγ : 0 < γ)
    (w : E) (hw : IsProxPt U ω ω' z (γ • ξ) w)
    (zp : E) (hzp : IsProxPt U ω ω' z (γ • η) zp) :
    ‖w - zp‖ ≤ α⁻¹ * γ * ‖ξ - η‖ := by
  have hviw := prox_vi Z U hUZ hUc ω ω' hω.2.1 z w zp (γ • ξ) hw hzp.1
  have hviz := prox_vi Z U hUZ hUc ω ω' hω.2.1 z zp w (γ • η) hzp hw.1
  have hmono := hω.2.2.2 w (hUZ hw.1) zp (hUZ hzp.1)
  have hcore : α * ‖w - zp‖ ^ 2 ≤ γ * (η - ξ) (w - zp) := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub] at *
    linarith
  have hdual : (η - ξ) (w - zp) ≤ ‖ξ - η‖ * ‖w - zp‖ := by
    calc
      (η - ξ) (w - zp) ≤ |(η - ξ) (w - zp)| := le_abs_self _
      _ = ‖(η - ξ) (w - zp)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖η - ξ‖ * ‖w - zp‖ := (η - ξ).le_opNorm _
      _ = _ := by rw [norm_sub_rev]
  have hbound := hcore.trans (mul_le_mul_of_nonneg_left hdual hγ.le)
  by_cases hn : ‖w - zp‖ = 0
  · rw [hn]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hω.1.le) hγ.le) (norm_nonneg _)
  have hnp : 0 < ‖w - zp‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  have hlin : α * ‖w - zp‖ ≤ γ * ‖ξ - η‖ := by
    by_contra! hcontr
    have hmul := mul_lt_mul_of_pos_right hcontr hnp
    nlinarith only [hbound, hmul]
  calc
    ‖w - zp‖ = α⁻¹ * (α * ‖w - zp‖) := by field_simp [hω.1.ne']
    _ ≤ α⁻¹ * (γ * ‖ξ - η‖) := mul_le_mul_of_nonneg_left hlin (inv_nonneg.mpr hω.1.le)
    _ = _ := by ring



theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (U : Set E) (hUZ : U ⊆ Z) (hUne : U.Nonempty) (hUc : Convex ℝ U) (hUcl : IsClosed U)
    (z : E) (hz : z ∈ Z) (ξ η : E →L[ℝ] ℝ) (γ : ℝ) (hγ : 0 < γ)
    (w : E) (hw : IsProxPt U ω ω' z (γ • ξ) w)
    (zp : E) (hzp : IsProxPt U ω ω' z (γ • η) zp) :
    γ * (η - ξ) (w - zp) + (ω z + ω' z (w - z) + ω' w (zp - w) - ω zp)
      ≤ α⁻¹ * γ ^ 2 * ‖ξ - η‖ ^ 2 - α / 2 * (‖w - z‖ ^ 2 + ‖w - zp‖ ^ 2) := by
  have h1 := dgf_bound Z hZc ω ω' α hω z w hz (hUZ hw.1)
  have h2 := dgf_bound Z hZc ω ω' α hω w zp (hUZ hw.1) (hUZ hzp.1)
  rw [norm_sub_rev zp w] at h2
  have hlip := prox_lip Z hZc hZk hZne ω ω' α hω U hUZ hUne hUc hUcl z hz ξ η γ hγ w hw zp hzp
  have hdual : (η - ξ) (w - zp) ≤ ‖ξ - η‖ * ‖w - zp‖ := by
    calc
      (η - ξ) (w - zp) ≤ |(η - ξ) (w - zp)| := le_abs_self _
      _ = ‖(η - ξ) (w - zp)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖η - ξ‖ * ‖w - zp‖ := (η - ξ).le_opNorm _
      _ = _ := by rw [norm_sub_rev]
  have hcross : γ * (η - ξ) (w - zp) ≤ α⁻¹ * γ ^ 2 * ‖ξ - η‖ ^ 2 := by
    calc
      γ * (η - ξ) (w - zp) ≤ γ * (‖ξ - η‖ * ‖w - zp‖) :=
        mul_le_mul_of_nonneg_left hdual hγ.le
      _ = (γ * ‖ξ - η‖) * ‖w - zp‖ := by ring
      _ ≤ (γ * ‖ξ - η‖) * (α⁻¹ * γ * ‖ξ - η‖) :=
        mul_le_mul_of_nonneg_left hlip (mul_nonneg hγ.le (norm_nonneg _))
      _ = _ := by ring
  nlinarith only [h1, h2, hcross]

#print axioms solution


