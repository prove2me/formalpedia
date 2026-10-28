-- Prove2me | solution 1 for ProxMethodVI.Rate.lemma3_1_c
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:49:39.249541+00:00
-- url     : https://prove2.me/submissions/cc8609e5-f832-4df7-be37-cffa7847fdd7

import Definitions.Def_ProxMethodVI_Rate_Setting
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open ProxMethodVI.Rate

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

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (U : Set E) (hUZ : U ⊆ Z) (hUne : U.Nonempty) (hUc : Convex ℝ U) (hUcl : IsClosed U)
    (z : E) (hz : z ∈ Z) (ξ η : E →L[ℝ] ℝ) (γ : ℝ) (hγ : 0 < γ)
    (w : E) (hw : IsProxPt U ω ω' z (γ • ξ) w)
    (zp : E) (hzp : IsProxPt U ω ω' z (γ • η) zp) :
    γ * η (w - zp) + (ω z + ω' z (zp - z) - ω zp)
      ≤ γ * (η - ξ) (w - zp) + (ω z + ω' z (w - z) + ω' w (zp - w) - ω zp) := by
  have hv := prox_vi Z U hUZ hUc ω ω' hω.2.1 z w zp (γ • ξ) hw hzp.1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub] at *
  linarith

#print axioms solution
