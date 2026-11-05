-- Prove2me | solution 1 for OffloadGNEP.Exist.partial_gradient_eq_F
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:54:58.814665+00:00
-- url     : https://prove2.me/submissions/1ca3af11-cca9-48c2-b30c-295638210b4f

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

open OffloadGNEP.Exist

theorem solution {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (u : Fin N) (x : Fin N → Tier → ℝ) (hm : P.alpha u * x u .m < 1) (hD : load P x < 1) :
    HasFDerivAt (fun y : Tier → ℝ => cost P u (Function.update x u y))
      (∑ i : Tier, F P x u i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Tier => ℝ) i)
      (x u) := by
  obtain ⟨hn, -, -⟩ := hS
  have hnR : (0 : ℝ) < P.n := by exact_mod_cast hn
  have hsumT : ∀ {M : Type} [AddCommMonoid M] (f : Tier → M), ∑ i, f i = f .m + f .clet + f .cloud := by
    intro M _ f
    show ∑ i ∈ ({Tier.m, Tier.clet, Tier.cloud} : Finset Tier), f i = _
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      add_assoc]
  set c := ∑ v ∈ Finset.univ.erase u, P.delta v * x v .clet with hc
  have hload : ∀ z, load P (Function.update x u z) = (1 / (P.n : ℝ)) * (P.delta u * z .clet + c) := by
    intro z
    unfold load
    rw [← Finset.add_sum_erase Finset.univ
      (fun v => P.delta v * Function.update x u z v .clet) (Finset.mem_univ u), hc]
    congr 2
    · simp
    · apply Finset.sum_congr rfl
      intro v hv
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  have hloadx : load P x = (1 / (P.n : ℝ)) * (P.delta u * x u .clet + c) := by
    have := hload (x u); simpa using this
  let α := P.alpha u
  let δ := P.delta u
  let gm : ℝ → ℝ := fun s => α * s / (1 - α * s)
  let gc : ℝ → ℝ := fun s => δ * s / (1 - (1 / (P.n : ℝ)) * (δ * s + c))
  have hfun : (fun y : Tier → ℝ => cost P u (Function.update x u y)) =
      fun y => gm (y .m) + P.beta u * y .clet + P.gamma u * y .cloud + gc (y .clet) := by
    funext y; unfold cost; rw [hload]; simp [gm, gc, α, δ]
  set t := x u .m
  set s := x u .clet
  have hB : (1 - α * t) ≠ 0 := by
    have : α * t < 1 := hm
    linarith
  have hD0 : (1 - (1 / (P.n : ℝ)) * (δ * s + c)) ≠ 0 := by
    rw [hloadx] at hD; simp only [δ, s]; linarith
  have hgm : HasDerivAt gm (α / (1 - α * t) ^ 2) t := by
    have h := ((hasDerivAt_id' t).const_mul α).div
      (((hasDerivAt_id' t).const_mul α).const_sub 1) hB
    refine h.congr_deriv ?_
    field_simp
    ring
  have hgc : HasDerivAt gc (δ * (1 - (1 / (P.n : ℝ)) * c) / (1 - (1 / (P.n : ℝ)) * (δ * s + c)) ^ 2) s := by
    have h := ((hasDerivAt_id' s).const_mul δ).div
      (((((hasDerivAt_id' s).const_mul δ).add_const c).const_mul (1 / (P.n : ℝ))).const_sub 1) hD0
    refine h.congr_deriv ?_
    field_simp
    ring
  rw [hfun]
  have h1 := HasDerivAt.comp_hasFDerivAt (f := fun y : Tier → ℝ => y Tier.m) (x u) hgm
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Tier => ℝ) Tier.m (x u))
  have h2 := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Tier => ℝ) Tier.clet (x u)).const_mul (P.beta u))
  have h3 := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Tier => ℝ) Tier.cloud (x u)).const_mul (P.gamma u))
  have h4 := HasDerivAt.comp_hasFDerivAt (f := fun y : Tier → ℝ => y Tier.clet) (x u) hgc
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Tier => ℝ) Tier.clet (x u))
  have := ((h1.add h2).add h3).add h4
  refine this.congr_fderiv ?_
  rw [hsumT]
  ext y
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hFm : F P x u .m = α / (1 - α * t) ^ 2 := rfl
  have hFc : F P x u .clet = P.beta u + δ * (1 - (1 / (P.n : ℝ)) * c) /
      (1 - (1 / (P.n : ℝ)) * (δ * s + c)) ^ 2 := by
    show P.beta u + P.delta u * _ / (1 - load P x) ^ 2 = _
    rw [hloadx]
  have hFl : F P x u .cloud = P.gamma u := rfl
  rw [hFm, hFc, hFl]
  simp
  ring
