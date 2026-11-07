-- Prove2me | solution 1 for SelfScaledIPM.ShortStep.corollary_3_14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:00:52.635237+00:00
-- url     : https://prove2.me/submissions/b1927759-6883-43e1-b1c2-d778dd7693b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Theorems.Thm_SelfScaledIPM_ShortStep_lemma_3_13
import Theorems.Thm_SelfScaledLongStep_PrimalDual_dual_isSelfScaledBarrier
import Theorems.Thm_ExpConeIPM_Corrector_homogeneity_identities

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

theorem hess_inner_eq' {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (x v w : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ F) x v w := by
  unfold hess
  have : gradient F = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ∘ fderiv ℝ F := by
    funext y; rfl
  rw [this, LinearIsometryEquiv.comp_fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

theorem hess_symm' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (v w : EuclideanSpace ℝ (Fin n)) : ⟪hess F x v, w⟫_ℝ = ⟪hess F x w, v⟫_ℝ := by
  have hcd : ContDiffAt ℝ 3 F x :=
    hF.1.1.2.1.contDiffAt (isOpen_interior.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℝ F x :=
    hcd.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast (by norm_num : (2:ℕ) ≤ 3))
  rw [hess_inner_eq', hess_inner_eq', hsymm v w]

theorem hess_psd' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (z : EuclideanSpace ℝ (Fin n)) : 0 ≤ ⟪hess F x z, z⟫_ℝ := by
  by_cases hz : z = 0
  · simp [hz]
  · exact (hF.1.2.2.2.2 x hx z hz).le


theorem dnorm_le_of_sandwich {n : ℕ}
    (H B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hpd : ∀ z, z ≠ 0 → 0 < ⟪H z, z⟫_ℝ)
    (hBsym : ∀ u v, ⟪B u, v⟫_ℝ = ⟪B v, u⟫_ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hlo : ∀ v, -(δ * ⟪H v, v⟫_ℝ) ≤ ⟪B v, v⟫_ℝ) (hhi : ∀ v, ⟪B v, v⟫_ℝ ≤ δ * ⟪H v, v⟫_ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt ⟪H.inverse (B v), B v⟫_ℝ ≤ δ * Real.sqrt ⟪H v, v⟫_ℝ := by
  have hpsd : ∀ z, 0 ≤ ⟪H z, z⟫_ℝ := by
    intro z; by_cases hz : z = 0
    · simp [hz]
    · exact (hpd z hz).le
  -- polarization
  have hpol : ∀ u w, 4 * ⟪B u, w⟫_ℝ ≤ 2 * δ * (⟪H u, u⟫_ℝ + ⟪H w, w⟫_ℝ) := by
    intro u w
    have e1 : ⟪B (u + w), u + w⟫_ℝ - ⟪B (u - w), u - w⟫_ℝ = 4 * ⟪B u, w⟫_ℝ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      rw [hBsym w u]; ring
    have e2 : ⟪H (u + w), u + w⟫_ℝ + ⟪H (u - w), u - w⟫_ℝ =
        2 * (⟪H u, u⟫_ℝ + ⟪H w, w⟫_ℝ) := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      ring
    have := hhi (u + w)
    have := hlo (u - w)
    nlinarith
  -- invertibility
  have hinj : Function.Injective H := by
    intro z₁ z₂ h
    by_contra hne
    have hz : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
    have := hpd (z₁ - z₂) hz
    rw [map_sub, h, sub_self, inner_zero_left] at this
    exact lt_irrefl _ this
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofInjectiveEndo H.toLinearMap hinj).toContinuousLinearEquiv
  have he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = H := by
    ext z; rfl
  set z := e.symm (B v) with hz_def
  have hHz : H z = B v := by rw [← he]; simp [z]
  have hinv : H.inverse (B v) = z := by
    rw [← he, ContinuousLinearMap.inverse_equiv]; rfl
  rw [hinv]
  set N2 := ⟪z, B v⟫_ℝ
  set M2 := ⟪H v, v⟫_ℝ
  have hN2 : N2 = ⟪H z, z⟫_ℝ := by rw [hHz, real_inner_comm]
  have hN0 : 0 ≤ N2 := by rw [hN2]; exact hpsd z
  have hM0 : 0 ≤ M2 := hpsd v
  -- for all t: 4 t N2 ≤ 2 δ (t² M2 + N2)
  have hq : ∀ t : ℝ, 4 * (t * N2) ≤ 2 * δ * (t * t * M2 + N2) := by
    intro t
    have := hpol (t • v) z
    simp only [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real] at this
    have e3 : ⟪B v, z⟫_ℝ = N2 := real_inner_comm _ _
    rw [e3, ← hN2] at this
    linarith
  have hkey : N2 ≤ δ ^ 2 * M2 := by
    by_cases hN : N2 = 0
    · rw [hN]; positivity
    · have hNpos : 0 < N2 := lt_of_le_of_ne hN0 (Ne.symm hN)
      have hdisc : discrim (2 * δ * M2) (-(4 * N2)) (2 * δ * N2) ≤ 0 := by
        apply discrim_le_zero
        intro t
        have := hq t
        nlinarith
      unfold discrim at hdisc
      have : N2 * N2 ≤ δ ^ 2 * M2 * N2 := by nlinarith
      exact le_of_mul_le_mul_right (by linarith) hNpos
  calc Real.sqrt N2 ≤ Real.sqrt (δ ^ 2 * M2) := Real.sqrt_le_sqrt hkey
    _ = δ * Real.sqrt M2 := by
      rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ]

theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x s w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) (hw : IsScalingPoint K F x s w)
    (μ : ℝ) (hμ : 0 < μ)
    (hδ : absn (ConvexOptimization.dualCone K) (-gradient F x) (μ⁻¹ • s + gradient F x) < 1) :
    let δ := absn (ConvexOptimization.dualCone K) (-gradient F x) (μ⁻¹ • s + gradient F x)
    let t := -gradient F w
    (∀ v : EuclideanSpace ℝ (Fin n),
      dnorm F x ((μ⁻¹ • hess F w - hess F x) v) ≤ δ * lnorm F x v) ∧
    (∀ u : EuclideanSpace ℝ (Fin n),
      dnorm (conj K F) s ((μ⁻¹ • hess (conj K F) t - hess (conj K F) s) u) ≤
        δ * lnorm (conj K F) s u) := by
  intro δ t
  have h313 := SelfScaledIPM.ShortStep.lemma_3_13 K hK F ν hν hF x s w hx hs hw μ hμ hδ
  obtain ⟨h1, h2⟩ := h313
  have hδ0 : 0 ≤ δ := le_max_of_le_left (Real.sInf_nonneg (fun _ hb => hb.1))
  obtain ⟨hK', hF'⟩ := SelfScaledLongStep.PrimalDual.dual_isSelfScaledBarrier K hK F ν hν hF
  have hwK := hw.1
  have ht : t ∈ interior (ConvexOptimization.dualCone K) := by
    have hh := (ExpConeIPM.Corrector.homogeneity_identities K F ν hK hF.1 w hwK 1 one_pos).2.2.1
    have := (hF.2 w hwK w hwK).1
    rw [hh] at this
    exact this
  constructor
  · intro v
    apply dnorm_le_of_sandwich (hess F x) _ (hF.1.2.2.2.2 x hx) _ δ hδ0 _ _ v
    · intro u v
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
        real_inner_smul_left]
      rw [hess_symm' K F ν hF w hwK u v, hess_symm' K F ν hF x hx u v]
    · intro v
      have := (h1 v).1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
        real_inner_smul_left]
      rw [inv_mul_eq_div]; linarith
    · intro v
      have := (h1 v).2
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
        real_inner_smul_left]
      rw [inv_mul_eq_div]; linarith
  · intro u
    apply dnorm_le_of_sandwich (hess (conj K F) s) _ (hF'.1.2.2.2.2 s hs) _ δ hδ0 _ _ u
    · intro u v
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
        real_inner_smul_left]
      rw [hess_symm' _ _ ν hF' t ht u v, hess_symm' _ _ ν hF' s hs u v]
    · intro v
      have := (h2 v).1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
        real_inner_smul_left]
      rw [inv_mul_eq_div]; linarith
    · intro v
      have := (h2 v).2
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
        real_inner_smul_left]
      rw [inv_mul_eq_div]; linarith
