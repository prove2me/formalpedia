-- Prove2me | solution 1 for SelfScaledLongStep.PathFollow.theorem_9_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:13:58.638213+00:00
-- url     : https://prove2.me/submissions/e1ff9c97-bf70-4f20-96a8-ed3c99ad7573
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PathFollow_Defs
import Theorems.Thm_SelfScaledLongStep_PathFollow_theorem_9_2
import Theorems.Thm_SelfScaledLongStep_PathFollow_theorem_4_3
import Theorems.Thm_SelfScaledLongStep_PathFollow_proposition_6_3
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_1
import Theorems.Thm_SelfScaledIPM_FuncProx_proposition_3_5

open scoped InnerProductSpace Pointwise
open SelfScaledIPM.ShortStep

namespace SSB93Aux

variable {n : ℕ}

/-- Cauchy–Schwarz for a symmetric positive semidefinite operator. -/
theorem cs_form (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsym : ∀ a b, ⟪H a, b⟫_ℝ = ⟪a, H b⟫_ℝ) (hpsd : ∀ a, 0 ≤ ⟪H a, a⟫_ℝ)
    (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪H a, b⟫_ℝ ^ 2 ≤ ⟪H a, a⟫_ℝ * ⟪H b, b⟫_ℝ := by
  have key : ∀ t : ℝ, 0 ≤ ⟪H b, b⟫_ℝ * (t * t) + (2 * ⟪H a, b⟫_ℝ) * t + ⟪H a, a⟫_ℝ := by
    intro t
    have h0 := hpsd (a + t • b)
    have hba : ⟪H b, a⟫_ℝ = ⟪H a, b⟫_ℝ := by
      rw [hsym, real_inner_comm]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real] at h0
    rw [hba] at h0
    nlinarith [h0]
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith [hd]

theorem sqrt_cs (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsym : ∀ a b, ⟪H a, b⟫_ℝ = ⟪a, H b⟫_ℝ) (hpsd : ∀ a, 0 ≤ ⟪H a, a⟫_ℝ)
    (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪H a, b⟫_ℝ ≤ Real.sqrt ⟪H a, a⟫_ℝ * Real.sqrt ⟪H b, b⟫_ℝ := by
  rw [← Real.sqrt_mul (hpsd a)]
  exact Real.le_sqrt_of_sq_le (cs_form H hsym hpsd a b)

/-- Inverse of a positive definite operator is a right inverse. -/
theorem inv_right (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hpd : ∀ a, a ≠ 0 → 0 < ⟪H a, a⟫_ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    H (H.inverse u) = u := by
  have hinj : Function.Injective (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
    intro a b hab
    by_contra hne
    have h1 := hpd (a - b) (sub_ne_zero.mpr hne)
    have : H (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hab
    rw [this, inner_zero_left] at h1
    exact lt_irrefl _ h1
  let e := (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv
  have he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = H := by
    ext x; rfl
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact e.apply_symm_apply u

/-- (D1) `⟨u, h⟩ ≤ ‖u‖* ‖h‖`. -/
theorem dual_le (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsym : ∀ a b, ⟪H a, b⟫_ℝ = ⟪a, H b⟫_ℝ) (hpd : ∀ a, a ≠ 0 → 0 < ⟪H a, a⟫_ℝ)
    (u h : EuclideanSpace ℝ (Fin n)) :
    ⟪u, h⟫_ℝ ≤ Real.sqrt ⟪H.inverse u, u⟫_ℝ * Real.sqrt ⟪H h, h⟫_ℝ := by
  have hpsd : ∀ a, 0 ≤ ⟪H a, a⟫_ℝ := by
    intro a; by_cases ha : a = 0
    · simp [ha]
    · exact (hpd a ha).le
  set q := H.inverse u
  have hq : H q = u := inv_right H hpd u
  have h1 := sqrt_cs H hsym hpsd q h
  rw [hq] at h1
  have e : ⟪u, q⟫_ℝ = ⟪q, u⟫_ℝ := real_inner_comm _ _
  rw [e] at h1
  exact h1

/-- (D2) if `⟨u, h⟩ ≤ M ‖h‖` for all `h` then `‖u‖* ≤ M`. -/
theorem dual_le_of (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hpd : ∀ a, a ≠ 0 → 0 < ⟪H a, a⟫_ℝ)
    (u : EuclideanSpace ℝ (Fin n)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ h, ⟪u, h⟫_ℝ ≤ M * Real.sqrt ⟪H h, h⟫_ℝ) :
    Real.sqrt ⟪H.inverse u, u⟫_ℝ ≤ M := by
  have hpsd : ∀ a, 0 ≤ ⟪H a, a⟫_ℝ := by
    intro a; by_cases ha : a = 0
    · simp [ha]
    · exact (hpd a ha).le
  set q := H.inverse u
  have hq : H q = u := inv_right H hpd u
  have h1 := hb q
  have ht : ⟪q, u⟫_ℝ = ⟪H q, q⟫_ℝ := by rw [hq, real_inner_comm]
  rw [real_inner_comm] at h1
  rw [ht] at h1 ⊢
  set t := ⟪H q, q⟫_ℝ
  have ht0 : 0 ≤ t := hpsd q
  have hs := Real.sq_sqrt ht0
  by_contra hcon
  push Not at hcon
  have hpos : 0 < Real.sqrt t := lt_of_le_of_lt hM hcon
  have := mul_lt_mul_of_pos_right hcon hpos
  nlinarith


theorem hess_inner (F : EuclideanSpace ℝ (Fin n) → ℝ) (w h k : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F w h, k⟫_ℝ = fderiv ℝ (fderiv ℝ F) w h k := by
  have hg : gradient F = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ∘
      fderiv ℝ F := by
    funext x; rfl
  unfold hess
  rw [hg, LinearIsometryEquiv.comp_fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

theorem hess_symm (F : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    (hF : ContDiffAt ℝ 3 F w) (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F w a, b⟫_ℝ = ⟪a, hess F w b⟫_ℝ := by
  have hs : IsSymmSndFDerivAt ℝ F w := hF.isSymmSndFDerivAt (by simp; norm_num)
  rw [real_inner_comm (hess F w b) a, hess_inner, hess_inner]
  exact hs a b

theorem grad_inner (F : EuclideanSpace ℝ (Fin n) → ℝ) (x h : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient F x, h⟫_ℝ = fderiv ℝ F x h := by
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

/-- Positive homogeneity of `σ` for a cone. -/
theorem sigma_smul (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcone : ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K)
    (x u : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 < t) :
    sigma K x (t • u) = t * sigma K x u := by
  unfold sigma
  have hset : {β : ℝ | 0 ≤ β ∧ β • x - t • u ∈ K} = t • {β : ℝ | 0 ≤ β ∧ β • x - u ∈ K} := by
    ext β
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨hβ, hK⟩
      refine ⟨β / t, ⟨div_nonneg hβ ht.le, ?_⟩, by field_simp⟩
      have := hcone _ hK (1 / t) (by positivity)
      have e : (1 / t) • (β • x - t • u) = (β / t) • x - u := by
        rw [smul_sub, smul_smul, smul_smul]
        congr 1
        · congr 1; field_simp
        · rw [show 1 / t * t = 1 by field_simp, one_smul]
      rwa [e] at this
    · rintro ⟨γ, ⟨hγ, hK⟩, rfl⟩
      refine ⟨mul_nonneg ht.le hγ, ?_⟩
      have := hcone _ hK t ht.le
      have e : t • (γ • x - u) = (t * γ) • x - t • u := by
        rw [smul_sub, smul_smul]
      rwa [e] at this
  rw [hset, Real.sInf_smul_of_nonneg ht.le, smul_eq_mul]

theorem sigma_nonneg (K : Set (EuclideanSpace ℝ (Fin n))) (x u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ sigma K x u := Real.sInf_nonneg (fun _ h => h.1)

end SSB93Aux


open SelfScaledLongStep.PathFollow

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A) (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n)), IsDualStrict K A c y s)
    (τ : ℝ) (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) (hx : IsPrimalStrict K A b x)
    (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : IsNewtonDir F A c τ x y p) (hπ : lnorm F x p ≤ 1 / 4)
    (ŷ : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n))
    (hvdir : IsTangentDir F A c x ŷ v) (hv : v ≠ 0)
    (Δτ τ₁ : ℝ) (z x₁ : EuclideanSpace ℝ (Fin n))
    (hΔτ : Δτ = tangentStep K F x v) (hz : z = x - Δτ • v) (hτ₁ : τ₁ = τ + Δτ)
    (yz : EuclideanSpace ℝ (Fin m)) (pz : EuclideanSpace ℝ (Fin n))
    (hpz : IsNewtonDir F A c τ₁ z yz pz) (hx₁ : x₁ = z - pz) :
    z ∈ interior K ∧ IsPrimalStrict K A b x₁ ∧
      (∀ (y' : EuclideanSpace ℝ (Fin m)) (p' : EuclideanSpace ℝ (Fin n)),
        IsNewtonDir F A c τ₁ x₁ y' p' → lnorm F x₁ p' ≤ 1 / 4) ∧
      (1 + 3 / (8 * Real.sqrt ν + 2) * Real.sqrt (lnorm F x v / absn K x v)) * τ ≤ τ₁ ∧
      (1 + 3 / (8 * Real.sqrt ν + 2)) * τ ≤
        (1 + 3 / (8 * Real.sqrt ν + 2) * Real.sqrt (lnorm F x v / absn K x v)) * τ := by
  obtain ⟨hxK, hAx⟩ := hx
  -- basic operator facts at interior points
  have hPD : ∀ w ∈ interior K, ∀ h, h ≠ 0 → 0 < ⟪hess F w h, h⟫_ℝ := hF.1.2.2.2.2
  have hPSD : ∀ w ∈ interior K, ∀ h, 0 ≤ ⟪hess F w h, h⟫_ℝ := by
    intro w hw h
    by_cases h0 : h = 0
    · simp [h0]
    · exact (hPD w hw h h0).le
  have hSym : ∀ w ∈ interior K, ∀ a b, ⟪hess F w a, b⟫_ℝ = ⟪a, hess F w b⟫_ℝ := by
    intro w hw a b
    exact SSB93Aux.hess_symm F w
      ((hF.1.1.2.1.contDiffAt (isOpen_interior.mem_nhds hw))) a b
  have D1 : ∀ w ∈ interior K, ∀ u h, ⟪u, h⟫_ℝ ≤ dnorm F w u * lnorm F w h :=
    fun w hw u h => SSB93Aux.dual_le (hess F w) (hSym w hw) (hPD w hw) u h
  have D2 : ∀ w ∈ interior K, ∀ u (M : ℝ), 0 ≤ M →
      (∀ h, ⟪u, h⟫_ℝ ≤ M * lnorm F w h) → dnorm F w u ≤ M :=
    fun w hw u M hM hb => SSB93Aux.dual_le_of (hess F w) (hPD w hw) u M hM hb
  have dn0 : ∀ w u, 0 ≤ dnorm F w u := fun w u => Real.sqrt_nonneg _
  have ln0 : ∀ w u, 0 ≤ lnorm F w u := fun w u => Real.sqrt_nonneg _
  have Dtri : ∀ w ∈ interior K, ∀ u₁ u₂, dnorm F w (u₁ + u₂) ≤ dnorm F w u₁ + dnorm F w u₂ := by
    intro w hw u₁ u₂
    apply D2 w hw _ _ (add_nonneg (dn0 _ _) (dn0 _ _))
    intro h
    rw [inner_add_left, add_mul]
    exact add_le_add (D1 w hw u₁ h) (D1 w hw u₂ h)
  have lcs : ∀ w ∈ interior K, ∀ a h, ⟪hess F w a, h⟫_ℝ ≤ lnorm F w a * lnorm F w h :=
    fun w hw a h => SSB93Aux.sqrt_cs (hess F w) (hSym w hw) (hPSD w hw) a h
  -- the norms of v
  set a := absn K x v with ha_def
  set l := lnorm F x v with hl_def
  have hl : 0 < l := Real.sqrt_pos.mpr (hPD x hxK v hv)
  have h35 := (SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF).1 x hxK v
  have hal : a ≤ l := h35.1
  have hsν : 1 ≤ Real.sqrt ν := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hν
  have ha : 0 < a := by
    by_contra hneg
    push Not at hneg
    have : Real.sqrt ν * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
    linarith [h35.2]
  -- the step size
  set s := Real.sqrt (a * l) with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos ha hl)
  have hs2 : s ^ 2 = a * l := Real.sq_sqrt (mul_pos ha hl).le
  have hΔ : Δτ = 3 / (8 * s) := by rw [hΔτ]; rfl
  have hΔpos : 0 < Δτ := by rw [hΔ]; positivity
  have has : a ≤ s := by
    rw [hs_def]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hΔa : Δτ * a ≤ 3 / 8 := by
    rw [hΔ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hΔ2 : Δτ * a * (Δτ * l) = 9 / 64 := by
    rw [hΔ]; field_simp; nlinarith [hs2]
  -- σ bounds
  have hσ1 : sigma K x v ≤ a := le_max_left _ _
  have hσ2 : sigma K x (-v) ≤ a := le_max_right _ _
  have hσ1' := SSB93Aux.sigma_nonneg K x v
  have hσ2' := SSB93Aux.sigma_nonneg K x (-v)
  -- Theorem 4.1
  have h41 := SelfScaledLongStep.PrimalDual.theorem_4_1 K hK F ν hν hF x v hxK Δτ hΔpos.le
    (by nlinarith)
  rw [← hz] at h41
  obtain ⟨hzK, hH⟩ := h41
  have hHz : ∀ h, ⟪hess F x h, h⟫_ℝ ≤ (1 + Δτ * a) ^ 2 * ⟪hess F z h, h⟫_ℝ := by
    intro h
    have h1 := (hH h).1
    have hq : 0 < (1 + Δτ * sigma K x (-v)) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hq] at h1
    have hz0 := hPSD z hzK h
    have : (1 + Δτ * sigma K x (-v)) ^ 2 ≤ (1 + Δτ * a) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); nlinarith
    nlinarith
  have hlz : ∀ h, lnorm F x h ≤ (1 + Δτ * a) * lnorm F z h := by
    intro h
    unfold lnorm
    rw [show (1 + Δτ * a) = Real.sqrt ((1 + Δτ * a) ^ 2) by
      rw [Real.sqrt_sq (by positivity)], ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (hHz h)
  -- dual norm of F''(x)p at z
  have hTp : dnorm F z (hess F x p) ≤ (1 + Δτ * a) * lnorm F x p := by
    apply D2 z hzK _ _ (mul_nonneg (by nlinarith [mul_pos hΔpos ha]) (ln0 _ _))
    intro h
    calc ⟪hess F x p, h⟫_ℝ ≤ lnorm F x p * lnorm F x h := lcs x hxK p h
      _ ≤ lnorm F x p * ((1 + Δτ * a) * lnorm F z h) :=
          mul_le_mul_of_nonneg_left (hlz h) (ln0 _ _)
      _ = (1 + Δτ * a) * lnorm F x p * lnorm F z h := by ring
  -- Theorem 4.3
  have h43 := theorem_4_3 K hK F ν hν hF x z hxK hzK
  have hzx : z - x = Δτ • (-v) := by rw [hz, smul_neg]; abel
  have habs : absn K x (z - x) = Δτ * a := by
    rw [hzx]; unfold absn
    rw [SSB93Aux.sigma_smul K hK.2.2.1 x _ Δτ hΔpos, ← smul_neg, neg_neg,
      SSB93Aux.sigma_smul K hK.2.2.1 x _ Δτ hΔpos, ← mul_max_of_nonneg _ _ hΔpos.le]
    rw [ha_def]; unfold absn; rw [max_comm]
  have hlnz : lnorm F x (z - x) = Δτ * l := by
    rw [hzx, hl_def]; unfold lnorm
    rw [map_smul, map_neg, inner_smul_left, inner_smul_right, inner_neg_left, inner_neg_right,
      neg_neg, RCLike.conj_to_real, ← mul_assoc, Real.sqrt_mul (by positivity),
      Real.sqrt_mul_self hΔpos.le]
  rw [habs, hlnz, hΔ2] at h43
  -- the key identity
  have hpe := hp.2
  have hve := hvdir.2
  have hid : τ₁ • c + gradient F z - ContinuousLinearMap.adjoint A (y + Δτ • ŷ) =
      (gradient F z - gradient F x - hess F x (z - x)) + hess F x p := by
    rw [hzx, hτ₁, add_smul, map_add, map_smul, map_smul, map_neg]
    have e1 : τ • c = ContinuousLinearMap.adjoint A y + hess F x p - gradient F x := by
      rw [hpe]; abel
    rw [e1, ← hve, smul_add]
    module
  -- Proposition 6.3 at z
  have h63 := (proposition_6_3 K hK F ν hν hF A hA z _ hzK yz pz hpz).1 (y + Δτ • ŷ)
  rw [hid] at h63
  have hπz : lnorm F z pz ≤ 1 / 2 := by
    have := Dtri z hzK (gradient F z - gradient F x - hess F x (z - x)) (hess F x p)
    have hm : (1 + Δτ * a) * lnorm F x p ≤ (1 + 3 / 8) * (1 / 4) :=
      mul_le_mul (by linarith) hπ (ln0 _ _) (by norm_num)
    linarith
  -- feasibility of z and Theorem 9.2
  have hAz : A z = b := by
    rw [hz, map_sub, map_smul, hvdir.1, smul_zero, sub_zero, hAx]
  have hτ₁pos : 0 < τ₁ := by rw [hτ₁]; linarith
  have h92 := theorem_9_2 K hK F ν hν hF A hA b c hD τ₁ hτ₁pos z ⟨hzK, hAz⟩ yz pz hpz
    (by linarith)
  rw [← hx₁] at h92
  obtain ⟨hx₁f, hx₁π⟩ := h92
  -- (9.5): τ ‖v‖_x ≤ √ν + 1/4
  have hg : dnorm F x (gradient F x) ≤ Real.sqrt ν := by
    apply D2 x hxK _ _ (by positivity)
    intro h
    rw [SSB93Aux.grad_inner]
    have hb := hF.1.2.2.1 x hxK h
    have : |fderiv ℝ F x h| ≤ Real.sqrt ν * lnorm F x h := by
      unfold lnorm
      rw [← Real.sqrt_mul (by linarith), ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hb
    exact (le_abs_self _).trans this
  have hHp : dnorm F x (hess F x p) ≤ lnorm F x p := by
    apply D2 x hxK _ _ (ln0 _ _)
    intro h; exact lcs x hxK p h
  have h95 : τ * l ≤ Real.sqrt ν + 1 / 4 := by
    have hl2 : l * l = ⟪hess F x v, v⟫_ℝ := by
      rw [hl_def]; unfold lnorm; exact Real.mul_self_sqrt (hPSD x hxK v)
    have hcv : ⟪c, v⟫_ℝ = ⟪hess F x v, v⟫_ℝ := by
      rw [← hve, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hvdir.1, inner_zero_right,
        zero_add]
    have hτc : τ * ⟪c, v⟫_ℝ = ⟪hess F x p - gradient F x, v⟫_ℝ := by
      have e2 : hess F x p - gradient F x = τ • c - ContinuousLinearMap.adjoint A y := by
        have e3 : τ • c = ContinuousLinearMap.adjoint A y + hess F x p - gradient F x := by
          rw [hpe]; abel
        rw [e3]; abel
      rw [e2, inner_sub_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left, hvdir.1,
        inner_zero_right, sub_zero]
    have hb1 := D1 x hxK (hess F x p - gradient F x) v
    have hb2 := Dtri x hxK (hess F x p) (-gradient F x)
    have hneg : dnorm F x (-gradient F x) = dnorm F x (gradient F x) := by
      unfold dnorm; rw [map_neg, inner_neg_neg]
    rw [← sub_eq_add_neg, hneg] at hb2
    rw [← hτc, hcv, ← hl2] at hb1
    have : τ * l * l ≤ (Real.sqrt ν + 1 / 4) * l := by
      calc τ * l * l = τ * (l * l) := by ring
        _ ≤ dnorm F x (hess F x p - gradient F x) * l := hb1
        _ ≤ (Real.sqrt ν + 1 / 4) * l := by
          apply mul_le_mul_of_nonneg_right _ hl.le; linarith
    exact le_of_mul_le_mul_right this hl
  -- final inequalities
  have hsq : Real.sqrt (l / a) = Real.sqrt l / Real.sqrt a := Real.sqrt_div' l ha.le
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsl : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hss : s = Real.sqrt a * Real.sqrt l := Real.sqrt_mul ha.le l
  have hll : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl.le
  have hκ : 0 < 8 * Real.sqrt ν + 2 := by positivity
  refine ⟨hzK, hx₁f, ?_, ?_, ?_⟩
  · intro y' p' hp'
    have := (hx₁π y' p' hp')
    have hz0 := ln0 z pz
    nlinarith [this.1, this.2]
  · rw [hτ₁, hsq]
    have key : 3 / (8 * Real.sqrt ν + 2) * (Real.sqrt l / Real.sqrt a) * τ ≤ Δτ := by
      rw [hΔ, hss]
      rw [div_mul_div_comm, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 8 * (τ * l) ≤ 8 * Real.sqrt ν + 2 := by linarith
      have e : 3 * Real.sqrt l * τ * (8 * (Real.sqrt a * Real.sqrt l)) =
          3 * Real.sqrt a * (8 * (τ * l)) := by
        linear_combination (24 * Real.sqrt a * τ) * hll
      rw [e]
      have : 3 * Real.sqrt a * (8 * (τ * l)) ≤ 3 * Real.sqrt a * (8 * Real.sqrt ν + 2) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith
    nlinarith
  · have h1 : 1 ≤ Real.sqrt (l / a) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ ha]; linarith)
    have : 3 / (8 * Real.sqrt ν + 2) ≤ 3 / (8 * Real.sqrt ν + 2) * Real.sqrt (l / a) :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith
