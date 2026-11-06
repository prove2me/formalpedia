-- Prove2me | solution 1 for SelfScaledIPM.FuncProx.theorem_7_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:25:46.229773+00:00
-- url     : https://prove2.me/submissions/5b9abfe9-fcae-41f2-b498-639e7eaf7e4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures
import Definitions.Def_SelfScaledIPM_FuncProx_Directions
import Theorems.Thm_SelfScaledIPM_FuncProx_proposition_3_5
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_2
import Theorems.Thm_SelfScaledLongStep_PrimalDual_eq_4_9
import Theorems.Thm_SelfScaledIPM_FuncProx_theorem_4_2_global
import Theorems.Thm_SelfScaledIPM_FuncProx_theorem_4_2_local
import Theorems.Thm_SelfScaledIPM_FuncProx_eq_4_28
import Theorems.Thm_SelfScaledIPM_FuncProx_lemma_5_2
import Theorems.Thm_SelfScaledIPM_FuncProx_theorem_5_3
import Theorems.Thm_SelfScaledIPM_FuncProx_lemma_5_4
import Theorems.Thm_SelfScaledIPM_FuncProx_lemma_5_6
import Theorems.Thm_SelfScaledIPM_FuncProx_theorem_5_7

open scoped InnerProductSpace


namespace SSFP71Aux
open SelfScaledIPM.ShortStep

lemma neg_log_bound {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1/2) :
    -τ - Real.log (1 - τ) ≤ 2 * τ ^ 2 := by
  have hpos : 0 < 1 - τ := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have h3 : (1 - τ)⁻¹ - 1 = τ / (1 - τ) := by field_simp; ring
  have h2 : τ / (1 - τ) ≤ τ + 2 * τ ^ 2 := by
    rw [div_le_iff₀ hpos]; nlinarith [mul_nonneg (sq_nonneg τ) (by linarith : (0:ℝ) ≤ 1 - 2 * τ)]
  linarith

lemma f_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a - Real.log (1 + a) ≤ b - Real.log (1 + b) := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos h2 h1)
  rw [Real.log_div h2.ne' h1.ne'] at h
  have : (1 + b) / (1 + a) - 1 ≤ b - a := by
    rw [div_sub_one h1.ne', div_le_iff₀ h1]; nlinarith
  linarith

lemma f_strict {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a - Real.log (1 + a) < b - Real.log (1 + b) := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have hne : (1 + b) / (1 + a) ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq h1.ne'] at h; linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos h2 h1) hne
  rw [Real.log_div h2.ne' h1.ne'] at h
  have : (1 + b) / (1 + a) - 1 ≤ b - a := by
    rw [div_sub_one h1.ne', div_le_iff₀ h1]; nlinarith
  linarith

lemma f_pos {a : ℝ} (ha : 0 < a) : 0 < a - Real.log (1 + a) := by
  have := f_strict (le_refl 0) ha
  simpa using this

lemma hess_surj {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsSelfScaledBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) : Function.Surjective (hess F x) := by
  have hinj : Function.Injective
      ((hess F x : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hh
    by_contra hne
    have := hF.1.2.2.2.2 x hx h hne
    simp only [ContinuousLinearMap.coe_coe] at hh
    rw [hh, inner_zero_left] at this
    exact lt_irrefl _ this
  exact LinearMap.injective_iff_surjective.mp hinj

lemma affine_exists {n m : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (s w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ interior K) :
    ∃ (px : EuclideanSpace ℝ (Fin n)) (py : EuclideanSpace ℝ (Fin m))
      (ps : EuclideanSpace ℝ (Fin n)), SelfScaledIPM.FuncProx.IsAffineScalingDir A F s w px py ps := by
  let E := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let L : (E × Y) →ₗ[ℝ] (Y × E) :=
    LinearMap.prod ((A : E →ₗ[ℝ] Y) ∘ₗ LinearMap.fst ℝ E Y)
      ((hess F w : E →ₗ[ℝ] E) ∘ₗ LinearMap.fst ℝ E Y -
        ((ContinuousLinearMap.adjoint A : Y →L[ℝ] E) : Y →ₗ[ℝ] E) ∘ₗ LinearMap.snd ℝ E Y)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro pq hpq
    have h1 : A pq.1 = 0 := by simpa [L] using congrArg Prod.fst hpq
    have h2 : hess F w pq.1 - ContinuousLinearMap.adjoint A pq.2 = 0 := by
      simpa [L] using congrArg Prod.snd hpq
    have h2' : hess F w pq.1 = ContinuousLinearMap.adjoint A pq.2 := sub_eq_zero.mp h2
    have hp0 : pq.1 = 0 := by
      by_contra hne
      have := hF.1.2.2.2.2 w hw pq.1 hne
      rw [h2', ContinuousLinearMap.adjoint_inner_left, h1, inner_zero_right] at this
      exact lt_irrefl _ this
    have hq : ContinuousLinearMap.adjoint A pq.2 = 0 := by rw [← h2', hp0]; simp
    obtain ⟨v, hv⟩ := hA pq.2
    have hqq : ⟪pq.2, pq.2⟫_ℝ = 0 := by
      conv_lhs => rw [← hv]
      rw [← ContinuousLinearMap.adjoint_inner_left, hv, hq, inner_zero_left]
    have : pq.2 = 0 := inner_self_eq_zero.mp hqq
    exact Prod.ext hp0 this
  have hfin : Module.finrank ℝ (E × Y) = Module.finrank ℝ (Y × E) := by
    rw [Module.finrank_prod, Module.finrank_prod, add_comm]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
  obtain ⟨⟨px, py⟩, h⟩ := hsurj (0, s)
  have hA0 : A px = 0 := by simpa [L] using congrArg Prod.fst h
  have hH : hess F w px - ContinuousLinearMap.adjoint A py = s := by
    simpa [L] using congrArg Prod.snd h
  refine ⟨px, py, -(ContinuousLinearMap.adjoint A py), ?_, hA0, by simp⟩
  rw [← sub_eq_add_neg]; exact hH

lemma step_bound {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (ξ : ℝ) (hξ : 0 < ξ)
    (hxp : x + ξ • p ∈ K) (hsmall : ξ * lnorm F x p ≤ 1 / 2) :
    F (x + ξ • p) - F x ≤ ξ * ⟪gradient F x, p⟫_ℝ + 2 * ξ ^ 2 * (lnorm F x p) ^ 2 := by
  have hL0 : 0 ≤ lnorm F x p := Real.sqrt_nonneg _
  have hLneg : lnorm F x (-p) = lnorm F x p := by
    unfold lnorm; rw [map_neg, inner_neg_neg]
  have hσ0 : 0 ≤ sigma K x (-p) := Real.sInf_nonneg (fun b hb => hb.1)
  have hσL : sigma K x (-p) ≤ lnorm F x p := by
    have := ((SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF).1 x hx (-p)).1
    rw [hLneg] at this
    exact le_trans (le_max_left _ _) this
  rcases hσ0.lt_or_eq with hσ | hσ
  · have hlt : ξ * sigma K x (-p) < 1 := by nlinarith
    have h := SelfScaledLongStep.PrimalDual.theorem_4_2 K hK F ν hν hF x (-p) hx hσ ξ hξ.le hlt
    rw [hLneg, smul_neg, sub_neg_eq_add, inner_neg_right] at h
    have hb := neg_log_bound (τ := ξ * sigma K x (-p)) (by positivity) (by nlinarith)
    have h2 : lnorm F x p ^ 2 / sigma K x (-p) ^ 2 *
        (-(ξ * sigma K x (-p)) - Real.log (1 - ξ * sigma K x (-p))) ≤
        2 * ξ ^ 2 * lnorm F x p ^ 2 := by
      calc _ ≤ lnorm F x p ^ 2 / sigma K x (-p) ^ 2 * (2 * (ξ * sigma K x (-p)) ^ 2) := by
              apply mul_le_mul_of_nonneg_left hb; positivity
        _ = 2 * ξ ^ 2 * lnorm F x p ^ 2 := by field_simp
    linarith
  · have hpK : p ∈ K := by
      let S : Set ℝ := {β : ℝ | 0 ≤ β ∧ β • x - -p ∈ K}
      have hne : S.Nonempty := by
        refine ⟨1 / ξ, by positivity, ?_⟩
        have := hK.2.2.1 _ hxp (1 / ξ) (by positivity)
        have e : (1 / ξ) • (x + ξ • p) = (1 / ξ) • x - -p := by
          rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ hξ.ne', one_smul, sub_neg_eq_add]
        rw [e] at this; exact this
      have hSeq : S = {β : ℝ | 0 ≤ β} ∩ ((fun β : ℝ => β • x - -p) ⁻¹' K) := rfl
      have hcl : IsClosed S := by
        rw [hSeq]
        apply IsClosed.inter (isClosed_le continuous_const continuous_id)
        exact hK.1.preimage (by fun_prop)
      have hmem := hcl.csInf_mem hne ⟨0, fun b hb => hb.1⟩
      have e2 : sigma K x (-p) = sInf S := rfl
      rw [← e2, ← hσ] at hmem
      simpa using hmem.2
    have h := SelfScaledLongStep.PrimalDual.eq_4_9 K hK F ν hν hF x p hx hpK ξ hξ.le
    nlinarith [sq_nonneg (ξ * lnorm F x p)]

lemma arith72 (Δ C₁ C₂ ν ξ L M g D : ℝ) (hΔ : 0 < Δ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 < C₂)
    (hν : 0 < ν) (hξ : 0 ≤ ξ) (hL0 : 0 ≤ L) (hLM : L ≤ M) (hMν : M ≤ ν * C₂)
    (hg : g ≤ ν * C₁) (hD : Δ ≤ D) (KB : ξ * L ≤ 1 / 2 → D ≤ ξ * g + 2 * ξ ^ 2 * L ^ 2) :
    min (min 1 (1 / (2 * C₂))) (Δ / (2 * (C₁ + 2 * C₂ ^ 2))) ≤ ξ * ν := by
  by_contra h
  push Not at h
  have hω1 := lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _))
  have hω2 := lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _))
  have hω3 := lt_of_lt_of_le h (min_le_right _ _)
  have ht0 : 0 ≤ ξ * ν := by positivity
  have hξL : ξ * L ≤ ξ * ν * C₂ := by
    have := mul_le_mul_of_nonneg_left (le_trans hLM hMν) hξ; linarith
  have h2c : ξ * ν * C₂ < 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hω2; linarith
  have hKB := KB (by linarith)
  have hξg : ξ * g ≤ ξ * ν * C₁ := by
    have := mul_le_mul_of_nonneg_left hg hξ; linarith
  have hsq : (ξ * L) ^ 2 ≤ (ξ * ν * C₂) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hξL 2
  have hpos : 0 < C₁ + 2 * C₂ ^ 2 := by positivity
  have h3 : ξ * ν * (C₁ + 2 * C₂ ^ 2) < Δ / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hω3; linarith
  have h4 : (ξ * ν) ^ 2 ≤ ξ * ν := by nlinarith
  have h5 : D ≤ ξ * ν * C₁ + 2 * (ξ * ν) ^ 2 * C₂ ^ 2 := by nlinarith
  have h6 : 2 * (ξ * ν) ^ 2 * C₂ ^ 2 ≤ 2 * (ξ * ν) * C₂ ^ 2 := by
    have := mul_le_mul_of_nonneg_right h4 (sq_nonneg C₂); nlinarith
  nlinarith

lemma arith73 (Δ C₃ ξ L M g D : ℝ) (hΔ : 0 < Δ) (hC₃ : 0 ≤ C₃) (hξ : 0 ≤ ξ) (hL0 : 0 ≤ L)
    (hLM : L ≤ M) (hg : g ≤ C₃ * M) (hD : Δ ≤ D)
    (KB : ξ * L ≤ 1 / 2 → D ≤ ξ * g + 2 * ξ ^ 2 * L ^ 2) :
    min (1 / 2) (Δ / (2 * (C₃ + 2))) ≤ ξ * M := by
  by_contra h
  push Not at h
  have hω1 := lt_of_lt_of_le h (min_le_left _ _)
  have hω2 := lt_of_lt_of_le h (min_le_right _ _)
  have hξL : ξ * L ≤ ξ * M := mul_le_mul_of_nonneg_left hLM hξ
  have hm0 : 0 ≤ ξ * M := le_trans (by positivity) hξL
  have hKB := KB (by linarith)
  have hξg : ξ * g ≤ C₃ * (ξ * M) := by
    have := mul_le_mul_of_nonneg_left hg hξ; linarith
  have hsq : (ξ * L) ^ 2 ≤ (ξ * M) ^ 2 := pow_le_pow_left₀ (by positivity) hξL 2
  have h3 : ξ * M * (C₃ + 2) < Δ / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hω2; linarith
  have h4 : (ξ * M) ^ 2 ≤ ξ * M := by nlinarith
  nlinarith

lemma gap_gen {n : ℕ} (s x ds dx : EuclideanSpace ℝ (Fin n)) (a k : ℝ)
    (h : ⟪s, dx⟫_ℝ + ⟪ds, x⟫_ℝ = k) (h0 : ⟪ds, dx⟫_ℝ = 0) :
    ⟪s - a • ds, x - a • dx⟫_ℝ = ⟪s, x⟫_ℝ - a * k := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, h0, ← h]
  ring

lemma orth {n m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) (q : EuclideanSpace ℝ (Fin m)) (r : EuclideanSpace ℝ (Fin n))
    (h1 : A p = 0) (h2 : ContinuousLinearMap.adjoint A q + r = 0) : ⟪r, p⟫_ℝ = 0 := by
  have : r = -(ContinuousLinearMap.adjoint A q) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
  rw [this, inner_neg_left, ContinuousLinearMap.adjoint_inner_left, h1, inner_zero_right, neg_zero]

lemma tau_lemma (β G I τb : ℝ) (hβ : 0 < β) (hτb : τb ^ 2 = 3 * β / (1 + β) / 4)
    (hτbpos : 0 < τb) (hGgt : β < G) (hI : 0 < 1 + I) (h428 : 3 / 4 * I - 1 / 4 ≤ G) :
    τb ≤ Real.sqrt (G / (1 + I)) := by
  by_contra hlt
  push Not at hlt
  rw [Real.sqrt_lt' hτbpos, div_lt_iff₀ hI, hτb] at hlt
  have h2 : 3 * β / (1 + β) / 4 * (1 + I) ≤ 3 * β / (1 + β) / 4 * (4 / 3 * (1 + G)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : G * (1 + β) < 3 * β / (1 + β) / 4 * (4 / 3 * (1 + G)) * (1 + β) :=
    mul_lt_mul_of_pos_right (by linarith) (by linarith)
  have e2 : 3 * β / (1 + β) / 4 * (4 / 3 * (1 + G)) * (1 + β) = β * (1 + G) := by
    field_simp
  rw [e2] at h3
  have e3 : G * (1 + β) - β * (1 + G) = G - β := by ring
  linarith

end SSFP71Aux

open SelfScaledIPM.FuncProx

theorem solution (Δ κ : ℝ) (hΔ : 0 < Δ) (hκ₀ : 0 < κ) (hκ₁ : κ < 1) :
    ∃ ω₁ ω₂ : ℝ, 0 < ω₁ ∧ 0 < ω₂ ∧
    ∀ {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
      (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
      (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
      (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : β = κ - Real.log (1 + κ))
      (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
      (hstart : InFuncNbhd K F ν A b c β (x, y, s))
      (w : EuclideanSpace ℝ (Fin n)) (hw : SelfScaledIPM.ShortStep.IsScalingPoint K F x s w)
      (px : EuclideanSpace ℝ (Fin n)) (py : EuclideanSpace ℝ (Fin m)) (ps : EuclideanSpace ℝ (Fin n))
      (hp : IsAffineScalingDir A F s w px py ps)
      (α : ℝ)
      (hα : IsGreatest {a : ℝ | 0 ≤ a ∧ a < 1 ∧
          (∀ a' ∈ Set.Icc (0 : ℝ) a,
            x - a' • px ∈ interior K ∧ s - a' • ps ∈ interior (ConvexOptimization.dualCone K)) ∧
          gammaF K F ν (x - a • px) (s - a • ps) = β + Δ} α)
      (z : ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
      (hz0 : z 0 = (x - α • px, y - α • py, s - α • ps))
      (hz : IsNewtonRun K F ν A z),
      ω₁ / ν ≤ α ^ 2 / (1 - α) ∧
      ω₂ / (SelfScaledIPM.ShortStep.absn K x px * SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps) ≤ α ^ 2 / (1 - α) ∧
      ω₂ / (Real.sqrt ν * SelfScaledIPM.ShortStep.absn K x px * SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) s ps) ≤
        ω₂ / (SelfScaledIPM.ShortStep.absn K x px * SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps) ∧
      ∃ N : ℕ, InFuncNbhd K F ν A b c β (z N) ∧
        (∀ j < N, β < gammaF K F ν (z j).1 (z j).2.2) ∧
        N ≤ ⌈Δ / ((1 / 2 : ℝ) * Real.sqrt (3 * β / (1 + β)) -
              Real.log (1 + (1 / 2 : ℝ) * Real.sqrt (3 * β / (1 + β))))⌉₊ ∧
        ⟪(z N).2.2, (z N).1⟫_ℝ ≤ (1 - α) * ⟪s, x⟫_ℝ := by
  have hβ0 : 0 < κ - Real.log (1 + κ) := SSFP71Aux.f_pos hκ₀
  have h1κ : 0 < 1 - κ := by linarith
  set C₁ : ℝ := Real.sqrt (κ - Real.log (1 + κ)) / (1 - κ) with hC₁
  set C₂ : ℝ := 1 / (2 * (1 - κ)) with hC₂
  set C₃ : ℝ := 2 * (1 + κ) * Real.sqrt (κ ^ 2 / (1 - κ)) with hC₃
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 < C₂ := by positivity
  have hC₃0 : 0 ≤ C₃ := by positivity
  set ω₁ : ℝ := min (min 1 (1 / (2 * C₂))) (Δ / (2 * (C₁ + 2 * C₂ ^ 2))) with hω₁
  set ω₂ : ℝ := min (1 / 2) (Δ / (2 * (C₃ + 2))) with hω₂
  have hω₁0 : 0 < ω₁ := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hω₂0 : 0 < ω₂ := lt_min (by norm_num) (by positivity)
  refine ⟨ω₁, ω₂, hω₁0, hω₂0, ?_⟩
  intro n m K hK F ν hν hF A hA b c β hβ x y s hstart w hw px py ps hp α hα z hz0 hz
  have hνpos : (0 : ℝ) < ν := by linarith
  have hβpos : 0 < β := hβ ▸ hβ0
  obtain ⟨⟨hx, hAx, hs, hdual⟩, hγ⟩ := hstart
  have hfeas : IsStrictlyFeasible K A b c x y s := ⟨hx, hAx, hs, hdual⟩
  have hpdir : IsAffineScalingDir A F s w px py ps := hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨⟨hα0, hα1, hαseg, hαγ⟩, -⟩ := hα
  have hxα := (hαseg α ⟨hα0, le_rfl⟩).1
  have hsα := (hαseg α ⟨hα0, le_rfl⟩).2
  have hfeas0 : IsStrictlyFeasible K A b c (x - α • px) (y - α • py) (s - α • ps) := by
    refine ⟨hxα, ?_, hsα, ?_⟩
    · rw [map_sub, map_smul, hp2, smul_zero, sub_zero, hAx]
    · rw [map_sub, map_smul]
      calc ContinuousLinearMap.adjoint A y - α • ContinuousLinearMap.adjoint A py + (s - α • ps)
          = (ContinuousLinearMap.adjoint A y + s) - α • (ContinuousLinearMap.adjoint A py + ps) := by
            rw [smul_add]; abel
        _ = c := by rw [hdual, hp3, smul_zero, sub_zero]
  have hαpos : 0 < α := by
    rcases hα0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hαγ; simp at hαγ; linarith
  -- Theorem 4.2 at (x, s)
  obtain ⟨⟨hl1, hl2, -⟩, -, -, h419, -, -⟩ := theorem_4_2_global K hK F ν hν hF x s hx hs
  have hlam2nn : 0 ≤ lambda2 F ν x s := Real.sqrt_nonneg _
  have hlam2 : lambda2 F ν x s ≤ κ := by
    by_contra hcon
    push Not at hcon
    have := SSFP71Aux.f_strict hκ₀.le hcon
    linarith
  have hlaminf_nn : 0 ≤ SelfScaledIPM.ShortStep.lambdaInf K F ν x s :=
    le_trans (Real.sInf_nonneg (fun b hb => hb.1)) (le_max_left _ _)
  have hlaminf : SelfScaledIPM.ShortStep.lambdaInf K F ν x s < 1 := by linarith
  obtain ⟨hl4, -, hl6⟩ := theorem_4_2_local K hK F ν hν hF x s hx hs hlaminf
  have hInf_le : 1 + gammaInf K F ν x s ≤ 1 / (1 - κ) := by
    have h1 : SelfScaledIPM.ShortStep.lambdaInf K F ν x s /
        (1 - SelfScaledIPM.ShortStep.lambdaInf K F ν x s) ≤ κ / (1 - κ) := by
      rw [div_le_div_iff₀ (by linarith) h1κ]; nlinarith
    have e : 1 + κ / (1 - κ) = 1 / (1 - κ) := by field_simp; ring
    linarith
  have hInf_ge : 0 ≤ 1 + gammaInf K F ν x s := by
    unfold gammaInf
    have hμ : 0 ≤ SelfScaledIPM.ShortStep.mu ν x s := by
      unfold SelfScaledIPM.ShortStep.mu
      apply div_nonneg _ hνpos.le
      rw [real_inner_comm]; exact (interior_subset hs) x (interior_subset hx)
    have hσ : 0 ≤ SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) s (-gradient F x) :=
      Real.sInf_nonneg (fun b hb => hb.1)
    nlinarith [mul_nonneg hμ hσ]
  have hGle : gammaG K F ν x s ≤ κ ^ 2 / (1 - κ) := by
    refine le_trans hl6 ?_
    exact div_le_div₀ (sq_nonneg κ) (pow_le_pow_left₀ hlam2nn hlam2 2) h1κ (by linarith)
  -- Theorem 5.3 and Lemma 5.4
  obtain ⟨zz, hzz⟩ := SSFP71Aux.hess_surj hF hw.1 ps
  obtain ⟨pp, hpp⟩ := SSFP71Aux.hess_surj hF hx (-(1 / 2 : ℝ) • third F x px zz)
  obtain ⟨-, h53⟩ := theorem_5_3 K hK F ν hν hF A hA b c x y s hfeas w hw px py ps hpdir zz pp hzz hpp
  obtain ⟨-, -, hxξ, he1, he2⟩ := h53 α hα0 hfeas0
  have hDF : Δ ≤ F (x + (α ^ 2 / (1 - α)) • pp) - F x := by linarith
  obtain ⟨h512, h513, h514a, h514b⟩ :=
    lemma_5_4 K hK F ν hν hF A hA b c x y s hfeas w hw px py ps hpdir zz pp hzz hpp
  have hξpos : 0 < α ^ 2 / (1 - α) := div_pos (by positivity) (by linarith)
  have KB := SSFP71Aux.step_bound K hK F ν hν hF x pp hx _ hξpos (interior_subset hxξ)
  have hg1 : ⟪gradient F x, pp⟫_ℝ ≤ ν * C₁ := by
    refine le_trans h513 ?_
    have hsq : Real.sqrt (gammaF K F ν x s) ≤ Real.sqrt (κ - Real.log (1 + κ)) :=
      Real.sqrt_le_sqrt (by linarith)
    calc ν * (1 + gammaInf K F ν x s) * Real.sqrt (gammaF K F ν x s)
        ≤ ν * (1 / (1 - κ)) * Real.sqrt (κ - Real.log (1 + κ)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hInf_le hνpos.le) hsq (Real.sqrt_nonneg _)
          positivity
      _ = ν * C₁ := by rw [hC₁]; ring
  have ha0 : 0 ≤ SelfScaledIPM.ShortStep.absn K x px :=
    le_trans (Real.sInf_nonneg (fun b hb => hb.1)) (le_max_left _ _)
  have hM0 : 0 ≤ SelfScaledIPM.ShortStep.absn K x px *
      SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps :=
    mul_nonneg ha0 (Real.sqrt_nonneg _)
  have hMν : SelfScaledIPM.ShortStep.absn K x px *
      SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps ≤ ν * C₂ := by
    refine le_trans h514b ?_
    calc (1 / 2 : ℝ) * ν * (1 + gammaInf K F ν x s) ≤ (1 / 2 : ℝ) * ν * (1 / (1 - κ)) :=
          mul_le_mul_of_nonneg_left hInf_le (by positivity)
      _ = ν * C₂ := by rw [hC₂]; field_simp
  have hg3 : ⟪gradient F x, pp⟫_ℝ ≤ C₃ * (SelfScaledIPM.ShortStep.absn K x px *
      SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps) := by
    refine le_trans h512 ?_
    have hlamp : lambdaPlusInf K F ν x s ≤ κ := by linarith
    have hsG : Real.sqrt (gammaG K F ν x s) ≤ Real.sqrt (κ ^ 2 / (1 - κ)) := Real.sqrt_le_sqrt hGle
    have hA1 : (1 + lambdaPlusInf K F ν x s) * Real.sqrt (gammaG K F ν x s) ≤
        (1 + κ) * Real.sqrt (κ ^ 2 / (1 - κ)) := by
      calc _ ≤ (1 + κ) * Real.sqrt (gammaG K F ν x s) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hsG (by linarith)
    calc _ = 2 * ((1 + lambdaPlusInf K F ν x s) * Real.sqrt (gammaG K F ν x s)) *
          (SelfScaledIPM.ShortStep.absn K x px *
            SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps) := by ring
      _ ≤ 2 * ((1 + κ) * Real.sqrt (κ ^ 2 / (1 - κ))) *
          (SelfScaledIPM.ShortStep.absn K x px *
            SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 (by norm_num)) hM0
      _ = _ := by rw [hC₃]; ring
  have h72 := SSFP71Aux.arith72 Δ C₁ C₂ ν (α ^ 2 / (1 - α)) _ _ _ _ hΔ hC₁0 hC₂0 hνpos hξpos.le
    (Real.sqrt_nonneg _) h514a hMν hg1 hDF KB
  have h73 := SSFP71Aux.arith73 Δ C₃ (α ^ 2 / (1 - α)) _ _ _ _ hΔ hC₃0 hξpos.le
    (Real.sqrt_nonneg _) h514a hg3 hDF KB
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hνpos]; exact h72
  · rcases hM0.lt_or_eq with hMpos | hMz
    · rw [div_le_iff₀ hMpos]; exact h73
    · rw [← hMz, div_zero]; exact hξpos.le
  · have hP := (SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF).2.2.1 s hs ps
    have hc0 : 0 ≤ SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) s ps :=
      le_trans (Real.sInf_nonneg (fun b hb => hb.1)) (le_max_left _ _)
    rcases hM0.lt_or_eq with hMpos | hMz
    · apply div_le_div_of_nonneg_left hω₂0.le hMpos
      calc SelfScaledIPM.ShortStep.absn K x px *
            SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s ps
          ≤ SelfScaledIPM.ShortStep.absn K x px *
            (Real.sqrt ν * SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) s ps) :=
            mul_le_mul_of_nonneg_left hP.2 ha0
        _ = _ := by ring
    · rw [← hMz, div_zero]
      rcases mul_eq_zero.mp hMz.symm with h | h
      · rw [h]; simp
      · have : SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) s ps = 0 :=
          le_antisymm (h ▸ hP.1) hc0
        rw [this]; simp
  -- Newton corrector
  set τb : ℝ := (1 / 2 : ℝ) * Real.sqrt (3 * β / (1 + β)) with hτb
  set c₀ : ℝ := τb - Real.log (1 + τb) with hc₀def
  have hr0 : 0 < 3 * β / (1 + β) := by positivity
  have hτbpos : 0 < τb := by rw [hτb]; positivity
  have hc₀ : 0 < c₀ := SSFP71Aux.f_pos hτbpos
  have hgap0 : ⟪s - α • ps, x - α • px⟫_ℝ = (1 - α) * ⟪s, x⟫_ℝ := by
    obtain ⟨h54, -, -, -⟩ := lemma_5_2 K hK F ν hν hF A hA b c x y s hfeas w hw px py ps hpdir
    rw [SSFP71Aux.gap_gen s x ps px α _ h54 (SSFP71Aux.orth A px py ps hp2 hp3)]
    ring
  have newton : ∀ j, IsStrictlyFeasible K A b c (z j).1 (z j).2.1 (z j).2.2 →
      IsStrictlyFeasible K A b c (z (j + 1)).1 (z (j + 1)).2.1 (z (j + 1)).2.2 ∧
      ⟪(z (j + 1)).2.2, (z (j + 1)).1⟫_ℝ = ⟪(z j).2.2, (z j).1⟫_ℝ ∧
      (β < gammaF K F ν (z j).1 (z j).2.2 →
        gammaF K F ν (z (j + 1)).1 (z (j + 1)).2.2 ≤ gammaF K F ν (z j).1 (z j).2.2 - c₀) := by
    intro j hfj
    obtain ⟨hfeas', hdec, -⟩ := theorem_5_7 K hK F ν hν hF A hA b c (z j).1 (z j).2.1 (z j).2.2
      hfj (z (j + 1)).1 (z (j + 1)).2.1 (z (j + 1)).2.2 (hz j)
    refine ⟨hfeas', ?_, ?_⟩
    · obtain ⟨w', dx, dy, ds, hw', hd, heq⟩ := hz j
      obtain ⟨px', py', ps', hp'⟩ := SSFP71Aux.affine_exists hF A hA (z j).2.2 w' hw'.1
      obtain ⟨zz', hzz'⟩ := SSFP71Aux.hess_surj hF hw'.1 ps'
      obtain ⟨h520, -⟩ := lemma_5_6 K hK F ν hν hF A hA b c _ _ _ hfj w' hw' dx dy ds hd
        px' py' ps' hp' zz' hzz'
      rw [heq]
      rw [SSFP71Aux.gap_gen _ _ ds dx _ _ h520 (SSFP71Aux.orth A dx dy ds hd.2.1 hd.2.2)]
      ring
    · intro hgt
      have hxj := hfj.1
      have hsj := hfj.2.2.1
      obtain ⟨-, ⟨hg1', hg2'⟩, ⟨-, hg4'⟩, -, -, -⟩ :=
        theorem_4_2_global K hK F ν hν hF _ _ hxj hsj
      have h428 := eq_4_28 K hK F ν hν hF _ _ hxj hsj
      have hGgt : β < gammaG K F ν (z j).1 (z j).2.2 := by linarith
      have hIpos : 0 < gammaInf K F ν (z j).1 (z j).2.2 := by
        by_contra h
        push Not at h
        have := mul_nonpos_iff.mpr (Or.inl ⟨hνpos.le, h⟩)
        linarith
      have e1 : τb ^ 2 = 3 * β / (1 + β) / 4 := by
        rw [hτb, mul_pow, Real.sq_sqrt hr0.le]; ring
      have hτ := SSFP71Aux.tau_lemma β _ _ τb hβpos e1 hτbpos hGgt (by linarith) h428
      have := SSFP71Aux.f_mono hτbpos.le hτ
      linarith
  have inv : ∀ j, IsStrictlyFeasible K A b c (z j).1 (z j).2.1 (z j).2.2 ∧
      ⟪(z j).2.2, (z j).1⟫_ℝ = (1 - α) * ⟪s, x⟫_ℝ := by
    intro j
    induction j with
    | zero => rw [hz0]; exact ⟨hfeas0, hgap0⟩
    | succ k ih =>
      obtain ⟨h1, h2, -⟩ := newton k ih.1
      exact ⟨h1, h2.trans ih.2⟩
  have hγ0 : gammaF K F ν (z 0).1 (z 0).2.2 = β + Δ := by rw [hz0]; exact hαγ
  have bound : ∀ k : ℕ, (∀ i < k, β < gammaF K F ν (z i).1 (z i).2.2) →
      gammaF K F ν (z k).1 (z k).2.2 ≤ β + Δ - k * c₀ := by
    intro k
    induction k with
    | zero => intro _; simp [hγ0]
    | succ k ih =>
      intro h
      have h1 := ih (fun i hi => h i (by omega))
      have h2 := (newton k (inv k).1).2.2 (h k (by omega))
      push_cast
      linarith
  have hKc : Δ ≤ (⌈Δ / c₀⌉₊ : ℝ) * c₀ := by
    have := Nat.le_ceil (Δ / c₀)
    rwa [div_le_iff₀ hc₀] at this
  have hex : ∃ k, gammaF K F ν (z k).1 (z k).2.2 ≤ β := by
    by_contra hne
    push Not at hne
    have h1 := bound ⌈Δ / c₀⌉₊ (fun i _ => hne i)
    have h2 := hne ⌈Δ / c₀⌉₊
    linarith
  classical
  refine ⟨Nat.find hex, ⟨(inv _).1, Nat.find_spec hex⟩, ?_, ?_, le_of_eq (inv _).2⟩
  · intro j hj
    have := Nat.find_min hex hj
    push Not at this
    exact this
  · by_contra hlt
    push Not at hlt
    have hall : ∀ i < ⌈Δ / c₀⌉₊ + 1, β < gammaF K F ν (z i).1 (z i).2.2 := by
      intro i hi
      have := Nat.find_min hex (by omega : i < Nat.find hex)
      push Not at this
      exact this
    have h1 := bound ⌈Δ / c₀⌉₊ (fun i hi => hall i (by omega))
    have h2 := hall ⌈Δ / c₀⌉₊ (by omega)
    linarith
