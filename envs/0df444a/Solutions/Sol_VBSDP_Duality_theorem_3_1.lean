-- Prove2me | solution 1 for VBSDP.Duality.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-08T00:16:34.556742+00:00
-- url     : https://prove2.me/submissions/5e632f94-0925-426f-a0bb-e4404446fa6f

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me 6e5c6be5-40ed-4a5c-b24b-d856b5ef458f.
-- Reused accepted contributions are attributed beside their full proof bodies.
import Definitions.Def_VBSDP_Duality_IsDualFeasible
import Definitions.Def_VBSDP_Duality_IsPrimalFeasible
import Definitions.Def_VBSDP_Duality_Xopt
import Definitions.Def_VBSDP_Duality_Zopt
import Definitions.Def_VBSDP_Duality_pStar
import Definitions.Def_dualCone
import Mathlib

set_option autoImplicit false


-- BEGIN MODULE AttributedConeZero
section
-- Prove2me | solution 1 for ConvexOptimization.zero_mem_of_closed_pos_cone
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T04:48:17.913505+00:00
-- url     : https://prove2.me/submissions/e33eed7e-5f1f-4d88-be79-7ae8d42dc68d


open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.zero_mem_of_closed_pos_cone {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKclosed : IsClosed K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K) (hne : K.Nonempty) :
    (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by
  obtain ⟨y, hy⟩ := hne
  have htend : Filter.Tendsto (fun k : ℕ => (1 / (k + 1 : ℝ)) • y) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun k : ℕ => (1 / (k + 1 : ℝ))) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h0.smul_const y
  refine hKclosed.mem_of_tendsto htend (Filter.Eventually.of_forall fun k => ?_)
  exact hKcone _ (by positivity) y hy

end
-- END MODULE AttributedConeZero

-- BEGIN MODULE AttributedConeAdd
section
-- Prove2me | solution 1 for ConvexOptimization.add_mem_of_convex_cone
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T04:48:18.621547+00:00
-- url     : https://prove2.me/submissions/34100613-f7b9-4ad8-96e3-de5424fe725c


open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.add_mem_of_convex_cone {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K)
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ K) (hv : v ∈ K) :
    u + v ∈ K := by
  have hmid : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v ∈ K :=
    hKconv hu hv (by norm_num) (by norm_num) (by norm_num)
  have h2 := hKcone 2 (by norm_num) _ hmid
  have hEq : (2 : ℝ) • ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) = u + v := by module
  rwa [hEq] at h2

end
-- END MODULE AttributedConeAdd

-- BEGIN MODULE AttributedDualScale
section
-- Prove2me | solution 1 for ConvexOptimization.smul_mem_dualCone
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T04:48:19.334518+00:00
-- url     : https://prove2.me/submissions/3c97301e-04e1-4e3a-aaa7-bfc2c6861568


open scoped RealInnerProductSpace ENNReal
open MeasureTheory

open ConvexOptimization in
theorem ConvexOptimization.smul_mem_dualCone {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ dualCone K) (c : ℝ) (hc : 0 ≤ c) :
    c • z ∈ dualCone K := by
  intro x hx
  rw [real_inner_smul_right]
  exact mul_nonneg hc (hz x hx)

end
-- END MODULE AttributedDualScale

-- BEGIN MODULE AttributedDualInterior
section
-- Prove2me | solution 1 for ConvexOptimization.dualCone_inner_pos_of_mem_interior
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T04:48:19.901644+00:00
-- url     : https://prove2.me/submissions/4db5f872-d1ac-46bd-9a6c-9a6c5173244a


open scoped RealInnerProductSpace ENNReal
open MeasureTheory

open ConvexOptimization in
theorem ConvexOptimization.dualCone_inner_pos_of_mem_interior {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (z w : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ dualCone K) (hzne : z ≠ 0) (hw : w ∈ interior K) :
    0 < ⟪w, z⟫ := by
  have hwK : w ∈ K := interior_subset hw
  have hnonneg : 0 ≤ ⟪w, z⟫ := hz w hwK
  rcases lt_or_eq_of_le hnonneg with h | h
  · exact h
  -- If `⟪w, z⟫ = 0`, move slightly against `z`: still in `K`, but with negative pairing.
  exfalso
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
  set δ : ℝ := ε / (2 * ‖z‖) with hδ
  have hδpos : 0 < δ := by positivity
  have hmem : w - δ • z ∈ K := by
    refine interior_subset (hball ?_)
    have : dist (w - δ • z) w = δ * ‖z‖ := by
      rw [dist_eq_norm]
      simp [norm_smul, abs_of_pos hδpos]
    rw [Metric.mem_ball, this, hδ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ‖z‖)]
    nlinarith [mul_pos hε hznorm]
  have := hz _ hmem
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ← h] at this
  nlinarith [this, mul_pos hδpos (pow_pos hznorm 2)]

end
-- END MODULE AttributedDualInterior

-- BEGIN MODULE AttributedConicSlater
section
-- Prove2me | solution 1 for ConvexOptimization.conic_slater_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T05:20:29.512729+00:00
-- url     : https://prove2.me/submissions/705b531c-e113-4c1d-9838-d77c20e0dc25


open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConicSlaterAux

open ConvexOptimization

/-- A strict convex combination of two strict inequalities. -/
theorem strict_combo {t₁ t₂ p₁ p₂ q₁ q₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hsum : t₁ + t₂ = 1) (h₁ : p₁ < q₁) (h₂ : p₂ < q₂) :
    t₁ * p₁ + t₂ * p₂ < t₁ * q₁ + t₂ * q₂ := by
  rcases eq_or_lt_of_le ht₁ with h | h
  · have ht2 : t₂ = 1 := by linarith
    rw [← h, ht2]; simpa using h₂
  · linarith [mul_lt_mul_of_pos_left h₁ h, mul_le_mul_of_nonneg_left h₂.le ht₂]

/-- For a convex cone `K`, the interior absorbs the cone: `interior K + K ⊆ interior K`. -/
theorem interior_add_mem {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hKconv : Convex ℝ K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K) {w k : EuclideanSpace ℝ (Fin d)}
    (hw : w ∈ interior K) (hk : k ∈ K) : w + k ∈ interior K := by
  have hsub : (fun y => y + k) '' interior K ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact ConvexOptimization.add_mem_of_convex_cone K hKconv hKcone y k (interior_subset hy) hk
  have hopen : IsOpen ((fun y => y + k) '' interior K) := by
    have := (Homeomorph.addRight k).isOpenMap (interior K) isOpen_interior
    simpa using this
  exact interior_maximal hsub hopen ⟨w, hw, rfl⟩

/-! ### Stage A: strong duality for the cone constraint alone -/

/-- **Stage A.** Over any convex set `M` of "already feasible" points, a Slater point for the
generalized inequality `f x ≼_K 0` produces a dual multiplier `z ∈ K*` whose Lagrangian
dominates the optimal value `P` on all of `M`. -/
theorem stageA {n d : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (hf : ∀ x y : EuclideanSpace ℝ (Fin n), ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ • f x + (1 - θ) • f y - f (θ • x + (1 - θ) • y) ∈ K)
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : Convex ℝ M)
    (xs : EuclideanSpace ℝ (Fin n)) (hxsM : xs ∈ M) (hxs : -f xs ∈ interior K)
    (P : ℝ) (hP : ∀ x ∈ M, -f x ∈ K → P ≤ f₀ x) :
    ∃ z ∈ dualCone K, ∀ x ∈ M, P ≤ f₀ x + ⟪z, f x⟫ := by
  classical
  have hKne : K.Nonempty := ⟨-f xs, interior_subset hxs⟩
  have h0K : (0 : EuclideanSpace ℝ (Fin d)) ∈ K :=
    ConvexOptimization.zero_mem_of_closed_pos_cone K hKclosed hKcone hKne
  -- The "achievable pairs" set and the "better than optimal" ray.
  set A : Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
    {q | ∃ x ∈ M, q.1 - f x ∈ K ∧ f₀ x ≤ q.2} with hAdef
  set B : Set (EuclideanSpace ℝ (Fin d) × ℝ) := {q | q.1 = 0 ∧ q.2 < P} with hBdef
  have hmemA : ∀ q : EuclideanSpace ℝ (Fin d) × ℝ,
      q ∈ A ↔ ∃ x ∈ M, q.1 - f x ∈ K ∧ f₀ x ≤ q.2 := by
    intro q; rw [hAdef]; rfl
  have hmemB : ∀ q : EuclideanSpace ℝ (Fin d) × ℝ, q ∈ B ↔ q.1 = 0 ∧ q.2 < P := by
    intro q; rw [hBdef]; rfl
  -- `A` is convex.
  have hAconv : Convex ℝ A := by
    rintro ⟨u₁, t₁⟩ h₁ ⟨u₂, t₂⟩ h₂ θ₁ θ₂ hθ₁ hθ₂ hsum
    obtain ⟨x₁, hx₁, hk₁, hl₁⟩ := (hmemA _).1 h₁
    obtain ⟨x₂, hx₂, hk₂, hl₂⟩ := (hmemA _).1 h₂
    dsimp only at hk₁ hl₁ hk₂ hl₂
    have hθ₂' : θ₂ = 1 - θ₁ := by linarith
    subst hθ₂'
    rw [hmemA]
    refine ⟨θ₁ • x₁ + (1 - θ₁) • x₂, hM hx₁ hx₂ hθ₁ hθ₂ hsum, ?_, ?_⟩
    · have hcomb : θ₁ • (u₁ - f x₁) + (1 - θ₁) • (u₂ - f x₂) ∈ K :=
        hKconv hk₁ hk₂ hθ₁ hθ₂ hsum
      have hcv := hf x₁ x₂ θ₁ hθ₁ (by linarith)
      have hEq : (θ₁ • u₁ + (1 - θ₁) • u₂) - f (θ₁ • x₁ + (1 - θ₁) • x₂) =
          (θ₁ • (u₁ - f x₁) + (1 - θ₁) • (u₂ - f x₂)) +
            (θ₁ • f x₁ + (1 - θ₁) • f x₂ - f (θ₁ • x₁ + (1 - θ₁) • x₂)) := by module
      show (θ₁ • u₁ + (1 - θ₁) • u₂) - f (θ₁ • x₁ + (1 - θ₁) • x₂) ∈ K
      rw [hEq]
      exact ConvexOptimization.add_mem_of_convex_cone K hKconv hKcone _ _ hcomb hcv
    · show f₀ (θ₁ • x₁ + (1 - θ₁) • x₂) ≤ θ₁ * t₁ + (1 - θ₁) * t₂
      have hjensen := hf₀.2 (Set.mem_univ x₁) (Set.mem_univ x₂) hθ₁ hθ₂ hsum
      simp only [smul_eq_mul] at hjensen
      have e₁ := mul_le_mul_of_nonneg_left hl₁ hθ₁
      have e₂ := mul_le_mul_of_nonneg_left hl₂ hθ₂
      linarith
  -- `B` is convex.
  have hBconv : Convex ℝ B := by
    rintro ⟨u₁, t₁⟩ h₁ ⟨u₂, t₂⟩ h₂ θ₁ θ₂ hθ₁ hθ₂ hsum
    obtain ⟨hu₁, ht₁⟩ := (hmemB _).1 h₁
    obtain ⟨hu₂, ht₂⟩ := (hmemB _).1 h₂
    dsimp only at hu₁ ht₁ hu₂ ht₂
    rw [hmemB]
    refine ⟨?_, ?_⟩
    · show θ₁ • u₁ + θ₂ • u₂ = 0
      rw [hu₁, hu₂]; simp
    · show θ₁ * t₁ + θ₂ * t₂ < P
      have hcomb := strict_combo hθ₁ hθ₂ hsum ht₁ ht₂
      have hPP : θ₁ * P + θ₂ * P = P := by rw [← add_mul, hsum, one_mul]
      linarith
  -- `A` has nonempty interior, thanks to the Slater point.
  have hAint : ((0 : EuclideanSpace ℝ (Fin d)), f₀ xs + 1) ∈ interior A := by
    have hsub : {q : EuclideanSpace ℝ (Fin d) × ℝ | q.1 - f xs ∈ interior K ∧ f₀ xs < q.2} ⊆ A := by
      rintro ⟨u, t⟩ ⟨hu, ht⟩
      rw [hmemA]
      exact ⟨xs, hxsM, interior_subset hu, ht.le⟩
    have hopen : IsOpen {q : EuclideanSpace ℝ (Fin d) × ℝ |
        q.1 - f xs ∈ interior K ∧ f₀ xs < q.2} := by
      refine IsOpen.inter ?_ ?_
      · exact isOpen_interior.preimage (continuous_fst.sub continuous_const)
      · exact isOpen_lt continuous_const continuous_snd
    refine interior_maximal hsub hopen ⟨?_, by linarith⟩
    show (0 : EuclideanSpace ℝ (Fin d)) - f xs ∈ interior K
    simpa using hxs
  -- The two sets are separated.
  have hdisj : Disjoint (interior A) B := by
    rw [Set.disjoint_left]
    rintro ⟨u, t⟩ hq hB
    obtain ⟨hu, ht⟩ := (hmemB _).1 hB
    obtain ⟨x, hxM, hk, hle⟩ := (hmemA _).1 (interior_subset hq)
    simp only at hu
    rw [hu] at hk
    have := hP x hxM (by simpa using hk)
    linarith
  obtain ⟨Φ, c, hΦne, hΦA, hΦB⟩ :=
    geometric_hahn_banach_of_nonempty_interior hAconv hBconv hdisj ⟨_, hAint⟩
      ⟨((0 : EuclideanSpace ℝ (Fin d)), P - 1), (hmemB _).2 ⟨rfl, by linarith⟩⟩
  -- Decompose the separating functional.
  set μ : ℝ := Φ (0, 1) with hμdef
  set L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    Φ.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ) with hLdef
  set z₀ : EuclideanSpace ℝ (Fin d) := (InnerProductSpace.toDual ℝ _).symm L with hz₀def
  have hz₀ : ∀ u, ⟪z₀, u⟫ = Φ (u, 0) := by
    intro u
    rw [hz₀def, InnerProductSpace.toDual_symm_apply]
    rfl
  have hdec : ∀ (u : EuclideanSpace ℝ (Fin d)) (t : ℝ), Φ (u, t) = ⟪z₀, u⟫ + t * μ := by
    intro u t
    have hsplit : ((u, t) : EuclideanSpace ℝ (Fin d) × ℝ)
        = (u, 0) + t • ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) := by
      simp
    rw [hsplit, map_add, map_smul, hz₀ u, smul_eq_mul, hμdef]
  -- The `t`-coefficient is nonpositive.
  have hμle : μ ≤ 0 := by
    by_contra hcon
    push Not at hcon
    set s : ℝ := min (P - 1) ((c - 1) / μ) with hsdef
    have hs1 : s < P := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hs2 : s * μ ≤ c - 1 := by
      have hle : s ≤ (c - 1) / μ := min_le_right _ _
      have := mul_le_mul_of_nonneg_right hle hcon.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hcon)] at this
    have hb := hΦB ((0 : EuclideanSpace ℝ (Fin d)), s) ((hmemB _).2 ⟨rfl, hs1⟩)
    rw [hdec, inner_zero_right, zero_add] at hb
    linarith
  -- Hence the separating constant is below `P * μ`.
  have hcP : c ≤ P * μ := by
    have htend : Filter.Tendsto (fun s : ℝ => s * μ) (nhdsWithin P (Set.Iio P)) (nhds (P * μ)) :=
      ((continuous_id.mul continuous_const).tendsto P).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hb := hΦB ((0 : EuclideanSpace ℝ (Fin d)), s) ((hmemB _).2 ⟨rfl, hs⟩)
    rwa [hdec, inner_zero_right, zero_add] at hb
  -- `-z₀` lies in the dual cone.
  have hz₀K : ∀ k ∈ K, ⟪z₀, k⟫ ≤ 0 := by
    intro k hk
    by_contra hcon
    push Not at hcon
    set C₀ : ℝ := ⟪z₀, f xs⟫ + f₀ xs * μ with hC₀def
    set lam : ℝ := (|c - C₀| + 1) / ⟪z₀, k⟫ with hlamdef
    have hlampos : 0 < lam := by
      rw [hlamdef]; positivity
    have hmem : ((f xs + lam • k, f₀ xs) : EuclideanSpace ℝ (Fin d) × ℝ) ∈ A := by
      rw [hmemA]
      refine ⟨xs, hxsM, ?_, le_rfl⟩
      show (f xs + lam • k) - f xs ∈ K
      have hsimp : (f xs + lam • k) - f xs = lam • k := by abel
      rw [hsimp]
      exact hKcone lam hlampos k hk
    have hb := hΦA _ hmem
    rw [hdec, inner_add_right, real_inner_smul_right] at hb
    have hprod : lam * ⟪z₀, k⟫ = |c - C₀| + 1 := by
      rw [hlamdef, div_mul_cancel₀ _ (ne_of_gt hcon)]
    rw [hprod] at hb
    have habs : c - C₀ ≤ |c - C₀| := le_abs_self _
    rw [hC₀def] at hb
    linarith
  -- The main domination inequality.
  have hmain : ∀ x ∈ M, ⟪z₀, f x⟫ + f₀ x * μ ≤ P * μ := by
    intro x hx
    have hmem : ((f x, f₀ x) : EuclideanSpace ℝ (Fin d) × ℝ) ∈ A := by
      rw [hmemA]
      refine ⟨x, hx, ?_, le_rfl⟩
      show f x - f x ∈ K
      simpa using h0K
    have hb := hΦA _ hmem
    rw [hdec] at hb
    linarith
  -- The `t`-coefficient is in fact strictly negative (this is where Slater is used).
  have hμlt : μ < 0 := by
    rcases lt_or_eq_of_le hμle with hlt | heq
    · exact hlt
    exfalso
    have hzz : z₀ = 0 := by
      by_contra hne
      have hz'dual : -z₀ ∈ dualCone K := by
        intro k hk
        rw [inner_neg_right]
        have h1 := hz₀K k hk
        rw [real_inner_comm] at h1
        linarith
      have hne' : -z₀ ≠ 0 := by simpa using hne
      have hpos :=
        ConvexOptimization.dualCone_inner_pos_of_mem_interior K (-z₀) (-f xs) hz'dual hne' hxs
      rw [inner_neg_neg, real_inner_comm] at hpos
      have hm := hmain xs hxsM
      rw [heq] at hm
      simp only [mul_zero, add_zero] at hm
      linarith
    apply hΦne
    refine ContinuousLinearMap.ext fun q => ?_
    obtain ⟨u, t⟩ := q
    rw [hdec, hzz, heq]
    simp
  -- Rescale to get the multiplier.
  refine ⟨(1 / μ) • z₀, ?_, ?_⟩
  · intro k hk
    rw [real_inner_smul_right]
    have h1 : ⟪z₀, k⟫ ≤ 0 := hz₀K k hk
    have h2 : ⟪k, z₀⟫ ≤ 0 := by rwa [real_inner_comm] at h1
    have h3 : 1 / μ < 0 := div_neg_of_pos_of_neg one_pos hμlt
    nlinarith
  · intro x hx
    have hm := hmain x hx
    rw [real_inner_smul_left]
    have hμne : μ ≠ 0 := ne_of_lt hμlt
    have key : (f₀ x + 1 / μ * ⟪z₀, f x⟫) * μ ≤ P * μ := by
      have hexp : (f₀ x + 1 / μ * ⟪z₀, f x⟫) * μ = f₀ x * μ + ⟪z₀, f x⟫ := by
        field_simp
      rw [hexp]; linarith
    exact (mul_le_mul_right_of_neg hμlt).mp key

/-! ### Stage B: eliminating the affine equality constraints -/

/-- A linearly independent family of vectors gives a *surjective* linear map
`x ↦ (⟪a j, x⟫)ⱼ`, and moreover a continuous linear right inverse. -/
theorem exists_right_inverse {n p : ℕ} (a : Fin p → EuclideanSpace ℝ (Fin n))
    (ha : LinearIndependent ℝ a) :
    ∃ R : (Fin p → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      Continuous R ∧ ∀ (v : Fin p → ℝ) (j : Fin p), ⟪a j, R v⟫ = v j := by
  classical
  set T : (Fin p → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Fintype.linearCombination ℝ a with hTdef
  have hTapp : ∀ c : Fin p → ℝ, T c = ∑ i, c i • a i := by
    intro c; rw [hTdef]; exact Fintype.linearCombination_apply (R := ℝ) a c
  set G : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ) :=
    LinearMap.pi (fun j => (innerSL ℝ (a j)).toLinearMap ∘ₗ T) with hGdef
  have hGapp : ∀ (c : Fin p → ℝ) (j : Fin p), G c j = ⟪a j, T c⟫ := by
    intro c j; rw [hGdef]; rfl
  have hGinj : Function.Injective G := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hj : ∀ j, ⟪a j, T c⟫ = 0 := by
      intro j
      have := congrFun hc j
      rwa [hGapp] at this
    have hsq : ⟪T c, T c⟫ = 0 := by
      calc ⟪T c, T c⟫ = ∑ i, c i * ⟪a i, T c⟫ := by
            conv_lhs => rw [hTapp c]
            rw [sum_inner]
            exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
        _ = 0 := by simp [hj]
    have hT0 : T c = 0 := by
      simpa using inner_self_eq_zero.mp hsq
    funext i
    exact Fintype.linearIndependent_iff.mp ha c (by rw [← hTapp c]; exact hT0) i
  have hGsurj : Function.Surjective G := LinearMap.injective_iff_surjective.mp hGinj
  set Ge : (Fin p → ℝ) ≃ₗ[ℝ] (Fin p → ℝ) := LinearEquiv.ofBijective G ⟨hGinj, hGsurj⟩ with hGedef
  refine ⟨T ∘ₗ (Ge.symm : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ)), ?_, ?_⟩
  · exact LinearMap.continuous_of_finiteDimensional _
  · intro v j
    have hGv : G (Ge.symm v) = v := Ge.apply_symm_apply v
    calc ⟪a j, (T ∘ₗ (Ge.symm : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ))) v⟫
        = G (Ge.symm v) j := (hGapp _ j).symm
      _ = v j := by rw [hGv]

/-- **Stage B.** A real-valued convex function bounded below by `P` on the affine subspace
`{x | ⟪a j, x⟫ = b j}` admits multipliers `ν` making the augmented function bounded below by `P`
everywhere. -/
theorem stageB {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a) (b : Fin p → ℝ)
    (P : ℝ) (hP : ∀ x, (∀ j, ⟪a j, x⟫ = b j) → P ≤ g x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : ∀ j, ⟪a j, x₀⟫ = b j) :
    ∃ nu : Fin p → ℝ, ∀ x, P ≤ g x + ∑ j, nu j * (⟪a j, x⟫ - b j) := by
  classical
  have hcont : Continuous g := hg.locallyLipschitz.continuous
  obtain ⟨R, hRcont, hRapp⟩ := exists_right_inverse a ha
  -- The (open, convex) set of achievable constraint-value / objective pairs.
  set C : Set ((Fin p → ℝ) × ℝ) :=
    {q | ∃ x, (∀ j, ⟪a j, x⟫ - b j = q.1 j) ∧ g x < q.2} with hCdef
  have hmemC : ∀ q : (Fin p → ℝ) × ℝ,
      q ∈ C ↔ ∃ x, (∀ j, ⟪a j, x⟫ - b j = q.1 j) ∧ g x < q.2 := by
    intro q; rw [hCdef]; rfl
  have hCconv : Convex ℝ C := by
    rintro ⟨v₁, s₁⟩ h₁ ⟨v₂, s₂⟩ h₂ θ₁ θ₂ hθ₁ hθ₂ hsum
    obtain ⟨x₁, he₁, hl₁⟩ := (hmemC _).1 h₁
    obtain ⟨x₂, he₂, hl₂⟩ := (hmemC _).1 h₂
    dsimp only at he₁ hl₁ he₂ hl₂
    rw [hmemC]
    refine ⟨θ₁ • x₁ + θ₂ • x₂, ?_, ?_⟩
    · intro j
      show ⟪a j, θ₁ • x₁ + θ₂ • x₂⟫ - b j = θ₁ • v₁ j + θ₂ • v₂ j
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have e₁ := he₁ j
      have e₂ := he₂ j
      simp only [smul_eq_mul]
      rw [← e₁, ← e₂]
      linear_combination (b j) * hsum
    · show g (θ₁ • x₁ + θ₂ • x₂) < θ₁ * s₁ + θ₂ * s₂
      have hjensen := hg.2 (Set.mem_univ x₁) (Set.mem_univ x₂) hθ₁ hθ₂ hsum
      simp only [smul_eq_mul] at hjensen
      have := strict_combo hθ₁ hθ₂ hsum hl₁ hl₂
      linarith
  have hCopen : IsOpen C := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨v₀, s₀⟩ hq
    obtain ⟨y, hey, hly⟩ := (hmemC _).1 hq
    dsimp only at hey hly
    have hUopen : IsOpen {q : (Fin p → ℝ) × ℝ | g (y + R (q.1 - v₀)) < q.2} := by
      refine isOpen_lt ?_ continuous_snd
      exact hcont.comp (continuous_const.add (hRcont.comp (continuous_fst.sub continuous_const)))
    have hUsub : {q : (Fin p → ℝ) × ℝ | g (y + R (q.1 - v₀)) < q.2} ⊆ C := by
      rintro ⟨v, s⟩ hs
      rw [hmemC]
      refine ⟨y + R (v - v₀), ?_, hs⟩
      intro j
      show ⟪a j, y + R (v - v₀)⟫ - b j = v j
      rw [inner_add_right, hRapp (v - v₀) j]
      have := hey j
      simp only [Pi.sub_apply]
      linarith
    refine Filter.mem_of_superset (hUopen.mem_nhds ?_) hUsub
    show g (y + R (v₀ - v₀)) < s₀
    simpa using hly
  have hnotmem : ((0 : Fin p → ℝ), P) ∉ C := by
    intro hcon
    obtain ⟨x, hex, hlx⟩ := (hmemC _).1 hcon
    dsimp only at hex hlx
    have hfeas : ∀ j, ⟪a j, x⟫ = b j := by
      intro j
      have := hex j
      simp only [Pi.zero_apply] at this
      linarith
    exact absurd (hP x hfeas) (not_le.2 hlx)
  obtain ⟨Ψ, hΨ⟩ := geometric_hahn_banach_open_point hCconv hCopen hnotmem
  -- Decompose the separating functional.
  set μ : ℝ := Ψ ((0 : Fin p → ℝ), (1 : ℝ)) with hμdef
  set ν₀ : Fin p → ℝ := fun j => Ψ ((Pi.single j (1 : ℝ) : Fin p → ℝ), (0 : ℝ)) with hν₀def
  have hdec : ∀ (v : Fin p → ℝ) (s : ℝ), Ψ (v, s) = (∑ j, ν₀ j * v j) + s * μ := by
    intro v s
    have hsplit : ((v, s) : (Fin p → ℝ) × ℝ)
        = (v, 0) + s • ((0 : Fin p → ℝ), (1 : ℝ)) := by
      simp
    have hv : ((v, (0 : ℝ)) : (Fin p → ℝ) × ℝ)
        = ∑ j, v j • ((Pi.single j (1 : ℝ) : Fin p → ℝ), (0 : ℝ)) := by
      rw [Prod.ext_iff]
      constructor
      · show v = (∑ j, v j • ((Pi.single j (1 : ℝ) : Fin p → ℝ), (0 : ℝ))).1
        rw [Prod.fst_sum]
        funext i
        simp [Finset.sum_apply, Pi.single_apply]
      · show (0 : ℝ) = (∑ j, v j • ((Pi.single j (1 : ℝ) : Fin p → ℝ), (0 : ℝ))).2
        rw [Prod.snd_sum]
        simp
    rw [hsplit, map_add, map_smul, hv, map_sum, smul_eq_mul, ← hμdef]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hν₀def, mul_comm]
  -- The `s`-coefficient is strictly negative.
  have hΨ0 : Ψ ((0 : Fin p → ℝ), P) = P * μ := by
    rw [hdec]; simp
  have hμlt : μ < 0 := by
    have hmemC' : ∀ s : ℝ, g x₀ < s → ((0 : Fin p → ℝ), s) ∈ C := by
      intro s hs
      rw [hmemC]
      refine ⟨x₀, ?_, hs⟩
      intro j
      show ⟪a j, x₀⟫ - b j = (0 : Fin p → ℝ) j
      rw [hx₀ j]; simp
    have hle : μ ≤ 0 := by
      by_contra hcon
      push Not at hcon
      set s : ℝ := max (g x₀ + 1) (P + 1) with hsdef
      have h1 : g x₀ < s := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have h2 : P < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have := hΨ ((0 : Fin p → ℝ), s) (hmemC' s h1)
      rw [hdec, hΨ0] at this
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at this
      nlinarith
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    exfalso
    have := hΨ ((0 : Fin p → ℝ), g x₀ + 1) (hmemC' _ (by linarith))
    rw [hdec, hΨ0, heq] at this
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at this
    linarith
  -- Pass to the limit `s → g x` and rescale.
  have hkey : ∀ x, (∑ j, ν₀ j * (⟪a j, x⟫ - b j)) + g x * μ ≤ P * μ := by
    intro x
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε : ℝ := δ / (-μ) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hδ (by linarith)
    have hmem : ((fun j => ⟪a j, x⟫ - b j : Fin p → ℝ), g x + ε) ∈ C := by
      rw [hmemC]
      exact ⟨x, fun j => rfl, by linarith⟩
    have hsep := hΨ _ hmem
    rw [hdec, hΨ0] at hsep
    have hεμ : ε * (-μ) = δ := by
      rw [hεdef, div_mul_cancel₀ _ (by linarith : (-μ) ≠ 0)]
    nlinarith [hsep, hεμ]
  refine ⟨fun j => ν₀ j / μ, fun x => ?_⟩
  have hk := hkey x
  have hμne : μ ≠ 0 := ne_of_lt hμlt
  have hsum : ∑ j, (ν₀ j / μ) * (⟪a j, x⟫ - b j)
      = (∑ j, ν₀ j * (⟪a j, x⟫ - b j)) / μ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by field_simp
  rw [hsum]
  have key : (g x + (∑ j, ν₀ j * (⟪a j, x⟫ - b j)) / μ) * μ ≤ P * μ := by
    have hexp : (g x + (∑ j, ν₀ j * (⟪a j, x⟫ - b j)) / μ) * μ
        = g x * μ + ∑ j, ν₀ j * (⟪a j, x⟫ - b j) := by
      field_simp
    rw [hexp]; linarith
  exact (mul_le_mul_right_of_neg hμlt).mp key

end ConicSlaterAux

open ConvexOptimization in
theorem ConvexOptimization.conic_slater_strong_duality {n d p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K)
    (hKclosed : IsClosed K) (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (hf : ∀ x y : EuclideanSpace ℝ (Fin n), ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ • f x + (1 - θ) • f y - f (θ • x + (1 - θ) • y) ∈ K)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs_slater : -f xs ∈ interior K)
    (hxs_eq : ∀ j, ⟪a j, xs⟫ = b j)
    (hbdd : BddBelow (f₀ '' {x | -f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j})) :
    ∃ (z : EuclideanSpace ℝ (Fin d)) (nu : Fin p → ℝ), z ∈ dualCone K ∧
      (⨅ x : EuclideanSpace ℝ (Fin n),
        ((f₀ x + ⟪z, f x⟫ + ∑ j, nu j * (⟪a j, x⟫ - b j) : ℝ) : EReal)) =
      ((sInf (f₀ '' {x | -f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j}) : ℝ) : EReal) := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin n)) := {x | -f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j} with hSdef
  set P : ℝ := sInf (f₀ '' S) with hPdef
  have hmemS : ∀ x, x ∈ S ↔ (-f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j) := by
    intro x; rw [hSdef]; rfl
  have hxsS : xs ∈ S := (hmemS _).2 ⟨interior_subset hxs_slater, hxs_eq⟩
  have hSne : (f₀ '' S).Nonempty := ⟨f₀ xs, ⟨xs, hxsS, rfl⟩⟩
  have hPle : ∀ x ∈ S, P ≤ f₀ x := fun x hx => csInf_le hbdd ⟨x, hx, rfl⟩
  -- The affine subspace cut out by the equality constraints is convex.
  have hMconv : Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ∀ j, ⟪a j, x⟫ = b j} := by
    intro x hx y hy s t hs ht hst j
    show ⟪a j, s • x + t • y⟫ = b j
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hx j, hy j]
    linear_combination (b j) * hst
  -- **Stage A**: the cone constraint gives a dual vector `z ∈ K*`.
  obtain ⟨z, hz, hAbound⟩ :=
    ConicSlaterAux.stageA f₀ hf₀ K hKconv hKclosed hKcone f hf
      {x : EuclideanSpace ℝ (Fin n) | ∀ j, ⟪a j, x⟫ = b j} hMconv xs hxs_eq hxs_slater P
      (fun x hxM hxK => hPle x ((hmemS _).2 ⟨hxK, hxM⟩))
  -- The partial Lagrangian is again a real-valued convex function.
  have hgconv : ConvexOn ℝ Set.univ (fun x => f₀ x + ⟪z, f x⟫) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ s t hs ht hst
    have hst' : t = 1 - s := by linarith
    subst hst'
    have h1 := hf₀.2 (Set.mem_univ x) (Set.mem_univ y) hs ht hst
    simp only [smul_eq_mul] at h1
    have hK := hf x y s hs (by linarith)
    have h2 : 0 ≤ ⟪s • f x + (1 - s) • f y - f (s • x + (1 - s) • y), z⟫ := hz _ hK
    rw [real_inner_comm, inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right] at h2
    show f₀ (s • x + (1 - s) • y) + ⟪z, f (s • x + (1 - s) • y)⟫
      ≤ s • (f₀ x + ⟪z, f x⟫) + (1 - s) • (f₀ y + ⟪z, f y⟫)
    simp only [smul_eq_mul]
    nlinarith [h1, h2]
  -- **Stage B**: the equality constraints give multipliers `ν`.
  obtain ⟨nu, hbound⟩ :=
    ConicSlaterAux.stageB (fun x => f₀ x + ⟪z, f x⟫) hgconv a ha b P
      (fun x hxM => hAbound x hxM) xs hxs_eq
  refine ⟨z, nu, hz, ?_⟩
  set I : EReal := ⨅ x : EuclideanSpace ℝ (Fin n),
      ((f₀ x + ⟪z, f x⟫ + ∑ j, nu j * (⟪a j, x⟫ - b j) : ℝ) : EReal) with hIdef
  -- `P ≤ I` is exactly the Lagrangian bound.
  have hIge : ((P : ℝ) : EReal) ≤ I := by
    rw [hIdef]
    exact le_iInf fun x => by exact_mod_cast hbound x
  -- `I ≤ P` because on the feasible set the Lagrangian is at most the objective.
  have hcoe : ∀ x ∈ S, I ≤ ((f₀ x : ℝ) : EReal) := by
    intro x hx
    obtain ⟨hxK, hxM⟩ := (hmemS _).1 hx
    rw [hIdef]
    refine le_trans (iInf_le _ x) ?_
    have h1 : ⟪z, f x⟫ ≤ 0 := by
      have hneg : (0 : ℝ) ≤ ⟪-f x, z⟫ := hz _ hxK
      rw [inner_neg_left] at hneg
      have h2 : ⟪f x, z⟫ ≤ 0 := by linarith
      rwa [real_inner_comm] at h2
    have h2 : ∑ j, nu j * (⟪a j, x⟫ - b j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hxM j]; ring
    have h3 : f₀ x + ⟪z, f x⟫ + ∑ j, nu j * (⟪a j, x⟫ - b j) ≤ f₀ x := by
      rw [h2]; linarith
    exact_mod_cast h3
  have hntop : I ≠ ⊤ := by
    intro htop
    have h := hcoe xs hxsS
    rw [htop, top_le_iff] at h
    exact EReal.coe_ne_top (f₀ xs) h
  have hnbot : I ≠ ⊥ := by
    intro hbot
    rw [hbot, le_bot_iff] at hIge
    exact EReal.coe_ne_bot P hIge
  have hr : ((I.toReal : ℝ) : EReal) = I := EReal.coe_toReal hntop hnbot
  have hle : I.toReal ≤ P := by
    rw [hPdef]
    refine le_csInf hSne ?_
    rintro y ⟨x, hx, rfl⟩
    have h := hcoe x hx
    rw [← hr] at h
    exact_mod_cast h
  refine le_antisymm ?_ hIge
  rw [← hr]
  exact_mod_cast hle

end
-- END MODULE AttributedConicSlater

-- BEGIN MODULE AttributedSDPSlater
section
-- Prove2me | solution 1 for ConvexOptimization.sdp_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T05:09:51.755271+00:00
-- url     : https://prove2.me/submissions/72104cb5-90b9-448b-a493-a42ab61d31f8


open scoped RealInnerProductSpace ENNReal MatrixOrder
open MeasureTheory
open Matrix

namespace SDPAux

variable {nn : ℕ}

/-! ### Symmetric matrices, entrywise -/

theorem isSymm_apply {M : Matrix (Fin nn) (Fin nn) ℝ} (h : M.IsSymm) (i j : Fin nn) :
    M j i = M i j := congrFun (congrFun h i) j

theorem isSymm_of_apply {M : Matrix (Fin nn) (Fin nn) ℝ} (h : ∀ i j, M j i = M i j) :
    M.IsSymm := by
  ext i j; exact h i j

/-- For a symmetric `N`, `tr (M N)` is the entrywise pairing of `M` and `N`. -/
theorem trace_mul_eq_sum (M N : Matrix (Fin nn) (Fin nn) ℝ) (hN : N.IsSymm) :
    (M * N).trace = ∑ i, ∑ j, M i j * N i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [isSymm_apply hN i j]

/-! ### Identifying matrices with a Euclidean space -/

/-- The coordinatewise identification of `nn × nn` matrices with `ℝ^(nn·nn)`, so that
the cone of positive semidefinite matrices becomes a cone in a Euclidean space of the
shape required by the cone-programming theorem. -/
noncomputable def toE (M : Matrix (Fin nn) (Fin nn) ℝ) :
    EuclideanSpace ℝ (Fin (nn * nn)) :=
  WithLp.toLp 2 (fun k => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

/-- The inverse identification. -/
def ofE (y : EuclideanSpace ℝ (Fin (nn * nn))) : Matrix (Fin nn) (Fin nn) ℝ :=
  Matrix.of fun i j => y (finProdFinEquiv (i, j))

@[simp] theorem ofE_toE (M : Matrix (Fin nn) (Fin nn) ℝ) : ofE (toE M) = M := by
  ext i j
  show M (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = M i j
  rw [Equiv.symm_apply_apply]

@[simp] theorem toE_ofE (y : EuclideanSpace ℝ (Fin (nn * nn))) : toE (ofE y) = y := by
  ext k
  show y (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = y k
  rw [Prod.mk.eta, Equiv.apply_symm_apply]

theorem toE_add (M N : Matrix (Fin nn) (Fin nn) ℝ) : toE (M + N) = toE M + toE N := by
  ext p; rfl

theorem toE_smul (c : ℝ) (M : Matrix (Fin nn) (Fin nn) ℝ) : toE (c • M) = c • toE M := by
  ext p; rfl

theorem toE_neg (M : Matrix (Fin nn) (Fin nn) ℝ) : toE (-M) = -toE M := by
  ext p; rfl

theorem toE_sub (M N : Matrix (Fin nn) (Fin nn) ℝ) : toE (M - N) = toE M - toE N := by
  ext p; rfl

theorem toE_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin nn) (Fin nn) ℝ) :
    toE (∑ i ∈ s, f i) = ∑ i ∈ s, toE (f i) := by
  classical
  induction s using Finset.induction with
  | empty => ext p; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toE_add, ih]

theorem inner_toE (M N : Matrix (Fin nn) (Fin nn) ℝ) :
    ⟪toE M, toE N⟫ = ∑ i, ∑ j, M i j * N i j := by
  have key : ∑ k : Fin (nn * nn), (inner ℝ ((toE M) k) ((toE N) k) : ℝ)
      = ∑ p : Fin nn × Fin nn, M p.1 p.2 * N p.1 p.2 :=
    Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun k => by simp [toE, mul_comm])
  rw [PiLp.inner_apply, key, Fintype.sum_prod_type]

/-! ### Quadratic forms -/

theorem quad_eq_sum (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, M i j * (x i * x j) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem quad_eq_inner (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ⟪toE M, toE (Matrix.vecMulVec x x)⟫ := by
  rw [inner_toE, quad_eq_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl

theorem vecMulVec_isSymm (x : Fin nn → ℝ) : (Matrix.vecMulVec x x).IsSymm :=
  isSymm_of_apply fun i j => by simp [Matrix.vecMulVec_apply, mul_comm]

theorem dotProduct_self_nonneg (x : Fin nn → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun _i _ => mul_self_nonneg _

theorem dotProduct_self_pos {x : Fin nn → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  rw [dotProduct]
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact mul_self_pos.mpr (by simpa using hi)

theorem norm_toE_vecMulVec (x : Fin nn → ℝ) :
    ‖toE (Matrix.vecMulVec x x)‖ = x ⬝ᵥ x := by
  have hsq : ‖toE (Matrix.vecMulVec x x)‖ ^ 2 = (x ⬝ᵥ x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toE]
    have h1 : ∀ i j : Fin nn, Matrix.vecMulVec x x i j * Matrix.vecMulVec x x i j
        = (x i * x i) * (x j * x j) := by
      intro i j; simp [Matrix.vecMulVec_apply]; ring
    calc ∑ i, ∑ j, Matrix.vecMulVec x x i j * Matrix.vecMulVec x x i j
        = ∑ i, ∑ j, (x i * x i) * (x j * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
      _ = (∑ i, x i * x i) * (∑ j, x j * x j) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ = (x ⬝ᵥ x) ^ 2 := by rw [dotProduct]; ring
  have h1 : (0 : ℝ) ≤ ‖toE (Matrix.vecMulVec x x)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ x ⬝ᵥ x := dotProduct_self_nonneg x
  nlinarith [hsq, h1, h2]

/-- Cauchy–Schwarz for the quadratic form: the perturbation of a quadratic form by
`Δ` is controlled by the Euclidean norm of `Δ`. -/
theorem abs_quad_le (Δ : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    |x ⬝ᵥ (Δ *ᵥ x)| ≤ ‖toE Δ‖ * (x ⬝ᵥ x) := by
  rw [quad_eq_inner, ← norm_toE_vecMulVec x]
  exact abs_real_inner_le_norm _ _

/-! ### Uniform positivity of a positive definite quadratic form -/

theorem norm_toLp (x : Fin nn → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin nn))‖ = Real.sqrt (x ⬝ᵥ x) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, pow_two]

theorem quad_smul (M : Matrix (Fin nn) (Fin nn) ℝ) (t : ℝ) (x : Fin nn → ℝ) :
    (t • x) ⬝ᵥ (M *ᵥ (t • x)) = t ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
  rw [quad_eq_sum, quad_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

theorem dot_smul_self (t : ℝ) (x : Fin nn → ℝ) : (t • x) ⬝ᵥ (t • x) = t ^ 2 * (x ⬝ᵥ x) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A positive definite quadratic form dominates a positive multiple of `‖x‖²`.
This is the compactness step: the form attains a positive minimum on the unit sphere. -/
theorem exists_pos_lower (M : Matrix (Fin nn) (Fin nn) ℝ)
    (hM : ∀ x : Fin nn → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin nn → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by
  classical
  rcases Nat.eq_zero_or_pos nn with h0 | hpos
  · subst h0
    exact ⟨1, one_pos, fun x => by simp [dotProduct]⟩
  · set φ : EuclideanSpace ℝ (Fin nn) → ℝ :=
      fun u => (WithLp.ofLp u) ⬝ᵥ (M *ᵥ (WithLp.ofLp u)) with hφdef
    have hcont : Continuous φ := by
      have hrw : φ = fun u : EuclideanSpace ℝ (Fin nn) => ∑ i, ∑ j, M i j * (u i * u j) := by
        funext u; rw [hφdef]; exact quad_eq_sum M _
      rw [hrw]
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      exact continuous_const.mul
        ((PiLp.continuous_apply 2 (fun _ : Fin nn => ℝ) i).mul
          (PiLp.continuous_apply 2 (fun _ : Fin nn => ℝ) j))
    have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin nn)) 1).Nonempty := by
      refine ⟨EuclideanSpace.single ⟨0, hpos⟩ 1, ?_⟩
      simp
    obtain ⟨u₀, hu₀mem, hu₀min⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin nn)) 1).exists_isMinOn hne hcont.continuousOn
    have hu₀norm : ‖u₀‖ = 1 := mem_sphere_zero_iff_norm.mp hu₀mem
    have hu₀ne : (WithLp.ofLp u₀ : Fin nn → ℝ) ≠ 0 := by
      intro hz
      have : u₀ = 0 := by ext i; exact congrFun hz i
      rw [this] at hu₀norm; simp at hu₀norm
    refine ⟨φ u₀, hM _ hu₀ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [dotProduct]
    · have hxx : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
      set r : ℝ := Real.sqrt (x ⬝ᵥ x) with hrdef
      have hrpos : 0 < r := Real.sqrt_pos.mpr hxx
      have hr2 : r ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hxx.le
      set u : EuclideanSpace ℝ (Fin nn) := WithLp.toLp 2 (r⁻¹ • x) with hudef
      have hunorm : ‖u‖ = 1 := by
        rw [hudef, norm_toLp, dot_smul_self, ← hr2]
        rw [show (r⁻¹) ^ 2 * r ^ 2 = 1 by field_simp]
        exact Real.sqrt_one
      have hmem : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin nn)) 1 :=
        mem_sphere_zero_iff_norm.mpr hunorm
      have hkey : φ u₀ ≤ φ u := hu₀min hmem
      have hφu : φ u = (r⁻¹) ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
        rw [hφdef]
        exact quad_smul M (r⁻¹) x
      rw [hφu] at hkey
      have hrne : r ≠ 0 := ne_of_gt hrpos
      have hmul : φ u₀ * r ^ 2 ≤ (r⁻¹ ^ 2 * (x ⬝ᵥ (M *ᵥ x))) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
      have hsimp : (r⁻¹ ^ 2 * (x ⬝ᵥ (M *ᵥ x))) * r ^ 2 = x ⬝ᵥ (M *ᵥ x) := by
        field_simp
      rw [hsimp, hr2] at hmul
      exact hmul

/-! ### Elementary algebra of quadratic forms -/

theorem quad_add (M N : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ ((M + N) *ᵥ x) = x ⬝ᵥ (M *ᵥ x) + x ⬝ᵥ (N *ᵥ x) := by
  rw [Matrix.add_mulVec, dotProduct_add]

theorem quad_neg (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ ((-M) *ᵥ x) = -(x ⬝ᵥ (M *ᵥ x)) := by
  rw [Matrix.neg_mulVec, dotProduct_neg]

theorem quad_smul_mat (c : ℝ) (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ ((c • M) *ᵥ x) = c * (x ⬝ᵥ (M *ᵥ x)) := by
  rw [quad_eq_sum, quad_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [Matrix.smul_apply]; ring

theorem quad_one (x : Fin nn → ℝ) : x ⬝ᵥ ((1 : Matrix (Fin nn) (Fin nn) ℝ) *ᵥ x) = x ⬝ᵥ x := by
  rw [Matrix.one_mulVec]

theorem quad_vecMulVec (v x : Fin nn → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec v v *ᵥ x) = (v ⬝ᵥ x) ^ 2 := by
  rw [quad_eq_sum]
  calc ∑ i, ∑ j, Matrix.vecMulVec v v i j * (x i * x j)
      = ∑ i, ∑ j, (v i * x i) * (v j * x j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          simp [Matrix.vecMulVec_apply]; ring
    _ = (∑ i, v i * x i) * (∑ j, v j * x j) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = (v ⬝ᵥ x) ^ 2 := by rw [dotProduct]; ring

theorem isHermitian_of_isSymm {M : Matrix (Fin nn) (Fin nn) ℝ} (h : M.IsSymm) :
    M.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact isSymm_apply h i j

/-! ### Trace positivity -/

theorem trace_mul_sq (P S : Matrix (Fin nn) (Fin nn) ℝ) (hS : S.IsSymm) :
    (P * (S * S)).trace = ∑ k, (fun i => S k i) ⬝ᵥ (P *ᵥ (fun i => S k i)) := by
  have hSS : (S * S).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, hS.eq]
  rw [trace_mul_eq_sum P (S * S) hSS]
  have hz : ∀ i j, (S * S) i j = ∑ k, S k i * S k j := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [isSymm_apply hS i k]
  calc ∑ i, ∑ j, P i j * (S * S) i j
      = ∑ i, ∑ j, ∑ k, P i j * (S k i * S k j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hz i j, Finset.mul_sum]
    _ = ∑ i, ∑ k, ∑ j, P i j * (S k i * S k j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, P i j * (S k i * S k j) := Finset.sum_comm
    _ = ∑ k, (fun i => S k i) ⬝ᵥ (P *ᵥ (fun i => S k i)) :=
        Finset.sum_congr rfl fun k _ => (quad_eq_sum P (fun i => S k i)).symm

/-- `tr(PZ) > 0` for `P` positive definite and `Z` positive semidefinite and nonzero. -/
theorem trace_mul_pos (P Z : Matrix (Fin nn) (Fin nn) ℝ) (hP : P.PosDef)
    (hZ : Z.PosSemidef) (hZne : Z ≠ 0) : 0 < (P * Z).trace := by
  classical
  obtain ⟨c, hc, hlow⟩ := exists_pos_lower P (fun x hx => by
    simpa using hP.dotProduct_mulVec_pos hx)
  have hSpsd : (CFC.sqrt Z).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Z)
  have hSsq : CFC.sqrt Z * CFC.sqrt Z = Z := by
    have h := CFC.sq_sqrt Z (Matrix.nonneg_iff_posSemidef.mpr hZ)
    rwa [sq] at h
  set S : Matrix (Fin nn) (Fin nn) ℝ := CFC.sqrt Z with hSdef
  have hSsymm : S.IsSymm := hSpsd.isHermitian
  have hSne : S ≠ 0 := by
    intro h; apply hZne; rw [← hSsq, h, Matrix.zero_mul]
  obtain ⟨k0, i0, hk0⟩ : ∃ k i, S k i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hSne (by ext k i; simp [hcon k i])
  rw [← hSsq, trace_mul_sq P S hSsymm]
  refine lt_of_lt_of_le ?_ (Finset.sum_le_sum fun k _ => hlow (fun i => S k i))
  refine Finset.sum_pos' (fun k _ => mul_nonneg hc.le (dotProduct_self_nonneg _))
    ⟨k0, Finset.mem_univ k0, ?_⟩
  exact mul_pos hc (dotProduct_self_pos (fun h => hk0 (congrFun h i0)))



/-! ### The cone of positive semidefinite matrices, as a cone in `ℝ^(nn·nn)` -/

/-- Matrices with nonnegative quadratic form. On symmetric matrices this is exactly
the positive semidefinite cone; the extra (non-symmetric) directions are what gives
it a nonempty interior inside the full matrix space. -/
def Kcone (nn : ℕ) : Set (EuclideanSpace ℝ (Fin (nn * nn))) :=
  {y | ∀ x : Fin nn → ℝ, 0 ≤ x ⬝ᵥ ((ofE y) *ᵥ x)}

/-- Matrices with positive definite quadratic form. -/
def PDset (nn : ℕ) : Set (EuclideanSpace ℝ (Fin (nn * nn))) :=
  {y | ∀ x : Fin nn → ℝ, x ≠ 0 → 0 < x ⬝ᵥ ((ofE y) *ᵥ x)}

theorem convex_Kcone : Convex ℝ (Kcone nn) := by
  rintro y₁ h₁ y₂ h₂ a b ha hb hab x
  have hof : ofE (a • y₁ + b • y₂) = a • ofE y₁ + b • ofE y₂ := rfl
  rw [hof, quad_add, quad_smul_mat, quad_smul_mat]
  exact add_nonneg (mul_nonneg ha (h₁ x)) (mul_nonneg hb (h₂ x))

theorem smul_mem_Kcone {t : ℝ} (ht : 0 < t) {y : EuclideanSpace ℝ (Fin (nn * nn))}
    (hy : y ∈ Kcone nn) : t • y ∈ Kcone nn := by
  intro x
  have hof : ofE (t • y) = t • ofE y := rfl
  rw [hof, quad_smul_mat]
  exact mul_nonneg ht.le (hy x)

theorem isClosed_Kcone : IsClosed (Kcone nn) := by
  have hrw : Kcone nn
      = ⋂ x : Fin nn → ℝ, {y : EuclideanSpace ℝ (Fin (nn * nn)) |
          0 ≤ (inner ℝ y (toE (Matrix.vecMulVec x x)) : ℝ)} := by
    ext y
    simp only [Kcone, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h x
      have := h x
      rwa [quad_eq_inner, toE_ofE] at this
    · intro h x
      have := h x
      rwa [quad_eq_inner, toE_ofE]
  rw [hrw]
  exact isClosed_iInter fun x =>
    isClosed_le continuous_const (continuous_id.inner continuous_const)

theorem isOpen_PDset : IsOpen (PDset nn) := by
  rw [Metric.isOpen_iff]
  intro y hy
  obtain ⟨c, hc, hclow⟩ := exists_pos_lower (ofE y) (fun x hx => hy x hx)
  refine ⟨c, hc, fun z hz x hx => ?_⟩
  have hzy : ‖z - y‖ < c := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
  have hxx : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
  have hdecomp : ofE y + (ofE z - ofE y) = ofE z := by abel
  have hsplit : x ⬝ᵥ ((ofE z) *ᵥ x)
      = x ⬝ᵥ ((ofE y) *ᵥ x) + x ⬝ᵥ ((ofE z - ofE y) *ᵥ x) := by
    rw [← quad_add, hdecomp]
  have hbound : |x ⬝ᵥ ((ofE z - ofE y) *ᵥ x)| ≤ ‖z - y‖ * (x ⬝ᵥ x) := by
    have h := abs_quad_le (ofE z - ofE y) x
    rwa [toE_sub, toE_ofE, toE_ofE] at h
  have h1 : -(‖z - y‖ * (x ⬝ᵥ x)) ≤ x ⬝ᵥ ((ofE z - ofE y) *ᵥ x) :=
    neg_le_of_abs_le hbound
  have h2 : ‖z - y‖ * (x ⬝ᵥ x) < c * (x ⬝ᵥ x) := mul_lt_mul_of_pos_right hzy hxx
  have h3 := hclow x
  rw [hsplit]
  linarith

theorem PDset_subset_Kcone : PDset nn ⊆ Kcone nn := by
  intro y hy x
  by_cases hx : x = 0
  · subst hx; simp [dotProduct, Matrix.mulVec]
  · exact (hy x hx).le

/-- On symmetric matrices, membership in `Kcone` is positive semidefiniteness. -/
theorem mem_Kcone_iff {M : Matrix (Fin nn) (Fin nn) ℝ} (hM : M.IsSymm) :
    toE M ∈ Kcone nn ↔ M.PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_isSymm hM) fun x => ?_
    rw [show (star x : Fin nn → ℝ) = x from star_trivial x]
    have := h x
    rwa [ofE_toE] at this
  · intro h x
    rw [ofE_toE]
    have := h.dotProduct_mulVec_nonneg x
    rwa [show (star x : Fin nn → ℝ) = x from star_trivial x] at this

theorem zero_mem_Kcone : (0 : EuclideanSpace ℝ (Fin (nn * nn))) ∈ Kcone nn := by
  intro x
  have h : ofE (0 : EuclideanSpace ℝ (Fin (nn * nn))) = 0 := rfl
  rw [h]
  simp [Matrix.zero_mulVec, dotProduct]

/-- An affine function of `x` has a finite infimum over `ℝⁿ` only if its linear part
vanishes, in which case the infimum is its constant term. -/
theorem iInf_affine_eq {n : ℕ} (A : ℝ) (g : Fin n → ℝ) (s : ℝ)
    (h : (⨅ u : EuclideanSpace ℝ (Fin n),
      ((A + ∑ i, (WithLp.ofLp u) i * g i : ℝ) : EReal)) = ((s : ℝ) : EReal)) :
    (∀ i, g i = 0) ∧ A = s := by
  classical
  have hall : ∀ i, g i = 0 := by
    intro i
    by_contra hgi
    have hle : (⨅ u : EuclideanSpace ℝ (Fin n),
        ((A + ∑ i, (WithLp.ofLp u) i * g i : ℝ) : EReal)) ≤ ((s - 1 : ℝ) : EReal) := by
      refine le_trans
        (iInf_le _ (WithLp.toLp 2 (fun k : Fin n => if k = i then (s - 1 - A) / g i else 0))) ?_
      have hsum : ∑ k, (WithLp.ofLp (WithLp.toLp 2
          (fun k : Fin n => if k = i then (s - 1 - A) / g i else 0) :
            EuclideanSpace ℝ (Fin n))) k * g k = s - 1 - A := by
        rw [Finset.sum_eq_single i]
        · show (if i = i then (s - 1 - A) / g i else 0) * g i = s - 1 - A
          rw [if_pos rfl, div_mul_cancel₀ _ hgi]
        · intro k _ hk
          show (if k = i then (s - 1 - A) / g i else 0) * g k = 0
          rw [if_neg hk, zero_mul]
        · intro hcon; exact absurd (Finset.mem_univ i) hcon
      rw [hsum]
      norm_num
    rw [h, EReal.coe_le_coe_iff] at hle
    linarith
  refine ⟨hall, ?_⟩
  have hconst : ∀ u : EuclideanSpace ℝ (Fin n),
      ((A + ∑ i, (WithLp.ofLp u) i * g i : ℝ) : EReal) = ((A : ℝ) : EReal) := by
    intro u
    have hz : ∑ i, (WithLp.ofLp u) i * g i = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hall i, mul_zero]
    rw [hz, add_zero]
  rw [iInf_congr hconst, iInf_const] at h
  exact EReal.coe_eq_coe_iff.mp h

end SDPAux

open ConvexOptimization SDPAux in
theorem ConvexOptimization.sdp_strong_duality {n nn : ℕ} (c : Fin n → ℝ)
    (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (hF : ∀ i, (F i).IsSymm)
    (G : Matrix (Fin nn) (Fin nn) ℝ) (hG : G.IsSymm)
    (xs : Fin n → ℝ) (hxs : (-(G + ∑ i, xs i • F i)).PosDef)
    (hbdd : BddBelow ((fun x : Fin n → ℝ => c ⬝ᵥ x) ''
      {x | (-(G + ∑ i, x i • F i)).PosSemidef})) :
    ∃ Z : Matrix (Fin nn) (Fin nn) ℝ, Z.PosSemidef ∧
      (∀ i, ((F i) * Z).trace + c i = 0) ∧
      (G * Z).trace =
        sInf ((fun x : Fin n → ℝ => c ⬝ᵥ x) ''
          {x | (-(G + ∑ i, x i • F i)).PosSemidef}) := by
  classical
  -- Entrywise description of the affine matrix family.
  have hFsum : ∀ (y : Fin n → ℝ) (i j : Fin nn),
      (∑ k, y k • F k) i j = ∑ k, y k * F k i j := by
    intro y i j
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun k _ => rfl
  have hAapply : ∀ (y : Fin n → ℝ) (i j : Fin nn),
      (G + ∑ k, y k • F k) i j = G i j + ∑ k, y k * F k i j := by
    intro y i j; rw [Matrix.add_apply, hFsum]
  have hAsymm : ∀ y : Fin n → ℝ, (G + ∑ k, y k • F k).IsSymm := by
    intro y
    refine isSymm_of_apply fun i j => ?_
    rw [hAapply, hAapply, isSymm_apply hG i j]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [isSymm_apply (hF k) i j]
  have hnegsymm : ∀ y : Fin n → ℝ, (-(G + ∑ k, y k • F k)).IsSymm := by
    intro y
    refine isSymm_of_apply fun i j => ?_
    simp only [Matrix.neg_apply]
    rw [isSymm_apply (hAsymm y) i j]
  -- The cone program data.
  set f₀ : EuclideanSpace ℝ (Fin n) → ℝ := fun u => c ⬝ᵥ (WithLp.ofLp u) with hf₀def
  set fm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (nn * nn)) :=
    fun u => toE (G + ∑ i, (WithLp.ofLp u) i • F i) with hfmdef
  have hfeas : ∀ u : EuclideanSpace ℝ (Fin n),
      -fm u ∈ Kcone nn ↔ (-(G + ∑ i, (WithLp.ofLp u) i • F i)).PosSemidef := by
    intro u
    rw [hfmdef]
    simp only
    rw [← toE_neg]
    exact mem_Kcone_iff (hnegsymm _)
  have hset : f₀ '' {u : EuclideanSpace ℝ (Fin n) |
        -fm u ∈ Kcone nn ∧ ∀ j : Fin 0, ⟪(Fin.elim0 j : EuclideanSpace ℝ (Fin n)), u⟫
          = (Fin.elim0 j : ℝ)}
      = (fun x : Fin n → ℝ => c ⬝ᵥ x) '' {x | (-(G + ∑ i, x i • F i)).PosSemidef} := by
    ext r
    constructor
    · rintro ⟨u, ⟨hu, -⟩, rfl⟩
      exact ⟨WithLp.ofLp u, (hfeas u).mp hu, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨WithLp.toLp 2 x, ⟨(hfeas (WithLp.toLp 2 x)).mpr hx, fun j => Fin.elim0 j⟩, rfl⟩
  -- Slater point.
  have hslater : -fm (WithLp.toLp 2 xs) ∈ interior (Kcone nn) := by
    refine interior_maximal PDset_subset_Kcone isOpen_PDset ?_
    intro x hx
    have h1 : (-fm (WithLp.toLp 2 xs)) = toE (-(G + ∑ i, xs i • F i)) := by
      rw [hfmdef, ← toE_neg]
    rw [h1, ofE_toE]
    have := hxs.dotProduct_mulVec_pos hx
    rwa [show (star x : Fin nn → ℝ) = x from star_trivial x] at this
  -- Apply cone-program strong duality.
  obtain ⟨z, nu, hz, hdual⟩ :=
    ConvexOptimization.conic_slater_strong_duality (n := n) (d := nn * nn) (p := 0)
      f₀ (by
        refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
        have hlin : f₀ (a • x + b • y) = a * f₀ x + b * f₀ y := by
          simp only [hf₀def, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by
            simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
              smul_eq_mul]
            ring
        rw [hlin]; simp)
      (Kcone nn) convex_Kcone isClosed_Kcone (fun t ht y hy => smul_mem_Kcone ht hy)
      fm (by
        intro x y θ hθ0 hθ1
        have hmat : θ • (G + ∑ i, (WithLp.ofLp x) i • F i)
            + (1 - θ) • (G + ∑ i, (WithLp.ofLp y) i • F i)
            - (G + ∑ i, (WithLp.ofLp (θ • x + (1 - θ) • y)) i • F i) = 0 := by
          ext i j
          rw [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
            smul_eq_mul, smul_eq_mul, hAapply, hAapply, hAapply, Matrix.zero_apply]
          have hterm : ∀ k : Fin n, (WithLp.ofLp (θ • x + (1 - θ) • y)) k * F k i j
              = θ * ((WithLp.ofLp x) k * F k i j)
                + (1 - θ) * ((WithLp.ofLp y) k * F k i j) := by
            intro k
            simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
              smul_eq_mul]
            ring
          rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
          ring
        have hzero : θ • fm x + (1 - θ) • fm y - fm (θ • x + (1 - θ) • y) = 0 := by
          rw [hfmdef]
          simp only
          rw [← toE_smul, ← toE_smul, ← toE_add, ← toE_sub, hmat]
          ext k; rfl
        rw [hzero]
        exact zero_mem_Kcone)
      Fin.elim0 (linearIndependent_empty_type) Fin.elim0
      (WithLp.toLp 2 xs) hslater (fun j => Fin.elim0 j)
      (by rw [hset]; exact hbdd)
  -- Read off the certificate.
  set W : Matrix (Fin nn) (Fin nn) ℝ := ofE z with hWdef
  set Z : Matrix (Fin nn) (Fin nn) ℝ := (2 : ℝ)⁻¹ • (W + Wᵀ) with hZdef
  have hZsymm : Z.IsSymm := by
    unfold Matrix.IsSymm
    rw [hZdef, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose,
      add_comm Wᵀ W]
  have hWE : toE W = z := by rw [hWdef, toE_ofE]
  have hpair : ∀ M : Matrix (Fin nn) (Fin nn) ℝ, M.IsSymm →
      (inner ℝ z (toE M) : ℝ) = (M * Z).trace := by
    intro M hM
    have hzM : (inner ℝ z (toE M) : ℝ) = ∑ i, ∑ j, W i j * M i j := by
      rw [← hWE, inner_toE]
    have hswap : ∑ i, ∑ j, W j i * M i j = ∑ i, ∑ j, W i j * M i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [isSymm_apply hM i j]
    have hZij : ∀ i j, M i j * Z i j = (W i j * M i j + W j i * M i j) / 2 := by
      intro i j
      simp only [hZdef, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      ring
    have hinner : ∀ i : Fin nn, ∑ j, (W i j * M i j + W j i * M i j) / 2
        = ((∑ j, W i j * M i j) + (∑ j, W j i * M i j)) / 2 := by
      intro i; rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [hzM, trace_mul_eq_sum M Z hZsymm,
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hZij i j,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i,
      ← Finset.sum_div, Finset.sum_add_distrib, hswap]
    ring
  have hZpsd : Z.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_isSymm hZsymm) ?_
    intro v
    rw [show (star v : Fin nn → ℝ) = v from star_trivial v]
    have hq : v ⬝ᵥ (Z *ᵥ v) = (Matrix.vecMulVec v v * Z).trace := by
      rw [trace_mul_eq_sum _ Z hZsymm, quad_eq_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        simp [Matrix.vecMulVec_apply]; ring
    rw [hq, ← hpair _ (vecMulVec_isSymm v)]
    have hmem : toE (Matrix.vecMulVec v v) ∈ Kcone nn := by
      intro x; rw [ofE_toE, quad_vecMulVec]; positivity
    have := hz _ hmem
    rwa [real_inner_comm] at this
  -- The Lagrangian is affine in `x`, so finiteness of its infimum forces stationarity.
  set A : ℝ := (G * Z).trace with hAdef
  set g : Fin n → ℝ := fun i => c i + (F i * Z).trace with hgdef
  have hlag : ∀ u : EuclideanSpace ℝ (Fin n),
      f₀ u + (inner ℝ z (fm u) : ℝ) + ∑ j : Fin 0, nu j * (⟪(Fin.elim0 j : EuclideanSpace ℝ (Fin n)), u⟫ - (Fin.elim0 j : ℝ))
        = A + ∑ i, (WithLp.ofLp u) i * g i := by
    intro u
    have hexp : (inner ℝ z (fm u) : ℝ) = A + ∑ i, (WithLp.ofLp u) i * ((F i * Z).trace) := by
      rw [hfmdef]
      simp only
      rw [hpair _ (hAsymm _), Matrix.add_mul, Matrix.trace_add, Finset.sum_mul, Matrix.trace_sum,
        ← hAdef]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [hexp, hf₀def]
    simp only [Finset.sum_empty, Finset.univ_eq_empty, add_zero, hgdef, dotProduct]
    have hR : ∑ i, (WithLp.ofLp u) i * (c i + (F i * Z).trace)
        = ∑ i, c i * (WithLp.ofLp u) i + ∑ i, (WithLp.ofLp u) i * (F i * Z).trace := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hR]
    ring
  have hdual2 : (⨅ u : EuclideanSpace ℝ (Fin n),
      ((A + ∑ i, (WithLp.ofLp u) i * g i : ℝ) : EReal))
      = ((sInf (f₀ '' {u : EuclideanSpace ℝ (Fin n) | -fm u ∈ Kcone nn ∧
          ∀ j : Fin 0, ⟪(Fin.elim0 j : EuclideanSpace ℝ (Fin n)), u⟫
            = (Fin.elim0 j : ℝ)}) : ℝ) : EReal) := by
    rw [← hdual]
    exact iInf_congr fun u => by rw [hlag u]
  obtain ⟨hg0, hA⟩ := iInf_affine_eq A g _ hdual2
  rw [hset] at hA
  refine ⟨Z, hZpsd, fun i => ?_, ?_⟩
  · have hi := hg0 i
    rw [hgdef] at hi
    simp only at hi
    linarith
  · rw [hAdef] at hA
    exact hA

end
-- END MODULE AttributedSDPSlater

-- BEGIN MODULE PrimalSlater
section

set_option autoImplicit false

namespace VBSDP.Duality.Proof

lemma sign_adjusted_lmi {m n : ℕ} (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) :
    -(-F₀ + ∑ i, x i • (-F i)) = lmi F₀ F x := by
  simp [lmi, Finset.sum_neg_distrib, add_comm]

lemma primal_slater_bounded_dual_witness {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsSymm) (hF : ∀ i, (F i).IsSymm)
    (xs : Fin m → ℝ) (hxs : (lmi F₀ F xs).PosDef)
    (hbdd : BddBelow ((fun x : Fin m → ℝ => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, IsDualFeasible F c Z ∧
      -(F₀ * Z).trace = sInf ((fun x : Fin m → ℝ => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x}) := by
  have hset : {x : Fin m → ℝ | (-(-F₀ + ∑ i, x i • (-F i))).PosSemidef} =
      {x | IsPrimalFeasible F₀ F x} := by
    ext x
    change (-(-F₀ + ∑ i, x i • (-F i))).PosSemidef ↔ (lmi F₀ F x).PosSemidef
    rw [sign_adjusted_lmi]
  obtain ⟨Z, hZ, htrace, hval⟩ := ConvexOptimization.sdp_strong_duality c
    (fun i => -F i) (fun i => (hF i).neg) (-F₀) hF₀.neg xs
    (by simpa only [sign_adjusted_lmi] using hxs) (by simpa only [hset] using hbdd)
  refine ⟨Z, ⟨hZ, ?_⟩, ?_⟩
  · intro i
    have h := htrace i
    simp only [Matrix.neg_mul, Matrix.trace_neg] at h
    linarith
  · simpa only [Matrix.neg_mul, Matrix.trace_neg, hset] using hval

end VBSDP.Duality.Proof

end
-- END MODULE PrimalSlater

-- BEGIN MODULE SymmetricKernel
section
namespace VBSDP.Duality.Proof
open scoped BigOperators

lemma functional_factors_finite {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} (A : E →ₗ[ℝ] (Fin m → ℝ)) (f : E →ₗ[ℝ] ℝ)
    (hf : ∀ z, A z = 0 → f z = 0) :
    ∃ c : Fin m → ℝ, ∀ z, f z = ∑ i, c i * A z i := by
  have hfmem : f ∈ (LinearMap.ker A).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]; exact hf
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hfmem
  obtain ⟨g,hg⟩ := hfmem
  refine ⟨fun i => g (Pi.single i 1), fun z => ?_⟩
  have hz : A z = ∑ i, A z i • Pi.single i 1 := by ext j; simp [Pi.single_apply]
  have he : f z = g (A z) := (congrArg (fun l : E →ₗ[ℝ] ℝ => l z) hg).symm
  rw [he]
  conv_lhs => rw [hz,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  simp only [smul_eq_mul]
  ring

def symmetricSpace (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {H | H.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hH hK => hH.add hK
  smul_mem' := fun c _ hH => hH.smul c

variable {m n : ℕ}
def traceForm (H : Matrix (Fin n) (Fin n) ℝ) : symmetricSpace n →ₗ[ℝ] ℝ where
  toFun Z := (H * (Z : Matrix (Fin n) (Fin n) ℝ)).trace
  map_add' := by intros; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' := by intros; simp

def constraints (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    symmetricSpace n →ₗ[ℝ] (Fin m → ℝ) := LinearMap.pi fun i => traceForm (F i)
noncomputable def kernelBasis (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Module.Basis (Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) ℝ (LinearMap.ker (constraints F)) :=
  by
    classical
    letI : Module.Free ℝ (LinearMap.ker (constraints F)) := Module.Free.of_divisionRing ℝ (LinearMap.ker (constraints F))
    exact Module.finBasis ℝ (LinearMap.ker (constraints F))
noncomputable def basisMatrix (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) : Matrix (Fin n) (Fin n) ℝ :=
  ((kernelBasis F a : LinearMap.ker (constraints F)) : symmetricSpace n)
lemma basisMatrix_symm (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) :
    (basisMatrix F a).IsSymm := ((kernelBasis F a : LinearMap.ker (constraints F)) : symmetricSpace n).property
lemma basisMatrix_trace_zero (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) (i : Fin m) :
    (F i * basisMatrix F a).trace = 0 := by
  have h := (kernelBasis F a).property
  exact congrFun h i
lemma exists_kernel_coordinates (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hzero : ∀ i, (F i * H).trace = 0) :
    ∃ t : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ,
      H = ∑ a, t a • basisMatrix F a := by
  let Z : LinearMap.ker (constraints F) := ⟨⟨H,hH⟩,funext hzero⟩
  refine ⟨(kernelBasis F).repr Z, ?_⟩
  have h := (kernelBasis F).sum_repr Z
  have he := congrArg (fun z : LinearMap.ker (constraints F) =>
    ((z : symmetricSpace n) : Matrix (Fin n) (Fin n) ℝ)) h
  change H = ∑ a, ((kernelBasis F).repr Z) a • basisMatrix F a
  simpa only [Submodule.coe_sum, Submodule.coe_smul, basisMatrix, Z] using he.symm
lemma trace_pairing_nondegenerate (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hz : ∀ Z : symmetricSpace n, traceForm H Z = 0) : H = 0 := by
  have hself : (H * H).trace = 0 := hz ⟨H,hH⟩
  have he : (H * H).trace = ∑ i, ∑ j, (H i j)^2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs : H j i = H i j := congrFun (congrFun hH i) j
    rw [hs,pow_two]
  rw [he] at hself
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (H i j))).mp hself
  ext i j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (H i j))).mp
    (hi i (Finset.mem_univ i)) j (Finset.mem_univ j)
  simpa using (sq_eq_zero_iff.mp hj)
lemma kernel_annihilator_span (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i, (F i).IsSymm) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hzero : ∀ a, (H * basisMatrix F a).trace = 0) :
    ∃ c : Fin m → ℝ, H = ∑ i, c i • F i := by
  have hk : ∀ Z : symmetricSpace n, constraints F Z = 0 → traceForm H Z = 0 := by
    intro Z hZ
    obtain ⟨t,ht⟩ := exists_kernel_coordinates F Z Z.property (fun i => congrFun hZ i)
    change (H * (Z : Matrix (Fin n) (Fin n) ℝ)).trace = 0
    rw [ht,Matrix.mul_sum,Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro a _
    simp [hzero a]
  obtain ⟨c,hc⟩ := functional_factors_finite (constraints F) (traceForm H) hk
  refine ⟨c, ?_⟩
  apply sub_eq_zero.mp
  have hsum : (∑ i, c i • F i).IsSymm := by
    change Matrix.transpose (∑ i, c i • F i) = ∑ i, c i • F i
    simp only [Matrix.transpose_sum, Matrix.transpose_smul]
    exact Finset.sum_congr rfl fun i _ => congrArg (fun H => c i • H) (hF i)
  apply trace_pairing_nondegenerate _ (hH.sub hsum)
  intro Z
  change ((H - ∑ i, c i • F i) * (Z : Matrix (Fin n) (Fin n) ℝ)).trace = 0
  rw [Matrix.sub_mul,Matrix.trace_sub,Matrix.sum_mul,Matrix.trace_sum]
  have hh := hc Z
  change (H * (Z : Matrix (Fin n) (Fin n) ℝ)).trace = ∑ i, c i * (F i * (Z : Matrix (Fin n) (Fin n) ℝ)).trace at hh
  simp only [Matrix.smul_mul,Matrix.trace_smul]
  exact sub_eq_zero.mpr hh
end VBSDP.Duality.Proof
end
-- END MODULE SymmetricKernel

-- BEGIN MODULE DualParam
section

set_option autoImplicit false

namespace VBSDP.Duality.Proof

variable {m n : ℕ}

lemma trace_lmi_right (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) :
    (lmi F₀ F x * Z).trace = (F₀ * Z).trace + ∑ i, x i * (F i * Z).trace := by
  rw [lmi, Matrix.add_mul, Matrix.trace_add, Matrix.sum_mul, Matrix.trace_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma trace_lmi_left (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) :
    (Z * lmi F₀ F x).trace = (Z * F₀).trace + ∑ i, x i * (Z * F i).trace := by
  rw [lmi, Matrix.mul_add, Matrix.trace_add, Matrix.mul_sum, Matrix.trace_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma dual_param_constraints (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (c : Fin m → ℝ) (Z₀ : Matrix (Fin n) (Fin n) ℝ)
    (hZ₀ : ∀ i, (F i * Z₀).trace = c i)
    (t : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ) :
    ∀ i, (F i * lmi Z₀ (basisMatrix F) t).trace = c i := by
  intro i
  rw [trace_lmi_left, hZ₀ i]
  simp [basisMatrix_trace_zero]

lemma dual_param_surjective (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (c : Fin m → ℝ) (Z₀ : Matrix (Fin n) (Fin n) ℝ) (hZ₀s : Z₀.IsSymm)
    (hZ₀ : ∀ i, (F i * Z₀).trace = c i)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : IsDualFeasible F c Z) :
    ∃ t : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ,
      Z = lmi Z₀ (basisMatrix F) t := by
  have hZs : Z.IsSymm := hZ.1.isHermitian
  have hz : ∀ i, (F i * (Z - Z₀)).trace = 0 := by
    intro i
    rw [Matrix.mul_sub, Matrix.trace_sub, hZ.2 i, hZ₀ i, sub_self]
  obtain ⟨t, ht⟩ := exists_kernel_coordinates F (Z - Z₀) (hZs.sub hZ₀s) hz
  refine ⟨t, ?_⟩
  rw [lmi, ← ht]
  abel

noncomputable def parameterObjective (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    (Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ) :=
  fun a => (F₀ * basisMatrix F a).trace

lemma dual_param_value (F₀ Z₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (t : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ) :
    -(F₀ * lmi Z₀ (basisMatrix F) t).trace =
      -(F₀ * Z₀).trace - parameterObjective F₀ F ⬝ᵥ t := by
  rw [trace_lmi_left]
  unfold parameterObjective dotProduct
  rw [neg_add]
  congr 1
  exact congrArg Neg.neg (Finset.sum_congr rfl (fun a _ => mul_comm _ _))

lemma dual_param_value_set (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (Z₀ : Matrix (Fin n) (Fin n) ℝ) (hZ₀s : Z₀.IsSymm)
    (hZ₀ : ∀ i, (F i * Z₀).trace = c i) :
    (fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z} =
      (fun a : ℝ => -(F₀ * Z₀).trace - a) ''
        ((fun t => parameterObjective F₀ F ⬝ᵥ t) ''
          {t | IsPrimalFeasible Z₀ (basisMatrix F) t}) := by
  ext r
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    obtain ⟨t, rfl⟩ := dual_param_surjective F c Z₀ hZ₀s hZ₀ Z hZ
    exact ⟨_, ⟨t, hZ.1, rfl⟩, (dual_param_value F₀ Z₀ F t).symm⟩
  · rintro ⟨a, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨lmi Z₀ (basisMatrix F) t, ⟨ht, dual_param_constraints F c Z₀ hZ₀ t⟩,
      dual_param_value F₀ Z₀ F t⟩

end VBSDP.Duality.Proof

end
-- END MODULE DualParam

-- BEGIN MODULE RealExtrema
section

namespace VBSDP.Duality.Proof
lemma sup_sub_image (A : Set ℝ) (hne : A.Nonempty) (hb : BddBelow A) (k : ℝ) :
    sSup ((fun a => k - a) '' A) = k - sInf A := by
  have hne' : ((fun a => k - a) '' A).Nonempty := hne.image _
  have hb' : BddAbove ((fun a => k - a) '' A) := by
    obtain ⟨b,hb⟩ := hb
    refine ⟨k-b, ?_⟩
    rintro _ ⟨a,ha,rfl⟩
    exact sub_le_sub_left (hb ha) k
  apply le_antisymm
  · apply csSup_le hne'
    rintro _ ⟨a,ha,rfl⟩
    exact sub_le_sub_left (csInf_le hb ha) k
  · have hlow : k - sSup ((fun a => k-a) '' A) ≤ sInf A := by
      apply le_csInf hne
      intro a ha
      have h := le_csSup hb' (show k-a ∈ ((fun a => k-a) '' A) from ⟨a,ha,rfl⟩)
      linarith
    linarith
end VBSDP.Duality.Proof
end
-- END MODULE RealExtrema

-- BEGIN MODULE DualSlater
section

set_option autoImplicit false

namespace VBSDP.Duality.Proof

lemma dual_slater_bounded_primal_witness {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsSymm) (hF : ∀ i, (F i).IsSymm)
    (Z₀ : Matrix (Fin n) (Fin n) ℝ) (hZ₀ : Z₀.PosDef)
    (hZ₀c : ∀ i, (F i * Z₀).trace = c i)
    (hbdd : BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})) :
    ∃ x : Fin m → ℝ, IsPrimalFeasible F₀ F x ∧
      c ⬝ᵥ x = sSup ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z}) := by
  have hZ₀s : Z₀.IsSymm := hZ₀.isHermitian
  let A : Set ℝ := (fun t => parameterObjective F₀ F ⬝ᵥ t) ''
    {t | IsPrimalFeasible Z₀ (basisMatrix F) t}
  have hzero : lmi Z₀ (basisMatrix F) (0 : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ) = Z₀ := by
    simp [lmi]
  have hAne : A.Nonempty := by
    refine ⟨_, ⟨0, ?_, rfl⟩⟩
    change (lmi Z₀ (basisMatrix F) 0).PosSemidef
    rw [hzero]
    exact hZ₀.posSemidef
  obtain ⟨b, hb⟩ := hbdd
  have hAbdd : BddBelow A := by
    refine ⟨-(F₀ * Z₀).trace - b, ?_⟩
    rintro a ⟨t, ht, rfl⟩
    have hZt : IsDualFeasible F c (lmi Z₀ (basisMatrix F) t) :=
      ⟨ht, dual_param_constraints F c Z₀ hZ₀c t⟩
    have hh := hb ⟨lmi Z₀ (basisMatrix F) t, hZt, rfl⟩
    change -(F₀ * lmi Z₀ (basisMatrix F) t).trace ≤ b at hh
    rw [dual_param_value] at hh
    linarith
  obtain ⟨Y, hY, hval⟩ := primal_slater_bounded_dual_witness
    (parameterObjective F₀ F) Z₀ (basisMatrix F) hZ₀s (basisMatrix_symm F) 0
    (by simpa only [hzero] using hZ₀) hAbdd
  have hYs : Y.IsSymm := hY.1.isHermitian
  have horth (a : Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) :
      ((Y - F₀) * basisMatrix F a).trace = 0 := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm Y (basisMatrix F a), hY.2 a]
    simp only [parameterObjective, sub_self]
  obtain ⟨x, hx⟩ := kernel_annihilator_span F hF (Y - F₀) (hYs.sub hF₀) horth
  have hlmi : lmi F₀ F x = Y := by
    rw [lmi, ← hx]
    abel
  have hxval : (lmi F₀ F x * Z₀).trace = (F₀ * Z₀).trace + c ⬝ᵥ x := by
    rw [trace_lmi_right]
    congr 1
    unfold dotProduct
    exact Finset.sum_congr rfl (fun i _ => by rw [hZ₀c i]; ring)
  rw [hlmi, Matrix.trace_mul_comm Y Z₀] at hxval
  have hobj : c ⬝ᵥ x = -(F₀ * Z₀).trace - sInf A := by
    change -(Z₀ * Y).trace = sInf A at hval
    linarith
  refine ⟨x, ?_, ?_⟩
  · change (lmi F₀ F x).PosSemidef
    rw [hlmi]
    exact hY.1
  · rw [dual_param_value_set F₀ F c Z₀ hZ₀s hZ₀c, sup_sub_image A hAne hAbdd]
    exact hobj

end VBSDP.Duality.Proof

end
-- END MODULE DualSlater

-- BEGIN MODULE WeakDuality
section

namespace VBSDP.Duality.Proof
open scoped BigOperators MatrixOrder

lemma trace_mul_nonneg {n : ℕ} (P Z : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (P * Z).trace := by
  have hs : (CFC.sqrt Z).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Z)
  have he : CFC.sqrt Z * CFC.sqrt Z = Z := by
    simpa [sq] using CFC.sq_sqrt Z (Matrix.nonneg_iff_posSemidef.mpr hZ)
  rw [← he, SDPAux.trace_mul_sq P (CFC.sqrt Z) hs.isHermitian]
  exact Finset.sum_nonneg fun k _ => by simpa using hP.dotProduct_mulVec_nonneg (fun i => CFC.sqrt Z k i)

lemma weak_duality {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : IsPrimalFeasible F₀ F x) (hZ : IsDualFeasible F c Z) :
    -(F₀ * Z).trace ≤ c ⬝ᵥ x := by
  have hn := trace_mul_nonneg (lmi F₀ F x) Z hx hZ.1
  have he : (lmi F₀ F x * Z).trace = (F₀ * Z).trace + c ⬝ᵥ x := by
    rw [lmi,Matrix.add_mul,Matrix.trace_add,Matrix.sum_mul,Matrix.trace_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.smul_mul,Matrix.trace_smul,hZ.2 i,smul_eq_mul]
    ring
  rw [he] at hn
  linarith

lemma dStar_le_pStar {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    dStar c F₀ F ≤ pStar c F₀ F := by
  apply sSup_le
  rintro a ⟨Z,hZ,rfl⟩
  apply le_sInf
  rintro b ⟨x,hx,rfl⟩
  exact EReal.coe_le_coe (weak_duality c F₀ F x Z hx hZ)

lemma primal_bounds_dual {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (hx : IsPrimalFeasible F₀ F x) :
    BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z}) := by
  refine ⟨c ⬝ᵥ x, ?_⟩
  rintro b ⟨Z,hZ,rfl⟩
  exact weak_duality c F₀ F x Z hx hZ

lemma dual_bounds_primal {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : IsDualFeasible F c Z) :
    BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x}) := by
  refine ⟨-(F₀ * Z).trace, ?_⟩
  rintro b ⟨x,hx,rfl⟩
  exact weak_duality c F₀ F x Z hx hZ
end VBSDP.Duality.Proof
end
-- END MODULE WeakDuality

-- BEGIN MODULE ERealValues
section

namespace VBSDP.Duality.Proof

lemma ereal_inf_coe (S : Set ℝ) (hne : S.Nonempty) (hb : BddBelow S) :
    sInf ((fun r : ℝ => (r : EReal)) '' S) = (sInf S : ℝ) := by
  let I : EReal := sInf ((fun r : ℝ => (r : EReal)) '' S)
  have hlo : ((sInf S : ℝ) : EReal) ≤ I := by
    apply le_sInf
    rintro _ ⟨r,hr,rfl⟩
    exact EReal.coe_le_coe (csInf_le hb hr)
  obtain ⟨r,hr⟩ := hne
  have hhi : I ≤ (r : EReal) := sInf_le ⟨r,hr,rfl⟩
  have htop : I ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r) hhi
  have hbot : I ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot (sInf S)) hlo
  have he := EReal.coe_toReal htop hbot
  have ht : I.toReal ≤ sInf S := by
    apply le_csInf ⟨r,hr⟩
    intro s hs
    apply EReal.coe_le_coe_iff.mp
    rw [he]
    exact sInf_le ⟨s,hs,rfl⟩
  apply le_antisymm _ hlo
  rw [← he]
  exact EReal.coe_le_coe ht

lemma ereal_sup_coe (S : Set ℝ) (hne : S.Nonempty) (hb : BddAbove S) :
    sSup ((fun r : ℝ => (r : EReal)) '' S) = (sSup S : ℝ) := by
  let I : EReal := sSup ((fun r : ℝ => (r : EReal)) '' S)
  have hhi : I ≤ ((sSup S : ℝ) : EReal) := by
    apply sSup_le
    rintro _ ⟨r,hr,rfl⟩
    exact EReal.coe_le_coe (le_csSup hb hr)
  obtain ⟨r,hr⟩ := hne
  have hlo : (r : EReal) ≤ I := le_sSup ⟨r,hr,rfl⟩
  have htop : I ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top (sSup S)) hhi
  have hbot : I ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot r) hlo
  have he := EReal.coe_toReal htop hbot
  have ht : sSup S ≤ I.toReal := by
    apply csSup_le ⟨r,hr⟩
    intro s hs
    apply EReal.coe_le_coe_iff.mp
    rw [he]
    exact le_sSup ⟨s,hs,rfl⟩
  apply le_antisymm hhi
  rw [← he]
  exact EReal.coe_le_coe ht

lemma ereal_inf_coe_unbounded (S : Set ℝ) (h : ¬ BddBelow S) :
    sInf ((fun r : ℝ => (r : EReal)) '' S) = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro r
  obtain ⟨s,hs,hsr⟩ := not_bddBelow_iff.mp h r
  exact lt_of_le_of_lt (sInf_le ⟨s,hs,rfl⟩) (EReal.coe_lt_coe_iff.mpr hsr)

lemma ereal_sup_coe_unbounded (S : Set ℝ) (h : ¬ BddAbove S) :
    sSup ((fun r : ℝ => (r : EReal)) '' S) = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  obtain ⟨s,hs,hrs⟩ := not_bddAbove_iff.mp h r
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hrs) (le_sSup ⟨s,hs,rfl⟩)

lemma pStar_eq_coe_inf {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hne : ∃ x, IsPrimalFeasible F₀ F x)
    (hb : BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})) :
    pStar c F₀ F = (sInf ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x}) : ℝ) := by
  have hi := ereal_inf_coe ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})
    (by obtain ⟨x,hx⟩ := hne; exact ⟨_,x,hx,rfl⟩) hb
  simpa only [Set.image_image,pStar,dStar] using hi

lemma dStar_eq_coe_sup {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hne : ∃ Z, IsDualFeasible F c Z)
    (hb : BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})) :
    dStar c F₀ F = (sSup ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z}) : ℝ) := by
  have hi := ereal_sup_coe ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})
    (by obtain ⟨Z,hZ⟩ := hne; exact ⟨_,Z,hZ,rfl⟩) hb
  simpa only [Set.image_image,pStar,dStar] using hi

lemma primal_unbounded_values {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hb : ¬ BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})) :
    pStar c F₀ F = ⊥ ∧ dStar c F₀ F = ⊥ := by
  have hp : pStar c F₀ F = ⊥ := by
    simpa only [Set.image_image,pStar,dStar] using ereal_inf_coe_unbounded _ hb
  refine ⟨hp, ?_⟩
  exact le_bot_iff.mp (hp ▸ dStar_le_pStar c F₀ F)

lemma dual_unbounded_values {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hb : ¬ BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})) :
    pStar c F₀ F = ⊤ ∧ dStar c F₀ F = ⊤ := by
  have hd : dStar c F₀ F = ⊤ := by
    simpa only [Set.image_image,pStar,dStar] using ereal_sup_coe_unbounded _ hb
  exact ⟨top_le_iff.mp (hd ▸ dStar_le_pStar c F₀ F),hd⟩

lemma dual_optimal_of_value {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : IsDualFeasible F c Z)
    (hv : ((-(F₀ * Z).trace : ℝ) : EReal) = pStar c F₀ F) :
    pStar c F₀ F = dStar c F₀ F ∧ Z ∈ Zopt c F₀ F := by
  have hl : ((-(F₀ * Z).trace : ℝ) : EReal) ≤ dStar c F₀ F := le_sSup ⟨Z,hZ,rfl⟩
  have he : pStar c F₀ F = dStar c F₀ F := le_antisymm (hv ▸ hl) (dStar_le_pStar c F₀ F)
  exact ⟨he,hZ,hv.trans he⟩

lemma primal_optimal_of_value {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (hx : IsPrimalFeasible F₀ F x)
    (hv : ((c ⬝ᵥ x : ℝ) : EReal) = dStar c F₀ F) :
    pStar c F₀ F = dStar c F₀ F ∧ x ∈ Xopt c F₀ F := by
  have hl : pStar c F₀ F ≤ ((c ⬝ᵥ x : ℝ) : EReal) := sInf_le ⟨x,hx,rfl⟩
  have he : pStar c F₀ F = dStar c F₀ F := le_antisymm (hv ▸ hl) (dStar_le_pStar c F₀ F)
  exact ⟨he,hx,hv.trans he.symm⟩

end VBSDP.Duality.Proof
end
-- END MODULE ERealValues

-- BEGIN MODULE SlaterAttainment
section

set_option autoImplicit false

namespace VBSDP.Duality.Proof

lemma primal_slater_optimal_of_bounded {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsSymm) (hF : ∀ i, (F i).IsSymm)
    (xs : Fin m → ℝ) (hxs : (lmi F₀ F xs).PosDef)
    (hbdd : BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})) :
    pStar c F₀ F = dStar c F₀ F ∧ (Zopt c F₀ F).Nonempty := by
  obtain ⟨Z, hZ, hval⟩ := primal_slater_bounded_dual_witness c F₀ F hF₀ hF xs hxs hbdd
  have hp := pStar_eq_coe_inf c F₀ F ⟨xs, hxs.posSemidef⟩ hbdd
  have hv : ((-(F₀ * Z).trace : ℝ) : EReal) = pStar c F₀ F := by rw [hp, hval]
  have ho := dual_optimal_of_value c F₀ F Z hZ hv
  exact ⟨ho.1, Z, ho.2⟩

lemma dual_slater_optimal_of_bounded {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsSymm) (hF : ∀ i, (F i).IsSymm)
    (Z₀ : Matrix (Fin n) (Fin n) ℝ) (hZ₀ : Z₀.PosDef)
    (hZ₀c : ∀ i, (F i * Z₀).trace = c i)
    (hbdd : BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})) :
    pStar c F₀ F = dStar c F₀ F ∧ (Xopt c F₀ F).Nonempty := by
  obtain ⟨x, hx, hval⟩ := dual_slater_bounded_primal_witness c F₀ F hF₀ hF Z₀ hZ₀ hZ₀c hbdd
  have hd := dStar_eq_coe_sup c F₀ F ⟨Z₀, hZ₀.posSemidef, hZ₀c⟩ hbdd
  have hv : ((c ⬝ᵥ x : ℝ) : EReal) = dStar c F₀ F := by rw [hd, hval]
  have ho := primal_optimal_of_value c F₀ F x hx hv
  exact ⟨ho.1, x, ho.2⟩

end VBSDP.Duality.Proof
end
-- END MODULE SlaterAttainment

-- BEGIN MODULE FullDuality
section

set_option autoImplicit false

namespace VBSDP.Duality

theorem theorem_3_1 {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian) :
    (((∃ x, (lmi F₀ F x).PosDef) ∨
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      pStar c F₀ F = dStar c F₀ F) ∧
    (((∃ x, (lmi F₀ F x).PosDef) ∧
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      (Xopt c F₀ F).Nonempty ∧ (Zopt c F₀ F).Nonempty) := by
  have hF₀s : F₀.IsSymm := hF₀
  have hFs : ∀ i, (F i).IsSymm := hF
  constructor
  · rintro (⟨xs, hxs⟩ | ⟨Z₀, hZ₀, hZ₀c⟩)
    · by_cases hb : BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})
      · exact (Proof.primal_slater_optimal_of_bounded c F₀ F hF₀s hFs xs hxs hb).1
      · have hu := Proof.primal_unbounded_values c F₀ F hb
        exact hu.1.trans hu.2.symm
    · by_cases hb : BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})
      · exact (Proof.dual_slater_optimal_of_bounded c F₀ F hF₀s hFs Z₀ hZ₀ hZ₀c hb).1
      · have hu := Proof.dual_unbounded_values c F₀ F hb
        exact hu.1.trans hu.2.symm
  · rintro ⟨⟨xs, hxs⟩, ⟨Z₀, hZ₀, hZ₀c⟩⟩
    have hp := Proof.dual_bounds_primal c F₀ F Z₀ ⟨hZ₀.posSemidef, hZ₀c⟩
    have hd := Proof.primal_bounds_dual c F₀ F xs hxs.posSemidef
    exact ⟨(Proof.dual_slater_optimal_of_bounded c F₀ F hF₀s hFs Z₀ hZ₀ hZ₀c hd).2,
      (Proof.primal_slater_optimal_of_bounded c F₀ F hF₀s hFs xs hxs hp).2⟩

end VBSDP.Duality

end
-- END MODULE FullDuality

-- BEGIN MODULE PublicSolution
section

open VBSDP.Duality

theorem solution {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian) :
    (((∃ x, (lmi F₀ F x).PosDef) ∨
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      pStar c F₀ F = dStar c F₀ F) ∧
    (((∃ x, (lmi F₀ F x).PosDef) ∧
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      (Xopt c F₀ F).Nonempty ∧ (Zopt c F₀ F).Nonempty) := by
  exact VBSDP.Duality.theorem_3_1 c F₀ F hF₀ hF



end
-- END MODULE PublicSolution

#print axioms VBSDP.Duality.theorem_3_1
#print axioms solution
