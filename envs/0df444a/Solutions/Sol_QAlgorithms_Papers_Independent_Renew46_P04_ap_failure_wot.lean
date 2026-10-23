-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.ap_failure_wot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:50:45.710538+00:00
-- url     : https://prove2.me/submissions/86ca799b-1665-41c0-979f-b88e937a61e6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

open Filter Set Metric

namespace X7APWot

/-- Hahn–Banach step: a convex set of operators whose WOT closure contains the identity
contains operators approximating the identity in norm at finitely many points. -/
theorem X7_sot_approx {K X : Type*} [RCLike K] [NormedAddCommGroup X] [NormedSpace K X]
    (S : Set (X →L[K] X))
    (hS : ∀ T1 ∈ S, ∀ T2 ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (a : K) • T1 + (b : K) • T2 ∈ S)
    (hW : ∀ (a : Finset X) (b : Finset (X →L[K] K)) (eps : ℝ), 0 < eps →
      ∃ T ∈ S, ∀ x ∈ a, ∀ f ∈ b, ‖f (x - T x)‖ < eps)
    (t : Finset X) (δ : ℝ) (hδ : 0 < δ) :
    ∃ T ∈ S, ∀ x ∈ t, ‖T x - x‖ < δ := by
  classical
  by_contra hcon
  push_neg at hcon
  letI : NormedSpace ℝ (t → X) := NormedSpace.restrictScalars ℝ K (t → X)
  haveI : IsScalarTower ℝ K (t → X) := Real.isScalarTower
  let φ : (X →L[K] X) → (t → X) := fun T i => T i - i
  let D : Set (t → X) := φ '' S
  have hdisj : Disjoint (ball (0 : t → X) δ) D := by
    rw [Set.disjoint_left]
    rintro v hv ⟨T, hT, rfl⟩
    obtain ⟨x, hx, hle⟩ := hcon T hT
    have h1 : ‖φ T ⟨x, hx⟩‖ ≤ ‖φ T‖ := norm_le_pi_norm (φ T) ⟨x, hx⟩
    rw [mem_ball_zero_iff] at hv
    have : ‖φ T ⟨x, hx⟩‖ = ‖T x - x‖ := rfl
    linarith
  have hconv : Convex ℝ D := by
    rintro _ ⟨T1, h1, rfl⟩ _ ⟨T2, h2, rfl⟩ a b ha hb hab
    refine ⟨(a : K) • T1 + (b : K) • T2, hS T1 h1 T2 h2 a b ha hb hab, ?_⟩
    have hab' : (a : K) + (b : K) = 1 := by exact_mod_cast hab
    funext i
    simp only [φ, Pi.add_apply, Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := K),
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab', one_smul]
  obtain ⟨f, u, hfs, hft⟩ := RCLike.geometric_hahn_banach_open (𝕜 := K)
    (convex_ball (0 : t → X) δ) isOpen_ball hconv hdisj
  have hu : 0 < u := by
    have := hfs 0 (mem_ball_self hδ)
    simpa using this
  let g : t → (X →L[K] K) := fun i => f.comp (ContinuousLinearMap.single K (fun _ : t => X) i)
  have hfg : ∀ v : t → X, f v = ∑ i, g i (v i) := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    rfl
  set m : ℕ := Fintype.card t
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  obtain ⟨T, hT, hTa⟩ := hW t (Finset.univ.image g) (u / ((m : ℝ) + 1)) (by positivity)
  have hlow := hft (φ T) ⟨T, hT, rfl⟩
  have hsum : RCLike.re (f (φ T)) ≤ (m : ℝ) * (u / ((m : ℝ) + 1)) := by
    rw [hfg, map_sum]
    calc ∑ i, RCLike.re (g i (φ T i)) ≤ ∑ _i : t, u / ((m : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 := hTa i i.2 (g i) (Finset.mem_image_of_mem g (Finset.mem_univ i))
          have h2 : RCLike.re (g i (φ T i)) ≤ ‖g i (φ T i)‖ := RCLike.re_le_norm _
          have h3 : ‖g i (φ T i)‖ = ‖g i ((i : X) - T i)‖ := by
            rw [← norm_neg, ← map_neg]
            simp [φ]
          linarith
      _ = (m : ℝ) * (u / ((m : ℝ) + 1)) := by simp [m]
  have : (m : ℝ) * (u / ((m : ℝ) + 1)) < u := by
    rw [mul_div_assoc', div_lt_iff₀ hm]
    nlinarith
  linarith

end X7APWot

open QAlgorithms.Papers.Independent.Renew46.P04

end

noncomputable section

set_option synthInstance.maxSize 8192

namespace QAlgorithms.Papers.Independent.Renew46.P04
end QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

open QAlgorithms.Papers.Independent.Renew46.P04 X7APWot in
theorem solution {K : Type*} [RCLike K] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
    [CompleteSpace X] (h : ¬ ApproximationProperty K X) (R : ℝ) (hR : 0 < R) :
    ¬ InWOTClosure {T : X →L[K] X | FiniteDimensional K T.range ∧ ‖T‖ ≤ R}
      (ContinuousLinearMap.id K X) := by
  intro hW
  apply h
  intro C hC eps heps
  have hr : 0 < eps / (3 * (R + 1)) := by positivity
  obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover (fun x => Metric.ball x (eps / (3 * (R + 1))))
    (fun x _ => Metric.ball_mem_nhds x hr)
  have hS : ∀ T1 ∈ {T : X →L[K] X | FiniteDimensional K T.range ∧ ‖T‖ ≤ R},
      ∀ T2 ∈ {T : X →L[K] X | FiniteDimensional K T.range ∧ ‖T‖ ≤ R},
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (a : K) • T1 + (b : K) • T2 ∈ {T : X →L[K] X | FiniteDimensional K T.range ∧ ‖T‖ ≤ R} := by
    rintro T1 ⟨hf1, hn1⟩ T2 ⟨hf2, hn2⟩ a b ha hb hab
    refine ⟨?_, ?_⟩
    · have hle : ((a : K) • T1 + (b : K) • T2).range ≤ T1.range ⊔ T2.range := by
        rintro _ ⟨x, rfl⟩
        exact Submodule.add_mem_sup ⟨(a : K) • x, by simp⟩ ⟨(b : K) • x, by simp⟩
      exact Submodule.finiteDimensional_of_le hle
    · calc ‖(a : K) • T1 + (b : K) • T2‖ ≤ ‖(a : K) • T1‖ + ‖(b : K) • T2‖ := norm_add_le _ _
        _ = a * ‖T1‖ + b * ‖T2‖ := by
          rw [norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal,
            abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * R + b * R := by gcongr
        _ = R := by rw [← add_mul, hab, one_mul]
  have hW' : ∀ (a : Finset X) (b : Finset (X →L[K] K)) (e : ℝ), 0 < e →
      ∃ T ∈ {T : X →L[K] X | FiniteDimensional K T.range ∧ ‖T‖ ≤ R},
        ∀ x ∈ a, ∀ f ∈ b, ‖f (x - T x)‖ < e := by
    intro a b e he
    obtain ⟨T, hT, hTa⟩ := hW a b e he
    exact ⟨T, hT, fun x hx f hf => by simpa using hTa x hx f hf⟩
  obtain ⟨T, ⟨hTfin, hTnorm⟩, hT⟩ := X7_sot_approx _ hS hW' t (eps / 3) (by positivity)
  refine ⟨T, hTfin, fun x hx => ?_⟩
  have hx' := hcov hx
  simp only [Set.mem_iUnion] at hx'
  obtain ⟨c, hct, hxc⟩ := hx'
  rw [Metric.mem_ball, dist_eq_norm] at hxc
  have hTc := hT c hct
  have e1 : T x - x = T (x - c) + (T c - c) + (c - x) := by
    rw [map_sub]; abel
  have e2 : ‖T (x - c)‖ ≤ R * ‖x - c‖ :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _))
  have e3 : ‖c - x‖ = ‖x - c‖ := norm_sub_rev _ _
  have e4 : (R + 1) * (eps / (3 * (R + 1))) = eps / 3 := by
    field_simp
  rw [e1]
  calc ‖T (x - c) + (T c - c) + (c - x)‖ ≤ ‖T (x - c)‖ + ‖T c - c‖ + ‖c - x‖ := norm_add₃_le
    _ ≤ R * ‖x - c‖ + eps / 3 + ‖x - c‖ := by rw [e3]; linarith
    _ ≤ (R + 1) * (eps / (3 * (R + 1))) + eps / 3 := by nlinarith
    _ ≤ eps := by rw [e4]; linarith
