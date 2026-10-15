-- Prove2me | solution 1 for Plasticity.Faces.exists_common_face_of_preimages
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:34:27.451622+00:00
-- url     : https://prove2.me/submissions/2ece0ffb-6f01-42b2-8516-8c4008206cbc

import Definitions.Def_Plasticity_Faces
import Theorems.Thm_Plasticity_Ext_InvarianceOfDimension
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.Module

/-!
# The smallest face of a pair of lens endpoints has dimension at most that of the target face

For a nonexpansive bijection `F` of unit balls, a finite-dimensional sphere face `C` of the target
ball, and ball points `u, v` with `F u ∈ C` and `-F (-v) ∈ C`, the smallest face `E` of the
source ball containing `m = (u + v) / 2` is a sphere face containing `u` and `v` whose dimension
is at most `dim C`.
-/

namespace Sol_Plasticity_Faces_exists_common_face_of_preimages

open Plasticity

section Ball

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma norm_comb_le {a b : X} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ‖(1 - θ) • a + θ • b‖ ≤ 1 := by
  have h1' : 0 ≤ 1 - θ := by linarith
  calc ‖(1 - θ) • a + θ • b‖ ≤ ‖(1 - θ) • a‖ + ‖θ • b‖ := norm_add_le _ _
    _ = (1 - θ) * ‖a‖ + θ * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h1', Real.norm_of_nonneg h0]
    _ ≤ (1 - θ) * 1 + θ * 1 := by gcongr
    _ = 1 := by ring

lemma norm_half_le {a b : X} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖(1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b‖ ≤ 1 := by
  have h := norm_comb_le ha hb (θ := 1 / 2) (by norm_num) (by norm_num)
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rwa [e] at h

lemma norm_shrink_le {m d : X} (hm : ‖m‖ ≤ 1) {ε δ : ℝ} (hε : 0 < ε) (hd : ‖m + ε • d‖ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ ε) : ‖m + δ • d‖ ≤ 1 := by
  have key := norm_comb_le hm hd (θ := δ / ε) (div_nonneg hδ0 hε.le) ((div_le_one hε).mpr hδ)
  have e : m + δ • d = (1 - δ / ε) • m + (δ / ε) • (m + ε • d) := by
    rw [smul_add, smul_smul, div_mul_cancel₀ δ hε.ne']; module
  rwa [e]

/-- An average of `k ≥ 1` points of the closed unit ball lies in the ball. -/
lemma avg_norm_le {k : ℕ} (hk : k ≠ 0) (m : X) (y : Fin k → X) (hy : ∀ i, ‖m + y i‖ ≤ 1) :
    ‖m + ∑ i, (1 / (k : ℝ)) • y i‖ ≤ 1 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have e : m + ∑ i, (1 / (k : ℝ)) • y i = ∑ i, (1 / (k : ℝ)) • (m + y i) := by
    simp only [smul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_one_div_cancel hk', one_smul]
  rw [e]
  calc ‖∑ i, (1 / (k : ℝ)) • (m + y i)‖ ≤ ∑ i, ‖(1 / (k : ℝ)) • (m + y i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, (1 / (k : ℝ)) := by
        gcongr with i
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        calc 1 / (k : ℝ) * ‖m + y i‖ ≤ 1 / (k : ℝ) * 1 := by gcongr; exact hy i
          _ = 1 / (k : ℝ) := mul_one _
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one_div_cancel hk']

/-- The directions in which `m` can move both ways inside the closed unit ball. -/
def absorb (m : X) (hm : ‖m‖ ≤ 1) : Submodule ℝ X where
  carrier := {w | ∃ δ > (0 : ℝ), ∀ t : ℝ, |t| ≤ δ → ‖m + t • w‖ ≤ 1}
  add_mem' := by
    rintro w₁ w₂ ⟨δ₁, hδ₁, h₁⟩ ⟨δ₂, hδ₂, h₂⟩
    refine ⟨min δ₁ δ₂ / 2, by positivity, fun t ht => ?_⟩
    have ht' : |2 * t| ≤ min δ₁ δ₂ := by rw [abs_mul, abs_two]; linarith
    have e : m + t • (w₁ + w₂) =
        (1 / 2 : ℝ) • (m + (2 * t) • w₁) + (1 / 2 : ℝ) • (m + (2 * t) • w₂) := by module
    rw [e]
    exact norm_half_le (h₁ _ (ht'.trans (min_le_left _ _))) (h₂ _ (ht'.trans (min_le_right _ _)))
  zero_mem' := ⟨1, one_pos, fun t _ => by simpa using hm⟩
  smul_mem' := by
    rintro c w ⟨δ, hδ, h⟩
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨1, one_pos, fun t _ => by simpa using hm⟩
    · refine ⟨δ / |c|, by positivity, fun t ht => ?_⟩
      have htc : |t * c| ≤ δ := by
        rw [abs_mul]; rwa [le_div_iff₀ (abs_pos.mpr hc)] at ht
      simpa [smul_smul] using h _ htc

/-- The smallest face of the closed unit ball containing `m` (display (2.1) of the source). -/
def face (m : X) : Set X := {z | ‖z‖ ≤ 1 ∧ ∃ ε > (0 : ℝ), ‖m + ε • (m - z)‖ ≤ 1}

lemma sub_mem_absorb {m z : X} (hm : ‖m‖ ≤ 1) (hz : z ∈ face m) : z - m ∈ absorb m hm := by
  obtain ⟨hz1, ε, hε, hzε⟩ := hz
  refine ⟨min 1 ε, by positivity, fun t ht => ?_⟩
  rcases le_or_gt 0 t with h0 | h0
  · have ht1 : t ≤ 1 := (le_abs_self t).trans (ht.trans (min_le_left _ _))
    have e : m + t • (z - m) = (1 - t) • m + t • z := by module
    rw [e]; exact norm_comb_le hm hz1 h0 ht1
  · have htε : -t ≤ ε := (neg_le_abs t).trans (ht.trans (min_le_right _ _))
    have e : m + t • (z - m) = m + (-t) • (m - z) := by module
    rw [e]; exact norm_shrink_le hm hε hzε (by linarith) htε

lemma vectorSpan_face_le {m : X} (hm : ‖m‖ ≤ 1) : vectorSpan ℝ (face m) ≤ absorb m hm := by
  rw [vectorSpan_def]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨z₁, hz₁, z₂, hz₂, rfl⟩
  have e : z₁ -ᵥ z₂ = (z₁ - m) - (z₂ - m) := by rw [vsub_eq_sub]; abel
  change z₁ -ᵥ z₂ ∈ absorb m hm
  rw [e]
  exact sub_mem (sub_mem_absorb hm hz₁) (sub_mem_absorb hm hz₂)

lemma isSphereFace_face {m : X} (hm : ‖m‖ = 1) : IsSphereFace (face m) := by
  refine ⟨⟨m, hm.le, 1, one_pos, by simpa using hm.le⟩, ?_, ?_, ?_⟩
  · -- convexity
    rintro z₁ ⟨hz₁, ε₁, hε₁, h₁⟩ z₂ ⟨hz₂, ε₂, hε₂, h₂⟩ a b ha hb hab
    obtain rfl : a = 1 - b := by linarith
    refine ⟨?_, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
    · exact norm_comb_le hz₁ hz₂ hb (by linarith)
    · have k₁ := norm_shrink_le hm.le hε₁ h₁ (le_min hε₁.le hε₂.le) (min_le_left _ _)
      have k₂ := norm_shrink_le hm.le hε₂ h₂ (le_min hε₁.le hε₂.le) (min_le_right _ _)
      have key := norm_comb_le k₁ k₂ hb (by linarith)
      convert key using 2
      module
  · -- inside the sphere
    rintro z ⟨hz, ε, hε, h⟩
    rw [mem_sphere_zero_iff_norm]
    refine le_antisymm hz ?_
    have e : (1 + ε) • m = (m + ε • (m - z)) + ε • z := by module
    have hle : (1 + ε) * ‖m‖ ≤ 1 + ε * ‖z‖ := by
      calc (1 + ε) * ‖m‖ = ‖(1 + ε) • m‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by linarith)]
        _ = ‖(m + ε • (m - z)) + ε • z‖ := by rw [e]
        _ ≤ ‖m + ε • (m - z)‖ + ‖ε • z‖ := norm_add_le _ _
        _ ≤ 1 + ε * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hε.le]; linarith
    rw [hm] at hle
    nlinarith
  · -- face property
    refine ⟨fun z hz => mem_closedBall_zero_iff.mpr hz.1, ?_⟩
    rintro x₁ hx₁ x₂ hx₂ x ⟨-, ε, hε, h⟩ ⟨a, b, ha, hb, hab, rfl⟩
    rw [mem_closedBall_zero_iff] at hx₁ hx₂
    obtain rfl : a = 1 - b := by linarith
    have hden : 0 < 1 + ε * b := by positivity
    refine ⟨hx₁, ε * (1 - b) / (1 + ε * b), div_pos (mul_pos hε ha) hden, ?_⟩
    have hθ0 : 0 ≤ ε * b / (1 + ε * b) := by positivity
    have hθ1 : ε * b / (1 + ε * b) ≤ 1 := by rw [div_le_one hden]; linarith
    have key := norm_comb_le h hx₂ hθ0 hθ1
    convert key using 2
    match_scalars <;> field_simp <;> ring

end Ball

section Lens

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
/-- The two-ball lens is mapped into the direction space of `C` (display (2.1) of the source). -/
lemma lens_mem {F : X → Y}
    (hlipn : ∀ x, ‖x‖ ≤ 1 → ∀ y, ‖y‖ ≤ 1 → ‖F x - F y‖ ≤ ‖x - y‖)
    {C : Set Y} (hC : IsSphereFace C) {u v h : X} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hFu : F u ∈ C) (hFv : -F (-v) ∈ C) (hh : ‖h‖ ≤ 1) (h1 : ‖u - h‖ ≤ 1) (h2 : ‖v + h‖ ≤ 1) :
    F h ∈ vectorSpan ℝ C := by
  obtain ⟨-, hconv, -, hext⟩ := hC
  have hmid : (1 / 2 : ℝ) • F u + (1 / 2 : ℝ) • (-F (-v)) ∈ C :=
    hconv hFu hFv (by norm_num) (by norm_num) (by norm_num)
  have hx₁ : F u - F h ∈ Metric.closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff]; exact (hlipn u hu h hh).trans h1
  have hx₂ : F h - F (-v) ∈ Metric.closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff]
    refine (hlipn h hh (-v) (by rwa [norm_neg])).trans ?_
    rw [sub_neg_eq_add, add_comm]; exact h2
  have hseg : (1 / 2 : ℝ) • F u + (1 / 2 : ℝ) • (-F (-v)) ∈
      openSegment ℝ (F u - F h) (F h - F (-v)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  have hC₁ : F u - F h ∈ C := hext.left_mem_of_mem_openSegment hx₁ hx₂ hmid hseg
  have := vsub_mem_vectorSpan ℝ hFu hC₁
  rwa [vsub_eq_sub, sub_sub_cancel] at this

/-- The key count: linearly independent directions in which `m = (u + v) / 2` moves both ways
inside the ball number at most `dim C`. -/
lemma card_le {F : X → Y}
    (hinj : Set.InjOn F (Metric.closedBall (0 : X) 1))
    (hcont : ContinuousOn F (Metric.closedBall (0 : X) 1))
    (hlipn : ∀ x, ‖x‖ ≤ 1 → ∀ y, ‖y‖ ≤ 1 → ‖F x - F y‖ ≤ ‖x - y‖)
    {C : Set Y} (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    {u v : X} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hFu : F u ∈ C) (hFv : -F (-v) ∈ C)
    {k : ℕ} (w : Fin k → X) (hw : LinearIndependent ℝ w)
    (hδ : ∀ i, ∃ δ > (0 : ℝ), ∀ t : ℝ, |t| ≤ δ → ‖(1 / 2 : ℝ) • (u + v) + t • w i‖ ≤ 1) :
    k ≤ Module.finrank ℝ (vectorSpan ℝ C) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Nat.zero_le _
  have hk : k ≠ 0 := hkpos.ne'
  choose δ hδpos hδ using hδ
  set m : X := (1 / 2 : ℝ) • (u + v) with hm_def
  set q : X := (1 / 2 : ℝ) • (u - v) with hq_def
  let s : (Fin k → ℝ) → X := fun t => ∑ i, (1 / (k : ℝ)) • ((t i * δ i) • w i)
  let φ : (Fin k → ℝ) → X := fun t => (1 / 2 : ℝ) • (q + s t)
  have hs : ∀ t ∈ Metric.ball (0 : Fin k → ℝ) 1, ‖m + s t‖ ≤ 1 ∧ ‖m - s t‖ ≤ 1 := by
    intro t ht
    have hti : ∀ i, |t i| ≤ 1 := fun i => by
      have h1 := norm_le_pi_norm t i
      rw [mem_ball_zero_iff] at ht
      rw [← Real.norm_eq_abs]; linarith
    have hb : ∀ i, |t i * δ i| ≤ δ i := fun i => by
      rw [abs_mul, abs_of_pos (hδpos i)]
      have := hδpos i
      calc |t i| * δ i ≤ 1 * δ i := by gcongr; exact hti i
        _ = δ i := one_mul _
    have hb' : ∀ i, |-(t i * δ i)| ≤ δ i := fun i => by rw [abs_neg]; exact hb i
    constructor
    · exact avg_norm_le hk m (fun i => (t i * δ i) • w i) (fun i => hδ i _ (hb i))
    · have e : m - s t = m + ∑ i, (1 / (k : ℝ)) • ((-(t i * δ i)) • w i) := by
        simp only [s, neg_smul, smul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
      rw [e]
      exact avg_norm_le hk m (fun i => (-(t i * δ i)) • w i) (fun i => hδ i _ (hb' i))
  have hφ : ∀ t ∈ Metric.ball (0 : Fin k → ℝ) 1,
      ‖φ t‖ ≤ 1 ∧ ‖u - φ t‖ ≤ 1 ∧ ‖v + φ t‖ ≤ 1 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hs t ht
    refine ⟨?_, ?_, ?_⟩
    · have hq : ‖q‖ ≤ 1 := by
        have e : q = (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • (-v) := by rw [hq_def]; module
        rw [e]; exact norm_half_le hu (by rwa [norm_neg])
      have hst : ‖s t‖ ≤ 1 := by
        have e : s t = (1 / 2 : ℝ) • (m + s t) + (1 / 2 : ℝ) • (-(m - s t)) := by module
        rw [e]; exact norm_half_le h1 (by rwa [norm_neg])
      have e : φ t = (1 / 2 : ℝ) • q + (1 / 2 : ℝ) • s t := by
        change (1 / 2 : ℝ) • (q + s t) = _; module
      rw [e]; exact norm_half_le hq hst
    · have e : u - φ t = (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • (m - s t) := by
        change u - (1 / 2 : ℝ) • (q + s t) = _
        rw [hm_def, hq_def]; module
      rw [e]; exact norm_half_le hu h2
    · have e : v + φ t = (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • (m + s t) := by
        change v + (1 / 2 : ℝ) • (q + s t) = _
        rw [hm_def, hq_def]; module
      rw [e]; exact norm_half_le hv h1
  have hφB : ∀ t ∈ Metric.ball (0 : Fin k → ℝ) 1, φ t ∈ Metric.closedBall (0 : X) 1 :=
    fun t ht => mem_closedBall_zero_iff.mpr (hφ t ht).1
  have hFV : ∀ t ∈ Metric.ball (0 : Fin k → ℝ) 1, F (φ t) ∈ vectorSpan ℝ C := fun t ht =>
    lens_mem hlipn hC hu hv hFu hFv (hφ t ht).1 (hφ t ht).2.1 (hφ t ht).2.2
  have hφc : Continuous φ := by
    simp only [φ, s]
    fun_prop
  have hFφ : ContinuousOn (fun t => F (φ t)) (Metric.ball (0 : Fin k → ℝ) 1) :=
    hcont.comp hφc.continuousOn hφB
  classical
  let f : (Fin k → ℝ) → vectorSpan ℝ C := fun t =>
    if h : F (φ t) ∈ vectorSpan ℝ C then ⟨F (φ t), h⟩ else 0
  have hfc : ContinuousOn f (Metric.ball (0 : Fin k → ℝ) 1) := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine hFφ.congr (fun t ht => ?_)
    simp [f, dif_pos (hFV t ht)]
  have hfi : Set.InjOn f (Metric.ball (0 : Fin k → ℝ) 1) := by
    intro t₁ h₁ t₂ h₂ heq
    have hF : F (φ t₁) = F (φ t₂) := by
      have := congrArg Subtype.val heq
      simpa [f, dif_pos (hFV t₁ h₁), dif_pos (hFV t₂ h₂)] using this
    have hφe : φ t₁ = φ t₂ := hinj (hφB t₁ h₁) (hφB t₂ h₂) hF
    have hse : s t₁ = s t₂ := by
      have h2 := smul_right_injective X (by norm_num : (1 / 2 : ℝ) ≠ 0) hφe
      exact add_left_cancel h2
    have hsum : ∑ i, ((1 / (k : ℝ)) * (t₁ i * δ i)) • w i =
        ∑ i, ((1 / (k : ℝ)) * (t₂ i * δ i)) • w i := by
      simpa only [s, smul_smul] using hse
    funext i
    have h3 := Fintype.linearIndependent_iffₛ.mp hw _ _ hsum i
    have hk' : (1 / (k : ℝ)) ≠ 0 := by positivity
    exact mul_right_cancel₀ (hδpos i).ne' (mul_left_cancel₀ hk' h3)
  have := Plasticity.Ext.InvarianceOfDimension (Metric.ball (0 : Fin k → ℝ) 1) Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self one_pos⟩ f hfc hfi
  rwa [Module.finrank_fin_fun] at this

end Lens

end Sol_Plasticity_Faces_exists_common_face_of_preimages

open Sol_Plasticity_Faces_exists_common_face_of_preimages Plasticity in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (u v : X) (hu : u ∈ Metric.closedBall (0 : X) 1) (hv : v ∈ Metric.closedBall (0 : X) 1)
    (hFu : F u ∈ C) (hFv : -F (-v) ∈ C) :
    ∃ E : Set X, IsSphereFace E ∧ FiniteDimensional ℝ (vectorSpan ℝ E) ∧
      Module.finrank ℝ (vectorSpan ℝ E) ≤ Module.finrank ℝ (vectorSpan ℝ C) ∧ u ∈ E ∧ v ∈ E := by
  have hlipn : ∀ x, ‖x‖ ≤ 1 → ∀ y, ‖y‖ ≤ 1 → ‖F x - F y‖ ≤ ‖x - y‖ := by
    intro x hx y hy
    have := hlip.dist_le_mul x (mem_closedBall_zero_iff.mpr hx) y (mem_closedBall_zero_iff.mpr hy)
    simpa [dist_eq_norm] using this
  rw [mem_closedBall_zero_iff] at hu hv
  have hu2 : ‖u + v‖ = 2 := by
    obtain ⟨-, hconv, hsph, -⟩ := hC
    have hmidC : (1 / 2 : ℝ) • F u + (1 / 2 : ℝ) • (-F (-v)) ∈ C :=
      hconv hFu hFv (by norm_num) (by norm_num) (by norm_num)
    have hmid1 : ‖(1 / 2 : ℝ) • F u + (1 / 2 : ℝ) • (-F (-v))‖ = 1 := by
      simpa using hsph hmidC
    have e : F u - F (-v) = (2 : ℝ) • ((1 / 2 : ℝ) • F u + (1 / 2 : ℝ) • (-F (-v))) := by
      module
    have hF2 : ‖F u - F (-v)‖ = 2 := by rw [e, norm_smul, hmid1]; norm_num
    have hle := hlipn u hu (-v) (by rwa [norm_neg])
    rw [sub_neg_eq_add] at hle
    have := norm_add_le u v
    linarith
  set m : X := (1 / 2 : ℝ) • (u + v) with hm_def
  have hm1 : ‖m‖ = 1 := by
    rw [hm_def, norm_smul, hu2]; norm_num
  have hmle : ‖m‖ ≤ 1 := hm1.le
  have H : ∀ s : Finset (vectorSpan ℝ (face m)),
      LinearIndependent ℝ (fun i : s => (i : vectorSpan ℝ (face m))) →
        s.card ≤ Module.finrank ℝ (vectorSpan ℝ C) := by
    intro s hs
    let e := s.equivFin
    let w : Fin s.card → X := fun j => ((e.symm j : vectorSpan ℝ (face m)) : X)
    have hw : LinearIndependent ℝ w := by
      have h1 := hs.comp e.symm e.symm.injective
      exact h1.map' (vectorSpan ℝ (face m)).subtype (Submodule.ker_subtype _)
    refine card_le hbij.injOn hlip.continuousOn hlipn hC hfin hu hv hFu hFv w hw (fun j => ?_)
    exact vectorSpan_face_le hmle (e.symm j : vectorSpan ℝ (face m)).2
  have hrank := rank_le H
  have hfinE : FiniteDimensional ℝ (vectorSpan ℝ (face m)) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  refine ⟨face m, isSphereFace_face hm1, hfinE, Module.finrank_le_of_rank_le hrank, ?_, ?_⟩
  · refine ⟨hu, 1, one_pos, ?_⟩
    have e : m + (1 : ℝ) • (m - u) = v := by rw [hm_def]; module
    rw [e]; exact hv
  · refine ⟨hv, 1, one_pos, ?_⟩
    have e : m + (1 : ℝ) • (m - v) = u := by rw [hm_def]; module
    rw [e]; exact hu
