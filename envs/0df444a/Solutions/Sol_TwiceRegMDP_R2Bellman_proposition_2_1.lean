-- Prove2me | solution 1 for TwiceRegMDP.R2Bellman.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:59:00.773732+00:00
-- url     : https://prove2.me/submissions/c928477a-dd4a-4f8d-a2fe-cd7632dc0c61

import Mathlib
import Definitions.Def_TwiceRegMDP_R2Bellman_SimplexConjugate

set_option autoImplicit false
open TwiceRegMDP.R2Bellman Filter Topology

section trm2
variable {Z : Type} [Fintype Z] [DecidableEq Z]

noncomputable def trmSf (Ω : (Z → ℝ) → ℝ) (y a : Z → ℝ) : ℝ := ∑ z, a z * y z - Ω a

lemma trm_sf_quad (Ω : (Z → ℝ) → ℝ) (m : ℝ) (hΩ : StrongConvexOn (stdSimplex ℝ Z) m Ω)
    (y a b : Z → ℝ) (ha : a ∈ stdSimplex ℝ Z) (hb : b ∈ stdSimplex ℝ Z)
    (hmax : ∀ c ∈ stdSimplex ℝ Z, trmSf Ω y c ≤ trmSf Ω y b) :
    (m / 4) * ‖a - b‖ ^ 2 ≤ trmSf Ω y b - trmSf Ω y a := by
  have hmid : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ stdSimplex ℝ Z :=
    hΩ.1 ha hb (by norm_num) (by norm_num) (by norm_num)
  have h1 := hΩ.2 ha hb (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num)
  have h2 := hmax _ hmid
  have hlin : ∑ z, ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) z * y z =
      1 / 2 * ∑ z, a z * y z + 1 / 2 * ∑ z, b z * y z := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  unfold trmSf at *
  rw [hlin] at h2
  simp only [smul_eq_mul] at h1
  nlinarith [h1, h2]

end trm2

theorem solution {Z : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (Ω : (Z → ℝ) → ℝ) (m : ℝ) (hm : 0 < m) (hΩ : StrongConvexOn (stdSimplex ℝ Z) m Ω)
    (hΩc : ContinuousOn Ω (stdSimplex ℝ Z)) :
    (∃ g : (Z → ℝ) → (Z → ℝ), (∃ K : NNReal, LipschitzWith K g) ∧
      ∀ y : Z → ℝ,
        HasFDerivAt (simplexConj Ω)
          (∑ z, g y z • (ContinuousLinearMap.proj z : (Z → ℝ) →L[ℝ] ℝ)) y ∧
        g y ∈ stdSimplex ℝ Z ∧
        ∀ a ∈ stdSimplex ℝ Z, a ≠ g y →
          ∑ z, a z * y z - Ω a < ∑ z, g y z * y z - Ω (g y)) ∧
    (∀ (c : ℝ) (y : Z → ℝ), simplexConj Ω (fun z => y z + c) = simplexConj Ω y + c) ∧
    Monotone (simplexConj Ω) := by
  obtain ⟨z0⟩ := ‹Nonempty Z›
  have hne : (stdSimplex ℝ Z).Nonempty := ⟨Pi.single z0 1, single_mem_stdSimplex ℝ z0⟩
  have hex : ∀ y : Z → ℝ, ∃ a ∈ stdSimplex ℝ Z, ∀ c ∈ stdSimplex ℝ Z, trmSf Ω y c ≤ trmSf Ω y a := by
    intro y
    have hcont : ContinuousOn (trmSf Ω y) (stdSimplex ℝ Z) := by
      unfold trmSf
      exact (continuous_finset_sum _ fun z _ => (continuous_apply z).mul continuous_const).continuousOn.sub hΩc
    obtain ⟨a, ha, hmax⟩ := (isCompact_stdSimplex ℝ Z).exists_isMaxOn hne hcont
    exact ⟨a, ha, fun c hc => hmax hc⟩
  choose g hgS hgmax using hex
  have hS : ∀ y, simplexConj Ω y = trmSf Ω y (g y) := by
    intro y
    unfold simplexConj
    apply IsGreatest.csSup_eq
    exact ⟨⟨g y, hgS y, rfl⟩, by rintro _ ⟨a, ha, rfl⟩; exact hgmax y a ha⟩
  have hquad : ∀ y a, a ∈ stdSimplex ℝ Z →
      (m / 4) * ‖a - g y‖ ^ 2 ≤ trmSf Ω y (g y) - trmSf Ω y a :=
    fun y a ha => trm_sf_quad Ω m hΩ y a (g y) ha (hgS y) (hgmax y)
  -- bound on the pairing
  have hpair : ∀ u v : Z → ℝ, ∑ z, u z * v z ≤ Fintype.card Z * (‖u‖ * ‖v‖) := by
    intro u v
    calc ∑ z, u z * v z ≤ ∑ z : Z, ‖u‖ * ‖v‖ := Finset.sum_le_sum fun z _ => by
          have h1 := norm_le_pi_norm u z
          have h2 := norm_le_pi_norm v z
          rw [Real.norm_eq_abs] at h1 h2
          calc u z * v z ≤ |u z * v z| := le_abs_self _
            _ = |u z| * |v z| := abs_mul _ _
            _ ≤ ‖u‖ * ‖v‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp
  have hcard : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  -- Lipschitz
  have hLip : ∀ y₁ y₂, ‖g y₁ - g y₂‖ ≤ (2 * Fintype.card Z / m) * ‖y₁ - y₂‖ := by
    intro y₁ y₂
    have q1 := hquad y₁ (g y₂) (hgS y₂)
    have q2 := hquad y₂ (g y₁) (hgS y₁)
    have hsum : (m / 2) * ‖g y₁ - g y₂‖ ^ 2 ≤ ∑ z, (g y₁ - g y₂) z * (y₁ - y₂) z := by
      have e : ∑ z, (g y₁ - g y₂) z * (y₁ - y₂) z =
          (trmSf Ω y₁ (g y₁) - trmSf Ω y₁ (g y₂)) + (trmSf Ω y₂ (g y₂) - trmSf Ω y₂ (g y₁)) := by
        unfold trmSf
        simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
        ring
      rw [norm_sub_rev (g y₂) (g y₁)] at q1
      rw [e]
      linarith [q1, q2]
    have hb := hpair (g y₁ - g y₂) (y₁ - y₂)
    set d := ‖g y₁ - g y₂‖ with hd
    set D := ‖y₁ - y₂‖ with hD
    have hd0 : 0 ≤ d := norm_nonneg _
    have hD0 : 0 ≤ D := norm_nonneg _
    by_cases hd00 : d = 0
    · rw [hd00]; positivity
    · have hdp : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd00)
      have : (m / 2) * d ^ 2 ≤ Fintype.card Z * (d * D) := hsum.trans hb
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]
      nlinarith [this, hdp]
  have hLipW : LipschitzWith (Real.toNNReal (2 * Fintype.card Z / m)) g := by
    apply LipschitzWith.of_dist_le_mul
    intro y₁ y₂
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    exact hLip y₁ y₂
  refine ⟨⟨g, ⟨_, hLipW⟩, fun y => ⟨?_, hgS y, ?_⟩⟩, ?_, ?_⟩
  · -- differentiability
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hbound : ∀ h : Z → ℝ,
        ‖simplexConj Ω (y + h) - simplexConj Ω y -
          (∑ z, g y z • (ContinuousLinearMap.proj z : (Z → ℝ) →L[ℝ] ℝ)) h‖ ≤
          (Fintype.card Z * (2 * Fintype.card Z / m)) * ‖‖h‖ ^ 2‖ := by
      intro h
      have hL : (∑ z, g y z • (ContinuousLinearMap.proj z : (Z → ℝ) →L[ℝ] ℝ)) h =
          ∑ z, g y z * h z := by simp
      rw [hL]
      have low : simplexConj Ω y + ∑ z, g y z * h z ≤ simplexConj Ω (y + h) := by
        rw [hS (y + h), hS y]
        have := hgmax (y + h) (g y) (hgS y)
        unfold trmSf at *
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at this ⊢
        linarith
      have upp : simplexConj Ω (y + h) ≤ simplexConj Ω y + ∑ z, g (y + h) z * h z := by
        rw [hS (y + h), hS y]
        have := hgmax y (g (y + h)) (hgS (y + h))
        unfold trmSf at *
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at *
        linarith
      have hE : ∑ z, g (y + h) z * h z - ∑ z, g y z * h z =
          ∑ z, (g (y + h) - g y) z * h z := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun z _ => by simp only [Pi.sub_apply]; ring
      have hp := hpair (g (y + h) - g y) h
      have hl := hLip (y + h) y
      have hnn : 0 ≤ ‖h‖ := norm_nonneg _
      rw [add_sub_cancel_left] at hl
      have hfin : ∑ z, (g (y + h) - g y) z * h z ≤
          (Fintype.card Z * (2 * Fintype.card Z / m)) * ‖h‖ ^ 2 := by
        calc _ ≤ Fintype.card Z * (‖g (y + h) - g y‖ * ‖h‖) := hp
          _ ≤ Fintype.card Z * ((2 * Fintype.card Z / m) * ‖h‖ * ‖h‖) := by
              gcongr
          _ = _ := by ring
      rw [Real.norm_eq_abs, abs_le]
      have hsq : ‖‖h‖ ^ 2‖ = ‖h‖ ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hsq]
      constructor <;> nlinarith [low, upp, hE, hfin]
    have hO : (fun h : Z → ℝ => simplexConj Ω (y + h) - simplexConj Ω y -
        (∑ z, g y z • (ContinuousLinearMap.proj z : (Z → ℝ) →L[ℝ] ℝ)) h) =O[𝓝 0]
        (fun h : Z → ℝ => ‖h‖ ^ 2) :=
      Asymptotics.IsBigO.of_bound (Fintype.card Z * (2 * Fintype.card Z / m))
        (Eventually.of_forall hbound)
    exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (n := 2) (by norm_num))
  · intro a ha hne'
    have := hquad y a ha
    have hpos : 0 < ‖a - g y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne')
    unfold trmSf at this
    have : 0 < m / 4 * ‖a - g y‖ ^ 2 := by positivity
    linarith
  · intro c y
    have key : ∀ a ∈ stdSimplex ℝ Z, trmSf Ω (fun z => y z + c) a = trmSf Ω y a + c := by
      intro a ha
      unfold trmSf
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ha.2, one_mul]
      ring
    rw [hS (fun z => y z + c), hS y]
    have hgr : IsGreatest ((fun a : Z → ℝ => ∑ z, a z * (y z + c) - Ω a) '' stdSimplex ℝ Z)
        (trmSf Ω y (g y) + c) := by
      refine ⟨⟨g y, hgS y, ?_⟩, ?_⟩
      · exact (key (g y) (hgS y))
      · rintro _ ⟨a, ha, rfl⟩
        have := key a ha
        have h2 := hgmax y a ha
        unfold trmSf at *
        linarith
    -- the maximizer for y + c has the same value
    have := hgmax (fun z => y z + c) (g y) (hgS y)
    have h3 := (hgr.2 ⟨g (fun z => y z + c), hgS _, rfl⟩)
    have h4 := key (g y) (hgS y)
    have h5 : trmSf Ω (fun z => y z + c) (g fun z => y z + c) ≤ trmSf Ω y (g y) + c := h3
    linarith
  · intro y y' hy
    rw [hS y, hS y']
    have h1 : trmSf Ω y (g y) ≤ trmSf Ω y' (g y) := by
      unfold trmSf
      have : ∑ z, g y z * y z ≤ ∑ z, g y z * y' z :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hy z) ((hgS y).1 z)
      linarith
    exact h1.trans (hgmax y' (g y) (hgS y))
