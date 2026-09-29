-- Prove2me | solution 1 for RockafellarMaxMono.Cyclic.subdiff_add_halfSqNorm
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:59:31.027565+00:00
-- url     : https://prove2.me/submissions/520148e7-ae60-4225-a466-14d13e40c2e0

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Shared_HalfSqNorm
open Pointwise


namespace RockafellarMaxMono.Cyclic

section SumRule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sr_convexB (x : E) :
    Convex ℝ {p : E × ℝ | p.2 < ‖x‖ ^ 2 / 2 - ‖p.1‖ ^ 2 / 2} := by
  intro p hp q hq s t hs ht hst
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hp hq ⊢
  have hn : ‖s • p.1 + t • q.1‖ ≤ s * ‖p.1‖ + t * ‖q.1‖ := by
    calc ‖s • p.1 + t • q.1‖ ≤ ‖s • p.1‖ + ‖t • q.1‖ := norm_add_le _ _
      _ = s * ‖p.1‖ + t * ‖q.1‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have h0 : 0 ≤ ‖s • p.1 + t • q.1‖ := norm_nonneg _
  have hsq : ‖s • p.1 + t • q.1‖ ^ 2 ≤ (s * ‖p.1‖ + t * ‖q.1‖) ^ 2 := by
    exact pow_le_pow_left₀ h0 hn 2
  have hconvx : (s * ‖p.1‖ + t * ‖q.1‖) ^ 2 ≤ s * ‖p.1‖ ^ 2 + t * ‖q.1‖ ^ 2 := by
    have : t = 1 - s := by linarith
    subst this
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (‖p.1‖ - ‖q.1‖))]
  have := mul_le_mul_of_nonneg_left hp.le hs
  have := mul_le_mul_of_nonneg_left hq.le ht
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · subst hs0
    have : t = 1 := by linarith
    subst this
    simp only [zero_mul, zero_add, one_mul, zero_smul, one_smul] at *
    exact hq
  · have := mul_lt_mul_of_pos_left hp hs0
    nlinarith

theorem sumrule_core (f : E → EReal) (hf : Shared.ProperConvex f) :
    ∀ x : E, Shared.subdiff (fun y => f y + Shared.halfSqNorm y) x =
      Shared.subdiff f x + Shared.subdiff Shared.halfSqNorm x := by
  intro x
  apply Set.Subset.antisymm
  · intro xs hxs
    simp only [Shared.subdiff, Set.mem_setOf_eq, Shared.halfSqNorm] at hxs
    -- f x finite
    have hfx : f x ≠ ⊤ := by
      intro htop
      obtain ⟨y0, hy0⟩ := hf.2.1
      have := hxs y0
      rw [htop, EReal.top_add_coe, EReal.top_add_coe, top_le_iff] at this
      have h2 : f y0 + ((‖y0‖ ^ 2 / 2 : ℝ) : EReal) ≠ ⊤ := by
        lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c
        rw [← EReal.coe_add]; exact EReal.coe_ne_top _
      exact h2 this
    lift f x to ℝ using ⟨hfx, hf.1 x⟩ with a ha
    set J : E → ℝ := fun y => ‖y‖ ^ 2 / 2 with hJ
    have hreal : ∀ y (c : ℝ), f y = c → a + J x + xs (y - x) ≤ c + J y := by
      intro y c hc
      have := hxs y
      rw [hc, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
        at this
      exact this
    set A : Set (E × ℝ) := {p | ∃ c : ℝ, f p.1 = c ∧ c - a - xs (p.1 - x) ≤ p.2} with hA
    set B : Set (E × ℝ) := {p : E × ℝ | p.2 < ‖x‖ ^ 2 / 2 - ‖p.1‖ ^ 2 / 2} with hB
    have hBo : IsOpen B := isOpen_lt continuous_snd (continuous_const.sub
      (((continuous_norm.comp continuous_fst).pow 2).div_const 2))
    have hAc : Convex ℝ A := by
      rintro ⟨y1, r1⟩ ⟨c1, hc1, hr1⟩ ⟨y2, r2⟩ ⟨c2, hc2, hr2⟩ s t hs ht hst
      simp only at hc1 hr1 hc2 hr2
      rcases eq_or_lt_of_le ht with ht0 | ht0
      · subst ht0
        have : s = 1 := by linarith
        subst this
        exact ⟨c1, by simpa using hc1, by simpa using hr1⟩
      rcases eq_or_lt_of_le hs with hs0 | hs0
      · subst hs0
        have : t = 1 := by linarith
        subst this
        exact ⟨c2, by simpa using hc2, by simpa using hr2⟩
      have hts : s = 1 - t := by linarith
      subst hts
      have hcv := hf.2.2 y1 y2 t ht0 (by linarith)
      rw [hc1, hc2, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hcv
      have hne : f ((1 - t) • y1 + t • y2) ≠ ⊤ :=
        ne_top_of_le_ne_top (EReal.coe_ne_top _) hcv
      lift f ((1 - t) • y1 + t • y2) to ℝ using ⟨hne, hf.1 _⟩ with c hcdef
      rw [EReal.coe_le_coe_iff] at hcv
      refine ⟨c, ?_, ?_⟩
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; exact hcdef.symm
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, map_sub, map_add, map_smul]
        simp only [map_sub] at hr1 hr2
        nlinarith
    have hdisj : Disjoint B A := by
      rw [Set.disjoint_left]
      rintro ⟨y, r⟩ hb ⟨c, hc, hr⟩
      simp only [hB, Set.mem_setOf_eq] at hb hc hr
      have := hreal y c hc
      simp only [hJ] at this
      linarith
    obtain ⟨ℓ, u, hℓB, hℓA⟩ := geometric_hahn_banach_open (sr_convexB x) hBo hAc hdisj
    set φ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
    set β : ℝ := ℓ (0, 1) with hβ
    have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
      intro y r
      have : (y, r) = ((y, 0) : E × ℝ) + r • ((0, 1) : E × ℝ) := by simp
      rw [this, map_add, map_smul, smul_eq_mul]
      rfl
    have hxA : (x, (0:ℝ)) ∈ A := ⟨a, ha.symm, by simp⟩
    have hu1 : u ≤ φ x := by have := hℓA _ hxA; rwa [hℓ, zero_mul, add_zero] at this
    have hxB : ∀ r : ℝ, r < 0 → φ x + r * β < u := by
      intro r hr
      have := hℓB (x, r) (by simp [hB]; exact hr)
      rwa [hℓ] at this
    have hβpos : 0 < β := by
      have := hxB (-1) (by norm_num)
      linarith
    have hu2 : u = φ x := by
      by_contra hne
      have hlt : u < φ x := lt_of_le_of_ne hu1 hne
      have := hxB ((u - φ x) / β) (div_neg_of_neg_of_pos (by linarith) hβpos)
      rw [div_mul_cancel₀ _ hβpos.ne'] at this
      linarith
    set x2 : StrongDual ℝ E := β⁻¹ • φ with hx2
    refine ⟨xs - x2, ?_, x2, ?_, by simp⟩
    · simp only [Shared.subdiff, Set.mem_setOf_eq]
      intro y
      rcases eq_or_ne (f y) ⊤ with hy | hy
      · rw [hy]; exact le_top
      lift f y to ℝ using ⟨hy, hf.1 y⟩ with c hc
      rw [← ha, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hmem : (y, c - a - xs (y - x)) ∈ A := ⟨c, hc.symm, le_rfl⟩
      have := hℓA _ hmem
      rw [hℓ] at this
      simp only [hx2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        map_sub]
      simp only [map_sub] at this
      rw [hu2] at this
      have e : β⁻¹ * (φ y - φ x) * β = φ y - φ x := by field_simp
      nlinarith
    · simp only [Shared.subdiff, Set.mem_setOf_eq, Shared.halfSqNorm]
      intro y
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      simp only [hx2, ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub]
      have key : φ y + (‖x‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2) * β ≤ φ x := by
        by_contra hcon
        push_neg at hcon
        have := hℓB (y, (φ x - φ y) / β) (by
          simp only [hB, Set.mem_setOf_eq]
          rw [div_lt_iff₀ hβpos]; linarith)
        rw [hℓ, div_mul_cancel₀ _ hβpos.ne'] at this
        linarith
      rw [← sub_nonneg] at key ⊢
      have e : ‖y‖ ^ 2 / 2 - (‖x‖ ^ 2 / 2 + (β⁻¹ * φ y - β⁻¹ * φ x))
          = β⁻¹ * (φ x - (φ y + (‖x‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2) * β)) := by field_simp; ring
      rw [e]; exact mul_nonneg (inv_nonneg.2 hβpos.le) key
  · rintro _ ⟨x1, hx1, x2, hx2, rfl⟩
    simp only [Shared.subdiff, Set.mem_setOf_eq] at hx1 hx2 ⊢
    intro y
    rw [ContinuousLinearMap.add_apply, EReal.coe_add]
    calc f x + Shared.halfSqNorm x + (((x1 (y - x) : ℝ) : EReal) + ((x2 (y - x) : ℝ) : EReal))
        = (f x + ((x1 (y - x) : ℝ) : EReal)) + (Shared.halfSqNorm x + ((x2 (y - x) : ℝ) : EReal)) :=
          add_add_add_comm _ _ _ _
      _ ≤ f y + Shared.halfSqNorm y := add_le_add (hx1 y) (hx2 y)

end SumRule
end RockafellarMaxMono.Cyclic

open RockafellarMaxMono.Cyclic
open RockafellarMaxMono

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.subdiff (fun y => f y + Shared.halfSqNorm y) x = Shared.subdiff f x + Shared.subdiff Shared.halfSqNorm x := by
  exact sumrule_core f hf
