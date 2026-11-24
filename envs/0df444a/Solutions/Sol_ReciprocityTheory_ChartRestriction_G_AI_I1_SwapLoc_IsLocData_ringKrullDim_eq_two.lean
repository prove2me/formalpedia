-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.ringKrullDim_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:23.348791+00:00
-- url     : https://prove2.me/submissions/72fe429d-b377-48b9-b26f-da637c0d0539

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_map_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_comap_maximalIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_maximalIdeal_mem_minimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI
variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {S : Submonoid R}
  {V Z : Ideal R} [Z.IsPrime]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
namespace IsLocData
theorem _root_.solution [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [V.IsPrime] (h : IsLocData R A Z.primeCompl V) (hVZ : V ≤ Z)
    (hex : ∀ Q : Ideal R, Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Q)
    {f t : R} (hfV : f ∉ V) (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)
    (hft : ∀ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes, W ≤ Z → t ∉ W) : ringKrullDim A = 2 := by
  classical
  have hZex := hex Z ‹_› hVZ le_rfl
  have hm := h.maximalIdeal_mem_minimalPrimes hZex hZ
  have hc := h.comap_maximalIdeal hZex
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have hle : (IsLocalRing.maximalIdeal A).height ≤ 2 := by
    have := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (s := {algebraMap R A f, algebraMap R A t}) (by simpa using hm)
    exact this.trans (by exact_mod_cast Finset.card_le_two)
  have hfZ : V ⊔ Ideal.span {f} ≤ Z := le_sup_left.trans hZ.1.2
  obtain ⟨W, hW, hWZ⟩ := Ideal.exists_minimalPrimes_le hfZ
  obtain ⟨p, hp, hpW⟩ := hex W hW.1.1 (le_sup_left.trans hW.1.2) hWZ
  haveI := hp
  have hf0 : algebraMap R A f ≠ 0 := fun e => hfV ((h.map_eq_zero_iff hVZ f).mp e)
  have hfp : algebraMap R A f ∈ p := by
    show f ∈ p.comap (algebraMap R A)
    rw [hpW]; exact hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have htp : algebraMap R A t ∉ p := by
    show t ∉ p.comap (algebraMap R A)
    rw [hpW]; exact hft W hW hWZ
  have htm : algebraMap R A t ∈ IsLocalRing.maximalIdeal A := by
    show t ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap R A)
    rw [hc]; exact hZ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  have hbot : (⊥ : Ideal A) < p :=
    bot_lt_iff_ne_bot.mpr fun e => hf0 (by rw [← Ideal.mem_bot, ← e]; exact hfp)
  have hpm : p < IsLocalRing.maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) fun e => htp (e ▸ htm)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hpm
  rw [Ideal.height_bot] at h1
  have h3 : (IsLocalRing.maximalIdeal A).height = 2 := by
    generalize (IsLocalRing.maximalIdeal A).height = b at h2 hle ⊢
    generalize p.height = a at h1 h2
    cases b with
    | top => simp at hle
    | coe b =>
      cases a with
      | top => simp at h2
      | coe a => norm_cast at h1 h2 hle ⊢; omega
  rw [h3]
  rfl
end IsLocData
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
