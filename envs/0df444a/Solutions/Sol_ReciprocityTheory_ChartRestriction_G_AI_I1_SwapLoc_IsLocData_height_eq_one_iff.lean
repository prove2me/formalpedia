-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.height_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:55.343357+00:00
-- url     : https://prove2.me/submissions/1cc39863-bf23-4bae-b10a-82b9848eb628

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_le_of_comap_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_comap_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_le_comap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_map_eq_zero_iff

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
theorem _root_.solution [IsDomain A] [IsNoetherianRing A] [V.IsPrime]
    (h : IsLocData R A Z.primeCompl V) (hVZ : V ≤ Z)
    (hex : ∀ Q : Ideal R, Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Q)
    {f : R} (hfV : f ∉ V) (p : Ideal A) [hp : p.IsPrime] :
    (p.height = 1 ∧ algebraMap R A f ∈ p) ↔
      p.comap (algebraMap R A) ∈ (V ⊔ Ideal.span {f}).minimalPrimes := by
  have hf0 : algebraMap R A f ≠ 0 := fun e => hfV ((h.map_eq_zero_iff hVZ f).mp e)
  have hpb : ∀ q : Ideal A, q.IsPrime → algebraMap R A f ∈ q → 1 ≤ q.height := by
    intro q hq hfq
    haveI := hq
    rw [Order.one_le_iff_ne_zero]
    intro h0
    rw [Ideal.height_eq_zero_iff_eq_bot] at h0
    exact hf0 (by rw [← Ideal.mem_bot, ← h0]; exact hfq)
  have hsup : ∀ q : Ideal A, algebraMap R A f ∈ q →
      V ⊔ Ideal.span {f} ≤ q.comap (algebraMap R A) :=
    fun q hq => sup_le (h.le_comap q) (Ideal.span_le.mpr (by simpa using hq))
  constructor
  · rintro ⟨h1, hfp⟩
    refine ⟨⟨Ideal.comap_isPrime _ _, hsup p hfp⟩, fun Q ⟨hQ, hQle⟩ hQp => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hex Q hQ (le_sup_left.trans hQle) (hQp.trans (h.comap_le p))
    haveI := hq
    have hqp : q ≤ p := h.le_of_comap_le hQp
    have hfq : algebraMap R A f ∈ q :=
      hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    rcases hqp.lt_or_eq with hlt | heq
    · exfalso
      have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h2 := hpb q hq hfq
      rw [h1] at h3
      generalize q.height = a at h2 h3
      cases a with
      | top => simp at h3
      | coe a => norm_cast at h2 h3; omega
    · rw [heq]
  · intro hmin
    have hfp : algebraMap R A f ∈ p :=
      hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    refine ⟨le_antisymm ?_ (hpb p hp hfp), hfp⟩
    apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {algebraMap R A f})
    refine ⟨⟨hp, Ideal.span_le.mpr (by simpa using hfp)⟩, fun q ⟨hq, hqle⟩ hqp => ?_⟩
    haveI := hq
    have hfq : algebraMap R A f ∈ q := hqle (Ideal.mem_span_singleton_self _)
    have := hmin.2 ⟨Ideal.comap_isPrime _ _, hsup q hfq⟩ (Ideal.comap_mono hqp)
    exact h.le_of_comap_le this
end IsLocData
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
