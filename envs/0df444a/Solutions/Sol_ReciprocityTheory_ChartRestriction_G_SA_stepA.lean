-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.stepA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:46.052564+00:00
-- url     : https://prove2.me/submissions/c8dcb1b6-fb29-49da-9177-c25b05ccc132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_exists_max_of_not_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {K : Type*} [CommRing K] {σ : K →+* K}
    (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
    (h2 : IsUnit (2 : K)) {α β ω ν c : K} (hν : IsUnit ν) (hdef : ν = α * σ β + σ α * β + ω)
    (hnc : ¬ IsCoprime α β) :
    IsCoprime (α - ω + c * β) β ∨ IsCoprime (α + ω + c * β) β := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h1'⟩ := hcon
  obtain ⟨m0, hm0, ha0, hb0⟩ := exists_max_of_not_coprime hnc
  obtain ⟨m1, hm1, ha1, hb1⟩ := exists_max_of_not_coprime h1
  obtain ⟨m2, hm2, ha2, hb2⟩ := exists_max_of_not_coprime h1'
  have key : ∀ m : Ideal K, m.IsMaximal → α ∈ m → β ∈ m → ω ∈ m → False := by
    intro m hm ha hb hw
    have hν' : ν ∈ m := by
      rw [hdef]
      exact m.add_mem (m.add_mem (m.mul_mem_right _ ha) (m.mul_mem_left _ hb)) hw
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hν' hν)
  have hA1 : α - ω ∈ m1 := by
    have := m1.sub_mem ha1 (m1.mul_mem_left c hb1)
    simpa using this
  have hA2 : α + ω ∈ m2 := by
    have := m2.sub_mem ha2 (m2.mul_mem_left c hb2)
    simpa using this
  rcases hmax m0 m1 m2 hm0 hm1 hm2 with h | h | h
  · subst h
    have := m0.sub_mem ha0 hA1
    exact key m0 hm0 ha0 hb0 (by simpa using this)
  · subst h
    have := m0.sub_mem hA2 ha0
    exact key m0 hm0 ha0 hb0 (by simpa using this)
  · subst h
    have h2a : 2 * α ∈ m1 := by
      have := m1.add_mem hA1 hA2
      convert this using 1
      ring
    obtain ⟨u, hu⟩ := h2
    have hα : α ∈ m1 := by
      have := m1.mul_mem_left (↑u⁻¹ : K) h2a
      rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
    have := m1.sub_mem hA2 hα
    exact key m1 hm1 hα hb1 (by simpa using this)
end ReciprocityTheory.ChartRestriction.G.SA
