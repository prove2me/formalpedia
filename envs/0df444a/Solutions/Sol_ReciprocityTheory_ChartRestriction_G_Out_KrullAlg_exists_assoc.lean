-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.exists_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:11.523218+00:00
-- url     : https://prove2.me/submissions/ae662203-0764-4303-9618-da7a0e7d7fe0

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]
namespace ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
theorem _root_.solution [IsNoetherianRing A] {ι : Type*} (x : ι → K)
    (hx : ∃ i, x i ∉ (algebraMap A K).range) :
    ∃ (d : A) (P : Ideal A), P.IsPrime ∧
      (∀ r, r ∈ P ↔ ∀ i, algebraMap A K r * (algebraMap A K d * x i) ∈ (algebraMap A K).range) ∧
      ∃ i, algebraMap A K d * x i ∉ (algebraMap A K).range := by
  classical
  have hne : (Ideal.Quotient.mk (denIdeal (A := A) x) 1) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    obtain ⟨i, hi⟩ := hx
    apply hi
    have := h i
    simpa using this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hne
  rw [isAssociatedPrime_iff] at hP
  obtain ⟨hPp, y, hy⟩ := hP
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
  have key : ∀ r, r ∈ P ↔ ∀ i, algebraMap A K r * (algebraMap A K d * x i) ∈ (algebraMap A K).range := by
    intro r
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    show (∀ i, algebraMap A K (r * d) * x i ∈ (algebraMap A K).range) ↔ _
    simp only [map_mul, mul_assoc]
  refine ⟨d, P, hPp, key, ?_⟩
  by_contra hcon
  push_neg at hcon
  apply hPp.ne_top
  rw [Ideal.eq_top_iff_one, key 1]
  intro i
  simpa using hcon i
end ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
