-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.BE.avoid_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:30.649627+00:00
-- url     : https://prove2.me/submissions/35612762-f2bf-45f4-89b7-119ee8931c2d

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_IsHermSemilocalLocRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open ReciprocityTheory.ChartRestriction.L3.WA.BE
namespace ReciprocityTheory.ChartRestriction.L3.WA.BE
theorem _root_.solution {R : Type*} [CommRing R] {P Q : Ideal R} (hQ : Q.IsPrime) {a s m : R} (k : R)
    (ha : a ∈ P) (hsP : s ∉ P) (hsQ : s ∉ Q) (hm : m ∉ Q) :
    (s - k * a ∉ P ∧ s - k * a ∉ Q) ∨ (s - (k + m) * a ∉ P ∧ s - (k + m) * a ∉ Q) := by
  have hP : ∀ c : R, s - c * a ∉ P := by
    intro c h
    apply hsP
    have := P.add_mem h (P.mul_mem_left c ha)
    simpa using this
  by_cases h1 : s - k * a ∈ Q
  · right
    refine ⟨hP _, fun h2 => ?_⟩
    have h3 : m * a ∈ Q := by
      have := Q.sub_mem h1 h2
      have e : s - k * a - (s - (k + m) * a) = m * a := by ring
      rwa [e] at this
    rcases hQ.mem_or_mem h3 with h | h
    · exact hm h
    · apply hsQ
      have := Q.add_mem h1 (Q.mul_mem_left k h)
      simpa using this
  · exact Or.inl ⟨hP _, h1⟩
end ReciprocityTheory.ChartRestriction.L3.WA.BE
