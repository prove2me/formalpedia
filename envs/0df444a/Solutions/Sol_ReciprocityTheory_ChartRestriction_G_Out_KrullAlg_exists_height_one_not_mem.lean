-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.exists_height_one_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:01.321951+00:00
-- url     : https://prove2.me/submissions/e526ee91-cef1-488f-9b1d-3a285833bb4d

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_KrullAlg_exists_clear

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
theorem _root_.solution [IsNoetherianRing A] [IsIntegrallyClosed A] (x : K)
    (hx : x ∉ (algebraMap A K).range) :
    ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧
      ∀ s ∉ P, algebraMap A K s * x ∉ (algebraMap A K).range := by
  obtain ⟨P, hP, h1, b, hbP, -, ⟨i, u, huP, hu⟩⟩ :=
    exists_clear (A := A) (ι := Unit) (fun _ => x) ⟨(), hx⟩
  have hu' : algebraMap A K u = algebraMap A K b * x := hu
  refine ⟨P, hP, h1, fun s hs hsx => ?_⟩
  obtain ⟨a, ha⟩ := hsx
  have e : algebraMap A K (s * u) = algebraMap A K (b * a) := by
    rw [map_mul, map_mul, hu', ha]
    ring
  have e2 : s * u = b * a := IsFractionRing.injective A K e
  have h3 : s * u ∈ P := e2 ▸ P.mul_mem_right a hbP
  rcases hP.mem_or_mem h3 with h4 | h4
  · exact hs h4
  · exact huP h4
end ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
