-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_locLen_cross_60ec489fea52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:30.410926+00:00
-- url     : https://prove2.me/submissions/7f9aa6a7-42be-4ddf-84a6-4bab926aa261

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_quot_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Inter.DiagPull
theorem _root_.solution {V : Ideal R} (hV : V.IsPrime) {f g u v : R} (hrel : f * v - g * u ∈ V)
    (p : PrimeSpectrum R) (hVp : V ≤ p.asIdeal) (hu : u ∉ p.asIdeal) (hv : v ∉ p.asIdeal) :
    locLen (R ⧸ (V ⊔ Ideal.span {f})) p = locLen (R ⧸ (V ⊔ Ideal.span {g})) p := by
  have e : V ⊔ Ideal.span {v * f} = V ⊔ Ideal.span {u * g} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e' : v * f = (f * v - g * u) + u * g := by ring
      rw [e']
      exact Ideal.add_mem _ (Ideal.mem_sup_left hrel)
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e' : u * g = v * f - (f * v - g * u) := by ring
      rw [e']
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_left hrel)
  have h1 := I1.locLen_mul hV (fun h => hv (hVp h)) f p
  have h2 := I1.locLen_mul hV (fun h => hu (hVp h)) g p
  rw [e, h2, I1.locLen_quot_eq_zero p hu, I1.locLen_quot_eq_zero p hv, add_zero, add_zero] at h1
  exact h1.symm
end GroundTheory.Heights₂.Heights.Inter.DiagPull
