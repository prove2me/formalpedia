-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multAt_eq_locLen_edc0f73897e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:06.882279+00:00
-- url     : https://prove2.me/submissions/2ef63c8f-4cf5-4d37-8644-a1ac5d57ca74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull

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
variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
  (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)
omit [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagPull
theorem _root_.solution (J W : Ideal (MRing (T.wwIdx ι ν κ))) (hW : W.IsPrime) :
    multAt J W = (locLen (MRing (T.wwIdx ι ν κ) ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, locLen]
end GroundTheory.Heights₂.Heights.Inter.DiagPull
