-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.VGe.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:24:43.803216+00:00
-- url     : https://prove2.me/submissions/2a443646-7cd7-4ded-a400-d57d370d1d32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ConstBFMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}
namespace ReciprocityTheory.ChartRestriction.G.DVR
namespace VGe
theorem _root_.solution {k : ℕ} {α : D.toPre.X}
    {s s' s'' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {r : ℚ}
    (h : VGe D F v k α s r) (h' : VGe D F v k α s' r) (hadd : ∀ j, s''.f j = s.f j + s'.f j) :
    VGe D F v k α s'' r := by
  unfold VGe at h h' ⊢
  obtain ⟨n, a, σ, σF, hσ, ha, hs⟩ := h
  obtain ⟨m, b, τ, τF, hτ, hb, hs'⟩ := h'
  refine ⟨n + m, Fin.append a b, Fin.append σ τ, Fin.append σF τF, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact hσ i
    · simp only [Fin.append_right]
      exact hτ i
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact ha i
    · simp only [Fin.append_right]
      exact hb i
  · intro j
    rw [hadd j, hs j, hs' j, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
end VGe
end ReciprocityTheory.ChartRestriction.G.DVR
