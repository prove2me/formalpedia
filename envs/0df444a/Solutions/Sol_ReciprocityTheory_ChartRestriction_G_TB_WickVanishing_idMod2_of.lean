-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.idMod2_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:38.557381+00:00
-- url     : https://prove2.me/submissions/3073087e-4372-4cda-99e9-9cae1330343d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {d : ℕ} (ℓ : Pt k 1 d) (h0 : ∀ i, constantCoeff (ℓ i) = 0) (h1 : dLin ℓ = 1) :
    Formalism.FG.IsIdMod2 (fun p : Fin 1 × Fin d => ℓ p.2) := by
  refine ⟨fun p => h0 p.2, fun j i => ?_⟩
  obtain ⟨j1, j2⟩ := j
  obtain ⟨i1, i2⟩ := i
  have hj : j1 = 0 := Subsingleton.elim _ _
  have hi : i1 = 0 := Subsingleton.elim _ _
  subst hj hi
  have := congrFun (congrFun h1 j2) i2
  simp only [dLin, Matrix.one_apply] at this
  simp only [this, Prod.mk.injEq, true_and]
  by_cases h : i2 = j2
  · simp [h]
  · simp [h, Ne.symm h]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
