-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.stdLat_isOrtho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:55:32.333502+00:00
-- url     : https://prove2.me/submissions/b3ea4b19-598c-4ca8-88a6-a35ce4d5cbed

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_stdForm_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
namespace ReciprocityTheory.ChartRestriction.L3
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (stdForm K n) (stdLat K n) n := by
  refine ⟨fun i => Pi.single i 1, ?_, ?_, rfl, ?_⟩
  · have := (Pi.basisFun K (Fin n)).linearIndependent
    rwa [show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from
      funext fun i => Pi.basisFun_apply K (Fin n) i] at this
  · have := (Pi.basisFun K (Fin n)).span_eq
    rwa [show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from
      funext fun i => Pi.basisFun_apply K (Fin n) i] at this
  · intro i j
    rw [stdForm_apply]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
end ReciprocityTheory.ChartRestriction.L3
