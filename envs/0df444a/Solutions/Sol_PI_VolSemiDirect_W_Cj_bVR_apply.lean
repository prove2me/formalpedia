-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.bVR_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:29.487637+00:00
-- url     : https://prove2.me/submissions/73bb2e9c-6d88-4b98-8713-e8c1bc77203a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_BVRApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct Matrix
variable (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (M : ℕ)
  (A : Type) [CommRing A] [Algebra F A]
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (i : Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) :
    bVR F E M A i = ratV (F := F) A (bV F E M i) := by
  rw [bVR, bV, Module.Basis.reindex_apply, Module.Basis.reindex_apply]
  generalize (Fintype.equivFin (Σ _ : Fin M, Fin (Module.finrank F E))).symm i = p
  obtain ⟨a, c⟩ := p
  funext j
  simp only [Pi.basis_apply, Algebra.TensorProduct.basis_apply, Formalism.L2.SG.Sub.ratV]
  by_cases hj : j = a
  · subst hj
    simp only [Pi.single_eq_same]
    first | rfl | simp
  · simp only [Pi.single_eq_of_ne hj]
    first | rfl | simp
end PI.VolSemiDirect.W.Cj
