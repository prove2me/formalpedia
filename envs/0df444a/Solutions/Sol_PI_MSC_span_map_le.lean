-- Prove2me | solution 1 for PI.MSC.span_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:43.147021+00:00
-- url     : https://prove2.me/submissions/3d9c6ad1-b130-4073-84e8-b88ecf12f9fa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinorSpanCompl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_RenameInitMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC
namespace PI.MSC
theorem _root_.solution {σ : Type*} (R : Type) [CommRing R] {A B : Set (MvPolynomial σ ℤ)}
    (h : A ⊆ Submodule.span ℤ B) :
    Submodule.span R (MvPolynomial.map (Int.castRingHom R) '' A) ≤
      Submodule.span R (MvPolynomial.map (Int.castRingHom R) '' B) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have := h ha
  clear ha
  induction this using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul z x _ hx =>
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul R]
    exact Submodule.smul_mem _ _ hx
end PI.MSC
