-- Prove2me | solution 1 for PI.DvRows.length_map_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:10.271798+00:00
-- url     : https://prove2.me/submissions/935c7a97-92d3-4bf7-ba3f-ad8f9340acc6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {R : Type*} [CommRing R] {W W' : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']
namespace PI.DvRows
theorem _root_.solution (f : W →ₗ[R] W') (hf : Function.Injective f) (X Z : Submodule R W) :
    Module.length R (↥(Z.map f) ⧸ (X.map f).comap (Z.map f).subtype) =
      Module.length R (↥Z ⧸ X.comap Z.subtype) := by
  symm
  refine LinearEquiv.length_eq
    (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Z) ?_)
  ext ⟨w, hw⟩
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨z', hz'⟩, hz'X, he⟩
    have : f z' = f z := congrArg Subtype.val he
    rw [← hf this]
    exact ⟨z', hz'X, rfl⟩
  · rintro ⟨z', hz'X, he⟩
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · have := hf he
      simpa [this] using hz'X
    · rfl
end PI.DvRows
