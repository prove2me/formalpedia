-- Prove2me | solution 1 for PI.IsoDetW.Loc.rlen_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:39.914715+00:00
-- url     : https://prove2.me/submissions/ee551890-f57f-4ada-9e69-f108e7e10f2c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs
variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
namespace PI.IsoDetW.Loc
theorem _root_.solution {W' : Type*} [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')
    (hf : Function.Injective f) (X Z : Submodule R W) :
    relative₂ (X.map f) (Z.map f) = relative₂ X Z := by
  unfold relative₂
  symm
  refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Z) ?_)
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
end PI.IsoDetW.Loc
