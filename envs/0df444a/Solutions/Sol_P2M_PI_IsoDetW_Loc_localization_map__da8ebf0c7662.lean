-- Prove2me | solution 1 for P2M_PI_IsoDetW_Loc_localization_map__da8ebf0c7662
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:49.130102+00:00
-- url     : https://prove2.me/submissions/ccb23b88-7b21-4ddf-af1a-25b827d27fc4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Theorems.Thm_PI_IsoDetW_Loc_mem_locP

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
variable (p : Ideal R) [p.IsPrime]
namespace PI.IsoDetW.Loc
theorem _root_.solution {W' : Type*} [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')
    (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A : Submodule R W) : localization₂ p (A.map f) = (localization₂ p A).map f := by
  ext y
  simp only [mem_locP, Submodule.mem_map]
  constructor
  · rintro ⟨s, hs, a, ha, hay⟩
    obtain ⟨x, rfl⟩ := hsat s y hs ⟨a, hay⟩
    refine ⟨x, ⟨s, hs, ?_⟩, rfl⟩
    have : f (s • x) = f a := by rw [map_smul, hay]
    rw [hf this]; exact ha
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    exact ⟨s, hs, s • x, hx, by rw [map_smul]⟩
end PI.IsoDetW.Loc
