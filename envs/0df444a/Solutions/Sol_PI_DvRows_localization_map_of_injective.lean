-- Prove2me | solution 1 for PI.DvRows.localization_map_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:17.696205+00:00
-- url     : https://prove2.me/submissions/dd4c63dc-6f58-4fd7-95df-c83e4cbb9320

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_P2M_PI_DvRows_mem_locP__7b0c6c9a7105
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
theorem _root_.solution (p : Ideal R) [p.IsPrime] (f : W →ₗ[R] W') (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f)
    (A : Submodule R W) : localization₂ p (A.map f) = (localization₂ p A).map f := by
  ext y
  simp only [mem_locP', Submodule.mem_map]
  constructor
  · rintro ⟨s, hs, a, ha, hay⟩
    obtain ⟨x, rfl⟩ := hsat s y hs ⟨a, hay⟩
    refine ⟨x, ⟨s, hs, ?_⟩, rfl⟩
    have : f (s • x) = f a := by rw [map_smul, hay]
    rw [hf this]; exact ha
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    exact ⟨s, hs, s • x, hx, by rw [map_smul]⟩
end PI.DvRows
