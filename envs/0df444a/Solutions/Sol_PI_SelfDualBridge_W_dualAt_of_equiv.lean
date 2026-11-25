-- Prove2me | solution 1 for PI.SelfDualBridge.W.dualAt_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:21:54.533013+00:00
-- url     : https://prove2.me/submissions/29f4fa75-5176-4baf-8fc5-ebb3da40c1a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_AdditiveCharacterNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualContinuity_ContinuousReTupSymm
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
open PI PI.SelfDualBridge PI.SelfDualBridge.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.SelfDualBridge.W
theorem _root_.solution {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [AddCommGroup V']
    [TopologicalSpace V'] (e : V ≃+ V') (he : Continuous e) (hes : Continuous e.symm)
    (B : V → V → Fv F v) (B' : V' → V' → Fv F v) (hB : ∀ x y, B x y = B' (e x) (e y))
    (h : DualAt v B') : DualAt v B := by
  unfold DualAt at h ⊢
  obtain ⟨L', hc, ho, hs, hK⟩ := h
  refine ⟨L'.comap e.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · have h1 : ((L'.comap e.toAddMonoidHom : AddSubgroup V) : Set V) = e.symm '' (L' : Set V') := by
      ext x
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [h1]
    exact hc.image hes
  · exact ho.preimage he
  · intro s hs' x hx
    obtain ⟨x'', hx'', hB''⟩ := hs s hs' (e x) hx
    refine ⟨e.symm x'', ?_, fun y => ?_⟩
    · show e.toAddMonoidHom (e.symm x'') ∈ L'
      simpa using hx''
    · rw [hB, hB, e.apply_symm_apply, hB'']
  · intro c
    obtain ⟨K', hK'c, hK'⟩ := hK c
    refine ⟨e.symm '' K', hK'c.image hes, fun y hy => ?_⟩
    refine ⟨e y, hK' ?_, e.symm_apply_apply y⟩
    intro x'' hx''
    have h1 := hy (e.symm x'') (by show e.toAddMonoidHom (e.symm x'') ∈ L'; simpa using hx'')
    rwa [hB, e.apply_symm_apply] at h1
end PI.SelfDualBridge.W
