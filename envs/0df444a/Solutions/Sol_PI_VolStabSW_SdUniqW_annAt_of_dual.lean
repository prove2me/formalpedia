-- Prove2me | solution 1 for PI.VolStabSW.SdUniqW.annAt_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:51.461279+00:00
-- url     : https://prove2.me/submissions/0b4c4d39-94f6-46ea-b5c7-168dec9c8dc7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Theorems.Thm_PI_VolStabSW_SdUniqW_mem_of_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.SdUniqW
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v)
    (ψ0 : Fv F v → ℂ) (hψ : Continuous ψ0) (hB : ∀ x, Continuous (B x)) (r0 : Fv F v)
    (h0 : ψ0 r0 ≠ 1) (hD : DualAt v B) : AnnAt (fun x y => ψ0 (B x y)) := by
  obtain ⟨L, hLc, hLo, hstab, hbd⟩ := hD
  refine ⟨L, hLc, hLo, ?_, ?_⟩
  · have e : ann (fun x y => ψ0 (B x y)) (L : Set V) = ⋂ x ∈ (L : Set V), {y | ψ0 (B x y) = 1} := by
      ext y
      simp [ann]
    rw [e]
    exact isClosed_biInter fun x _ => isClosed_eq (hψ.comp (hB x)) continuous_const
  · obtain ⟨K, hK, hsub⟩ := hbd r0
    refine ⟨K, hK, fun y hy => hsub ?_⟩
    intro x hx
    apply mem_of_psi v ψ0 r0 (B x y) h0
    intro s hs
    obtain ⟨x', hx', hB'⟩ := hstab s hs x hx
    rw [← hB' y]
    exact hy x' hx'
end PI.VolStabSW.SdUniqW
