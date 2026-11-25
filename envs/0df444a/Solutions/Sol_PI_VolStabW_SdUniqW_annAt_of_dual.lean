-- Prove2me | solution 1 for PI.VolStabW.SdUniqW.annAt_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:03.044782+00:00
-- url     : https://prove2.me/submissions/eaf1b679-a2bf-4155-ac53-b0c40e7b30ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Theorems.Thm_PI_VolStabW_SdUniqW_mem_of_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.SdUniqW
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v)
    (ψ0 : Fv F v → ℂ) (hψ : Continuous ψ0) (hB : ∀ x, Continuous (B x)) (r0 : Fv F v)
    (h0 : ψ0 r0 ≠ 1) (hD : DualAt v B) : AnnAt (fun x y => ψ0 (B x y)) := by
  obtain ⟨L, hLc, hLo, hst, hK⟩ := hD
  obtain ⟨K, hKc, hKsub⟩ := hK r0
  refine ⟨L, hLc, hLo, ?_, K, hKc, ?_⟩
  · have hset : ann (fun x y => ψ0 (B x y)) (L : Set V) =
        ⋂ x ∈ (L : Set V), (fun y => ψ0 (B x y)) ⁻¹' {1} := by
      ext y
      simp [ann]
    rw [hset]
    exact isClosed_biInter fun x _ => isClosed_singleton.preimage (hψ.comp (hB x))
  · intro y hy
    refine hKsub (fun x hx => ?_)
    apply mem_of_psi v ψ0 r0 (B x y) h0
    intro s hs
    obtain ⟨x', hx', hB'⟩ := hst s hs x hx
    rw [← hB' y]
    exact hy x' hx'
end PI.VolStabW.SdUniqW
