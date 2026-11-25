-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.oev_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:43.363604+00:00
-- url     : https://prove2.me/submissions/118f79ff-bfb3-41fe-aa8f-6258e65b3781

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sigR_smul
import Theorems.Thm_PI_VolStabSW_HasDens_add
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
private theorem sigR_smulO_lemma (σ : E →ₐ[F] E) (c : v.adicCompletionIntegers F)
    (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  first
    | rw [← algebraMap_smul (Fv F v) c x, sigR_smul, algebraMap_smul]
    | (induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [sigR, TensorProduct.smul_tmul']
        | add y z hy hz => simp only [smul_add, map_add, hy, hz])
end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (σ : E →ₐ[F] E) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  unfold OEv at hx ⊢
  rw [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a', -, rfl⟩ := ha
    apply Submodule.subset_span
    first
      | exact ⟨NumberField.RingOfIntegers.mapRingHom (σ : E →+* E) a', Set.mem_univ _,
          by simp [sigR, inclR]⟩
      | exact ⟨⟨σ a', (a'.isIntegral_coe.map (σ : E →+* E).toIntAlgHom)⟩, Set.mem_univ _,
          by simp [sigR, inclR]⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [sigR_smulO_lemma]
    exact Submodule.smul_mem _ c hx
end PI.UnitaryGroupMassFormula.LocJacTyp
