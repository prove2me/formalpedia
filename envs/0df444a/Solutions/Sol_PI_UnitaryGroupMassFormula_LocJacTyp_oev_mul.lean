-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.oev_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:11.121332+00:00
-- url     : https://prove2.me/submissions/eeda6085-e4cd-488d-94eb-e44a8b03df0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
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
theorem _root_.solution {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  unfold OEv at hx hy ⊢
  rw [SetLike.mem_coe] at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a', -, rfl⟩ := ha
      obtain ⟨b', -, rfl⟩ := hb
      apply Submodule.subset_span
      refine ⟨a' * b', Set.mem_univ _, ?_⟩
      first
        | exact map_mul _ _ _
        | simp
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      first
        | rw [mul_smul_comm]
        | rw [← algebraMap_smul (Fv F v) c y, mul_smul_comm, algebraMap_smul]
      exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x z _ _ hx hz =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    first
      | rw [smul_mul_assoc]
      | rw [← algebraMap_smul (Fv F v) c x, smul_mul_assoc, algebraMap_smul]
    exact Submodule.smul_mem _ c hx
end PI.UnitaryGroupMassFormula.LocJacTyp
