-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.tens_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:44.435205+00:00
-- url     : https://prove2.me/submissions/6396aa36-587c-421e-ac97-411bf1976a73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_inclR_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_oev_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_oev_one
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
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (x : Fv F v ⊗[F] E) :
    (Algebra.TensorProduct.comm F E (Fv F v)).symm x ∈
        PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
          (v.adicCompletionIntegers F).toSubring ↔ x ∈ OEv (E := E) v := by
  constructor
  · intro h
    have hle : PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
        (v.adicCompletionIntegers F).toSubring ≤
        (oevSub v).comap (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom := by
      apply Subring.closure_le.2
      rintro y (⟨⟨a, ha⟩, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
      · obtain ⟨b, rfl⟩ := ha
        show Algebra.TensorProduct.comm F E (Fv F v) (((algebraMap (𝓞 E) E) b) ⊗ₜ[F] (1 : Fv F v)) ∈
          OEv (E := E) v
        simp only [Algebra.TensorProduct.comm_tmul]
        exact Sd.inclR_mem (F := F) v b
      · show Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] t) ∈ OEv (E := E) v
        have h1 : Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] t) = t • (1 : Fv F v ⊗[F] E) := by
          simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
        rw [h1]
        exact Sd.oev_smul v ht (oev_one v)
    have h2 := Subring.mem_comap.1 (hle h)
    have h3 : (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom
        ((Algebra.TensorProduct.comm F E (Fv F v)).symm x) = x := by simp
    rw [h3] at h2
    exact h2
  · intro hx
    change x ∈ Submodule.span _ _ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      apply Subring.subset_closure
      left
      exact ⟨⟨(a : E), ⟨a, rfl⟩⟩, by simp [inclR]⟩
    | zero => simpa using zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul t y _ hy =>
      have h1 : t • y = ((t : Fv F v) ⊗ₜ[F] (1 : E)) * y := by
        rw [show t • y = (t : Fv F v) • y from rfl, Algebra.smul_def]
        rfl
      rw [h1, map_mul]
      refine mul_mem ?_ hy
      apply Subring.subset_closure
      right
      exact ⟨⟨t, t.2⟩, by simp⟩
end PI.UnitaryGroupMassFormula.LocJacTyp
