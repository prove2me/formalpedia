-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.exists_SD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:05.938475+00:00
-- url     : https://prove2.me/submissions/035db1f6-e518-4a76-9d3c-1f22aff53906

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_decomp
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_ext
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sigR_eq_congr
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sigR_smul
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
variable {σ v}
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (hS : SplitHyp σ v) : Nonempty (SD σ v) := by
  obtain ⟨hfin, hσ, e, hee, he0, he1⟩ := hS
  have hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hfin
  have he : IsIdempotentElem e := hee
  let P := PI.LocDualGen.EpS.pr hr e he he0 he1
  have dec := PI.LocDualGen.EpS.decomp hr e he he0 he1
  have pair := PI.LocDualGen.EpS.repr_pair hr e he he0 he1
  obtain ⟨τ, hτ⟩ := sigR_eq_congr (σ := σ) (v := v) hfin
  have hinj : Function.Injective (sigR (Fv F v) σ) := by
    intro z w h
    rw [hτ, hτ] at h
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : Fv F v ≃ₐ[F] Fv F v) τ).injective h
  set f := sigR (Fv F v) σ e with hfdef
  have hfi : f * f = f := by rw [hfdef, ← map_mul, hee]
  have h01 : ∀ i, P i f = 0 ∨ P i f = 1 := by
    intro i
    have : P i f * P i f = P i f := by rw [← map_mul, hfi]
    have h2 : P i f * (P i f - 1) = 0 := by rw [mul_sub, this, mul_one, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hfdec : f = P 0 f • e + P 1 f • (1 - e) := dec f
  refine ⟨⟨e, he, he0, he1, hr, ?_⟩⟩
  rcases h01 0 with a0 | a1 <;> rcases h01 1 with b0 | b1
  · exfalso
    apply he0
    apply hinj
    rw [map_zero, ← hfdef, hfdec, a0, b0]; simp
  · rw [← hfdef, hfdec, a0, b1]; simp
  · exfalso
    apply hσ
    have hfe : f = e := by rw [hfdec, a1, b0]; simp
    have hfix : ∀ z, sigR (Fv F v) σ z = z := by
      intro z
      conv_lhs => rw [dec z]
      rw [(sigR (Fv F v) σ).map_add, sigR_smul, sigR_smul, (sigR (Fv F v) σ).map_sub,
        (sigR (Fv F v) σ).map_one, ← hfdef, hfe, ← dec z]
    ext x
    have h1 := hfix ((1 : Fv F v) ⊗ₜ[F] x)
    have h2 : sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] x) = (1 : Fv F v) ⊗ₜ[F] (σ x) := by
      simp [sigR]
    rw [h2] at h1
    exact Algebra.TensorProduct.includeRight_injective (algebraMap F (Fv F v)).injective h1
  · exfalso
    apply he1
    apply hinj
    rw [map_one, ← hfdef, hfdec, a1, b1]; simp
end PI.UnitaryGroupMassFormula.LocJacTyp
