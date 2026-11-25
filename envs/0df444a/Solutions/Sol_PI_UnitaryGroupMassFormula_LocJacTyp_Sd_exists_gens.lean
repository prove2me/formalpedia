-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:51.553464+00:00
-- url     : https://prove2.me/submissions/08b29087-00bb-46a4-b5f8-2d77518be368

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_inclR_mem
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
theorem _root_.solution : ∃ (m : ℕ) (w : Fin m → Fv F v ⊗[F] E), (∀ k, w k ∈ OEv (E := E) v) ∧
    ∀ x ∈ OEv (E := E) v, ∃ c : Fin m → Fv F v, (∀ k, c k ∈ v.adicCompletionIntegers F) ∧
      x = ∑ k, c k • w k := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  set w : Fin m → Fv F v ⊗[F] E := fun k => inclR (F := F) (Fv F v) ((s k : 𝓞 E) : E) with hw
  refine ⟨m, w, fun k => inclR_mem v _, fun x hx => ?_⟩
  have hle : Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) ≤
      Submodule.span (v.adicCompletionIntegers F) (Set.range w) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    have ha : a ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      have e : inclR (F := F) (Fv F v) (((a + b : 𝓞 E)) : E) =
          inclR (F := F) (Fv F v) (a : E) + inclR (F := F) (Fv F v) (b : E) := by
        simp [map_add]
      show inclR (F := F) (Fv F v) (((a + b : 𝓞 E)) : E) ∈ _
      rw [e]
      exact Submodule.add_mem _ ha hb
    | smul z a _ ha =>
      have e : inclR (F := F) (Fv F v) (((z • a : 𝓞 E)) : E) =
          ((z : v.adicCompletionIntegers F)) • inclR (F := F) (Fv F v) (a : E) := by
        rw [Int.cast_smul_eq_zsmul]
        simp
      show inclR (F := F) (Fv F v) (((z • a : 𝓞 E)) : E) ∈ _
      rw [e]
      exact Submodule.smul_mem _ _ ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hle hx)
  exact ⟨fun k => (c k : Fv F v), fun k => (c k).2, hc.symm⟩
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
