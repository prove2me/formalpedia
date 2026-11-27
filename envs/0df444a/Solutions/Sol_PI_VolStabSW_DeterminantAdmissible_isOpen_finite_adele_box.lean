-- Prove2me | solution 1 for PI.VolStabSW.DeterminantAdmissible.isOpen_finite_adele_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:17:27.866698+00:00
-- url     : https://prove2.me/submissions/6b244496-4839-4a25-a9fc-2ff6e56d6cee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_isOpen_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabSW.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabSW.DeterminantAdmissible
theorem _root_.solution {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (ho : ∀ v, IsOpen (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsOpen {x : Af F | ∀ v, x v ∈ D v} := by
  classical
  have hfin : {v | ¬ D v = (v.adicCompletionIntegers F : Set (Fv F v))}.Finite := hf
  set S := hfin.toFinset
  have e : {x : Af F | ∀ v, x v ∈ D v} =
      {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} ∩
        ⋂ v ∈ S, {x : Af F | x v ∈ D v} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro h
      refine ⟨fun v hv => ?_, fun v _ => h v⟩
      have hv' : D v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
        by_contra hc
        exact hv (hfin.mem_toFinset.2 hc)
      have := h v
      rwa [hv'] at this
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ S
      · exact h2 v hv
      · have hv' : D v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
          by_contra hc
          exact hv (hfin.mem_toFinset.2 hc)
        rw [hv']
        exact h1 v hv
  rw [e]
  refine IsOpen.inter ?_ (isOpen_biInter_finset fun v _ =>
    (ho v).preimage (RestrictedProduct.continuous_eval v))
  exact RestrictedProduct.isOpen_forall_imp_mem (TopoAF.isOpen_integers F) (p := fun v => v ∉ S)
end PI.VolStabSW.DeterminantAdmissible
