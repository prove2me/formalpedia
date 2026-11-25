-- Prove2me | solution 1 for PI.VolStabW.TopoNuFin.eventually_int_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:08.784389+00:00
-- url     : https://prove2.me/submissions/403c08e7-8d6c-44d2-8c2c-efac378e3017

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoNuFin
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
open PI PI.VolStabW PI.VolStabW.TopoNuFin
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Filter Topology
  PI.VolFromSW PI.VolStabW.PositiveNearLattice
open scoped TensorProduct ENNReal
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabW.TopoNuFin
theorem _root_.solution {C : Set (Af F)} (hC : IsCompact C) :
    ∀ᶠ v in cofinite, ∀ x ∈ C, x v ∈ v.adicCompletionIntegers F := by
  let U : Finset (HeightOneSpectrum (𝓞 F)) → Set (Af F) :=
    fun S => {x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    RestrictedProduct.isOpen_forall_imp_mem (TopoAF.isOpen_integers F) (p := fun v => v ∉ S)
  have hcov : C ⊆ ⋃ S, U S := by
    intro x _
    have hx : {v | x v ∉ v.adicCompletionIntegers F}.Finite := x.eventually
    refine Set.mem_iUnion.2 ⟨hx.toFinset, fun v hv => ?_⟩
    by_contra h
    exact hv (hx.mem_toFinset.2 h)
  have hdir : Directed (· ⊆ ·) U := by
    refine Monotone.directed_le fun S S' hSS' x hx v hv => hx v fun h => hv (Finset.mem_of_subset hSS' h)
  obtain ⟨S, hS⟩ := hC.elim_directed_cover U hUo hcov hdir
  refine eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
  by_contra h
  exact hv fun x hx => hS hx v h
end PI.VolStabW.TopoNuFin
