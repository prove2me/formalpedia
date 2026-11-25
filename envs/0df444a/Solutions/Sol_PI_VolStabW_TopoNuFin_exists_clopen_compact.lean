-- Prove2me | solution 1 for PI.VolStabW.TopoNuFin.exists_clopen_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:29.302865+00:00
-- url     : https://prove2.me/submissions/4c93a759-5176-4a00-b005-3a27372952fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoNuFin
import Theorems.Thm_PI_VolStabW_TopoNuFin_zero_mem_latV
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isCompact_latV


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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
include b
namespace PI.VolStabW.TopoNuFin
theorem _root_.solution {a M : ℕ} {K : Set (Fin a → Fin M → Fv F v ⊗[F] E)}
    (hK : IsCompact K) : ∃ C, IsClopen C ∧ IsCompact C ∧ K ⊆ C := by
  classical
  let L := latV (M := M) (n := a) b v
  have hLo := isClopen_latV b v a M
  have hLc := isCompact_latV b v a M
  let tr : (Fin a → Fin M → Fv F v ⊗[F] E) → Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun y => (Homeomorph.subRight y) ⁻¹' L
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => tr (y : Fin a → Fin M → Fv F v ⊗[F] E))
    (fun y => hLo.isOpen.preimage (Homeomorph.subRight _).continuous)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, by
      show z - z ∈ L
      rw [sub_self]
      exact zero_mem_latV b v a M⟩)
  refine ⟨⋃ y ∈ t, tr (y : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_, ht⟩
  · exact isClopen_biUnion_finset fun y _ => hLo.preimage (Homeomorph.subRight _).continuous
  · exact t.isCompact_biUnion fun y _ => (Homeomorph.subRight _).isCompact_preimage.2 hLc
end PI.VolStabW.TopoNuFin
