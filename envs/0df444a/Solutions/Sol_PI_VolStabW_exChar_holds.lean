-- Prove2me | solution 1 for PI.VolStabW.exChar_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:02:57.038718+00:00
-- url     : https://prove2.me/submissions/cf761973-8d04-49f5-8355-8e3f57b4bcf9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExChar

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution : ExChar := by
  intro F E _ _ _ _ _ σ hE M J _hJ _ha hc a _ha1 ha2 _X0 _hT _hdet
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have h0 : 2 * 0 < M := by omega
  have hrd : RapidDecay b (fun _ : Fin 0 → Fin M → Ainf F ⊗[F] E => (1 : ℂ)) :=
    fun N => ⟨1, fun X => by simp [sizeTup]⟩
  have hpf : IsPureFin b (fun _ : Fin 0 → Fin M → Af F ⊗[F] E => (1 : ℂ))
      (fun v (_ : Fin 0 → Fin M → Fv F v ⊗[F] E) => (1 : ℂ)) := by
    refine ⟨fun v => ⟨IsLocallyConstant.const 1, ?_⟩, Filter.Eventually.of_forall fun v => ?_,
      fun X => by simp⟩
    · exact (Set.subsingleton_of_subsingleton).isCompact
    · funext X
      simp [latV, Set.indicator]
  have hS := hc 0 h0 (0 : Matrix (Fin 0) (Fin 0) E) (fun i => Fin.elim0 i) (by simp)
    (Module.finrank F E) b (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
    continuous_const hrd hpf (fun _ => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  exact ((hS.2 μ hμ).2 𝓕 h𝓕).1
end PI.VolStabW
