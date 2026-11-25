-- Prove2me | solution 1 for PI.VolStabW.densInf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:03.016078+00:00
-- url     : https://prove2.me/submissions/3e086e68-4793-4eef-a1bf-a74c3d7910ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfSt
import Theorems.Thm_PI_VolStabW_densAll_transport
import Theorems.Thm_PI_VolStabW_densAll_mono

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hSub : SubmDens) (hCo : CoordInf) : DensInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ μinf hμ νinf hν
  obtain ⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩ :=
    hCo F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet
  have := hμ.1
  have := hν.1
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μinf.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μinf (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (νinf.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map νinf (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hD := hSub n m _ _ hμ' hν' f' hC
  refine densAll_transport μinf νinf (gramR (Ainf F) σ J) Subtype.val _ eV eH f'
    Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)
  rintro y ⟨X, hX, rfl⟩
  exact hS X hX
end PI.VolStabW
