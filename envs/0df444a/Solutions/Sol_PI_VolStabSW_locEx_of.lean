-- Prove2me | solution 1 for PI.VolStabSW.locEx_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:34:49.041792+00:00
-- url     : https://prove2.me/submissions/1a632f9b-413d-4fe2-a52f-8961dbc9eefa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SWeqOm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocExOf
import Theorems.Thm_PI_VolStabSW_rapidDecay_of_compact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (hI : FibInfEx) (hV : FibVEx) (hL : LatSB) : LocEx := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  let Lv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (latV b v).indicator 1
  have hp : IsPureFin b (fun X => ∏ᶠ v, Lv v (projV v X)) Lv :=
    ⟨fun v => hL F E _ M a b v, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩
  have hS := hc a ha2 (gramE σ J X0) hT hdet _ b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ))
    (fun X => ∏ᶠ v, Lv v (projV v X)) Lv continuous_const
    (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp (fun X => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
  obtain ⟨μinf, hμinf⟩ := h3.1
  obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
  have h4 := ((h3.2 μinf hμinf).2 νinf hνinf)
  obtain ⟨μv, hμv⟩ := h4.1
  obtain ⟨νv, hνv⟩ := (h4.2 μv hμv).1
  obtain ⟨fibInf, hfi⟩ := hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
  choose fibV hfv using fun v =>
    hV F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v)
  exact ⟨μinf, νinf, μv, νv, fibInf, fibV, hμinf, hνinf, hμv, hνv, hfi, hfv⟩
end PI.VolStabSW
