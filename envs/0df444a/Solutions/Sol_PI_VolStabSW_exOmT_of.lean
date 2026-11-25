-- Prove2me | solution 1 for PI.VolStabSW.exOmT_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:35.397268+00:00
-- url     : https://prove2.me/submissions/446073f6-e173-4f82-8f81-47faf8fea9b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd

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
theorem _root_.solution (h1 : LocEx) (h2 : SdUniq) (h3 : FibPin) (h4 : MultFib) (h5 : RestrProd) :
    ExOmT := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c1 := h1 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c2 := h2 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c3 := h3 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c4 := h4 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c5 := h5 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μinf, νinf, μv, νv, fibInf, fibV, hμi, hνi, hμv, hνv, hfi, hfv⟩ := c1
  obtain ⟨νX, hsupp, hform⟩ :=
    c5 μinf hμi νinf hνi μv hμv νv hνv fibInf hfi fibV hfv (c4 μv hμv νv hνv fibV hfv)
  refine ⟨νX, hsupp, ⟨μinf, hμi⟩, fun μinf' hμi' => ?_⟩
  obtain rfl := c2.1 _ _ hμi hμi'
  refine ⟨⟨νinf, hνi⟩, fun νinf' hνi' => ?_⟩
  obtain rfl := c2.2.1 _ _ hνi hνi'
  refine ⟨⟨μv, hμv⟩, fun μv' hμv' => ?_⟩
  obtain rfl : μv = μv' := funext fun v => (c2.2.2 v).1 _ _ (hμv v) (hμv' v)
  refine ⟨⟨νv, hνv⟩, fun νv' hνv' => ?_⟩
  obtain rfl : νv = νv' := funext fun v => (c2.2.2 v).2 _ _ (hνv v) (hνv' v)
  refine ⟨⟨fibInf, hfi⟩, fun fibInf' hfi' => ⟨⟨fibV, hfv⟩, fun fibV' hfv' => ?_⟩⟩
  intro d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  obtain ⟨hI, hF⟩ := hform d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  refine ⟨hI, c4 μv hμv νv hνv fibV' hfv' d b Φf Φv hp, ?_⟩
  rw [hF, c3.1 μinf hμi νinf hνi fibInf fibInf' hfi hfi' Φinf hc1 hc2]
  congr 1
  exact tprod_congr fun v => c3.2 v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (fibV' v) (hfv v)
    (hfv' v) (Φv v) (hp.1 v)
end PI.VolStabSW
