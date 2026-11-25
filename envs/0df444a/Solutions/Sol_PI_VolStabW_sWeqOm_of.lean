-- Prove2me | solution 1 for PI.VolStabW.sWeqOm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:31.823106+00:00
-- url     : https://prove2.me/submissions/c7e765bc-30a1-4d05-935d-f2bf45c35f35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SWeqOm
import Theorems.Thm_PI_VolStabW_rapidDecay_of_compact

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
theorem _root_.solution (h1 : DensFibInf) (h2 : DensFibV) : SWeqOm := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν Φ hΦ
  obtain ⟨d, b, Φinf, Φf, Φv, hci, hsi, hpf, hpr⟩ := hΦ
  have hS := hc a ha2 (gramE σ J X0) hT hdet d b Φ Φinf Φf Φv hci
    (rapidDecay_of_compact b Φinf hci hsi) hpf hpr
  obtain ⟨_, hν2⟩ := hν
  obtain ⟨μinf, hμinf⟩ := hν2.1
  have hν3 := hν2.2 μinf hμinf
  obtain ⟨νinf, hνinf⟩ := hν3.1
  have hν4 := hν3.2 νinf hνinf
  obtain ⟨μv, hμv⟩ := hν4.1
  have hν5 := hν4.2 μv hμv
  obtain ⟨νv, hνv⟩ := hν5.1
  have hν6 := hν5.2 νv hνv
  obtain ⟨fibInf, hfibInf⟩ := hν6.1
  have hν7 := hν6.2 fibInf hfibInf
  obtain ⟨fibV, hfibV⟩ := hν7.1
  have hν8 := hν7.2 fibV hfibV d b Φ Φinf Φf Φv hci hsi hpf hpr
  obtain ⟨ginf, gv, hdi, hdv, _, hmean⟩ :=
    (((((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv)
  rw [hmean, hν8.2.2, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
    fibInf hfibInf Φinf ginf hci hsi hdi]
  congr 1
  exact tprod_congr fun v => h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfibV v) (Φv v) (gv v) (hpf.1 v) (hdv v)
end PI.VolStabW
