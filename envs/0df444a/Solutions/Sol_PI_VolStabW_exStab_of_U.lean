-- Prove2me | solution 1 for PI.VolStabW.exStab_of_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:46.712711+00:00
-- url     : https://prove2.me/submissions/da3e3106-b86e-49a0-9d01-5359f7f28bf3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabU
import Theorems.Thm_PI_VolStabW_weil_orbit_u
import Theorems.Thm_PI_VolStabW_orbEmb_of
import Theorems.Thm_PI_VolStabW_secCtblG_of
import Theorems.Thm_PI_VolStabW_stabClosed_holds


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
open scoped TensorProduct ENNReal NNReal Pointwise
namespace PI.VolStabW
theorem _root_.solution (hW : SecCtblW) (hP : LCSCPolish) (hO : OrbTup) (hI : NuInv) (hF : NuFin)
    (hN : NuNeZero) : ExStab := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secCtblG_of hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))
  have : μ.IsHaarMeasure := hμ
  have hnull : νX {y | ¬ ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y} = 0 := by
    apply measure_mono_null _ hν.1
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    intro hg
    exact hy (hO F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet y hg)
  obtain ⟨hemb, hcont⟩ := orbEmb_of hW hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨μ', h1, h2⟩ := weil_orbit_u (G := HA (AF F) σ J) (ratTup (AF F) X0)
    (stabClosed_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet) μ νX hnull
    (hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν)
    (hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν)
    (hN F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν) hemb hcont
  exact ⟨μ', h1, hnull, fun f hf s hs => h2 f hf s hs⟩
end PI.VolStabW
