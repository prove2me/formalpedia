-- Prove2me | solution 1 for PI.ScRefExists.TH.prod_le_radical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:16.15021+00:00
-- url     : https://prove2.me/submissions/d522d462-2429-4d32-bf28-2fdbc33d4d0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaSeriesExistence
import Theorems.Thm_PI_ScRefExists_TH_mem_primesG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.TH
theorem _root_.solution (g : ℕ) (hg : 1 ≤ g) :
    (∏ P ∈ primesG I g hg, P.asIdeal) ≤ (Ideal.span {(g : 𝓞 I.E)}).radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J hJ => ?_
  obtain ⟨hJle, hJp⟩ := hJ
  have hgJ : (g : 𝓞 I.E) ∈ J := hJle (Ideal.mem_span_singleton_self _)
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply spanG_ne I g hg
    rw [Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rw [h] at hgJ
    exact (Submodule.mem_bot _).mp hgJ
  let Q : HeightOneSpectrum (𝓞 I.E) := ⟨J, hJp, hJ0⟩
  have hQ : Q ∈ primesG I g hg := (mem_primesG I g hg Q).mpr hgJ
  exact Ideal.prod_le_inf.trans (Finset.inf_le hQ)
end PI.ScRefExists.TH
