-- Prove2me | solution 2 for P2M_PI_PolydiscIntegrality__norm_natCast_eq_one_3f360323e265
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:16:00.204989+00:00
-- url     : https://prove2.me/submissions/205391de-4337-48d1-8657-93eda6b371b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_NormPPosLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_Lemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PolydiscIntegrality₂
open Filter Topology
variable {p : ℕ} [Fact p.Prime]
namespace PI.PolydiscIntegrality₂
theorem _root_.solution {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' p (N : ℚ_[p])
  simp only [map_natCast, PadicComplex.coe_natCast] at h1
  rw [h1]
  exact Padic.norm_natCast_eq_one_iff.mpr (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr h)
end PI.PolydiscIntegrality₂
