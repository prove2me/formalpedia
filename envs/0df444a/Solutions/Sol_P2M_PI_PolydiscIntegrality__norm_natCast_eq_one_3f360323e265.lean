-- Prove2me | solution 1 for P2M_PI_PolydiscIntegrality__norm_natCast_eq_one_3f360323e265
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:08.884527+00:00
-- url     : https://prove2.me/submissions/bc947ca5-0ab1-4711-9790-9a8cd88ad3fe

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
theorem _root_.solution {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have hc : Nat.Coprime N p := ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 h).symm
  have h1 : ‖(N : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hc.symm
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) N, norm_algebraMap', h1]



