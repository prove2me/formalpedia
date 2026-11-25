-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_residue_algebraMap_7319e467ce67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:46.411084+00:00
-- url     : https://prove2.me/submissions/cf19e0d4-f52b-42fb-b9bd-bf5f68b48ca4

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (c : ℤ_[l]) :
    residue ↥(OL LL) (algebraMap ℤ_[l] ↥(OL LL) c) = (((PadicInt.toZMod c).val : ℕ) : ResidueField ↥(OL LL)) := by
  have h := PadicInt.toZMod_spec c
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨d, hd⟩ := h
  have hc : c = (((PadicInt.toZMod c).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) * d := by
    rw [← hd, ZMod.natCast_val]; ring
  conv_lhs => rw [hc]
  rw [map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast]
  have h0 : (((l : ℕ) : ResidueField ↥(OL LL))) = 0 := by
    rw [← map_natCast (residue ↥(OL LL))]
    exact (residue_eq_zero_iff _).mpr (l_mem_max LL)
  rw [h0, zero_mul, add_zero]
end Formalism.BasicNotions.Examples₂.LB
