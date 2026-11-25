-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LevelValuationRings_hidaSettingOfEven_6fc5b055357a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:58.319199+00:00
-- url     : https://prove2.me/submissions/4d4604bd-1687-47a8-b846-3cd73944be0e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_alg_337981bcf272
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_period_ae7893d3da20
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__GatR_isAdicComplete_e5d83f2ed8a2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings
open Formalism.MainNotions.G QuadraticAlgebra
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
namespace Formalism.BasicNotions.Examples₂.LevelValuationRings
theorem _root_.solution (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    HidaSetting p n (Wn p n) (Qn p n) (On p n) (Kn p n) (iotaN p n) (sigN p n)
      (algebraMap (Wn p n) (On p n)) ω where
  prime := hp.out
  five_le := h5
  two_le := h2
  even := he
  frac_alt := inferInstance
  frac_O := inferInstance
  p_unif := WittVector.irreducible p
  res_card := by
    rw [Nat.card_congr (WittVector.quotientPEquiv (p := p) (k := GaloisField p n)).toEquiv,
      GaloisField.card p n (by omega)]
  eq_sum_herm_smul_frame_of_inW := inferInstance
  frob := fun x => by
    have h : WittVector.frobenius x - x ^ p ∈ Ideal.span {(p : Wn p n)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
      show WittVector.constantCoeff (WittVector.frobenius x - x ^ p) = 0
      rw [map_sub, map_pow]
      show (WittVector.frobenius x).coeff 0 - x.coeff 0 ^ p = 0
      rw [WittVector.coeff_frobenius_charP, sub_self]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp h
    exact ⟨y, by rw [sigN_alg, ← hy]; congr 1; ring⟩
  period := sigN_period p n (by omega)
  ι_comp := fun x => IsFractionRing.lift_algebraMap (inj_WK p n) x
  finite := RingHom.finite_algebraMap.mpr inferInstance
  complete_O := GatR.isAdicComplete (WittVector.irreducible p) inferInstance
  w_sq := by rw [GatR.om_sq, map_natCast]
end Formalism.BasicNotions.Examples₂.LevelValuationRings
