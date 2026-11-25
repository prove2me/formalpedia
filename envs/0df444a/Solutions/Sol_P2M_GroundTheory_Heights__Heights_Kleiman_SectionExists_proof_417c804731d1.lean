-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionExists_proof_417c804731d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:00.376411+00:00
-- url     : https://prove2.me/submissions/878c32af-0beb-484a-8116-42391f46b429

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmplePowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sectionExists_of_gap_fdd95ec62f45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_twistMul_fe4f7be26a50
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistMul_3585a8ef645c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SectionExists
theorem _root_.solution (hcount : SectionCount.Statement.{u, w})
    (hpow : VeryAmplePow.Statement.{u, w}) (hlead : LeadingCoeffPos.Statement.{u, w}) :
    SectionExists.Statement.{u, w} := by
  intro k _ Ω _ _ N x d M t s' hZ hM hs' hst hq
  obtain ⟨q, m, hq1, hm, hva⟩ := hq
  have hδ : 0 < t / (d + 1) - s' := by linarith
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq1
  have hqδ := mul_pos hqpos hδ
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (1 / ((q : ℚ) * (t / (d + 1) - s')))
  rw [div_lt_iff₀ hqδ] at hj₀
  have hgap : 1 < (((j₀ + 1) * q : ℕ) : ℚ) * (t / (d + 1) - s') := by
    push_cast
    have : ((j₀ : ℚ) + 1) * q * (t / (d + 1) - s') =
        j₀ * (q * (t / (d + 1) - s')) + q * (t / (d + 1) - s') := by ring
    rw [this]
    linarith
  obtain ⟨Nb0, hNb0⟩ := exists_lineBundle_twistMul M q m
  have hvaQ : IsVeryAmple (twistMul M.toSubSystem ((j₀ + 1) * q) (((j₀ + 1 : ℕ) : ℤ) * m)) := by
    have := hpow k Ω N x Nb0 (j₀ + 1) (by rw [hNb0]; exact hva) (by omega)
    rw [hNb0, pow_twistMul] at this
    exact this
  exact sectionExists_of_gap hcount hlead hZ hM hs' (Nat.mul_pos (Nat.succ_pos _) hq1)
    (by push_cast; rw [hm]; ring) hvaQ hgap
end SectionExists
end GroundTheory.Heights₂.Heights.Kleiman
