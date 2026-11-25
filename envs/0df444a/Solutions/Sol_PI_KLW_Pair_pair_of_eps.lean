-- Prove2me | solution 1 for PI.KLW.Pair.pair_of_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:31.714814+00:00
-- url     : https://prove2.me/submissions/66a2936d-fc0a-451c-9b58-fb9e1a6fab48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Theorems.Thm_P2M_PI_KLW_Pair_smul_mem__4f5cbb083064
import Theorems.Thm_P2M_PI_KLW_Pair_add_mem__5e06d2fd9611
import Theorems.Thm_PI_KLW_Pair_near_one
import Theorems.Thm_PI_KLW_Ind_hf_add_left
import Theorems.Thm_PI_KLW_Ind_hf_add_right
import Theorems.Thm_PI_KLW_Ind_hf_smul_left
import Theorems.Thm_PI_KLW_Ind_hf_smul_right
import Theorems.Thm_PI_KLW_Ind_rp_add
import Theorems.Thm_PI_KLW_Ind_rp_mul
import Theorems.Thm_PI_KLW_Ind_rp_one
import Theorems.Thm_PI_KLW_NO_one_add_p_unit
import Theorems.Thm_PI_KLW_NO_rp_add
import Theorems.Thm_PI_KLW_NO_rp_c
import Theorems.Thm_PI_KLW_NO_rp_mul
import Theorems.Thm_PI_KLW_NO_rp_natCast
import Theorems.Thm_PI_KLW_NO_rp_one
import Theorems.Thm_PI_KLW_NO_rp_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Pair
open PI.KLW
namespace PI.KLW.Pair
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) {p : ℕ} (hp : p.Prime) {ι : Type}
    [Fintype ι] [Nonempty ι] {L : Set (ι → K)} (hL : Unimod K c p L) (hS : Spans K L) {ε : K}
    (hε : Rp K p ε) (hsum : ε + c ε = 1) (hδ : Rp K p (ε * c ε / (p : K) ^ 2)) :
    ∃ x ∈ L, ∃ y ∈ L, hf c x y = 1 := by
  obtain ⟨x1, hx1, y1, hy1, r1, hr1, h1⟩ := near_one c hc hK hne hp hL hS hε hsum hδ
  have hε' : Rp K p (c ε) := NO.rp_c c hε
  have hsum' : c ε + c (c ε) = 1 := by rw [hc, add_comm, hsum]
  have hδ' : Rp K p (c ε * c (c ε) / (p : K) ^ 2) := by rw [hc, mul_comm]; exact hδ
  obtain ⟨x2, hx2, y2, hy2, r2, hr2, h2⟩ := near_one c hc hK hne hp hL hS hε' hsum' hδ'
  rw [hc] at h2
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hxL : ε • x1 + c ε • x2 ∈ L := add_mem' hL (smul_mem' hL hx1 hε) (smul_mem' hL hx2 hε')
  have hyL : c ε • y1 + ε • y2 ∈ L := add_mem' hL (smul_mem' hL hy1 hε') (smul_mem' hL hy2 hε)
  have hd : (p : K) * ((p : K) * (ε * c ε / (p : K) ^ 2)) = ε * c ε := by field_simp
  have hxy : hf c (ε • x1 + c ε • x2) (c ε • y1 + ε • y2) = 1 + (p : K) * ((p : K)
      * (ε * c ε / (p : K) ^ 2) * (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1)) := by
    simp only [Ind.hf_add_left, Ind.hf_add_right, Ind.hf_smul_left, Ind.hf_smul_right, hc]
    linear_combination ε * h1 + c ε * h2
      - (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1) * hd + (ε + c ε + 1) * hsum
  have hQ : Rp K p ((p : K) * (ε * c ε / (p : K) ^ 2)
      * (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1)) :=
    NO.rp_mul (NO.rp_mul (NO.rp_natCast p) hδ)
      (NO.rp_sub (NO.rp_sub (NO.rp_add (NO.rp_add (NO.rp_add (NO.rp_mul hε hr1)
        ((hL x1).1 hx1 y2 hy2)) ((hL x2).1 hx2 y1 hy1)) (NO.rp_mul hε' hr2)) NO.rp_one) NO.rp_one)
  obtain ⟨ha0, hai⟩ := NO.one_add_p_unit c hc hK hne hp hQ
  rw [← hxy] at ha0 hai
  refine ⟨_, hxL, c ((hf c (ε • x1 + c ε • x2) (c ε • y1 + ε • y2))⁻¹) • (c ε • y1 + ε • y2),
    smul_mem' hL hyL (NO.rp_c c hai), ?_⟩
  rw [Ind.hf_smul_right, hc, inv_mul_cancel₀ ha0]
end PI.KLW.Pair
