-- Prove2me | solution 1 for PI.KLW.Pair.near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:03.339658+00:00
-- url     : https://prove2.me/submissions/2bc20d25-2e20-40ac-9dee-8cb5762c84e8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Theorems.Thm_P2M_PI_KLW_Pair_smul_mem__4f5cbb083064
import Theorems.Thm_PI_KLW_Pair_half
import Theorems.Thm_PI_KLW_Ind_hf_smul_right
import Theorems.Thm_PI_KLW_Ind_rp_add
import Theorems.Thm_PI_KLW_Ind_rp_mul
import Theorems.Thm_PI_KLW_Ind_rp_neg
import Theorems.Thm_PI_KLW_Ind_rp_one
import Theorems.Thm_PI_KLW_NO_rp_add
import Theorems.Thm_PI_KLW_NO_rp_c
import Theorems.Thm_PI_KLW_NO_rp_mul
import Theorems.Thm_PI_KLW_NO_rp_natCast
import Theorems.Thm_PI_KLW_NO_rp_neg
import Theorems.Thm_PI_KLW_NO_rp_one
import Theorems.Thm_PI_KLW_NO_rp_sub
import Theorems.Thm_PI_KLW_NO_unit_of_norm


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
    ∃ x ∈ L, ∃ y ∈ L, ∃ r, Rp K p r ∧ ε * (hf c x y - 1) = ε * c ε * r := by
  obtain ⟨x', hx', y', hy', hn⟩ := half c hc hK hne hp hL hS hε hsum hδ
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hce : c ε = 1 - ε := by linear_combination hsum
  obtain ⟨ρ', hρ'⟩ : ∃ ρ', ρ' = hf c x' y' := ⟨_, rfl⟩
  have hρR : Rp K p ρ' := by rw [hρ']; exact (hL x').1 hx' y' hy'
  rw [← hρ'] at hn
  obtain ⟨z, hz⟩ : ∃ z, z = ε * ρ' + c ε := ⟨_, rfl⟩
  have hzR : Rp K p z := by rw [hz]; exact NO.rp_add (NO.rp_mul hε hρR) (NO.rp_c c hε)
  have hcz : c z = c ε * c ρ' + ε := by rw [hz, map_add, map_mul, hc]
  have hnz : ¬ Rp K p (z * c z / p) := by
    intro h
    apply hn
    have key : ε * ρ' / p = ε * (z * c z / p) + ((p : K) * (ε * c ε / (p : K) ^ 2))
        * (-ε * (ρ' * c ρ' - ρ' - c ρ' + 1) + ρ' - c ρ') := by
      rw [hcz, hz, hce]
      field_simp
      ring
    rw [key]
    have hcρ : Rp K p (c ρ') := NO.rp_c c hρR
    have hW : Rp K p (-ε * (ρ' * c ρ' - ρ' - c ρ' + 1) + ρ' - c ρ') :=
      NO.rp_sub (NO.rp_add (NO.rp_mul (NO.rp_neg hε)
        (NO.rp_add (NO.rp_sub (NO.rp_sub (NO.rp_mul hρR hcρ) hρR) hcρ) NO.rp_one)) hρR) hcρ
    exact NO.rp_add (NO.rp_mul hε h) (NO.rp_mul (NO.rp_mul (NO.rp_natCast p) hδ) hW)
  obtain ⟨hz0, hzi⟩ := NO.unit_of_norm c hc hK hne hp hzR hnz
  refine ⟨x', hx', c (z⁻¹) • y', smul_mem' hL hy' (NO.rp_c c hzi), z⁻¹ * (ρ' - 1),
    NO.rp_mul hzi (NO.rp_sub hρR NO.rp_one), ?_⟩
  rw [Ind.hf_smul_right, hc, ← hρ']
  have h1 : ε * (ρ' - z) = ε * c ε * (ρ' - 1) := by rw [hz, hce]; ring
  have hzz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
  linear_combination z⁻¹ * h1 + ε * hzz
end PI.KLW.Pair
