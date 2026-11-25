-- Prove2me | solution 1 for PI.KLW.NO.generic_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:54.275958+00:00
-- url     : https://prove2.me/submissions/c63b9b86-93ee-4ac8-9a6e-76454e472419

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneC
import Theorems.Thm_PI_KLW_NO_pick
import Theorems.Thm_PI_KLW_Rp_inv_natCast
import Theorems.Thm_PI_KLW_Rp_natCast
import Theorems.Thm_PI_KLW_Unimod_smul_mem
import Theorems.Thm_PI_KLW_hf_smul_left
import Theorems.Thm_PI_KLW_hf_smul_right


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
open PI PI.KLW PI.KLW.NO
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] [NumberField K] {c : K →+* K} (hc : ∀ x, c (c x) = x)
    {p : ℕ} (hp : p.Prime) {ι : Type} [Fintype ι] {L : Set (ι → K)} (hU : Unimod K c p L)
    {x y : ι → K} (hx : x ∈ L) (hy : y ∈ L) (hxy : hf c x y = 1) (v₀ : ι → K) :
    ∃ x₁ ∈ L, ∃ y₁ ∈ L, hf c x₁ y₁ = 1 ∧ hf c v₀ x₁ ≠ 1 ∧ hf c v₀ y₁ ≠ 1 := by
  have key : ∀ q : ℕ, Nat.Coprime q p → q ≠ 0 → (q : K) * hf c v₀ x ≠ 1 → hf c v₀ y ≠ (q : K) →
      ∃ x₁ ∈ L, ∃ y₁ ∈ L, hf c x₁ y₁ = 1 ∧ hf c v₀ x₁ ≠ 1 ∧ hf c v₀ y₁ ≠ 1 := by
    intro q hq hq0 hX hY
    have hqK : (q : K) ≠ 0 := by exact_mod_cast hq0
    refine ⟨(q : K) • x, hU.smul_mem (Rp_natCast q) hx, (q : K)⁻¹ • y,
      hU.smul_mem (Rp_inv_natCast hq) hy, ?_, ?_, ?_⟩
    · rw [hf_smul_left, hf_smul_right, hxy, map_inv₀, map_natCast, mul_one, mul_inv_cancel₀ hqK]
    · rw [hf_smul_right, map_natCast]; exact hX
    · rw [hf_smul_right, map_inv₀, map_natCast]
      intro h; apply hY
      rw [inv_mul_eq_iff_eq_mul₀ hqK, mul_one] at h
      exact h
  have hp2 := hp.two_le
  have hp1 : Nat.Coprime (p + 1) p := Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)
  have h1 : ((p + 1 : ℕ) : K) ≠ 1 := by exact_mod_cast (show p + 1 ≠ 1 by omega)
  have h2 : ((p + 1 : ℕ) : K) ^ 2 ≠ 1 := by
    exact_mod_cast (show (p + 1) ^ 2 ≠ 1 by intro h; nlinarith)
  have h3 : ((p + 1 : ℕ) : K) ≠ ((p + 1 : ℕ) : K) ^ 2 := by
    exact_mod_cast (show p + 1 ≠ (p + 1) ^ 2 by intro h; nlinarith)
  rcases pick (hf c v₀ x) (hf c v₀ y) ((p + 1 : ℕ) : K) h1 h2 h3 with h | h | h
  · exact key 1 (Nat.coprime_one_left p) one_ne_zero (by simpa using h.1) (by simpa using h.2)
  · exact key (p + 1) hp1 (Nat.succ_ne_zero p) h.1 h.2
  · exact key ((p + 1) ^ 2) (Nat.Coprime.pow_left 2 hp1) (pow_ne_zero _ (Nat.succ_ne_zero p))
      (by exact_mod_cast h.1) (by exact_mod_cast h.2)
end PI.KLW.NO
