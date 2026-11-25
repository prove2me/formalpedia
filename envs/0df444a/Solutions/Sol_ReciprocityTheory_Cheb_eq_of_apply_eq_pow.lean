-- Prove2me | solution 1 for ReciprocityTheory.Cheb.eq_of_apply_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:01.077442+00:00
-- url     : https://prove2.me/submissions/3da22cb7-9a85-4fc4-a204-47c681c04e15

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix
import Theorems.Thm_ReciprocityTheory_Cheb_eq_one_of_restrict_eq_one
import Theorems.Thm_ReciprocityTheory_Cheb_zeta_pow_eq_pow_iff_natCast
import Theorems.Thm_ReciprocityTheory_Cheb_pow_apply_zeta_eq_units_pow
import Theorems.Thm_ReciprocityTheory_Cheb_restrictNormal_pow_of_gal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb
variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (hσ : orderOf σ ∣ l - 1) (τ : (ZMod l)ˣ) (hτ : orderOf τ = l - 1)
    (g : Gal(M/ℚ)) (hg : AlgEquiv.restrictNormal g K = σ) (hgζ : g ζ = ζ ^ (τ : ZMod l).val)
    (φ : M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers g)] M) (n : ℕ) (hφ : φ ζ = ζ ^ n) (hn : (n : ZMod l) = τ) :
    φ.restrictScalars ℚ = g := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hmem' : φ.restrictScalars ℚ ∈
      IntermediateField.fixingSubgroup (IntermediateField.fixedField (Subgroup.zpowers g)) := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact φ.commutes ⟨x, hx⟩
  have hmem : φ.restrictScalars ℚ ∈ Subgroup.zpowers g := by
    rwa [IntermediateField.fixingSubgroup_fixedField] at hmem'
  obtain ⟨k, hk : g ^ k = _⟩ := mem_powers_iff_mem_zpowers.mpr hmem
  have hpos := orderOf_pos g
  set m := k + orderOf g - 1 with hm
  have hkm : g ^ (m + 1) = g ^ k := by
    rw [show m + 1 = k + orderOf g by omega, pow_add, pow_orderOf_eq_one, mul_one]
  have hφ' : (g ^ (m + 1)) ζ = ζ ^ n := by rw [hkm, hk]; exact hφ
  rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, zeta_pow_eq_pow_iff_natCast hζ, ZMod.natCast_zmod_val, hn] at hφ'
  have hτm : τ ^ m = 1 := by
    have h2 : τ ^ (m + 1) = τ := Units.ext hφ'
    rw [pow_succ] at h2
    exact mul_eq_right.mp h2
  have hdiv : l - 1 ∣ m := hτ ▸ orderOf_dvd_of_pow_eq_one hτm
  have hσm : σ ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp (hσ.trans hdiv)
  have hgm : g ^ m = 1 := by
    refine eq_one_of_restrict_eq_one (K := K) hζ (g ^ m) ?_ ?_
    · rw [restrictNormal_pow_of_gal, hg, hσm]
    · rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, hτm, Units.val_one, ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (Fact.out : l.Prime).one_lt, pow_one]
  rw [← hk, ← hkm, pow_succ, hgm, one_mul]
end ReciprocityTheory.Cheb
