-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_unramified_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:51.282868+00:00
-- url     : https://prove2.me/submissions/559d073a-efa0-43de-836e-5d47a1929e29

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finiteDimensional_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_extendScalars_Kn_eq_adjoin
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_natDegree_minpoly_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_primitiveRoot
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_Kn_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_not_dvd_qK_pow_sub_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_pow_qK_eq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_eq_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_of_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kn_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Obar_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_resK_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_sub_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_qK_le_pow_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) = n ∧ qK p (Kn p K n) = qK p K ^ n := by
  have hq := one_lt_qK p K hK
  have hnd := UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn
  have hm0 : qK p K ^ n - 1 ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero p)
  obtain ⟨ζ, hζ⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hfd := finiteDimensional_Kn p K hK hn
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hup : Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) ≤ n := by
    rw [extendScalars_Kn_eq_adjoin p K hζ hm0, IntermediateField.adjoin.finrank hint]
    exact natDegree_minpoly_le p K hK hn hζ.pow_eq_one
  obtain ⟨f, hf, hqf, hle⟩ := qK_le_pow_finrank p K hK hfd (le_Kn p K n)
  have hmul := IntermediateField.finrank_bot_mul_relfinrank (le_Kn p K n)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_Kn p K n)] at hmul
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have h1 := UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ.pow_eq_one

  have hnf : n ≤ f := by
    have hmem : UnramifiedExtensions.red ζ ∈ resK p (Kn p K n) :=
      (UnramifiedExtensions.mem_resK_iff _ _).2 ⟨⟨ζ, mem_Obar_iff.2 h1.le⟩, mem_Kn_of_pow p K hζ.pow_eq_one,
        (UnramifiedExtensions.red_of_le h1.le).symm⟩
    have h2 := UnramifiedExtensions.pow_qK_eq (Kn p K n) hfd hmem
    rw [hqf, ← UnramifiedExtensions.red_pow h1.le] at h2
    have hζf : (ζ ^ (qK p K ^ f)) ^ (qK p K ^ n - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h3 : ζ ^ (qK p K ^ f) = ζ := by
      by_contra hne
      have h4 := UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one hnd hζf hζ.pow_eq_one hne
      have h5 := (UnramifiedExtensions.red_eq_iff (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζf).le h1.le).1 h2
      exact absurd h4 (ne_of_lt h5)
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [norm_zero] at h1; exact zero_ne_one h1
    have hf1 : 1 ≤ qK p K ^ f := Nat.one_le_pow _ _ (by omega)
    have h6 : ζ ^ (qK p K ^ f - 1) = 1 := by
      have h7 : qK p K ^ f = (qK p K ^ f - 1) + 1 := by omega
      rw [h7, pow_succ] at h3
      exact mul_right_cancel₀ hζ0 (by rw [h3, one_mul])
    have h8 := (hζ.pow_eq_one_iff_dvd _).1 h6
    have h9 : 1 < qK p K ^ f := Nat.one_lt_pow hf.ne' hq
    have h10 := Nat.le_of_dvd (by omega) h8
    have h11 : qK p K ^ n ≤ qK p K ^ f := by
      have : 1 ≤ qK p K ^ n := Nat.one_le_pow _ _ (by omega)
      omega
    exact (Nat.pow_le_pow_iff_right hq).1 h11
  have hkey : f * Module.finrank ℚ_[p] K ≤
      Module.finrank ℚ_[p] K * Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [hmul]; exact hle
  have hfle : f ≤ Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [mul_comm] at hkey
    exact Nat.le_of_mul_le_mul_left hkey hd
  have hfn : f = n := by omega
  exact ⟨by omega, by rw [hqf, hfn]⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
