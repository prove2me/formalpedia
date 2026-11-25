-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrobOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:20.060331+00:00
-- url     : https://prove2.me/submissions/da118a41-ec00-49c5-8a27-bd51bca7a6c1

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_qK_pow_sub_one_ne_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_eqOn_Kn_of_primitive
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrobOn_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_pow_of_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_primitiveRoot
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_pow_pow_succ_sub
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finrank_extendScalars_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isGalois_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_lt_qK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    ∃ φ : GK p K, IsFrobOn p K n φ := by
  classical
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  have hq := one_lt_qK p K hK
  have : NeZero (qK p K ^ n - 1) := ⟨hm0⟩
  obtain ⟨ζ₀, hζ₀⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hζ1 := hζ₀.pow_eq_one
  let E : IntermediateField K (PadicAlgCl p) := IntermediateField.extendScalars (le_Kn p K n)
  have hgal : IsGalois K E := isGalois_Kn p K hK hn
  have hfr : Module.finrank K E = n := finrank_extendScalars_Kn p K hK hn
  have hfd : FiniteDimensional K E := Module.finite_of_finrank_pos (by rw [hfr]; exact hn)
  have hcard : Nat.card (E ≃ₐ[K] E) = n := by rw [IsGalois.card_aut_eq_finrank, hfr]
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (PadicAlgCl p)
  have hex : ∀ τ : E ≃ₐ[K] E, ∃ i : Fin n, ∃ σ : GK p K,
      AlgEquiv.restrictNormalHom E σ = τ ∧ σ ζ₀ = ζ₀ ^ (qK p K ^ (i : ℕ)) := by
    intro τ
    obtain ⟨σ, hσ⟩ := hsurj τ
    obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ1
    exact ⟨⟨i, hi⟩, σ, hσ, h⟩
  choose f g hg1 hg2 using hex
  have hinj : Function.Injective f := by
    intro τ1 τ2 h
    rw [← hg1 τ1, ← hg1 τ2]
    ext x
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
    exact UnramifiedExtensions.eqOn_Kn_of_primitive hm0 hζ₀ (by rw [hg2, hg2, h]) x.2
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_fin])
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨1 % n, Nat.mod_lt _ hn⟩
  refine ⟨g τ, (isFrobOn_iff p K hK hn _).2 ?_⟩
  have h0 : g τ ζ₀ = ζ₀ ^ qK p K := by
    rw [hg2, hτ]
    rcases Nat.lt_or_ge 1 n with h | h
    · simp only [Nat.mod_eq_of_lt h, pow_one]
    · obtain rfl : n = 1 := by omega
      have h1 := UnramifiedExtensions.pow_pow_succ_sub (q := qK p K) (n := 1) (by omega) hζ1
      simp only [Nat.mod_self, pow_zero, pow_one] at h1 ⊢
      exact h1.symm
  intro ζ hζ
  obtain ⟨k, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  rw [map_pow, h0, ← pow_mul, ← pow_mul, mul_comm]
end ReciprocityTheory.DiscreteGroups.LocalClassField
