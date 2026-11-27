-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.relIndex_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:43:03.79064+00:00
-- url     : https://prove2.me/submissions/86a32d46-03d2-490c-bf89-4690fa161d53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_contId_ne_bot
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_absNorm_mul_relIndex_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) :
    (((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex
      (((contId G₀ : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).toAddSubgroup : ℕ) : ℚ) = Ideal.absNorm (contId G₀) := by
  set J : FractionalIdeal (𝓞 K)⁰ K := ↑(contId G₀) with hJdef
  have hJ : J ≠ 0 := by
    rw [hJdef, Ne, FractionalIdeal.coeIdeal_eq_zero]; exact contId_ne_bot G₀ h
  have hfg : ((J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).FG :=
    FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  have h1 : (1 : Submodule (𝓞 K) K) ≤ ((J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    have h2 := FractionalIdeal.inv_anti_mono hJ one_ne_zero FractionalIdeal.coeIdeal_le_one
    rw [inv_one] at h2
    have h3 : ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤
        ((J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := h2
    rwa [FractionalIdeal.coe_one] at h3
  have key := ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one _ hfg h1
  have he : (⟨((J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (𝓞 K)⁰ K) = J⁻¹ := rfl
  have hN : (Ideal.absNorm (contId G₀) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact contId_ne_bot G₀ h
  rw [he, map_inv₀, show FractionalIdeal.absNorm J = Ideal.absNorm (contId G₀) from
    FractionalIdeal.coeIdeal_absNorm _, inv_mul_eq_one₀ hN] at key
  exact key.symm
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
