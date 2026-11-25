-- Prove2me | solution 1 for ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:34.675814+00:00
-- url     : https://prove2.me/submissions/53b2f0b9-8057-4e58-a021-8dbe5388d2ce

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Theorems.Thm_ReciprocityTheory_CA_height_add_height_maximal_quotient_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
universe u
namespace ReciprocityTheory.CA
theorem _root_.solution (K : Type*) [Field K] (N : ℕ)
    (𝔔 : Ideal (MvPolynomial (Fin N) K)) [𝔔.IsPrime] :
    (𝔔.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin N) K ⧸ 𝔔) = N := by
  obtain ⟨𝔪0, h𝔪0⟩ := Ideal.exists_maximal (MvPolynomial (Fin N) K ⧸ 𝔔)
  have cancel : ∀ a b : ℕ∞, 𝔔.height + a = N → 𝔔.height + b = N → a = b := by
      intro a b ha hb
      have hq : 𝔔.height ≠ ⊤ := fun h => by rw [h, top_add] at ha; exact ENat.top_ne_coe N ha
      have ha' : a ≠ ⊤ := fun h => by rw [h, add_top] at ha; exact ENat.top_ne_coe N ha
      have hb' : b ≠ ⊤ := fun h => by rw [h, add_top] at hb; exact ENat.top_ne_coe N hb
      obtain ⟨q, hq0⟩ := ENat.ne_top_iff_exists.1 hq
      obtain ⟨a0, ha0⟩ := ENat.ne_top_iff_exists.1 ha'
      obtain ⟨b0, hb0⟩ := ENat.ne_top_iff_exists.1 hb'
      rw [← hq0, ← ha0] at ha
      rw [← hq0, ← hb0] at hb
      rw [← ha0, ← hb0]
      have e1 : q + a0 = N := by exact_mod_cast ha
      have e2 : q + b0 = N := by exact_mod_cast hb
      congr 1
      omega
  have hall : ∀ 𝔪 : Ideal (MvPolynomial (Fin N) K ⧸ 𝔔), 𝔪.IsMaximal → 𝔪.height = 𝔪0.height := by
    intro 𝔪 h𝔪
    exact cancel _ _ (height_add_height_maximal_quotient_field K N 𝔔 𝔪)
      (height_add_height_maximal_quotient_field K N 𝔔 𝔪0)
  have hsup : (⨆ I : Ideal (MvPolynomial (Fin N) K ⧸ 𝔔), ⨆ (_ : I.IsMaximal), I.height) = 𝔪0.height :=
    le_antisymm (iSup₂_le fun I hI => (hall I hI).le) (le_iSup₂_of_le 𝔪0 h𝔪0 le_rfl)
  rw [← Ideal.sup_isMaximal_height_eq_ringKrullDim, hsup]
  have e := height_add_height_maximal_quotient_field K N 𝔔 𝔪0
  exact_mod_cast e
end ReciprocityTheory.CA
