-- Prove2me | solution 1 for ReciprocityTheory.CA.length_le_height_of_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:49.531816+00:00
-- url     : https://prove2.me/submissions/b5909729-92f5-4631-b16b-da9ff1796d8d

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularOfLeHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Theorems.Thm_ReciprocityTheory_CA_depthGE_localization_of_isWeaklyRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
namespace ReciprocityTheory.CA
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Q : Ideal R) [Q.IsPrime] {rs : List R} (hrs : ∀ x ∈ rs, x ∈ Q) (reg : IsWeaklyRegular R rs) :
    (rs.length : ℕ∞) ≤ Q.height := by
  obtain ⟨ss, hlen, hmem, hreg⟩ := depthGE_localization_of_isWeaklyRegular Q hrs reg
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have e := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ss hreg
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)] at e
  have hne : Ideal.ofList ss ≠ ⊤ := by
    intro htop
    have : Ideal.ofList ss ≤ maximalIdeal (Localization.AtPrime Q) := by
      rw [Ideal.ofList, Ideal.span_le]; exact fun x hx => hmem x hx
    exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop ▸ this))
  have : Nontrivial (Localization.AtPrime Q ⧸ Ideal.ofList ss) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := Localization.AtPrime Q ⧸ Ideal.ofList ss)
  have : ((ss.length : ℕ) : WithBot ℕ∞) ≤ (Q.height : WithBot ℕ∞) := by
    rw [← e]
    calc ((ss.length : ℕ) : WithBot ℕ∞) = 0 + ss.length := (zero_add _).symm
      _ ≤ _ := add_le_add_left h0 _
  rw [← hlen]
  exact_mod_cast this
end ReciprocityTheory.CA
