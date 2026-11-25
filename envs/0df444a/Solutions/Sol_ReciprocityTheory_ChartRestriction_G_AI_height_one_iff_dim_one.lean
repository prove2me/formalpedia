-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.height_one_iff_dim_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:16.455927+00:00
-- url     : https://prove2.me/submissions/ee6de10e-b27d-4d56-8aed-719a6118f459

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
universe u v
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (p : PrimeSpectrum A)
    (hap : a ∈ p.asIdeal) : p.asIdeal.height = 1 ↔ ringKrullDim (A ⧸ p.asIdeal) = 1 := by
  have hs : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p := by
    ext q
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_Ici]
    rfl
  have hdim : ringKrullDim (A ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici, hs]
  have hsum : Order.height p + Order.coheight p ≤ 2 := by
    have h := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum A)
    have h2' : Order.krullDim (PrimeSpectrum A) = 2 := h2
    rw [h2'] at h
    have h3 : (⨆ q : PrimeSpectrum A, Order.height q + Order.coheight q) = 2 := by
      have h' := h.symm
      rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at h'
      exact WithBot.coe_injective h'
    rw [← h3]
    exact le_iSup (fun q : PrimeSpectrum A => Order.height q + Order.coheight q) p
  have h1 : 1 ≤ Order.height p := by
    have hb : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) < p := by
      show (⊥ : Ideal A) < p.asIdeal
      exact bot_lt_iff_ne_bot.mpr (fun h => ha (Ideal.mem_bot.mp (h ▸ hap)))
    exact le_trans le_add_self (Order.height_add_one_le hb)
  have hm : Order.height (IsLocalRing.closedPoint A) = 2 := by
    rw [← PrimeSpectrum.height_eq_orderHeight]
    show (IsLocalRing.maximalIdeal A).height = 2
    have := (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).trans h2
    rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at this
    exact WithBot.coe_injective this
  have hpm : Order.height p = 2 ∨ 1 ≤ Order.coheight p := by
    by_cases hp : p = IsLocalRing.closedPoint A
    · left; rw [hp]; exact hm
    · right
      have hle : p ≤ IsLocalRing.closedPoint A := by
        show p.asIdeal ≤ IsLocalRing.maximalIdeal A
        exact IsLocalRing.le_maximalIdeal p.isPrime.ne_top
      exact le_trans le_add_self (Order.coheight_add_one_le (lt_of_le_of_ne hle hp))
  rw [PrimeSpectrum.height_eq_orderHeight, hdim]
  clear hm hdim hs
  generalize Order.height p = h at *
  generalize Order.coheight p = c at *
  have hc : c ≠ ⊤ := by rintro rfl; simp at hsum
  have hh : h ≠ ⊤ := by rintro rfl; simp at hsum
  lift c to ℕ using hc
  lift h to ℕ using hh
  norm_cast at *
  omega
end ReciprocityTheory.ChartRestriction.G.AI
