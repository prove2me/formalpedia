-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.bR_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:10.755319+00:00
-- url     : https://prove2.me/submissions/c69bb330-1f9b-4380-a309-638312579f67

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_prod_pow_unitVector_val
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_bR_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.UnitVectorPowers
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers
theorem _root_.solution (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) (hl : D.κ l ≠ U.φ (D.κ j)) : bR hv D j (e1 l) = 0 := by
  obtain ⟨j'', hj''⟩ : ∃ j'', D.κ j'' = U.φ (D.κ j) := by
    have h := D.card_phi (D.κ j)
    have hpos : 0 < (Finset.univ.filter fun j' => D.κ j' = D.κ j).card :=
      Finset.card_pos.mpr ⟨j, by simp⟩
    rw [← h] at hpos
    obtain ⟨j'', hj''⟩ := Finset.card_pos.mp hpos
    exact ⟨j'', (Finset.mem_filter.mp hj'').2⟩
  obtain ⟨k, hk⟩ := D.sep l j'' (by rw [hj'']; exact hl)
  have he := bR_eig hv hp1 D j k (e1 l)
  rw [prod_pow_unitVector_val, ← hj''] at he
  have h0 : (U.sg (D.κ l) (D.b k) - U.sg (D.κ j'') (D.b k)) * bR hv D j (e1 l) = 0 := by
    rw [sub_mul, he, sub_self]
  have hne : U.sg (D.κ l) (D.b k) - U.sg (D.κ j'') (D.b k) ≠ 0 := by
    intro h0'
    rw [h0', map_zero, map_zero] at hk
    exact zero_ne_one hk
  have h2 := congrArg (algebraMap R C) h0
  rw [map_mul, map_zero] at h2
  have h3 : algebraMap R C (bR hv D j (e1 l)) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (hv.hom_inj (h.trans (map_zero _).symm)) hne
    · exact h
  exact hv.hom_inj (h3.trans (map_zero _).symm)
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
