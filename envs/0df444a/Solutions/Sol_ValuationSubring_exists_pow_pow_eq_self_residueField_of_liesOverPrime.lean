-- Prove2me | solution 1 for ValuationSubring.exists_pow_pow_eq_self_residueField_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e7f00902-191a-5c21-b5f3-850935a75a3a

import Mathlib
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
set_option autoImplicit false

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q)
    (a : IsLocalRing.ResidueField A) :
    ∃ r : ℕ, 0 < r ∧ a ^ q ^ r = a := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (IsLocalRing.ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have halg : IsAlgebraic (ZMod q) (IsLocalRing.residue A a₀) := ValuationSubring.isAlgebraic_residue A hq a₀
  have hint : IsIntegral (ZMod q) (IsLocalRing.residue A a₀) := halg.isIntegral
  set x : IsLocalRing.ResidueField A := IsLocalRing.residue A a₀ with hxdef
  haveI : FiniteDimensional (ZMod q) ↥(IntermediateField.adjoin (ZMod q) ({x} : Set (IsLocalRing.ResidueField A))) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite ↥(IntermediateField.adjoin (ZMod q) ({x} : Set (IsLocalRing.ResidueField A))) :=
    Module.finite_of_finite (ZMod q)
  letI : Fintype ↥(IntermediateField.adjoin (ZMod q) ({x} : Set (IsLocalRing.ResidueField A))) := Fintype.ofFinite _
  refine ⟨Module.finrank (ZMod q) ↥(IntermediateField.adjoin (ZMod q) ({x} : Set (IsLocalRing.ResidueField A))),
    Module.finrank_pos, ?_⟩
  have hmem : x ∈ IntermediateField.adjoin (ZMod q) ({x} : Set (IsLocalRing.ResidueField A)) :=
    IntermediateField.mem_adjoin_simple_self (ZMod q) x
  have h := FiniteField.pow_card (⟨x, hmem⟩ : ↥(IntermediateField.adjoin (ZMod q) ({x} : Set (IsLocalRing.ResidueField A))))
  rw [Module.card_eq_pow_finrank (K := ZMod q), ZMod.card] at h
  have h' := congrArg (fun z : ↥(IntermediateField.adjoin (ZMod q) ({x} : Set (IsLocalRing.ResidueField A))) =>
    (z : IsLocalRing.ResidueField A)) h
  simp only [SubmonoidClass.coe_pow] at h'
  exact h'

end S_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime (solution)
