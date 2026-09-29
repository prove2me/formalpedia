-- Prove2me | solution 1 for ValuationSubring.exists_isDiscreteValuationRing_isFractionRing_ratClosure_finite_residueField_and_irreducible_natCast_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8f1ccad3-db44-5d30-99e5-2aca0c5e509d

import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_isFractionRing_ratClosure_finite_residueField_and_irreducible_natCast_of_liesOverPrime

set_option autoImplicit false

open ValuationSubring

namespace PR0

variable (A : ValuationSubring (AlgebraicClosure ℚ))

noncomputable abbrev O₀ : ValuationSubring ↥(ratClosure A) := (Valued.v.comap (ratClosure A).subtype).valuationSubring

theorem mem_O₀_iff (x : ↥(ratClosure A)) :
    x ∈ O₀ A ↔ Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1 := by
  show x ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring ↔ _
  rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply]
  rfl

theorem range_algebraMap_O₀ (x : ↥(ratClosure A)) :
    x ∈ Set.range (algebraMap ↥(O₀ A) ↥(ratClosure A)) ↔
      Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1 := by
  rw [← mem_O₀_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro hx; exact ⟨⟨x, hx⟩, rfl⟩

end PR0

open PR0 in
theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsDiscreteValuationRing R₀)
      (_ : Algebra R₀ ↥(ratClosure A)) (_ : IsFractionRing R₀ ↥(ratClosure A))
      (_ : Finite (IsLocalRing.ResidueField R₀)),
      (∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔
          Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1) ∧
      Irreducible ((r : ℕ) : R₀) := by
  obtain ⟨hmem, hdvr, hrest⟩ :=
    ValuationSubring.isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime
      r A hA
  obtain ⟨hirr, hfin, -⟩ := hrest hmem
  haveI : IsDiscreteValuationRing ↥(O₀ A) := hdvr

  have hcast : (⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), hmem⟩ :
      ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring) = ((r : ℕ) : ↥(O₀ A)) := by
    apply Subtype.ext; apply Subtype.ext
    simp
  rw [hcast] at hirr hfin
  have hmax : IsLocalRing.maximalIdeal ↥(O₀ A) = Ideal.span {((r : ℕ) : ↥(O₀ A))} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr
  have hfinRes : Finite (IsLocalRing.ResidueField ↥(O₀ A)) := by
    haveI := hfin
    exact Finite.of_equiv _ (Ideal.quotEquivOfEq hmax.symm).toEquiv
  exact ⟨↥(O₀ A), inferInstance, inferInstance, hdvr, inferInstance, inferInstance, hfinRes,
    range_algebraMap_O₀ A, hirr⟩

end S_ValuationSubring_exists_isDiscreteValuationRing_isFractionRing_ratClosure_finite_residueField_and_irreducible_natCast_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_isFractionRing_ratClosure_finite_residueField_and_irreducible_natCast_of_liesOverPrime (solution)
