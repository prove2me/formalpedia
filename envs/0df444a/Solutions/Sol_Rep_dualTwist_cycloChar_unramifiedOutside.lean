-- Prove2me | solution 1 for Rep.dualTwist_cycloChar_unramifiedOutside
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9ecbde17-1abf-57d3-884f-cf4dddceb735

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
import Theorems.Thm_IntermediateField_inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_dualTwist_cycloChar_unramifiedOutside

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 3200000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (M.dualTwist (cycloChar p)).ρ g = 1 := by
  have hp : p.Prime := Fact.out
  intro q hqS A hA g hg
  have hqp : (q : ℕ) ≠ p := by
    intro h
    apply hqS
    have : q = pPrime p := Subtype.ext h
    rw [this]
    exact hpS

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure ℚ) (n := p)
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {ζ}
  haveI hF : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional ((hζ.isIntegral hp.pos).tower_top)
  haveI : IsCyclotomicExtension {p} ℚ F :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin p ℚ (AlgebraicClosure ℚ) F hζ).mpr rfl
  haveI : NumberField F := @NumberField.mk _ _ inferInstance hF
  have hdisc : ¬ ((q : ℕ) : ℤ) ∣ NumberField.discr F := by
    rw [IsCyclotomicExtension.Rat.discr_prime p F]
    intro h
    have h1 : ((q : ℕ) : ℤ) ∣ (p : ℤ) ^ (p - 2) :=
      ((isUnit_one.neg.pow _).dvd_mul_left).mp h
    rw [← Int.natCast_pow, Int.natCast_dvd_natCast] at h1
    exact hqp ((Nat.prime_dvd_prime_iff_eq q.prop hp).mp (q.prop.dvd_of_dvd_pow h1))
  have hgF : g ∈ F.fixingSubgroup :=
    IntermediateField.inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr F q q.prop hdisc A hA hg
  have hχ : cycloChar p g = 1 :=
    ExtCitation.cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p g hζ
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hgF ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ))

  have hρ : M.ρ g⁻¹ = 1 := hMur q hqS A hA g⁻¹ ((A.inertiaSubgroupIn ℚ).inv_mem hg)
  apply LinearMap.ext
  intro f
  rw [Rep.dualTwist_ρ_apply, hχ, Units.val_one, one_smul, hρ, Module.End.one_eq_id, LinearMap.comp_id]
  rfl

end S_Rep_dualTwist_cycloChar_unramifiedOutside
end P2MW
export P2MW.S_Rep_dualTwist_cycloChar_unramifiedOutside (solution)
