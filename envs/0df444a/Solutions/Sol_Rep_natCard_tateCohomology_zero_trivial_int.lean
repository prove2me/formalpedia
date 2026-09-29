-- Prove2me | solution 1 for Rep.natCard_tateCohomology_zero_trivial_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e81f06c5-628c-5af6-8b56-f91bbf7e2d60

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_natCard_tateCohomology_zero_trivial_int

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {G : Type} [Group G] [Fintype G] :
    Nat.card ((Rep.trivial ℤ G ℤ).tateCohomology 0) = Fintype.card G := by

  let Z := Rep.trivial ℤ G ℤ
  have hinv : ∀ n : ℤ, n ∈ Z.ρ.invariants := fun n =>
    (Representation.mem_invariants _ _).2 fun g => Representation.isTrivial_apply _ g n
  have hnorm : ∀ n : ℤ, Z.ρ.norm n = (Fintype.card G : ℤ) * n := fun n => by
    simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun g _ => Representation.isTrivial_apply Z.ρ g n, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]

  let ψ : ℤ →+ Z.tateH0 :=
    { toFun := fun n => Submodule.Quotient.mk ⟨n, hinv n⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨n, hn⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨n, rfl⟩
  have hker : ψ.ker = AddSubgroup.zmultiples (Fintype.card G : ℤ) := by
    ext n
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_zmultiples_iff]
    change Submodule.Quotient.mk (⟨n, hinv n⟩ : Z.ρ.invariants) = (0 : Z.tateH0) ↔ _
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      refine ⟨m, ?_⟩
      have := congrArg Subtype.val hc
      change Z.ρ.norm m = n at this
      rw [← this, hnorm, smul_eq_mul, mul_comm]
    · rintro ⟨m, rfl⟩
      refine ⟨Submodule.Quotient.mk m, Subtype.ext ?_⟩
      change Z.ρ.norm m = m • (Fintype.card G : ℤ)
      rw [hnorm, smul_eq_mul, mul_comm]
  have e : ℤ ⧸ AddSubgroup.zmultiples (Fintype.card G : ℤ) ≃+ Z.tateH0 :=
    (QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ)
  change Nat.card Z.tateH0 = _
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr (Int.quotientZMultiplesNatEquivZMod (Fintype.card G)).toEquiv,
    Nat.card_zmod]

end S_Rep_natCard_tateCohomology_zero_trivial_int
end P2MW
export P2MW.S_Rep_natCard_tateCohomology_zero_trivial_int (solution)
