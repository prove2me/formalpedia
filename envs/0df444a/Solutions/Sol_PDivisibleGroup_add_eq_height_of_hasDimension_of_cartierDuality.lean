-- Prove2me | solution 1 for PDivisibleGroup.add_eq_height_of_hasDimension_of_cartierDuality
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3fc83dfc-2a17-5a67-b967-ce5f546ede59

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PDivisibleGroup_BaseChange
import Theorems.Thm_PDivisibleGroup_cotangentBaseChange_bijective
import Theorems.Thm_PDivisibleGroup_IsCartierDual_baseChange
import Theorems.Thm_PDivisibleGroup_CartierDuality_finrank_cotangent_one_add_finrank_cotangent_one_eq_height
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_add_eq_height_of_hasDimension_of_cartierDuality
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

open scoped TensorProduct

namespace PDivProp3

variable {R : Type} [CommRing R] [IsLocalRing R]

local notation "k" => IsLocalRing.ResidueField R

theorem finrank_tensor_quotient {J : Ideal R} (hJ : J ≤ IsLocalRing.maximalIdeal R) :
    Module.finrank k (k ⊗[R] (R ⧸ J)) = 1 := by
  have hmap : J.map (algebraMap R k) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact hJ hx
  have e : (k ⧸ J.map (algebraMap R k)) ≃ₗ[k] k ⊗[R] (R ⧸ J) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot k J).toLinearEquiv
  rw [← e.finrank_eq]
  have e' : (k ⧸ J.map (algebraMap R k)) ≃ₗ[k] k :=
    Submodule.quotEquivOfEqBot _ (by rw [hmap])
  rw [e'.finrank_eq, Module.finrank_self]

theorem finrank_tensor_pi_quotient {J : Ideal R} (hJ : J ≤ IsLocalRing.maximalIdeal R) (n : ℕ) :
    Module.finrank k (k ⊗[R] (Fin n → R ⧸ J)) = n := by
  rw [(TensorProduct.piRight R k k (fun _ : Fin n => R ⧸ J)).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, finrank_tensor_quotient hJ, smul_eq_mul]
  exact mul_one n

variable {p h : ℕ}

theorem finrank_cotangent_baseChange_one (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (G : PDivisibleGroup R p h) {n : ℕ} (hn : G.HasDimension n) :
    Module.finrank k ((G.baseChange k).Cotangent 1) = n := by

  have e1 : (k ⊗[R] G.Cotangent 1) ≃ₗ[k]
      (PDivisibleGroup.Hopf.augIdeal k (k ⊗[R] G.level 1)).Cotangent :=
    LinearEquiv.ofBijective (G.cotangentBaseChange k 1) (G.cotangentBaseChange_bijective k 1)
  have e2 : (k ⊗[R] G.Cotangent 1) ≃ₗ[k] (k ⊗[R] (Fin n → R ⧸ Ideal.span {(p : R) ^ 1})) :=
    (hn 1).some.baseChange R k _ _
  change Module.finrank k (PDivisibleGroup.Hopf.augIdeal k (k ⊗[R] G.level 1)).Cotangent = n
  rw [← e1.finrank_eq, e2.finrank_eq]
  refine finrank_tensor_pi_quotient ?_ n
  rw [pow_one, Ideal.span_le, Set.singleton_subset_iff]
  exact hp

end PDivProp3

open PDivProp3 in
theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {p h : ℕ} [Fact p.Prime] (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G') {n n' : ℕ}
    (hn : G.HasDimension n) (hn' : G'.HasDimension n') : n + n' = h := by

  haveI : CharP (IsLocalRing.ResidueField R) p := by
    rw [CharP.charP_iff_prime_eq_zero Fact.out]
    rw [← map_natCast (algebraMap R (IsLocalRing.ResidueField R)) p,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact hp

  obtain ⟨Dk⟩ := PDivisibleGroup.IsCartierDual.baseChange (⟨D⟩ : G.IsCartierDual G')
    (IsLocalRing.ResidueField R)
  have hsum := Dk.finrank_cotangent_one_add_finrank_cotangent_one_eq_height
  rwa [finrank_cotangent_baseChange_one hp G hn, finrank_cotangent_baseChange_one hp G' hn'] at hsum

end S_PDivisibleGroup_add_eq_height_of_hasDimension_of_cartierDuality
end P2MW
export P2MW.S_PDivisibleGroup_add_eq_height_of_hasDimension_of_cartierDuality (solution)
