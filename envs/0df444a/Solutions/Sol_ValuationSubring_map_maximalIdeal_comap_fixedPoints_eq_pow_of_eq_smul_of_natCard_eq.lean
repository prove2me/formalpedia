-- Prove2me | solution 1 for ValuationSubring.map_maximalIdeal_comap_fixedPoints_eq_pow_of_eq_smul_of_natCard_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e4db709c-cbae-5a17-ac93-2098653ddd32

import Mathlib
import Theorems.Thm_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_pow_of_eq_smul_of_natCard_eq

set_option autoImplicit false

open scoped Pointwise

namespace E9B5

theorem isDiscreteValuationRing_of_isPrincipalIdealRing {F : Type*} [Field F] (P : ValuationSubring F)
    (hPIR : IsPrincipalIdealRing ↥P) (x : F) (hx : x ∈ P.nonunits) (hx0 : x ≠ 0) :
    IsDiscreteValuationRing ↥P := by
  classical
  haveI := hPIR
  obtain ⟨hxP, hxm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  have hne : IsLocalRing.maximalIdeal ↥P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hxm
    exact hx0 (congrArg Subtype.val hxm)
  have hexu : ∃! Q : Ideal ↥P, Q ≠ ⊥ ∧ Q.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal ↥P, ⟨hne, inferInstance⟩, fun Q hQ => ?_⟩
    haveI := hQ.2
    exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hQ.1)
  exact (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime ↥P).mpr ⟨hPIR, hexu⟩

end E9B5

namespace B5

section Generic

variable {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F]

theorem TRUNK_mem_nonunits_iff (P : ValuationSubring F) (x : F) :
    x ∈ P.nonunits ↔ ∃ hx : x ∈ P, ¬ IsUnit (⟨x, hx⟩ : ↥P) := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  rfl

theorem TRUNK_exists_ringEquiv_smul (P : ValuationSubring F) (g : G) :
    ∃ e : ↥P ≃+* ↥(g • P), (∀ x : ↥P, ((e x : ↥(g • P)) : F) = g • (x : F)) ∧
      ∀ y : ↥(g • P), ((e.symm y : ↥P) : F) = g⁻¹ • (y : F) := by
  refine ⟨{ toFun := fun x => ⟨g • (x : F), ValuationSubring.smul_mem_pointwise_smul g _ P x.2⟩
            invFun := fun y => ⟨g⁻¹ • (y : F), ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp y.2⟩
            left_inv := fun x => Subtype.ext (inv_smul_smul g (x : F))
            right_inv := fun y => Subtype.ext (smul_inv_smul g (y : F))
            map_mul' := fun a b => Subtype.ext (smul_mul' g (a : F) (b : F))
            map_add' := fun a b => Subtype.ext (smul_add g (a : F) (b : F)) }, fun _ => rfl, fun _ => rfl⟩

theorem TRUNK_smul_mem_nonunits_smul (P : ValuationSubring F) (g : G) {x : F} (hx : x ∈ P.nonunits) :
    g • x ∈ (g • P).nonunits := by
  classical
  obtain ⟨e, he, he'⟩ := TRUNK_exists_ringEquiv_smul P g
  rw [TRUNK_mem_nonunits_iff] at hx ⊢
  obtain ⟨hxP, hu⟩ := hx
  refine ⟨ValuationSubring.smul_mem_pointwise_smul g x P hxP, fun hu' => hu ?_⟩
  have h1 : e ⟨x, hxP⟩ = ⟨g • x, ValuationSubring.smul_mem_pointwise_smul g x P hxP⟩ := Subtype.ext (he _)
  rw [← h1] at hu'
  simpa using hu'.map e.symm

theorem TRUNK_natCard_inertia_smul (P : ValuationSubring F) (g : G) :
    Nat.card {h : G // h • (g • P) = g • P ∧ ∀ e : ↥(g • P), h • (e : F) - e ∈ (g • P).nonunits} =
      Nat.card {h : G // h • P = P ∧ ∀ e : ↥P, h • (e : F) - e ∈ P.nonunits} := by
  classical

  have key : ∀ (g : G) (P : ValuationSubring F) (h : G), (h • P = P ∧ ∀ e : ↥P, h • (e : F) - e ∈ P.nonunits) →
      ((g * h * g⁻¹) • (g • P) = g • P ∧ ∀ e : ↥(g • P), (g * h * g⁻¹) • (e : F) - e ∈ (g • P).nonunits) := by
    rintro g P h ⟨h1, h2⟩
    refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, h1], fun e => ?_⟩
    have he : g⁻¹ • (e : F) ∈ P := ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp e.2
    have hcalc : (g * h * g⁻¹) • (e : F) - e = g • (h • (g⁻¹ • (e : F)) - g⁻¹ • (e : F)) := by
      rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
    rw [hcalc]
    exact TRUNK_smul_mem_nonunits_smul P g (h2 ⟨g⁻¹ • (e : F), he⟩)
  refine Nat.card_congr
    { toFun := fun h => ⟨g⁻¹ * h.1 * g⁻¹⁻¹, by
        have := key g⁻¹ (g • P) h.1 h.2
        rwa [inv_smul_smul] at this⟩
      invFun := fun h => ⟨g * h.1 * g⁻¹, key g P h.1 h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc]) }

theorem TRUNK_comap_smul_eq (P : ValuationSubring F) (g : G) :
    (g • P).comap (FixedPoints.subfield G F).subtype = P.comap (FixedPoints.subfield G F).subtype := by
  ext e
  show ((e : F) ∈ g • P) ↔ ((e : F) ∈ P)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have : g⁻¹ • (e : F) = e := e.2 g⁻¹
  rw [this]

theorem TRUNK_isDiscreteValuationRing_smul (P : ValuationSubring F) [IsDiscreteValuationRing ↥P] (g : G) :
    IsDiscreteValuationRing ↥(g • P) := by
  classical
  obtain ⟨e, he, -⟩ := TRUNK_exists_ringEquiv_smul P g
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥P
  have hPIR : IsPrincipalIdealRing ↥(g • P) := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  refine E9B5.isDiscreteValuationRing_of_isPrincipalIdealRing (g • P) hPIR (g • (ϖ : F)) ?_ ?_
  · apply TRUNK_smul_mem_nonunits_smul
    rw [TRUNK_mem_nonunits_iff]
    exact ⟨ϖ.2, by simpa using hϖ.not_isUnit⟩
  · intro h0
    apply hϖ.ne_zero
    have : (ϖ : F) = 0 := by simpa using congrArg (g⁻¹ • ·) h0
    exact Subtype.ext this

theorem TRUNK_map_maximalIdeal_eq_of_coe_eq {S : Subfield F} (Q : ValuationSubring F)
    (R₁ R₂ : ValuationSubring ↥S) (h12 : R₁ = R₂)
    (j₁ : ↥R₁ →+* ↥Q) (j₂ : ↥R₂ →+* ↥Q)
    (hj₁ : ∀ r, ((j₁ r : ↥Q) : F) = ((r : ↥S) : F)) (hj₂ : ∀ r, ((j₂ r : ↥Q) : F) = ((r : ↥S) : F)) :
    Ideal.map j₁ (IsLocalRing.maximalIdeal ↥R₁) = Ideal.map j₂ (IsLocalRing.maximalIdeal ↥R₂) := by
  subst h12
  have : j₁ = j₂ := RingHom.ext fun r => Subtype.ext (by rw [hj₁, hj₂])
  rw [this]

end Generic

end B5

open B5 in
theorem solution
    {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F] [Fintype G] [FaithfulSMul G F]
    (P : ValuationSubring F) [IsDiscreteValuationRing ↥P]
    [PerfectField (IsLocalRing.ResidueField ↥(P.comap (FixedPoints.subfield G F).subtype))]
    (n : ℕ) (hn : Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} = n) :
    ∀ (g : G) (Q : ValuationSubring F), Q = g • P →
      ∀ (j : ↥(P.comap (FixedPoints.subfield G F).subtype) →+* ↥Q),
      (∀ r, ((j r : ↥Q) : F) = ((r : ↥(FixedPoints.subfield G F)) : F)) →
      Ideal.map j (IsLocalRing.maximalIdeal ↥(P.comap (FixedPoints.subfield G F).subtype))
        = IsLocalRing.maximalIdeal ↥Q ^ n := by
  classical
  intro g Q hQ jm hjm
  subst hQ
  haveI : IsDiscreteValuationRing ↥(g • P) := TRUNK_isDiscreteValuationRing_smul P g
  have hQP := TRUNK_comap_smul_eq (G := G) P g
  haveI : PerfectField (IsLocalRing.ResidueField ↥((g • P).comap (FixedPoints.subfield G F).subtype)) := by
    rw [hQP]; infer_instance
  have h := ValuationSubring.map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia (G := G) (g • P)
  rw [TRUNK_natCard_inertia_smul, hn] at h
  rw [← h]
  exact TRUNK_map_maximalIdeal_eq_of_coe_eq (g • P) _ _ hQP.symm jm _ hjm (fun _ => rfl)

end S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_pow_of_eq_smul_of_natCard_eq
end P2MW
export P2MW.S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_pow_of_eq_smul_of_natCard_eq (solution)
