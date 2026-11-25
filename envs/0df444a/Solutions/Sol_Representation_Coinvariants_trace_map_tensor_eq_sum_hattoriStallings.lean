-- Prove2me | solution 1 for Representation.Coinvariants.trace_map_tensor_eq_sum_hattoriStallings
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T10:01:36.181972+00:00
-- url     : https://prove2.me/submissions/04d192d1-ccbd-4df2-b322-32fe68535d0f

import Mathlib
import Definitions.Def_RPLib_F2_025

set_option autoImplicit false

theorem solution
    (R G P M : Type) [CommRing R] [Group G] [Fintype G] [DecidableEq G]
    [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (ρ : Representation R G P) (τ : Representation R G M)
    [Module.Free R (Representation.Coinvariants (ρ.tprod τ))]
    (E : P →ₗ[R] P) (hE : ∑ h : G, ρ h ∘ₗ E ∘ₗ ρ h⁻¹ = LinearMap.id)
    (φ : ρ.IntertwiningMap ρ) (ψ : τ.IntertwiningMap τ)
    (hs : ConjClasses G → R)
    (hhs : ∀ c, hs c = ∑ g : G with ConjClasses.mk g = c,
      LinearMap.trace R P (ρ g⁻¹ ∘ₗ φ.toLinearMap ∘ₗ E)) :
    (∀ r : ConjClasses G → G, (∀ c, ConjClasses.mk (r c) = c) →
      LinearMap.trace R (Representation.Coinvariants (ρ.tprod τ))
          (Representation.Coinvariants.map (ρ.tprod τ) (ρ.tprod τ) (φ.tensor ψ)) =
        ∑ c : ConjClasses G, hs c * LinearMap.trace R M (τ (r c)⁻¹ ∘ₗ ψ.toLinearMap)) ∧
    (∀ γ : G, LinearMap.trace R P (ρ γ⁻¹ ∘ₗ φ.toLinearMap) =
      (Nat.card (Subgroup.centralizer {γ}) : R) * hs (ConjClasses.mk γ)) ∧
    (∀ E' : P →ₗ[R] P, ∑ h : G, ρ h ∘ₗ E' ∘ₗ ρ h⁻¹ = LinearMap.id →
      ∀ c, hs c = ∑ g : G with ConjClasses.mk g = c,
        LinearMap.trace R P (ρ g⁻¹ ∘ₗ φ.toLinearMap ∘ₗ E')) := by
  classical
  have hHig : RamanujanPetersson.HattoriStallings.IsHigman ρ E := hE
  have hφ : RamanujanPetersson.HattoriStallings.IsEquivariant ρ ρ φ.toLinearMap :=
    fun g => φ.isIntertwining' g
  have hψ : RamanujanPetersson.HattoriStallings.IsEquivariant τ τ ψ.toLinearMap :=
    fun g => ψ.isIntertwining' g
  have hsum : ∀ (E' : P →ₗ[R] P) (c : ConjClasses G),
      (∑ g : G with ConjClasses.mk g = c, LinearMap.trace R P (ρ g⁻¹ ∘ₗ φ.toLinearMap ∘ₗ E')) =
        RamanujanPetersson.HattoriStallings.classSum
          (RamanujanPetersson.HattoriStallings.hsFun ρ E' φ.toLinearMap) c := by
    intro E' c
    rw [RamanujanPetersson.HattoriStallings.classSum_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases h : ConjClasses.mk g = c
    · simp only [h, if_true]
      rfl
    · simp only [h, if_false]
  have hsE : ∀ c, hs c = RamanujanPetersson.HattoriStallings.classSum
      (RamanujanPetersson.HattoriStallings.hsFun ρ E φ.toLinearMap) c := fun c => by
    rw [hhs c, hsum E c]
  refine ⟨fun r hr => ?_, fun γ => ?_, fun E' hE' c => ?_⟩
  · have e : Representation.Coinvariants.map (ρ.tprod τ) (ρ.tprod τ) (φ.tensor ψ) =
        RamanujanPetersson.HattoriStallings.coinvMap (Representation.tprod ρ τ)
          (TensorProduct.map φ.toLinearMap ψ.toLinearMap)
          (RamanujanPetersson.HattoriStallings.isEquivariant_tensorMap hφ hψ) :=
      Representation.Coinvariants.hom_ext (LinearMap.ext fun x => rfl)
    rw [e, RamanujanPetersson.HattoriStallings.trace_coinvMap_tprod hHig hφ hψ]
    have hχ : ∀ g : G, LinearMap.trace R M (τ (r (ConjClasses.mk g))⁻¹ ∘ₗ ψ.toLinearMap) =
        LinearMap.trace R M (τ g⁻¹ ∘ₗ ψ.toLinearMap) := by
      intro g
      obtain ⟨k, hk⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 (hr (ConjClasses.mk g)))
      calc LinearMap.trace R M (τ (r (ConjClasses.mk g))⁻¹ ∘ₗ ψ.toLinearMap)
          = LinearMap.trace R M (τ (k * r (ConjClasses.mk g) * k⁻¹)⁻¹ ∘ₗ ψ.toLinearMap) :=
            (RamanujanPetersson.HattoriStallings.trace_inv_comp_conj hψ k _).symm
        _ = LinearMap.trace R M (τ g⁻¹ ∘ₗ ψ.toLinearMap) := by rw [hk]
    rw [RamanujanPetersson.HattoriStallings.sum_mul_eq_sum_classSum _ _
      (fun c => LinearMap.trace R M (τ (r c)⁻¹ ∘ₗ ψ.toLinearMap)) hχ]
    exact Finset.sum_congr rfl fun c _ => by rw [hsE c]
  · rw [RamanujanPetersson.HattoriStallings.trace_inv_comp_eq_sum hHig hφ γ,
      RamanujanPetersson.HattoriStallings.sum_conj_eq_card_mul_classSum, hsE]
    have hc : Nat.card {z : G // z⁻¹ * γ * z = γ} = Nat.card (Subgroup.centralizer {γ}) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
      rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, inv_mul_eq_iff_eq_mul]
      exact eq_comm
    rw [hc]
  · have hE'' : RamanujanPetersson.HattoriStallings.IsHigman ρ E' := hE'
    rw [hsE c, hsum E' c, ← RamanujanPetersson.HattoriStallings.hs_eq hHig hφ,
      ← RamanujanPetersson.HattoriStallings.hs_eq hE'' hφ]
