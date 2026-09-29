-- Prove2me | solution 1 for ResidualGaloisRep.iSup_range_sub_one_eq_top_and_trace_quotient_eq_zero_of_forall_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e447f6fe-c177-5664-95fa-7599f7a5bc4c

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_iSup_range_sub_one_eq_top_and_trace_quotient_eq_zero_of_forall_stable

set_option autoImplicit false

namespace K1C3CoinvIrr

open Module

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]
variable {G : Type} [Group G]

theorem iSup_range_le (ρ : G →* Module.End k V) (I : Subgroup G) (L : Submodule k V)
    (hI : ∀ τ ∈ I, ∀ v : V, ρ τ v - v ∈ L) :
    (⨆ τ ∈ I, LinearMap.range (ρ τ - 1)) ≤ L := by
  refine iSup₂_le fun τ hτ => ?_
  rintro _ ⟨v, rfl⟩
  simpa using hI τ hτ v

theorem range_le_iSup (ρ : G →* Module.End k V) (I : Subgroup G) {τ : G} (hτ : τ ∈ I) :
    LinearMap.range (ρ τ - 1) ≤ ⨆ τ ∈ I, LinearMap.range (ρ τ - 1) :=
  le_iSup₂_of_le (f := fun τ (_ : τ ∈ I) => LinearMap.range (ρ τ - 1)) τ hτ le_rfl

theorem eq_of_le_of_ne_bot_of_finrank_eq_one [FiniteDimensional k V]
    {W L : Submodule k V} (hWL : W ≤ L) (hW : W ≠ ⊥) (hL : finrank k L = 1) : W = L := by
  refine Submodule.eq_of_le_of_finrank_le hWL ?_
  rw [hL, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  exact hW

theorem iSup_range_eq_of_line [FiniteDimensional k V] (ρ : G →* Module.End k V) (I : Subgroup G)
    (L : Submodule k V) (hL : finrank k L = 1)
    (hI : ∀ τ ∈ I, ∀ v : V, ρ τ v - v ∈ L) (hram : ∃ τ ∈ I, ρ τ ≠ 1) :
    (⨆ τ ∈ I, LinearMap.range (ρ τ - 1)) = L := by
  refine eq_of_le_of_ne_bot_of_finrank_eq_one (iSup_range_le ρ I L hI) ?_ hL
  obtain ⟨τ, hτ, hne⟩ := hram
  intro hbot
  apply hne
  have hr : LinearMap.range (ρ τ - 1) = ⊥ :=
    le_bot_iff.mp (hbot ▸ range_le_iSup ρ I hτ)
  have h0 : ρ τ - 1 = 0 := LinearMap.range_eq_bot.mp hr
  exact sub_eq_zero.mp h0

theorem trace_eq_of_induced_of_sub_smul_mem [FiniteDimensional k V] (W : Submodule k V)
    (φ : Module.End k V) (a : k) (hφ : ∀ v : V, φ v - a • v ∈ W)
    (E : (V ⧸ W) →ₗ[k] (V ⧸ W))
    (hE : ∀ v : V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ v)) :
    LinearMap.trace k (V ⧸ W) E = a * (finrank k (V ⧸ W) : k) := by
  have hEa : E = a • LinearMap.id := by
    refine Submodule.quot_hom_ext _ _ _ fun v => ?_
    rw [hE, LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    exact hφ v
  rw [hEa, map_smul, LinearMap.trace_id, smul_eq_mul]

theorem trace_eq_zero_of_eq_top (W : Submodule k V) (hW : W = ⊤)
    (E : (V ⧸ W) →ₗ[k] (V ⧸ W)) : LinearMap.trace k (V ⧸ W) E = 0 := by
  have hE : E = 0 := by
    refine Submodule.quot_hom_ext _ _ _ fun v => ?_
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective W (E (Submodule.Quotient.mk v))
    rw [← hw, LinearMap.zero_apply, (Submodule.Quotient.mk_eq_zero W).mpr (hW ▸ Submodule.mem_top)]
  rw [hE, map_zero]

theorem map_le_iSup_range (ρ : G →* Module.End k V) (I : Subgroup G) {σ : G}
    (hσ : ∀ τ ∈ I, σ * τ * σ⁻¹ ∈ I) :
    ∀ v ∈ (⨆ τ ∈ I, LinearMap.range (ρ τ - 1)), ρ σ v ∈ ⨆ τ ∈ I, LinearMap.range (ρ τ - 1) := by
  intro v hv
  change v ∈ (⨆ τ ∈ I, LinearMap.range (ρ τ - 1)).comap (ρ σ)
  revert hv v
  change (⨆ τ ∈ I, LinearMap.range (ρ τ - 1)) ≤ (⨆ τ ∈ I, LinearMap.range (ρ τ - 1)).comap (ρ σ)
  refine iSup₂_le fun τ hτ => ?_
  rintro _ ⟨v, rfl⟩
  rw [Submodule.mem_comap]
  have key : ρ σ ((ρ τ - 1) v) = (ρ (σ * τ * σ⁻¹) - 1) (ρ σ v) := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_mul]
    congr 1
    change _ = ρ σ (ρ τ (ρ σ⁻¹ (ρ σ v)))
    rw [← Module.End.mul_apply (ρ σ⁻¹) (ρ σ) v, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  rw [key]
  exact range_le_iSup ρ I (hσ τ hτ) ⟨ρ σ v, rfl⟩

theorem iSup_range_eq_top (ρ : G →* Module.End k V) (I D : Subgroup G)
    (hID : ∀ σ ∈ D, ∀ τ ∈ I, σ * τ * σ⁻¹ ∈ I)
    (hirr : ∀ L : Submodule k V, (∀ σ ∈ D, ∀ v ∈ L, ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤)
    (hram : ∃ τ ∈ I, ρ τ ≠ 1) :
    (⨆ τ ∈ I, LinearMap.range (ρ τ - 1)) = ⊤ := by
  rcases hirr _ (fun σ hσ => map_le_iSup_range ρ I (hID σ hσ)) with hbot | htop
  · exfalso
    obtain ⟨τ, hτ, hne⟩ := hram
    apply hne
    have hr : LinearMap.range (ρ τ - 1) = ⊥ :=
      le_bot_iff.mp (hbot ▸ range_le_iSup ρ I hτ)
    exact sub_eq_zero.mp (LinearMap.range_eq_bot.mp hr)
  · exact htop

end K1C3CoinvIrr

theorem solution
    {k : Type} [Field k] (ρ : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hirr : ∀ L : Submodule k ρ.V,
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤)
    (hram : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ τ ≠ 1) :
    (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)) = ⊤ ∧
    ∀ E : (ρ.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)) →ₗ[k]
        (ρ.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)),
      LinearMap.trace k _ E = 0 := by
  have hID : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      σ * τ * σ⁻¹ ∈ P.inertiaSubgroupIn ℚ := by
    intro σ hσ τ hτ
    obtain ⟨τ', hτ', rfl⟩ := hτ
    refine ⟨⟨σ, hσ⟩ * τ' * ⟨σ, hσ⟩⁻¹, ?_, rfl⟩
    have hN : (P.inertiaSubgroup ℚ).Normal := by
      delta ValuationSubring.inertiaSubgroup; exact MonoidHom.normal_ker _
    exact hN.conj_mem τ' hτ' ⟨σ, hσ⟩
  have hW := K1C3CoinvIrr.iSup_range_eq_top ρ.ρ (P.inertiaSubgroupIn ℚ)
    (P.decompositionSubgroup ℚ) hID hirr hram
  exact ⟨hW, fun E => K1C3CoinvIrr.trace_eq_zero_of_eq_top _ hW E⟩

end S_ResidualGaloisRep_iSup_range_sub_one_eq_top_and_trace_quotient_eq_zero_of_forall_stable
end P2MW
export P2MW.S_ResidualGaloisRep_iSup_range_sub_one_eq_top_and_trace_quotient_eq_zero_of_forall_stable (solution)
