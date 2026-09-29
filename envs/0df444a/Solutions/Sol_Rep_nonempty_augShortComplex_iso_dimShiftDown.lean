-- Prove2me | solution 1 for Rep.nonempty_augShortComplex_iso_dimShiftDown
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c40a08df-ef54-587e-939d-3420ce25a4c7

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_SplittingModule
import Theorems.Thm_Rep_indBot_rho_indBotMk
import Theorems.Thm_Rep_indBotPi_indBotMk
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_augShortComplex_iso_dimShiftDown

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace P2mS26A11
p2m_open "Representation TensorProduct Representation.TensorProduct"

variable {k G : Type*} [CommRing k] [Group G]

section model
variable {A : Type*} [AddCommGroup A] [Module k A] (ρ : Representation k (⊥ : Subgroup G) A)

lemma ker_tprod_bot_eq_bot :
    Representation.Coinvariants.ker (V := MonoidAlgebra k G ⊗[k] A)
      (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ) = ⊥ := by
  rw [Representation.Coinvariants.ker, Submodule.span_eq_bot]
  rintro _ ⟨⟨g, v⟩, rfl⟩
  have hg : g = 1 := Subsingleton.elim _ _
  simp [hg]

noncomputable def E [DecidableEq G] : (G →₀ A) ≃ₗ[k] Representation.IndV (⊥ : Subgroup G).subtype ρ :=
  (finsuppScalarLeft k A G).symm.trans <|
    (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k).symm (LinearEquiv.refl k A)).trans
      ((Submodule.quotEquivOfEqBot _ (ker_tprod_bot_eq_bot ρ)).symm :
      (MonoidAlgebra k G ⊗[k] A) ≃ₗ[k] Representation.Coinvariants (V := MonoidAlgebra k G ⊗[k] A)
        (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ))

lemma E_single [DecidableEq G] (g : G) (a : A) :
    E ρ (Finsupp.single g a) = Representation.IndV.mk (⊥ : Subgroup G).subtype ρ g a := by
  rw [E, LinearEquiv.trans_apply, finsuppScalarLeft_symm_apply_single, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul]
  rfl

end model
end P2mS26A11

theorem solution (k G : Type u) [CommRing k] [Group G] :
    Nonempty (Rep.augShortComplex k G ≅ (Rep.trivial k G k).dimShiftDown) := by
  classical
  let T : Rep.{u} k G := Rep.trivial k G k
  let ρ₀ : Representation k (⊥ : Subgroup G) k := (Rep.res (⊥ : Subgroup G).subtype T).ρ

  let Φ : (G →₀ k) ≃ₗ[k] T.indBot := (Finsupp.domLCongr (Equiv.inv G)).trans (P2mS26A11.E (G := G) ρ₀)
  have hΦ_single : ∀ (g : G) (a : k), Φ (Finsupp.single g a) = T.indBotMk g⁻¹ a := fun g a => by
    change P2mS26A11.E ρ₀ (Finsupp.domLCongr (Equiv.inv G) (Finsupp.single g a)) = _
    rw [Finsupp.domLCongr_single, Equiv.inv_apply, P2mS26A11.E_single]
    rfl
  have hreg : ∀ (g h : G) (a : k), (Rep.leftRegularFinsupp k G).ρ g (Finsupp.single h a) = Finsupp.single (g * h) a :=
    fun g h a => by
      change Finsupp.lmapDomain k k (g * ·) (Finsupp.single h a) = _
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  have hequiv : ∀ g : G, Φ.toLinearMap ∘ₗ (Rep.leftRegularFinsupp k G).ρ g = T.indBot.ρ g ∘ₗ Φ.toLinearMap := by
    intro g
    apply Finsupp.lhom_ext
    intro h a
    change Φ ((Rep.leftRegularFinsupp k G).ρ g (Finsupp.single h a)) = T.indBot.ρ g (Φ (Finsupp.single h a))
    rw [hreg, hΦ_single, hΦ_single, Rep.indBot_rho_indBotMk, mul_inv_rev]
  have hequiv' : ∀ (g : G) (f : G →₀ k), Φ ((Rep.leftRegularFinsupp k G).ρ g f) = T.indBot.ρ g (Φ f) := fun g f =>
    LinearMap.congr_fun (hequiv g) f
  have hequiv_symm : ∀ g : G, Φ.symm.toLinearMap ∘ₗ T.indBot.ρ g = (Rep.leftRegularFinsupp k G).ρ g ∘ₗ Φ.symm.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨f, rfl⟩ := Φ.surjective y
    change Φ.symm (T.indBot.ρ g (Φ f)) = (Rep.leftRegularFinsupp k G).ρ g (Φ.symm (Φ f))
    rw [← hequiv', Φ.symm_apply_apply, Φ.symm_apply_apply]

  let e₂ : Rep.leftRegularFinsupp k G ≅ T.indBot :=
    { hom := Rep.ofHom ⟨Φ.toLinearMap, hequiv⟩
      inv := Rep.ofHom ⟨Φ.symm.toLinearMap, hequiv_symm⟩
      hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => Φ.symm_apply_apply f))
      inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun y => Φ.apply_symm_apply y)) }

  have hcompat : (Rep.indBotπ T).hom.toLinearMap ∘ₗ Φ.toLinearMap = (Rep.augε k G).hom.toLinearMap := by
    apply Finsupp.lhom_ext
    intro h a
    change (Rep.indBotπ T).hom (Φ (Finsupp.single h a)) = (Rep.augε k G).hom (Finsupp.single h a)
    rw [hΦ_single, Rep.indBotPi_indBotMk, inv_inv, Rep.leftRegularHomFinsupp_hom_single, Rep.trivial_ρ_apply,
      Rep.trivial_ρ_apply, smul_eq_mul, mul_one]
  have hcompat' : ∀ f : G →₀ k, (Rep.indBotπ T).hom (Φ f) = (Rep.augε k G).hom f := fun f =>
    LinearMap.congr_fun hcompat f

  have hker : (LinearMap.ker (Rep.augε k G).hom.toLinearMap).map (Φ : (G →₀ k) →ₗ[k] T.indBot)
      = LinearMap.ker (Rep.indBotπ T).hom.toLinearMap := by
    rw [← hcompat, LinearMap.ker_comp]
    exact Submodule.map_comap_eq_of_surjective Φ.surjective _
  let e₁lin : Rep.augIdeal k G ≃ₗ[k] T.dimShiftDownObj :=
    (Φ.submoduleMap (LinearMap.ker (Rep.augε k G).hom.toLinearMap)).trans (LinearEquiv.ofEq _ _ hker)
  have he₁ : ∀ x : Rep.augIdeal k G, ((e₁lin x : T.dimShiftDownObj) : T.indBot) = Φ (x : G →₀ k) := fun x =>
    LinearEquiv.submoduleMap_apply Φ _ x
  have he₁equiv : ∀ g : G, e₁lin.toLinearMap ∘ₗ (Rep.augIdeal k G).ρ g = T.dimShiftDownObj.ρ g ∘ₗ e₁lin.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((e₁lin ((Rep.augIdeal k G).ρ g x) : T.dimShiftDownObj) : T.indBot) = T.indBot.ρ g ((e₁lin x : T.dimShiftDownObj) : T.indBot)
    rw [he₁, he₁, Rep.coe_augIdeal_ρ_apply, ← hequiv']
    rfl
  have he₁equiv' : ∀ (g : G) (x : Rep.augIdeal k G), e₁lin ((Rep.augIdeal k G).ρ g x) = T.dimShiftDownObj.ρ g (e₁lin x) :=
    fun g x => LinearMap.congr_fun (he₁equiv g) x
  have he₁equiv_symm : ∀ g : G, e₁lin.symm.toLinearMap ∘ₗ T.dimShiftDownObj.ρ g = (Rep.augIdeal k G).ρ g ∘ₗ e₁lin.symm.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e₁lin.surjective y
    change e₁lin.symm (T.dimShiftDownObj.ρ g (e₁lin x)) = (Rep.augIdeal k G).ρ g (e₁lin.symm (e₁lin x))
    rw [← he₁equiv', e₁lin.symm_apply_apply, e₁lin.symm_apply_apply]
  let e₁ : Rep.augIdeal k G ≅ T.dimShiftDownObj :=
    { hom := Rep.ofHom ⟨e₁lin.toLinearMap, he₁equiv⟩
      inv := Rep.ofHom ⟨e₁lin.symm.toLinearMap, he₁equiv_symm⟩
      hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => e₁lin.symm_apply_apply x))
      inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun y => e₁lin.apply_symm_apply y)) }
  refine ⟨ShortComplex.isoMk e₁ e₂ (Iso.refl _) ?_ ?_⟩
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact he₁ x
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    change (Rep.indBotπ T).hom (Φ f) = (Rep.augε k G).hom f
    exact hcompat' f

end

end S_Rep_nonempty_augShortComplex_iso_dimShiftDown
end P2MW
export P2MW.S_Rep_nonempty_augShortComplex_iso_dimShiftDown (solution)
