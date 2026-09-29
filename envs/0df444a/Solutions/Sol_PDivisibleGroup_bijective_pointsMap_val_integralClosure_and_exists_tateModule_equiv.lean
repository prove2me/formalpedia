-- Prove2me | solution 1 for PDivisibleGroup.bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7fbe2bbc-3826-5aae-918a-7481cb1099e5

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv

set_option autoImplicit false

open PDivisibleGroup

namespace PDivIntegralPoints

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
variable (L : Type) [CommRing L] [Algebra R L]

noncomputable abbrev O (R : Type) [CommRing R] (L : Type) [CommRing L] [Algebra R L] : Subalgebra R L :=
  integralClosure R L

theorem apply_mem_integralClosure (v : ℕ) (f : G.level v →ₐ[R] L) (a : G.level v) :
    f a ∈ integralClosure R L :=
  (mem_integralClosure_iff (R := R) (A := L)).mpr ((Algebra.IsIntegral.isIntegral (R := R) a).map f)

noncomputable def cores (v : ℕ) (f : G.level v →ₐ[R] L) : G.level v →ₐ[R] O R L :=
  f.codRestrict (O R L) (apply_mem_integralClosure G L v f)

theorem val_comp_cores (v : ℕ) (f : G.level v →ₐ[R] L) : (O R L).val.comp (cores G L v f) = f :=
  AlgHom.ext fun _ => rfl

theorem pointMap_val_surjective (v : ℕ) : Function.Surjective (G.pointMap (O R L).val v) := by
  intro f
  refine ⟨Point.ofAlgHom (cores G L v (Point.toAlgHom f)), Point.ext fun a => ?_⟩
  rfl

theorem pointsMap_val_injective : Function.Injective (G.pointsMap (O R L).val) :=
  G.pointsMap_injective_of_injective _ Subtype.val_injective

theorem pointsMap_val_surjective : Function.Surjective (G.pointsMap (O R L).val) := by
  intro z
  obtain ⟨v, f, rfl⟩ := Points.exists_mkAdd G z
  obtain ⟨g, rfl⟩ := pointMap_val_surjective G L v f
  exact ⟨G.pointsMkAdd (O R L) v (Additive.ofMul g), G.pointsMap_pointsMkAdd _ v g⟩

theorem pointsMap_val_bijective : Function.Bijective (G.pointsMap (O R L).val) :=
  ⟨pointsMap_val_injective G L, pointsMap_val_surjective G L⟩

variable (R) in

noncomputable def restrict (σ : L ≃ₐ[R] L) : O R L ≃ₐ[R] O R L :=
  (σ.subalgebraMap (O R L)).trans (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv σ))

variable (R) in
@[scoped simp] theorem coe_restrict (σ : L ≃ₐ[R] L) (x : O R L) : ((restrict R L σ x : O R L) : L) = σ x := rfl

theorem pointsMap_val_smul (σ : L ≃ₐ[R] L) (σ' : O R L ≃ₐ[R] O R L) (hσ : ∀ x : O R L, ((σ' x : O R L) : L) = σ x)
    (z : G.Points (O R L)) :
    G.pointsMap (O R L).val (σ' • z) = σ • G.pointsMap (O R L).val z := by
  rw [Points.smul_def, Points.smul_def, ← AddMonoidHom.comp_apply, ← pointsMap_comp,
    ← AddMonoidHom.comp_apply, ← pointsMap_comp]
  congr 2
  exact AlgHom.ext fun x => hσ x

variable [Fact p.Prime]

noncomputable def tateMap : TateModule p (G.Points (O R L)) →ₗ[ℤ_[p]] TateModule p (G.Points L) where
  toFun x := ⟨fun n => G.pointsMap (O R L).val ((x : ℕ → G.Points (O R L)) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    change G.pointsMap (O R L).val (((x + y : TateModule p _) : ℕ → G.Points (O R L)) n) =
      G.pointsMap (O R L).val ((x : ℕ → G.Points (O R L)) n) + G.pointsMap (O R L).val ((y : ℕ → G.Points (O R L)) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    change G.pointsMap (O R L).val (((a • x : TateModule p _) : ℕ → G.Points (O R L)) n) =
      ((a • (⟨fun n => G.pointsMap (O R L).val ((x : ℕ → G.Points (O R L)) n), _⟩ : TateModule p (G.Points L)) :
        TateModule p (G.Points L)) : ℕ → G.Points L) n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem tateMap_apply (x : TateModule p (G.Points (O R L))) (n : ℕ) :
    ((tateMap G L x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
      G.pointsMap (O R L).val ((x : ℕ → G.Points (O R L)) n) := rfl

theorem tateMap_injective : Function.Injective (tateMap G L) := by
  intro x y hxy
  refine Subtype.ext (funext fun n => pointsMap_val_injective G L ?_)
  have := congrArg (fun z : TateModule p (G.Points L) => (z : ℕ → G.Points L) n) hxy
  exact this

theorem tateMap_surjective : Function.Surjective (tateMap G L) := by
  intro y

  choose x hx using fun n => pointsMap_val_surjective G L ((y : ℕ → G.Points L) n)
  refine ⟨⟨x, fun n => ⟨?_, ?_⟩⟩, Subtype.ext (funext fun n => hx n)⟩
  · apply pointsMap_val_injective G L
    rw [map_zsmul, hx, map_zero, TateModule.torsion]
  · apply pointsMap_val_injective G L
    rw [map_zsmul, hx, hx, TateModule.compat]

noncomputable def tateEquiv : TateModule p (G.Points (O R L)) ≃ₗ[ℤ_[p]] TateModule p (G.Points L) :=
  LinearEquiv.ofBijective (tateMap G L) ⟨tateMap_injective G L, tateMap_surjective G L⟩

theorem tateEquiv_apply (x : TateModule p (G.Points (O R L))) (n : ℕ) :
    ((tateEquiv G L x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
      G.pointsMap (O R L).val ((x : ℕ → G.Points (O R L)) n) := rfl

theorem tateEquiv_rep (σ : L ≃ₐ[R] L) (σ' : O R L ≃ₐ[R] O R L) (hσ : ∀ x : O R L, ((σ' x : O R L) : L) = σ x)
    (x : TateModule p (G.Points (O R L))) :
    tateEquiv G L (G.tateModuleRep (O R L) σ' x) = G.tateModuleRep L σ (tateEquiv G L x) := by
  refine Subtype.ext (funext fun n => ?_)
  rw [tateEquiv_apply, tateModuleRep_apply, tateModuleRep_apply, tateEquiv_apply]
  exact pointsMap_val_smul G L σ σ' hσ _

end PDivIntegralPoints
p2m_reactivate "P2MW.S_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv.PDivIntegralPoints"

open PDivIntegralPoints in

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h)
    (L : Type) [CommRing L] [Algebra R L] :
    Function.Bijective (G.pointsMap (integralClosure R L).val) ∧
    (∀ σ : L ≃ₐ[R] L, ∃ σ' : integralClosure R L ≃ₐ[R] integralClosure R L,
        ∀ x : integralClosure R L, ((σ' x : integralClosure R L) : L) = σ x) ∧
    (∀ (σ : L ≃ₐ[R] L) (σ' : integralClosure R L ≃ₐ[R] integralClosure R L),
        (∀ x : integralClosure R L, ((σ' x : integralClosure R L) : L) = σ x) →
        ∀ z : G.Points (integralClosure R L),
          G.pointsMap (integralClosure R L).val (σ' • z) = σ • G.pointsMap (integralClosure R L).val z) ∧
    ∃ e : TateModule p (G.Points (integralClosure R L)) ≃ₗ[ℤ_[p]] TateModule p (G.Points L),
      (∀ (x : TateModule p (G.Points (integralClosure R L))) (n : ℕ),
          ((e x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
            G.pointsMap (integralClosure R L).val ((x : ℕ → G.Points (integralClosure R L)) n)) ∧
      ∀ (σ : L ≃ₐ[R] L) (σ' : integralClosure R L ≃ₐ[R] integralClosure R L),
        (∀ x : integralClosure R L, ((σ' x : integralClosure R L) : L) = σ x) →
        ∀ x : TateModule p (G.Points (integralClosure R L)),
          e (G.tateModuleRep (integralClosure R L) σ' x) = G.tateModuleRep L σ (e x) :=
  ⟨pointsMap_val_bijective G L, fun σ => ⟨restrict R L σ, coe_restrict R L σ⟩, pointsMap_val_smul G L,
    tateEquiv G L, tateEquiv_apply G L, tateEquiv_rep G L⟩

end S_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv
end P2MW
export P2MW.S_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv (solution)
