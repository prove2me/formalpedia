-- Prove2me | solution 1 for PDivisibleGroup.exists_linearMap_tateModule_of_comp_transition_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fcc4551c-a14a-578a-a6c6-817c2ea7939c

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq

set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000
set_option Elab.async false

noncomputable section

namespace Ws47
namespace FUNC

open PDivisibleGroup Coalgebra

variable {p : ℕ} [Fact p.Prime]
variable {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
variable {h h' : ℕ} (G : PDivisibleGroup R p h) (Γ : PDivisibleGroup R p h')
variable (φ : ∀ v : ℕ, G.level v →ₐc[R] Γ.level v)

def q (w : ℕ) : Γ.Point L w →* G.Point L w := Hopf.convCompMonoidHom L (φ w)

theorem q_eq_ofAlgHom (w : ℕ) (f₁ : Γ.Point L w) :
    q G Γ φ w f₁ = Point.ofAlgHom ((Point.toAlgHom f₁).comp (φ w : G.level w →ₐ[R] Γ.level w)) := rfl

@[scoped simp] theorem q_apply (w : ℕ) (f₁ : Γ.Point L w) (a : G.level w) :
    Point.toAlgHom (q G Γ φ w f₁) a = Point.toAlgHom f₁ (φ w a) := rfl

variable {G Γ φ}

theorem q_pointIncl (hφ : ∀ v, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    (v : ℕ) (f₁ : Γ.Point L v) :
    q G Γ φ (v + 1) (Γ.pointIncl L v f₁) = G.pointIncl L v (q G Γ φ v f₁) := by
  refine Point.ext fun a => ?_
  show Point.toAlgHom f₁ (Γ.transition v (φ (v + 1) a)) = Point.toAlgHom f₁ (φ v (G.transition v a))
  have := DFunLike.congr_fun (hφ v) a
  simp only [BialgHom.coe_comp, Function.comp_apply] at this
  rw [this]

theorem q_pointInclLE (hφ : ∀ v, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    {v w : ℕ} (hvw : v ≤ w) (f₁ : Γ.Point L v) :
    q G Γ φ w (Γ.pointInclLE L hvw f₁) = G.pointInclLE L hvw (q G Γ φ v f₁) := by
  induction hvw with
  | refl => rw [Γ.pointInclLE_self, G.pointInclLE_self]
  | step hvw ih => rw [Γ.pointInclLE_succ hvw, G.pointInclLE_succ hvw, q_pointIncl hφ, ih]

variable (G Γ φ) in

def Φ (hφ : ∀ v, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1))) : Γ.Points L →+ G.Points L :=
  AddCommGroup.DirectLimit.map (G := fun v => Additive (Γ.Point L v)) (G' := fun v => Additive (G.Point L v))
    (f := fun v w hvw => Γ.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (q G Γ φ v))
    (fun _ _ hvw => AddMonoidHom.ext fun x => congrArg Additive.ofMul (q_pointInclLE hφ hvw (Additive.toMul x)))

theorem Φ_mkAdd (hφ : ∀ v, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    (w : ℕ) (f₁ : Γ.Point L w) :
    Φ G Γ φ hφ (Γ.pointsMkAdd L w (Additive.ofMul f₁)) = G.pointsMkAdd L w (Additive.ofMul (q G Γ φ w f₁)) :=
  AddCommGroup.DirectLimit.map_apply_of (G := fun v => Additive (Γ.Point L v)) (G' := fun v => Additive (G.Point L v))
    (f := fun v w hvw => Γ.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (q G Γ φ v)) _ (Additive.ofMul f₁)

theorem Φ_smul (hφ : ∀ v, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    (τ : L ≃ₐ[R] L) (z : Γ.Points L) : Φ G Γ φ hφ (τ • z) = τ • Φ G Γ φ hφ z := by
  induction z using Points.induction_on with
  | ih v x =>
    rw [Points.smul_pointsMkAdd, Φ_mkAdd, Φ_mkAdd, Points.smul_pointsMkAdd]
    rfl

variable (G Γ φ) in

def jT (hφ : ∀ v, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1))) :
    TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (G.Points L) where
  toFun x := ⟨fun n => Φ G Γ φ hφ ((x : ℕ → Γ.Points L) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show Φ G Γ φ hφ (((x + y : TateModule p (Γ.Points L)) : ℕ → Γ.Points L) n) = _
    rw [TateModule.coe_add, Pi.add_apply, map_add]; rfl)
  map_smul' a x := Subtype.ext (funext fun n => by
    show Φ G Γ φ hφ (((a • x : TateModule p (Γ.Points L)) : ℕ → Γ.Points L) n) =
      (((a • ⟨fun n => Φ G Γ φ hφ ((x : ℕ → Γ.Points L) n), _⟩ : TateModule p (G.Points L))) : ℕ → G.Points L) n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem jT_apply (hφ : ∀ v, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    (x : TateModule p (Γ.Points L)) (n : ℕ) :
    ((jT G Γ φ hφ x : TateModule p (G.Points L)) : ℕ → G.Points L) n = Φ G Γ φ hφ ((x : ℕ → Γ.Points L) n) :=
  rfl

end Ws47.FUNC
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq.Ws47 P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq.Ws47.FUNC"
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq.Ws47"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq.Ws47 P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq.Ws47.FUNC"

open Ws47.FUNC PDivisibleGroup in

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (L : Type) [Field L] [Algebra R L]
    {h h' : ℕ} (G : PDivisibleGroup R p h) (Γ : PDivisibleGroup R p h')
    (φ : ∀ v : ℕ, G.level v →ₐc[R] Γ.level v)
    (hφ : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1))) :
    ∃ Tφ : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (G.Points L),
      (∀ (x : TateModule p (Γ.Points L)) (n w : ℕ) (g : Γ.Point L w),
        Γ.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → Γ.Points L) n →
        ((Tφ x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
          G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : G.level w →ₐ[R] Γ.level w))))) ∧
      (∀ (τ : L ≃ₐ[R] L) (x : TateModule p (Γ.Points L)),
        Tφ (Γ.tateModuleRep L τ x) = G.tateModuleRep L τ (Tφ x)) := by
  refine ⟨jT G Γ φ hφ, ?_, ?_⟩
  · intro x n w g hg
    rw [jT_apply, ← hg, Φ_mkAdd]
    rfl
  · intro τ x
    refine Subtype.ext (funext fun n => ?_)
    rw [jT_apply, tateModuleRep_apply, tateModuleRep_apply, jT_apply]
    exact Φ_smul hφ τ _

end S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq
end P2MW
export P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq (solution)
