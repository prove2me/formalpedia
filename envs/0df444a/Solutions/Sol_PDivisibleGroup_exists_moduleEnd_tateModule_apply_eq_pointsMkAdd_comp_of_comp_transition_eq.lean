-- Prove2me | solution 1 for PDivisibleGroup.exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d1d46703-8e92-5e10-83bd-ba19bf56c00a

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] {L : Type} [CommRing L] [Algebra O L]
    {h : ℕ} (G : PDivisibleGroup O p h)
    (u : ∀ v : ℕ, G.level v →ₐc[O] G.level v)
    (hu : ∀ v : ℕ, (G.transition v).comp (u (v + 1)) = (u v).comp (G.transition v)) :
    ∃ U : Module.End ℤ_[p] (TateModule p (G.Points L)),
      ∀ (x : TateModule p (G.Points L)) (n w : ℕ) (f : G.Point L w),
        G.pointsMkAdd L w (Additive.ofMul f) = (x : ℕ → G.Points L) n →
        ((U x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
          G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w : G.level w →ₐ[O] G.level w)))) := by
  classical

  let uPt : ∀ v : ℕ, G.Point L v →* G.Point L v := fun v => PDivisibleGroup.Hopf.convCompMonoidHom L (u v)
  have huPt : ∀ (v : ℕ) (x : G.Point L v), uPt v x =
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (u v : G.level v →ₐ[O] G.level v)) :=
    fun v x => rfl

  have hincl : ∀ (v : ℕ) (x : G.Point L v), uPt (v + 1) (G.pointIncl L v x) = G.pointIncl L v (uPt v x) := by
    intro v x
    refine PDivisibleGroup.Point.ext fun a => ?_
    rw [huPt, huPt, PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.toAlgHom_pointIncl,
      PDivisibleGroup.toAlgHom_pointIncl, PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.comp_apply, AlgHom.comp_apply,
      AlgHom.comp_apply, AlgHom.comp_apply]
    exact congrArg (PDivisibleGroup.Point.toAlgHom x) (DFunLike.congr_fun (hu v) a)
  have hinclLE : ∀ {v w : ℕ} (hvw : v ≤ w) (x : G.Point L v),
      uPt w (G.pointInclLE L hvw x) = G.pointInclLE L hvw (uPt v x) := by
    intro v w hvw x
    induction hvw with
    | refl => rw [G.pointInclLE_self, G.pointInclLE_self]
    | step hle ih => rw [G.pointInclLE_succ hle, G.pointInclLE_succ hle, hincl, ih]

  let uPts : G.Points L →+ G.Points L :=
    AddCommGroup.DirectLimit.map (G := fun v => Additive (G.Point L v)) (G' := fun v => Additive (G.Point L v))
      (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
      (f' := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
      (fun v => MonoidHom.toAdditive (uPt v))
      (fun _ _ hvw => AddMonoidHom.ext fun x => congrArg Additive.ofMul (hinclLE hvw (Additive.toMul x)))
  have huPts : ∀ (v : ℕ) (x : G.Point L v),
      uPts (G.pointsMkAdd L v (Additive.ofMul x)) = G.pointsMkAdd L v (Additive.ofMul (uPt v x)) := fun v x =>
    AddCommGroup.DirectLimit.map_apply_of (G := fun v => Additive (G.Point L v)) (G' := fun v => Additive (G.Point L v))
      (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
      (f' := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
      (fun v => MonoidHom.toAdditive (uPt v)) _ (Additive.ofMul x)

  let Ufun : TateModule p (G.Points L) → TateModule p (G.Points L) := fun x =>
    ⟨fun n => uPts ((x : ℕ → G.Points L) n), fun n =>
      ⟨by rw [← map_zsmul, TateModule.torsion, map_zero], by rw [← map_zsmul, TateModule.compat]⟩⟩
  have hUfun : ∀ (x : TateModule p (G.Points L)) (n : ℕ),
      ((Ufun x : TateModule p (G.Points L)) : ℕ → G.Points L) n = uPts ((x : ℕ → G.Points L) n) := fun x n => rfl
  let U : Module.End ℤ_[p] (TateModule p (G.Points L)) :=
    { toFun := Ufun
      map_add' := fun x y => Subtype.ext (funext fun n => by
        rw [hUfun, TateModule.coe_add, Pi.add_apply, map_add, TateModule.coe_add, Pi.add_apply, hUfun, hUfun])
      map_smul' := fun a x => Subtype.ext (funext fun n => by
        rw [hUfun, TateModule.smul_apply, map_zsmul, RingHom.id_apply, TateModule.smul_apply, hUfun]) }
  refine ⟨U, fun x n w f hf => ?_⟩
  change uPts ((x : ℕ → G.Points L) n) = _
  rw [← hf, huPts, huPt]

end S_PDivisibleGroup_exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq
end P2MW
export P2MW.S_PDivisibleGroup_exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq (solution)
