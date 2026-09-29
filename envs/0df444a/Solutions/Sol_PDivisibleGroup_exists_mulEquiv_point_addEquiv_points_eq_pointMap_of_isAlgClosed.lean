-- Prove2me | solution 1 for PDivisibleGroup.exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/800ae788-89f8-52e6-affe-ef6dba95c56f

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed

set_option autoImplicit false

namespace PX

open PDivisibleGroup Polynomial

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
  {L L' : Type} [Field L] [IsAlgClosed L] [Algebra R L] [Field L'] [Algebra R L'] (j : L →ₐ[R] L')

theorem apply_mem_range (v : ℕ) (y : G.level v →ₐ[R] L') (a : G.level v) : y a ∈ j.range := by

  haveI : Algebra.IsIntegral R (G.level v) := Algebra.IsIntegral.of_finite R (G.level v)
  have hint : IsIntegral R (y a) := (Algebra.IsIntegral.isIntegral a).map y
  obtain ⟨q, hqm, hq⟩ := hint

  have hsplit : (q.map (algebraMap R L)).Splits := IsAlgClosed.splits _
  have hmap : q.map (algebraMap R L') = (q.map (algebraMap R L)).map (j : L →+* L') := by
    rw [Polynomial.map_map, j.comp_algebraMap]
  have hne : q.map (algebraMap R L') ≠ 0 := (hqm.map _).ne_zero
  have hroot : y a ∈ (q.map (algebraMap R L')).roots := by
    rw [Polynomial.mem_roots hne, IsRoot.def, eval_map]
    exact hq
  rw [hmap, hsplit.roots_map, Multiset.mem_map] at hroot
  obtain ⟨r, -, hr⟩ := hroot
  exact ⟨r, hr⟩

theorem pointMap_bijective (v : ℕ) : Function.Bijective (G.pointMap j v) := by
  have hj : Function.Injective j := (j : L →+* L').injective
  refine ⟨fun x x' hxx' => ?_, fun y => ?_⟩
  ·
    have h' : ∀ a, j (Point.toAlgHom x a) = j (Point.toAlgHom x' a) := fun a =>
      congrArg (fun z : G.Point L' v => Point.toAlgHom z a) hxx'
    exact congrArg Point.ofAlgHom (AlgHom.ext fun a => hj (h' a) : Point.toAlgHom x = Point.toAlgHom x')
  ·
    let e : L ≃ₐ[R] j.range := AlgEquiv.ofInjective j hj
    let x : G.level v →ₐ[R] L :=
      (e.symm : j.range →ₐ[R] L).comp ((Point.toAlgHom y).codRestrict j.range (apply_mem_range G j v (Point.toAlgHom y)))
    refine ⟨Point.ofAlgHom x, ?_⟩
    apply congrArg Point.ofAlgHom
    apply AlgHom.ext
    intro a
    show j (e.symm ⟨Point.toAlgHom y a, _⟩) = Point.toAlgHom y a
    have := AlgEquiv.ofInjective_apply j hj (e.symm ⟨Point.toAlgHom y a, apply_mem_range G j v (Point.toAlgHom y) a⟩)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm

noncomputable def pointEquiv (v : ℕ) : G.Point L v ≃* G.Point L' v :=
  MulEquiv.ofBijective (G.pointMap j v) (pointMap_bijective G j v)

@[scoped simp] theorem pointEquiv_apply (v : ℕ) (x : G.Point L v) : pointEquiv G j v x = G.pointMap j v x := rfl

end PX
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed.PX"

namespace PX

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
  {L L' : Type} [Field L] [IsAlgClosed L] [Algebra R L] [Field L'] [Algebra R L'] (j : L →ₐ[R] L')

theorem pointsMap_bijective : Function.Bijective (G.pointsMap j) := by
  refine ⟨G.pointsMap_injective_of_injective j (RingHom.injective (j : L →+* L')), fun z' => ?_⟩
  obtain ⟨v, x', rfl⟩ := PDivisibleGroup.Points.exists_mkAdd G z'
  obtain ⟨x, rfl⟩ := (pointMap_bijective G j v).2 x'
  exact ⟨G.pointsMkAdd L v (Additive.ofMul x), G.pointsMap_pointsMkAdd j v x⟩

noncomputable def pointsEquiv : G.Points L ≃+ G.Points L' :=
  AddEquiv.ofBijective (G.pointsMap j) (pointsMap_bijective G j)

@[scoped simp] theorem pointsEquiv_apply (z : G.Points L) : pointsEquiv G j z = G.pointsMap j z := rfl

theorem pointsEquiv_pointsMkAdd (v : ℕ) (x : G.Point L v) :
    pointsEquiv G j (G.pointsMkAdd L v (Additive.ofMul x)) = G.pointsMkAdd L' v (Additive.ofMul (G.pointMap j v x)) :=
  G.pointsMap_pointsMkAdd j v x

theorem pointsEquiv_smul (σ : L ≃ₐ[R] L) (σ' : L' ≃ₐ[R] L') (hσ : ∀ a : L, j (σ a) = σ' (j a)) (z : G.Points L) :
    pointsEquiv G j (σ • z) = σ' • pointsEquiv G j z := by
  rw [pointsEquiv_apply, pointsEquiv_apply, PDivisibleGroup.Points.smul_def, PDivisibleGroup.Points.smul_def,
    ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply, ← PDivisibleGroup.pointsMap_comp, ← PDivisibleGroup.pointsMap_comp]
  congr 2
  exact AlgHom.ext hσ

end PX
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed.PX"

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (L : Type) [Field L] [IsAlgClosed L] [Algebra R L] (L' : Type) [Field L'] [Algebra R L'] (j : L →ₐ[R] L') :
    ∃ (e : ∀ v : ℕ, G.Point L v ≃* G.Point L' v) (E : G.Points L ≃+ G.Points L'),
      (∀ (v : ℕ) (x : G.Point L v), e v x = G.pointMap j v x) ∧
      (∀ z : G.Points L, E z = G.pointsMap j z) ∧
      (∀ (v : ℕ) (x : G.Point L v),
        E (G.pointsMkAdd L v (Additive.ofMul x)) = G.pointsMkAdd L' v (Additive.ofMul (e v x))) ∧
      (∀ (σ : L ≃ₐ[R] L) (σ' : L' ≃ₐ[R] L'), (∀ a : L, j (σ a) = σ' (j a)) →
        ∀ z : G.Points L, E (σ • z) = σ' • E z) := by
  exact ⟨fun v => PX.pointEquiv G j v, PX.pointsEquiv G j, fun v x => rfl, fun z => rfl,
    fun v x => PX.pointsEquiv_pointsMkAdd G j v x, fun σ σ' hσ z => PX.pointsEquiv_smul G j σ σ' hσ z⟩

end S_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed
end P2MW
export P2MW.S_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed (solution)
