-- Prove2me | solution 1 for PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/19610ee4-c0bf-5414-b651-8f150c19fe73

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field

set_option autoImplicit false

namespace T1

open PDivisibleGroup

variable {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {p : ℕ}

@[reducible] noncomputable def galAction {h : ℕ} (X : PDivisibleGroup K p h) (v : ℕ) :
    DistribMulAction (L ≃ₐ[K] L) (Additive (X.Point L v)) where
  smul σ a := Additive.ofMul (X.pointMap (σ : L →ₐ[K] L) v (Additive.toMul a))
  one_smul a := by
    change Additive.ofMul (X.pointMap ((1 : L ≃ₐ[K] L) : L →ₐ[K] L) v (Additive.toMul a)) = a
    rw [show ((1 : L ≃ₐ[K] L) : L →ₐ[K] L) = AlgHom.id K L from rfl, pointMap_id]
    rfl
  mul_smul σ τ a := by
    change Additive.ofMul (X.pointMap ((σ * τ : L ≃ₐ[K] L) : L →ₐ[K] L) v (Additive.toMul a)) =
      Additive.ofMul (X.pointMap (σ : L →ₐ[K] L) v (Additive.toMul
        (Additive.ofMul (X.pointMap (τ : L →ₐ[K] L) v (Additive.toMul a)))))
    rw [show ((σ * τ : L ≃ₐ[K] L) : L →ₐ[K] L) = (σ : L →ₐ[K] L).comp (τ : L →ₐ[K] L) from rfl, pointMap_comp]
    rfl
  smul_zero σ := by
    change Additive.ofMul (X.pointMap (σ : L →ₐ[K] L) v (Additive.toMul 0)) = 0
    rw [toMul_zero, map_one]; rfl
  smul_add σ a b := by
    change Additive.ofMul (X.pointMap (σ : L →ₐ[K] L) v (Additive.toMul (a + b))) =
      Additive.ofMul (X.pointMap (σ : L →ₐ[K] L) v (Additive.toMul a)) +
        Additive.ofMul (X.pointMap (σ : L →ₐ[K] L) v (Additive.toMul b))
    rw [toMul_add, map_mul]; rfl

theorem galAction_smul_def {h : ℕ} (X : PDivisibleGroup K p h) (v : ℕ) (σ : L ≃ₐ[K] L) (a : Additive (X.Point L v)) :
    (letI := galAction L X v; σ • a) = Additive.ofMul (X.pointMap (σ : L →ₐ[K] L) v (Additive.toMul a)) := rfl

def eqv {h : ℕ} (X : PDivisibleGroup K p h) (v : ℕ) : WithConv (X.level v →ₐ[K] L) ≃ Additive (X.Point L v) :=
  Additive.ofMul (α := X.Point L v)

theorem eqv_apply {h : ℕ} (X : PDivisibleGroup K p h) (v : ℕ) (f : WithConv (X.level v →ₐ[K] L)) :
    eqv L X v f = Additive.ofMul (Point.ofConv f : X.Point L v) := rfl

theorem eqv_mul {h : ℕ} (X : PDivisibleGroup K p h) (v : ℕ) (f g : WithConv (X.level v →ₐ[K] L)) :
    eqv L X v (f * g) = eqv L X v f + eqv L X v g := rfl

theorem eqv_act {h : ℕ} (X : PDivisibleGroup K p h) (v : ℕ) (σ : L ≃ₐ[K] L) (f g : WithConv (X.level v →ₐ[K] L))
    (hfg : ∀ x : X.level v, g x = σ (f x)) :
    eqv L X v g = (letI := galAction L X v; σ • eqv L X v f) := by
  rw [galAction_smul_def, eqv_apply, eqv_apply]
  congr 1
  apply congrArg Point.ofAlgHom
  apply AlgHom.ext
  intro x
  exact hfg x

end T1

open T1 PDivisibleGroup in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {K : Type} [Field K] [CharZero K]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    {h h' : ℕ} (G : PDivisibleGroup K p h) (H : PDivisibleGroup K p h')
    (F : G.Points L →+ H.Points L)

    (hFlev : ∀ (v : ℕ) (x : G.Point L v), ∃ y : H.Point L v,
      F (G.pointsMkAdd L v (Additive.ofMul x)) = H.pointsMkAdd L v (Additive.ofMul y))

    (hFgal : ∀ (τ : L ≃ₐ[K] L) (z : G.Points L), F (τ • z) = τ • F z) :
    ∃ φ : ∀ v : ℕ, H.level v →ₐc[K] G.level v,
      (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (H.transition v)) ∧
      (∀ (v : ℕ) (x : G.Point L v),
        F (G.pointsMkAdd L v (Additive.ofMul x)) =
          H.pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[K] G.level v))))) ∧

      (∀ φ' : ∀ v : ℕ, H.level v →ₐc[K] G.level v,
        (∀ (v : ℕ) (x : G.Point L v),
          F (G.pointsMkAdd L v (Additive.ofMul x)) =
            H.pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[K] G.level v))))) →
        φ' = φ) := by
  classical

  have hlev : ∀ v : ℕ, ∃ φᵥ : Additive (G.Point L v) →+ Additive (H.Point L v),
      ∀ a, H.pointsMkAdd L v (φᵥ a) = F (G.pointsMkAdd L v a) := by
    intro v
    choose y hy using hFlev v
    refine ⟨AddMonoidHom.mk' (fun a => Additive.ofMul (y (Additive.toMul a))) ?_, fun a => (hy (Additive.toMul a)).symm⟩
    intro a b
    apply H.pointsMkAdd_injective v
    rw [AddMonoidHom.map_add, ← hy, ← hy, ← hy, ← AddMonoidHom.map_add, ← AddMonoidHom.map_add]
    rfl
  choose φl hφl using hlev

  have hφl_gal : ∀ (v : ℕ) (σ : L ≃ₐ[K] L) (a : Additive (G.Point L v)),
      φl v (letI := galAction L G v; σ • a) = (letI := galAction L H v; σ • φl v a) := by
    intro v σ a
    apply H.pointsMkAdd_injective v
    rw [hφl, galAction_smul_def, galAction_smul_def, ← Points.smul_pointsMkAdd, ← Points.smul_pointsMkAdd, hFgal]
    congr 1
    exact (hφl v a).symm

  have key : ∀ (v : ℕ) (ψ : H.level v →ₐc[K] G.level v) (x : G.Point L v),
      (F (G.pointsMkAdd L v (Additive.ofMul x)) =
          H.pointsMkAdd L v (Additive.ofMul (Point.ofAlgHom ((Point.toAlgHom x).comp (ψ : H.level v →ₐ[K] G.level v))))) ↔
        eqv L H v (WithConv.toConv ((WithConv.ofConv (Point.toConv x)).comp (ψ : H.level v →ₐ[K] G.level v))) =
          φl v (eqv L G v (Point.toConv x)) := by
    intro v ψ x
    rw [← (H.pointsMkAdd_injective v).eq_iff, hφl]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

  have hfin : ∀ v : ℕ, ∃! ψ : H.level v →ₐc[K] G.level v, ∀ x : G.Point L v,
      F (G.pointsMkAdd L v (Additive.ofMul x)) =
        H.pointsMkAdd L v (Additive.ofMul (Point.ofAlgHom ((Point.toAlgHom x).comp (ψ : H.level v →ₐ[K] G.level v)))) := by
    intro v
    letI := galAction L G v
    letI := galAction L H v
    obtain ⟨ψ, hψ, huniq⟩ := HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero K L
      (G.level v) (eqv L G v) (eqv_mul L G v) (eqv_act L G v)
      (H.level v) (eqv L H v) (eqv_mul L H v) (eqv_act L H v) (φl v) (hφl_gal v)
    refine ⟨ψ, fun x => (key v ψ x).mpr (hψ (Point.toConv x)), fun ψ' hψ' => huniq ψ' fun f => ?_⟩
    exact (key v ψ' (Point.ofConv f)).mp (hψ' (Point.ofConv f))
  choose φ hφ hφuniq using hfin
  refine ⟨φ, fun v => ?_, hφ, fun φ' hφ' => funext fun v => hφuniq v (φ' v) (hφ' v)⟩

  letI := galAction L G v
  letI := galAction L H (v + 1)

  let ι : Additive (H.Point L v) →+ Additive (H.Point L (v + 1)) := (H.pointIncl L v).toAdditive
  have hι_gal : ∀ (σ : L ≃ₐ[K] L) (a : Additive (G.Point L v)),
      (ι.comp (φl v)) (σ • a) = σ • (ι.comp (φl v)) a := by
    intro σ a
    show ι (φl v (σ • a)) = σ • ι (φl v a)
    rw [hφl_gal v σ a, galAction_smul_def, galAction_smul_def]
    show Additive.ofMul (H.pointIncl L v (Additive.toMul (Additive.ofMul (H.pointMap (σ : L →ₐ[K] L) v _)))) = _
    rw [toMul_ofMul, ← pointMap_pointIncl]
    rfl
  obtain ⟨χ, -, hχuniq⟩ := HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero K L
    (G.level v) (eqv L G v) (eqv_mul L G v) (eqv_act L G v)
    (H.level (v + 1)) (eqv L H (v + 1)) (eqv_mul L H (v + 1)) (eqv_act L H (v + 1)) (ι.comp (φl v)) hι_gal

  have hval : ∀ x : G.Point L v, φl v (Additive.ofMul x) =
      Additive.ofMul (Point.ofAlgHom ((Point.toAlgHom x).comp (φ v : H.level v →ₐ[K] G.level v))) := by
    intro x
    apply H.pointsMkAdd_injective v
    rw [hφl, hφ v x]

  have hval' : ∀ x : G.Point L v, φl (v + 1) (Additive.ofMul (G.pointIncl L v x)) =
      Additive.ofMul (H.pointIncl L v (Additive.toMul (φl v (Additive.ofMul x)))) := by
    intro x
    apply H.pointsMkAdd_injective (v + 1)
    rw [hφl, pointsMkAdd_pointIncl, pointsMkAdd_pointIncl, ← hφl]
    rfl
  have h1 : ∀ f : WithConv (G.level v →ₐ[K] L),
      eqv L H (v + 1) (WithConv.toConv ((WithConv.ofConv f).comp
        (((G.transition v).comp (φ (v + 1)) : H.level (v + 1) →ₐc[K] G.level v) : H.level (v + 1) →ₐ[K] G.level v))) =
        (ι.comp (φl v)) (eqv L G v f) := by
    intro f
    have hx := hφ (v + 1) (G.pointIncl L v (Point.ofConv f))
    rw [← hφl] at hx
    have hx' := H.pointsMkAdd_injective (v + 1) hx

    show _ = Additive.ofMul (H.pointIncl L v (Additive.toMul (φl v (Additive.ofMul (Point.ofConv f)))))
    rw [← hval', hx', toAlgHom_pointIncl]
    rfl
  have h2 : ∀ f : WithConv (G.level v →ₐ[K] L),
      eqv L H (v + 1) (WithConv.toConv ((WithConv.ofConv f).comp
        (((φ v).comp (H.transition v) : H.level (v + 1) →ₐc[K] G.level v) : H.level (v + 1) →ₐ[K] G.level v))) =
        (ι.comp (φl v)) (eqv L G v f) := by
    intro f
    show _ = Additive.ofMul (H.pointIncl L v (Additive.toMul (φl v (Additive.ofMul (Point.ofConv f)))))
    rw [hval, toMul_ofMul]
    rfl
  exact (hχuniq _ h1).trans (hχuniq _ h2).symm

end S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field
end P2MW
export P2MW.S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field (solution)
