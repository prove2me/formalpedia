-- Prove2me | solution 1 for PDivisibleGroup.exists_linearMap_tateModule_injective_of_surjective_comp_transition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5cd44d5e-f491-5290-a7f6-11fbcbbcc63a

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_injective_of_surjective_comp_transition

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace Ws50S10

open PDivisibleGroup Coalgebra

variable {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
variable {h h₁ : ℕ} (H : PDivisibleGroup O p h) (H₁ : PDivisibleGroup O p h₁)
variable (π : ∀ v : ℕ, H.level v →ₐc[O] H₁.level v)

local notation "Qb" => AlgebraicClosure ℚ

def q (w : ℕ) : H₁.Point Qb w →* H.Point Qb w := Hopf.convCompMonoidHom Qb (π w)

theorem toAlgHom_q (w : ℕ) (f₁ : H₁.Point Qb w) :
    Point.toAlgHom (q H H₁ π w f₁) = (Point.toAlgHom f₁).comp (π w : H.level w →ₐ[O] H₁.level w) := rfl

@[scoped simp] theorem q_apply (w : ℕ) (f₁ : H₁.Point Qb w) (a : H.level w) :
    Point.toAlgHom (q H H₁ π w f₁) a = Point.toAlgHom f₁ (π w a) := rfl

theorem q_eq_ofAlgHom (w : ℕ) (f₁ : H₁.Point Qb w) :
    q H H₁ π w f₁ = Point.ofAlgHom ((Point.toAlgHom f₁).comp (π w : H.level w →ₐ[O] H₁.level w)) := rfl

variable {H H₁ π}

theorem q_injective (hπ : ∀ v, Function.Surjective (π v)) (w : ℕ) : Function.Injective (q H H₁ π w) := by
  intro f g hfg
  refine Point.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hπ w b
  have := DFunLike.congr_fun (congrArg Point.toAlgHom hfg) a
  exact this

theorem q_pointIncl (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1)))
    (v : ℕ) (f₁ : H₁.Point Qb v) :
    q H H₁ π (v + 1) (H₁.pointIncl Qb v f₁) = H.pointIncl Qb v (q H H₁ π v f₁) := by
  refine Point.ext fun a => ?_
  show Point.toAlgHom f₁ (H₁.transition v (π (v + 1) a)) = Point.toAlgHom f₁ (π v (H.transition v a))
  have := DFunLike.congr_fun (hπt v) a
  simp only [BialgHom.coe_comp, Function.comp_apply] at this
  rw [this]

theorem q_pointInclLE (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1)))
    {v w : ℕ} (hvw : v ≤ w) (f₁ : H₁.Point Qb v) :
    q H H₁ π w (H₁.pointInclLE Qb hvw f₁) = H.pointInclLE Qb hvw (q H H₁ π v f₁) := by
  induction hvw with
  | refl => rw [H₁.pointInclLE_self, H.pointInclLE_self]
  | step hvw ih => rw [H₁.pointInclLE_succ hvw, H.pointInclLE_succ hvw, q_pointIncl hπt, ih]

variable (H H₁ π) in

def Φ (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1))) :
    H₁.Points Qb →+ H.Points Qb :=
  AddCommGroup.DirectLimit.map (G := fun v => Additive (H₁.Point Qb v)) (G' := fun v => Additive (H.Point Qb v))
    (f := fun v w hvw => H₁.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => H.pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (q H H₁ π v))
    (fun _ _ hvw => AddMonoidHom.ext fun x =>
      congrArg Additive.ofMul (q_pointInclLE hπt hvw (Additive.toMul x)))

theorem Φ_mkAdd (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1)))
    (w : ℕ) (f₁ : H₁.Point Qb w) :
    Φ H H₁ π hπt (H₁.pointsMkAdd Qb w (Additive.ofMul f₁)) = H.pointsMkAdd Qb w (Additive.ofMul (q H H₁ π w f₁)) :=
  AddCommGroup.DirectLimit.map_apply_of (G := fun v => Additive (H₁.Point Qb v)) (G' := fun v => Additive (H.Point Qb v))
    (f := fun v w hvw => H₁.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => H.pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (q H H₁ π v)) _ (Additive.ofMul f₁)

theorem Φ_injective (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1))) :
    Function.Injective (Φ H H₁ π hπt) := by
  intro z w hzw
  induction z using Points.induction_on with
  | ih v x =>
    induction w using Points.induction_on with
    | ih w y =>
      rw [← H₁.pointsMkAdd_pointInclLE (le_max_left v w) x, ← H₁.pointsMkAdd_pointInclLE (le_max_right v w) y]
        at hzw ⊢
      rw [Φ_mkAdd, Φ_mkAdd, pointsMkAdd_eq_pointsMkAdd_iff] at hzw
      rw [pointsMkAdd_eq_pointsMkAdd_iff]
      exact q_injective hπ _ hzw

theorem Φ_smul (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1)))
    (τ' : Qb ≃ₐ[O] Qb) (z : H₁.Points Qb) :
    Φ H H₁ π hπt (τ' • z) = τ' • Φ H H₁ π hπt z := by
  induction z using Points.induction_on with
  | ih v x =>
    rw [Points.smul_pointsMkAdd, Φ_mkAdd, Φ_mkAdd, Points.smul_pointsMkAdd]
    rfl

variable (H H₁ π) in

def jT (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1))) :
    TateModule p (H₁.Points Qb) →ₗ[ℤ_[p]] TateModule p (H.Points Qb) where
  toFun x := ⟨fun n => Φ H H₁ π hπt ((x : ℕ → H₁.Points Qb) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show Φ H H₁ π hπt (((x + y : TateModule p (H₁.Points Qb)) : ℕ → H₁.Points Qb) n) = _
    rw [TateModule.coe_add, Pi.add_apply, map_add]; rfl)
  map_smul' a x := Subtype.ext (funext fun n => by
    show Φ H H₁ π hπt (((a • x : TateModule p (H₁.Points Qb)) : ℕ → H₁.Points Qb) n) =
      (((a • ⟨fun n => Φ H H₁ π hπt ((x : ℕ → H₁.Points Qb) n), _⟩ : TateModule p (H.Points Qb))) : ℕ → H.Points Qb) n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem jT_apply (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1)))
    (x : TateModule p (H₁.Points Qb)) (n : ℕ) :
    ((jT H H₁ π hπt x : TateModule p (H.Points Qb)) : ℕ → H.Points Qb) n = Φ H H₁ π hπt ((x : ℕ → H₁.Points Qb) n) :=
  rfl

theorem jT_injective (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1))) :
    Function.Injective (jT H H₁ π hπt) := by
  intro x y hxy
  refine Subtype.ext (funext fun n => Φ_injective hπ hπt ?_)
  have := congrArg (fun z : TateModule p (H.Points Qb) => (z : ℕ → H.Points Qb) n) hxy
  exact this

theorem exists_q_eq (hπ : ∀ v, Function.Surjective (π v)) (w : ℕ) (f : H.Point Qb w)
    (hf : ∀ a : H.level w, π w a = 0 → Point.toAlgHom f a = 0) :
    ∃ f₁ : H₁.Point Qb w, q H H₁ π w f₁ = f := by
  have hker : RingHom.ker (π w : H.level w →+* H₁.level w) ≤ RingHom.ker (Point.toAlgHom f : H.level w →+* Qb) := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    exact hf a ha
  let g : H₁.level w →+* Qb := RingHom.liftOfSurjective (π w : H.level w →+* H₁.level w) (hπ w) ⟨_, hker⟩
  have hg : ∀ a, g (π w a) = Point.toAlgHom f a := fun a =>
    RingHom.liftOfSurjective_comp_apply (π w : H.level w →+* H₁.level w) (hπ w) ⟨_, hker⟩ a
  let g' : H₁.level w →ₐ[O] Qb :=
    { g with
      commutes' := fun r => by
        have h1 : (π w : H.level w →+* H₁.level w) (algebraMap O (H.level w) r) = algebraMap O (H₁.level w) r :=
          (π w : H.level w →ₐ[O] H₁.level w).commutes r
        show g (algebraMap O (H₁.level w) r) = algebraMap O Qb r
        rw [← h1]
        exact (hg _).trans ((Point.toAlgHom f).commutes r) }
  refine ⟨Point.ofAlgHom g', Point.ext fun a => ?_⟩
  exact hg a

variable (P : ValuationSubring Qb)

def Red {G : PDivisibleGroup O p h} {w : ℕ} (f : G.Point Qb w) : Prop :=
  ∀ a, P.valuation (Point.toAlgHom f a - algebraMap O Qb (counit a)) < 1

omit [Fact p.Prime] in
theorem red_pointIncl {hh : ℕ} {G : PDivisibleGroup O p hh} {v : ℕ} {f : G.Point Qb v}
    (hf : ∀ a, P.valuation (Point.toAlgHom f a - algebraMap O Qb (counit a)) < 1) :
    ∀ a, P.valuation (Point.toAlgHom (G.pointIncl Qb v f) a - algebraMap O Qb (counit a)) < 1 := by
  intro a
  rw [pointIncl_apply, ← CoalgHomClass.counit_comp_apply (G.transition v) a]
  exact hf _

omit [Fact p.Prime] in
theorem red_pointInclLE {hh : ℕ} {G : PDivisibleGroup O p hh} {v w : ℕ} (hvw : v ≤ w) {f : G.Point Qb v}
    (hf : ∀ a, P.valuation (Point.toAlgHom f a - algebraMap O Qb (counit a)) < 1) :
    ∀ a, P.valuation (Point.toAlgHom (G.pointInclLE Qb hvw f) a - algebraMap O Qb (counit a)) < 1 := by
  induction hvw with
  | refl => rw [G.pointInclLE_self]; exact hf
  | step hvw ih => rw [G.pointInclLE_succ hvw]; exact red_pointIncl P ih

end Ws50S10
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_injective_of_surjective_comp_transition.Ws50S10"

open Ws50S10 PDivisibleGroup Coalgebra in

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {h h₁ : ℕ} (H : PDivisibleGroup O p h) (H₁ : PDivisibleGroup O p h₁)
    (π : ∀ v : ℕ, H.level v →ₐc[O] H₁.level v) (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1))) :
    ∃ j : TateModule p (H₁.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (H.Points (AlgebraicClosure ℚ)),
      Function.Injective j ∧
      (∀ (x : TateModule p (H₁.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f₁ : H₁.Point (AlgebraicClosure ℚ) w),
        H₁.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f₁) =
          (x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n →
        ((j x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f₁).comp (π w : H.level w →ₐ[O] H₁.level w))))) ∧
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ LinearMap.range j ↔
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, π w a = 0 → PDivisibleGroup.Point.toAlgHom f a = 0) ∧
      (∀ τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ,
        j ∘ₗ H₁.tateModuleRep (AlgebraicClosure ℚ) τ' = H.tateModuleRep (AlgebraicClosure ℚ) τ' ∘ₗ j) ∧
      (∀ x : TateModule p (H₁.Points (AlgebraicClosure ℚ)),
        (∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (j x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ↔
        (∀ n : ℕ, ∃ (w : ℕ) (f : H₁.Point (AlgebraicClosure ℚ) w),
          H₁.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H₁.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)) := by
  refine ⟨jT H H₁ π hπt, jT_injective hπ hπt, ?_, ?_, ?_, ?_⟩
  ·
    intro x n w f₁ hf₁
    rw [jT_apply, ← hf₁, Φ_mkAdd]
    rfl
  ·
    intro y
    constructor
    · rintro ⟨x, rfl⟩ n
      obtain ⟨w, f₁, hf₁⟩ := Points.exists_mkAdd H₁ ((x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n)
      refine ⟨w, q H H₁ π w f₁, ?_, fun a ha => ?_⟩
      · rw [jT_apply, ← hf₁, Φ_mkAdd]
      · rw [q_apply, ha, map_zero]
    · intro hy
      choose w f hf hker using hy
      have hlift : ∀ n, ∃ f₁ : H₁.Point (AlgebraicClosure ℚ) (w n), q H H₁ π (w n) f₁ = f n :=
        fun n => exists_q_eq hπ (w n) (f n) (hker n)
      choose f₁ hf₁ using hlift

      have hΦ : ∀ n, Φ H H₁ π hπt (H₁.pointsMkAdd (AlgebraicClosure ℚ) (w n) (Additive.ofMul (f₁ n))) =
          (y : ℕ → H.Points (AlgebraicClosure ℚ)) n := fun n => by
        rw [Φ_mkAdd, hf₁, hf]
      let x : TateModule p (H₁.Points (AlgebraicClosure ℚ)) :=
        ⟨fun n => H₁.pointsMkAdd (AlgebraicClosure ℚ) (w n) (Additive.ofMul (f₁ n)), fun n =>
          ⟨Φ_injective hπ hπt (by rw [map_zsmul, hΦ, map_zero, TateModule.torsion]),
           Φ_injective hπ hπt (by rw [map_zsmul, hΦ, hΦ, TateModule.compat])⟩⟩
      refine ⟨x, Subtype.ext (funext fun n => ?_)⟩
      rw [jT_apply]
      exact hΦ n
  ·
    intro τ'
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    show Φ H H₁ π hπt (τ' • (x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n) =
      τ' • Φ H H₁ π hπt ((x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n)
    exact Φ_smul hπt τ' _
  ·
    intro x
    constructor
    · intro hred n
      obtain ⟨w, f, hf, hfred⟩ := hred n
      obtain ⟨w', g, hg⟩ := Points.exists_mkAdd H₁ ((x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n)

      set W := max w w' with hW
      have hcmp : H.pointInclLE (AlgebraicClosure ℚ) (le_max_left w w') f =
          q H H₁ π W (H₁.pointInclLE (AlgebraicClosure ℚ) (le_max_right w w') g) := by
        rw [q_pointInclLE hπt, ← pointsMkAdd_eq_pointsMkAdd_iff (G := H), pointsMkAdd_pointInclLE,
          pointsMkAdd_pointInclLE, hf, jT_apply, ← hg, Φ_mkAdd]
      refine ⟨W, H₁.pointInclLE (AlgebraicClosure ℚ) (le_max_right w w') g, ?_, fun a => ?_⟩
      · rw [pointsMkAdd_pointInclLE, hg]
      · obtain ⟨b, rfl⟩ := hπ W a
        rw [← q_apply, ← hcmp, CoalgHomClass.counit_comp_apply]
        exact red_pointInclLE P (le_max_left w w') hfred b
    · intro hred n
      obtain ⟨w, f₁, hf₁, hred₁⟩ := hred n
      refine ⟨w, q H H₁ π w f₁, ?_, fun a => ?_⟩
      · rw [jT_apply, ← hf₁, Φ_mkAdd]
      · rw [q_apply, ← CoalgHomClass.counit_comp_apply (π w) a]
        exact hred₁ _

end
end S_PDivisibleGroup_exists_linearMap_tateModule_injective_of_surjective_comp_transition
end P2MW
export P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_injective_of_surjective_comp_transition (solution)
