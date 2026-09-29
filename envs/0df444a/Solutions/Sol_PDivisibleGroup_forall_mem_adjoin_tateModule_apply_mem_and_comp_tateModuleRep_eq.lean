-- Prove2me | solution 1 for PDivisibleGroup.forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/47d20858-862d-5e42-943d-d457bc27231c

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_PDivisibleGroup_tateModule_induced_mem_and_comm_and_add_and_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {h : ℕ} (H : PDivisibleGroup O p h)
    (u : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hU : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ)
      (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
        (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
      ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom f).comp (u w : H.level w →ₐ[O] H.level w)))))
    (S : Submodule ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hS : ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S ↔
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    ∀ V ∈ Algebra.adjoin ℤ_[p] ({U} : Set (Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))),
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S → V y ∈ S) ∧
      (∀ τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ,
        H.tateModuleRep (AlgebraicClosure ℚ) τ' ∘ₗ V = V ∘ₗ H.tateModuleRep (AlgebraicClosure ℚ) τ') := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    PDivisibleGroup.tateModule_induced_mem_and_comm_and_add_and_comp p P H S hS

  let Ind : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))) →
      (∀ w : ℕ, H.level w →ₐ[O] H.level w) → Prop := fun V v =>
    ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
      ((V x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom f).comp (v w))))

  let CP : (∀ w : ℕ, H.level w →ₐ[O] H.level w) → Prop := fun v =>
    ∀ w, (Bialgebra.counitAlgHom O (H.level w)).comp (v w) = Bialgebra.counitAlgHom O (H.level w)
  have hCP : ∀ v, CP v → ∀ (w : ℕ) (a : H.level w), Coalgebra.counit (R := O) (v w a) = Coalgebra.counit (R := O) a :=
    fun v hv w a => AlgHom.congr_fun (hv w) a

  have cp_mul : ∀ v v', CP v → CP v' → CP fun w => (WithConv.toConv (v w) * WithConv.toConv (v' w)).ofConv := by
    intro v v' hv hv' w
    show (Bialgebra.counitAlgHom O (H.level w)).comp (WithConv.toConv (v w) * WithConv.toConv (v' w)).ofConv = _
    rw [AlgHom.comp_convMul_distrib, WithConv.ofConv_toConv, WithConv.ofConv_toConv, hv w, hv' w]
    show (1 * 1 : WithConv (H.level w →ₐ[O] O)).ofConv = _
    rw [mul_one]
    rfl
  have cp_comp : ∀ v v', CP v → CP v' → CP fun w => (v' w).comp (v w) := by
    intro v v' hv hv' w
    show ((Bialgebra.counitAlgHom O (H.level w)).comp (v' w)).comp (v w) = _
    rw [hv' w, hv w]
  have cp_pow : ∀ (k : ℕ → ℕ), CP fun w => (WithConv.toConv (AlgHom.id O (H.level w)) ^ k w).ofConv := by
    intro k w
    show (Bialgebra.counitAlgHom O (H.level w)).comp ((WithConv.toConv (AlgHom.id O (H.level w))) ^ k w).ofConv = _
    rw [PDivisibleGroup.Hopf.algHom_comp_convPow, WithConv.ofConv_toConv, AlgHom.comp_id]
    show ((1 : WithConv (H.level w →ₐ[O] O)) ^ k w).ofConv = _
    rw [one_pow]
    rfl

  have key : ∀ V ∈ Algebra.adjoin ℤ_[p] ({U} : Set (Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))),
      ∃ v, Ind V v ∧ CP v := by
    intro V hV
    induction hV using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨fun w => (u w : H.level w →ₐ[O] H.level w), hU, fun w => ?_⟩
      exact BialgHom.counitAlgHom_comp (u w)
    | algebraMap r =>
      refine ⟨fun w => (WithConv.toConv (AlgHom.id O (H.level w)) ^ PadicInt.appr r w).ofConv, ?_, cp_pow _⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact h7 _ _ h5 r
    | add x y _ _ ihx ihy =>
      obtain ⟨v, hv, cv⟩ := ihx
      obtain ⟨v', hv', cv'⟩ := ihy
      exact ⟨_, h3 v v' x y hv hv', cp_mul v v' cv cv'⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨v, hv, cv⟩ := ihx
      obtain ⟨v', hv', cv'⟩ := ihy
      refine ⟨fun w => (v' w).comp (v w), ?_, cp_comp v v' cv cv'⟩
      rw [Module.End.mul_eq_comp]
      exact h4 v v' x y hv hv'
  intro V hV
  obtain ⟨v, hv, cv⟩ := key V hV
  exact ⟨h1 v V hv (hCP v cv), h2 v V hv⟩

end S_PDivisibleGroup_forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq
end P2MW
export P2MW.S_PDivisibleGroup_forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq (solution)
