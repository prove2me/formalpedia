-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/368e75ac-e31a-55f6-8ec9-9715e51bfc21

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PDivisibleGroup_CartierDuality
import Theorems.Thm_PDivisibleGroup_exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn
import Theorems.Thm_PDivisibleGroup_CartierDuality_exists_tateModule_pairing_eq_pair
import Theorems.Thm_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed
import Theorems.Thm_TateModule_nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} {H H' : PDivisibleGroup O p h} (D : H.CartierDuality H')

    (horth : ∀ (v : ℕ) (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
      (∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      D.pair (AlgebraicClosure ℚ) v f ψ = 1)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ)
    (hττ' : ∀ x : AlgebraicClosure ℚ, τ' x = τ x) (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (x : TateModule p (H.Points (AlgebraicClosure ℚ)))

    (hx : ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    H.tateModuleRep (AlgebraicClosure ℚ) τ' x =
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x := by
  classical

  have hup : ∀ (G : PDivisibleGroup O p h) (w : ℕ) (g : G.Point (AlgebraicClosure ℚ) w),
      (∀ a : G.level w, P.valuation (PDivisibleGroup.Point.toAlgHom g a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      ∀ a : G.level (w + 1), P.valuation (PDivisibleGroup.Point.toAlgHom (G.pointIncl (AlgebraicClosure ℚ) w g) a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1 := by
    intro G w g hg a
    rw [PDivisibleGroup.toAlgHom_pointIncl, AlgHom.comp_apply, ← G.counit_transition w a]
    exact hg _
  have hdown : ∀ (G : PDivisibleGroup O p h) (w : ℕ) (g : G.Point (AlgebraicClosure ℚ) w),
      (∀ a : G.level (w + 1), P.valuation (PDivisibleGroup.Point.toAlgHom (G.pointIncl (AlgebraicClosure ℚ) w g) a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      ∀ a : G.level w, P.valuation (PDivisibleGroup.Point.toAlgHom g a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1 := by
    intro G w g hg a
    obtain ⟨b, rfl⟩ := G.transition_surjective w a
    have := hg b
    rwa [PDivisibleGroup.toAlgHom_pointIncl, AlgHom.comp_apply, ← G.counit_transition w b] at this

  have hlevel : ∀ (G : PDivisibleGroup O p h) (s : TateModule p (G.Points (AlgebraicClosure ℚ))),
      (∀ n : ℕ, ∃ (w : ℕ) (f : G.Point (AlgebraicClosure ℚ) w),
        G.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (s : ℕ → G.Points (AlgebraicClosure ℚ)) n ∧
        ∀ a : G.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      ∀ v : ℕ, ∃ f : G.Point (AlgebraicClosure ℚ) v,
        G.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul f) = (s : ℕ → G.Points (AlgebraicClosure ℚ)) v ∧
        ∀ a : G.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1 := by
    intro G s hs v
    obtain ⟨w, f, hf, hff⟩ := hs v
    rcases le_total w v with hwv | hvw
    ·
      refine ⟨G.pointInclLE (AlgebraicClosure ℚ) hwv f, by rw [G.pointsMkAdd_pointInclLE]; exact hf, ?_⟩
      clear hf
      induction hwv with
      | refl => rw [G.pointInclLE_self]; exact hff
      | step hle ih => rw [G.pointInclLE_succ hle]; exact hup G _ _ ih
    ·
      have hpow : f ^ (p ^ v) = 1 := by
        have ht := TateModule.torsion s v
        rw [← hf, natCast_zsmul, ← map_nsmul, ← ofMul_pow] at ht
        exact Additive.ofMul.injective (G.pointsMkAdd_injective w (ht.trans (map_zero _).symm))
      obtain ⟨f', rfl⟩ := G.exists_pointInclLE_eq_of_pow_eq_one hvw f hpow
      refine ⟨f', by rw [← hf, G.pointsMkAdd_pointInclLE], ?_⟩
      clear hf hpow
      induction hvw with
      | refl => rw [G.pointInclLE_self] at hff; exact hff
      | step hle ih => rw [G.pointInclLE_succ hle] at hff; exact ih (hdown G _ _ hff)

  obtain ⟨⟨S, hS, -⟩, hinH⟩ :=
    PDivisibleGroup.exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn p P hOP H
  obtain ⟨⟨S', hS', -⟩, hinH'⟩ :=
    PDivisibleGroup.exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn p P hOP H'
  have hxS : x ∈ S := (hS x).2 hx
  have hτxS : H.tateModuleRep (AlgebraicClosure ℚ) τ' x ∈ S := by
    have hmem : H.tateModuleRep (AlgebraicClosure ℚ) τ' x - x ∈ S := (hS _).2 (hinH τ τ' hττ' hτ x)
    simpa using S.add_mem hmem hxS
  have hτyS' : ∀ y : TateModule p (H'.Points (AlgebraicClosure ℚ)), H'.tateModuleRep (AlgebraicClosure ℚ) τ' y - y ∈ S' := fun y =>
    (hS' _).2 (hinH' τ τ' hττ' hτ y)

  obtain ⟨B, hB, hBσ⟩ := D.exists_tateModule_pairing_eq_pair (AlgebraicClosure ℚ)

  have horthT : ∀ s ∈ S, ∀ s' ∈ S', B s s' = 0 := by
    intro s hs s' hs'
    refine Subtype.ext (funext fun v => ?_)
    obtain ⟨f, hf, hff⟩ := hlevel H s ((hS s).1 hs) v
    obtain ⟨ψ, hψ, hψf⟩ := hlevel H' s' ((hS' s').1 hs') v
    have hv := hB s s' v f ψ hf hψ
    rw [horth v f ψ hff hψf] at hv
    rw [TateModule.coe_zero, Pi.zero_apply]
    exact (congrArg Additive.ofMul (Units.ext hv)).trans ofMul_one

  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (p ^ i) := fun i => inferInstance
  let ι : TateModule p (Additive (AlgebraicClosure ℚ)ˣ) →ₗ[ℤ_[p]] TateModule p (Unit → Additive (AlgebraicClosure ℚ)ˣ) :=
    { toFun := fun z => ⟨fun v _ => (z : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v, fun v =>
        ⟨funext fun _ => by simpa using TateModule.torsion z v,
         funext fun _ => by simpa using TateModule.compat z v⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hιinj : Function.Injective ι := by
    intro z z' hzz'
    refine Subtype.ext (funext fun v => ?_)
    exact congrFun (congrFun (congrArg Subtype.val hzz') v) ()
  have hχ : ∀ (s : TateModule p (H.Points (AlgebraicClosure ℚ))) (y : TateModule p (H'.Points (AlgebraicClosure ℚ))),
      B (H.tateModuleRep (AlgebraicClosure ℚ) τ' s) (H'.tateModuleRep (AlgebraicClosure ℚ) τ' y) =
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • B s y := by
    intro s y
    apply hιinj
    rw [map_smul]
    refine (TateModule.nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq p (AlgebraicClosure ℚ) Unit).2
      τ.toRingEquiv _ _ fun v _ => ?_
    change ((Additive.toMul ((B (H.tateModuleRep (AlgebraicClosure ℚ) τ' s) (H'.tateModuleRep (AlgebraicClosure ℚ) τ' y) :
        ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      τ.toRingEquiv (((Additive.toMul ((B s y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    rw [hBσ τ' s y v]
    exact hττ' _

  have hall : ∀ y : TateModule p (H'.Points (AlgebraicClosure ℚ)),
      B (H.tateModuleRep (AlgebraicClosure ℚ) τ' x) y =
        B (((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x) y := by
    intro y
    have h1 := hχ x y
    have h2 : B (H.tateModuleRep (AlgebraicClosure ℚ) τ' x) (H'.tateModuleRep (AlgebraicClosure ℚ) τ' y) =
        B (H.tateModuleRep (AlgebraicClosure ℚ) τ' x) y := by
      have := horthT _ hτxS _ (hτyS' y)
      rw [map_sub, sub_eq_zero] at this
      exact this
    rw [map_smul, LinearMap.smul_apply, ← h1, h2]
  have hinj := (D.bijective_tateModule_pairing_of_isAlgClosed (AlgebraicClosure ℚ) B hB).2.1
  exact hinj (LinearMap.ext hall)

end S_PDivisibleGroup_CartierDuality_tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one (solution)
