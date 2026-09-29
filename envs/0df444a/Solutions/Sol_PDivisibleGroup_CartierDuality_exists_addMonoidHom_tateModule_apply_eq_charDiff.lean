-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_apply_eq_charDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ae83cabb-79d9-5594-ad61-c9f0528e24fb

import Mathlib
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Theorems.Thm_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_apply_eq_charDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false

open PDivisibleGroup
open scoped TensorProduct

namespace PDivHTFam

variable {R : Type} [CommRing R] {p h : ℕ}

section Lift

variable (G : PDivisibleGroup R p h) {L : Type} [CommRing L] [Algebra R L]

theorem exists_point_of_nsmul_eq_zero (v : ℕ) (z : G.Points L) (hz : (p ^ v) • z = 0) :
    ∃ f : G.Point L v, G.pointsMkAdd L v (Additive.ofMul f) = z := by
  obtain ⟨m, y, rfl⟩ := Points.exists_mkAdd G z
  set w := max m v
  have hy : G.pointsMkAdd L w (Additive.ofMul (G.pointInclLE L (le_max_left m v) y)) =
      G.pointsMkAdd L m (Additive.ofMul y) := G.pointsMkAdd_pointInclLE _ y
  rw [← hy] at hz ⊢
  set y' := G.pointInclLE L (le_max_left m v) y
  have hpow : y' ^ (p ^ v) = 1 := by
    apply G.pointsMkAdd_injective w
    change G.pointsMkAdd L w (Additive.ofMul (y' ^ p ^ v)) = G.pointsMkAdd L w (Additive.ofMul 1)
    rw [ofMul_pow, map_nsmul, hz, ofMul_one, map_zero]
  obtain ⟨x, hx⟩ := G.exists_pointInclLE_eq_of_pow_eq_one (le_max_right m v) y' hpow
  exact ⟨x, by rw [← hx, pointsMkAdd_pointInclLE]⟩

variable [Fact p.Prime]

omit [Fact p.Prime] in
theorem natCast_pow_zsmul_eq_nsmul (v : ℕ) (z : G.Points L) :
    ((p ^ v : ℕ) : ℤ) • z = (p ^ v) • z := natCast_zsmul z (p ^ v)

noncomputable def lift (x : TateModule p (G.Points L)) (v : ℕ) : G.Point L v :=
  Classical.choose (exists_point_of_nsmul_eq_zero G v ((x : ℕ → G.Points L) v)
    (by rw [← natCast_pow_zsmul_eq_nsmul]; exact TateModule.torsion x v))

omit [Fact p.Prime] in
theorem pointsMkAdd_lift (x : TateModule p (G.Points L)) (v : ℕ) :
    G.pointsMkAdd L v (Additive.ofMul (lift G x v)) = (x : ℕ → G.Points L) v :=
  Classical.choose_spec (exists_point_of_nsmul_eq_zero G v ((x : ℕ → G.Points L) v)
    (by rw [← natCast_pow_zsmul_eq_nsmul]; exact TateModule.torsion x v))

omit [Fact p.Prime] in
theorem lift_unique {x : TateModule p (G.Points L)} {v : ℕ} {f : G.Point L v}
    (hf : G.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → G.Points L) v) : f = lift G x v :=
  (G.pointsMkAdd_eq_pointsMkAdd_iff _ _).1 (by rw [hf, pointsMkAdd_lift])

omit [Fact p.Prime] in
theorem lift_add (x y : TateModule p (G.Points L)) (v : ℕ) :
    lift G (x + y) v = lift G x v * lift G y v := by
  symm
  apply lift_unique
  rw [ofMul_mul, map_add, pointsMkAdd_lift, pointsMkAdd_lift]
  rfl

theorem lift_smul (a : ℤ_[p]) (x : TateModule p (G.Points L)) (v : ℕ) :
    lift G (a • x) v = lift G x v ^ (a.appr v) := by
  symm
  apply lift_unique
  rw [ofMul_pow, map_nsmul, pointsMkAdd_lift, TateModule.smul_apply, natCast_zsmul]

omit [Fact p.Prime] in

theorem lift_succ_pow (x : TateModule p (G.Points L)) (v : ℕ) :
    lift G x (v + 1) ^ p = G.pointIncl L v (lift G x v) := by
  apply (G.pointsMkAdd_eq_pointsMkAdd_iff _ _).1
  rw [ofMul_pow, map_nsmul, pointsMkAdd_lift, pointsMkAdd_pointIncl, pointsMkAdd_lift, ← natCast_zsmul]
  exact TateModule.compat x v

theorem lift_rep (σ : L ≃ₐ[R] L) (x : TateModule p (G.Points L)) (v : ℕ) :
    lift G (G.tateModuleRep L σ x) v = G.pointMap (σ : L →ₐ[R] L) v (lift G x v) := by
  symm
  apply lift_unique
  rw [tateModuleRep_apply, ← Points.smul_pointsMkAdd, pointsMkAdd_lift]

end Lift

section Family

variable [Fact p.Prime] {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (S : Type) [CommRing S] [Algebra R S]

omit [Fact p.Prime] in

theorem charDiff_pow (v : ℕ) (ψ : G'.Point S v) (n : ℕ) :
    D.charDiff S v (ψ ^ n) = n • D.charDiff S v ψ := by
  have key := PDivisibleGroup.CartierDuality.charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
    D S v
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact key.2.2.2.2.2.1
  | succ n ih => rw [pow_succ, key.2.2.2.2.1, ih, succ_nsmul]

noncomputable def HT₀ (y : TateModule p (G'.Points S)) : (v : ℕ) → S ⊗[R] G.Cotangent v :=
  fun v => D.charDiff S v (lift G' y v)

theorem HT₀_add (y y' : TateModule p (G'.Points S)) : HT₀ D S (y + y') = HT₀ D S y + HT₀ D S y' := by
  funext v
  change D.charDiff S v (lift G' (y + y') v) = D.charDiff S v (lift G' y v) + D.charDiff S v (lift G' y' v)
  rw [lift_add]
  exact (PDivisibleGroup.CartierDuality.charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
    D S v).2.2.2.2.1 _ _

noncomputable def HT : TateModule p (G'.Points S) →+ ((v : ℕ) → S ⊗[R] G.Cotangent v) where
  toFun := HT₀ D S
  map_zero' := by
    have h0 := HT₀_add D S 0 0
    rw [add_zero] at h0
    exact left_eq_add.mp h0
  map_add' := HT₀_add D S

theorem HT_apply (y : TateModule p (G'.Points S)) (v : ℕ) : HT D S y v = D.charDiff S v (lift G' y v) :=
  rfl

theorem HT_level (y : TateModule p (G'.Points S)) (v : ℕ) (ψ : G'.Point S v)
    (hψ : G'.pointsMkAdd S v (Additive.ofMul ψ) = (y : ℕ → G'.Points S) v) :
    HT D S y v = D.charDiff S v ψ := by
  rw [HT_apply, ← lift_unique G' hψ]

theorem HT_compat (y : TateModule p (G'.Points S)) (v : ℕ) :
    (G.cotangentMap v).lTensor S (HT D S y (v + 1)) = HT D S y v := by
  rw [HT_apply, HT_apply]
  exact (PDivisibleGroup.CartierDuality.charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
    D S v).2.2.2.2.2.2.2.2.2 _ _ (lift_succ_pow G' y v).symm

theorem HT_smul (a : ℤ_[p]) (y : TateModule p (G'.Points S)) (v : ℕ) :
    HT D S (a • y) v = a.appr v • HT D S y v := by
  rw [HT_apply, HT_apply, lift_smul, charDiff_pow]

theorem HT_rep (σ : S ≃ₐ[R] S) (y : TateModule p (G'.Points S)) (v : ℕ) :
    HT D S (G'.tateModuleRep S σ y) v =
      TensorProduct.map (σ : S →ₐ[R] S).toLinearMap LinearMap.id (HT D S y v) := by
  rw [HT_apply, HT_apply, lift_rep]
  exact ((PDivisibleGroup.CartierDuality.charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
    D S v).2.2.2.2.2.2.2.1 S (σ : S →ₐ[R] S) _).symm

end Family

end PDivHTFam

open PDivHTFam in

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (S : Type) [CommRing S] [Algebra R S] :
    ∃ HT : TateModule p (G'.Points S) →+ ((v : ℕ) → TensorProduct R S (G.Cotangent v)),
      (∀ (y : TateModule p (G'.Points S)) (v : ℕ) (ψ : G'.Point S v),
          G'.pointsMkAdd S v (Additive.ofMul ψ) = (y : ℕ → G'.Points S) v →
            HT y v = D.charDiff S v ψ) ∧
      (∀ (y : TateModule p (G'.Points S)) (v : ℕ),
          (G.cotangentMap v).lTensor S (HT y (v + 1)) = HT y v) ∧
      (∀ (a : ℤ_[p]) (y : TateModule p (G'.Points S)) (v : ℕ), HT (a • y) v = a.appr v • HT y v) ∧
      (∀ (σ : S ≃ₐ[R] S) (y : TateModule p (G'.Points S)) (v : ℕ),
          HT (G'.tateModuleRep S σ y) v =
            TensorProduct.map (σ : S →ₐ[R] S).toLinearMap LinearMap.id (HT y v)) :=
  ⟨HT D S, HT_level D S, HT_compat D S, HT_smul D S, HT_rep D S⟩

end S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_apply_eq_charDiff
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_apply_eq_charDiff (solution)
