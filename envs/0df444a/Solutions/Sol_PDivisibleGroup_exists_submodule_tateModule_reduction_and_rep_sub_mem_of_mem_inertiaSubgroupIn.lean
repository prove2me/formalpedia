-- Prove2me | solution 1 for PDivisibleGroup.exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/290d442f-0c09-57cd-a45f-8261aa74a465

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Point Point.toAlgHom Point.one_apply pointIncl pointIncl_apply pointInclLE pointInclLE_self pointInclLE_succ Points pointsMkAdd pointsMkAdd_pointInclLE Points.exists_mkAdd pointMap toAlgHom_pointMap Points.smul_pointsMkAdd tateModuleRep tateModuleRep_apply counit_transition transition level"
namespace KerRed
p2m_open "PDivisibleGroup"

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
variable (P : ValuationSubring (AlgebraicClosure ℚ))
variable (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
variable {h : ℕ} (H : PDivisibleGroup O p h)

local notation "ℚbar" => AlgebraicClosure ℚ

section Integral

variable {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A]

include hOP in

theorem apply_mem (φ : A →ₐ[O] ℚbar) (a : A) : φ a ∈ P := by

  let ι : O →+* P :=
    { toFun := fun x => ⟨algebraMap O ℚbar x, hOP x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  letI : Algebra O P := ι.toAlgebra
  haveI : IsScalarTower O P ℚbar := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have hint : IsIntegral O (φ a) := (Algebra.IsIntegral.isIntegral (R := O) a).map φ
  have hint' : IsIntegral P (φ a) := hint.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := ℚbar)).1 hint'
  rw [← hy]
  exact y.2

include hOP in
theorem valuation_apply_le_one (φ : A →ₐ[O] ℚbar) (a : A) : P.valuation (φ a) ≤ 1 :=
  (P.valuation_le_one_iff _).2 (apply_mem P hOP φ a)

end Integral

section Conv

variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A]

theorem mul_lt_one_of_le_of_lt {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
  calc a * b ≤ 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ < 1 := hb

theorem convMul_apply_eq_sum (φ ψ : A →ₐ[O] ℚbar) (a : A) {ι : Type*} (𝓡 : Coalgebra.Repr O a ι) :
    (WithConv.toConv φ * WithConv.toConv ψ) a = ∑ i ∈ 𝓡.index, φ (𝓡.left i) * ψ (𝓡.right i) := by
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, ← 𝓡.eq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.lift_tmul]

include hOP in

theorem valuation_mul_sub_mul_lt_one (φ φ' ψ ψ' : A →ₐ[O] ℚbar)
    (hφ : ∀ a, P.valuation (φ a - φ' a) < 1) (hψ : ∀ a, P.valuation (ψ a - ψ' a) < 1) (a : A) :
    P.valuation ((WithConv.toConv φ * WithConv.toConv ψ) a -
      (WithConv.toConv φ' * WithConv.toConv ψ') a) < 1 := by
  let 𝓡 := Coalgebra.Repr.arbitrary O a
  rw [convMul_apply_eq_sum φ ψ a 𝓡, convMul_apply_eq_sum φ' ψ' a 𝓡, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
  have hsplit : φ (𝓡.left i) * ψ (𝓡.right i) - φ' (𝓡.left i) * ψ' (𝓡.right i) =
      (φ (𝓡.left i) - φ' (𝓡.left i)) * ψ (𝓡.right i) +
        φ' (𝓡.left i) * (ψ (𝓡.right i) - ψ' (𝓡.right i)) := by ring
  rw [hsplit]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [Valuation.map_mul, mul_comm]
    exact mul_lt_one_of_le_of_lt (valuation_apply_le_one P hOP ψ _) (hφ _)
  · rw [Valuation.map_mul]
    exact mul_lt_one_of_le_of_lt (valuation_apply_le_one P hOP φ' _) (hψ _)

end Conv

def RedPt {w : ℕ} (f : H.Point ℚbar w) : Prop :=
  ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
    algebraMap O ℚbar (Coalgebra.counit a)) < 1

variable {P H}

theorem redPt_one (w : ℕ) : RedPt P H (1 : H.Point ℚbar w) := fun a => by
  rw [PDivisibleGroup.Point.one_apply, sub_self, Valuation.map_zero]
  exact zero_lt_one

theorem redPt_iff {w : ℕ} (f : H.Point ℚbar w) :
    RedPt P H f ↔ ∀ a, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
      PDivisibleGroup.Point.toAlgHom (1 : H.Point ℚbar w) a) < 1 := by
  simp only [RedPt, PDivisibleGroup.Point.one_apply]

theorem toAlgHom_mul {w : ℕ} (f g : H.Point ℚbar w) (a : H.level w) :
    PDivisibleGroup.Point.toAlgHom (f * g) a =
      (WithConv.toConv (PDivisibleGroup.Point.toAlgHom f) *
        WithConv.toConv (PDivisibleGroup.Point.toAlgHom g)) a := rfl

include hOP in
theorem redPt_mul {w : ℕ} {f g : H.Point ℚbar w} (hf : RedPt P H f) (hg : RedPt P H g) :
    RedPt P H (f * g) := by
  rw [redPt_iff] at hf hg ⊢
  intro a
  have key := valuation_mul_sub_mul_lt_one P hOP (PDivisibleGroup.Point.toAlgHom f)
    (PDivisibleGroup.Point.toAlgHom (1 : H.Point ℚbar w)) (PDivisibleGroup.Point.toAlgHom g)
    (PDivisibleGroup.Point.toAlgHom (1 : H.Point ℚbar w)) hf hg a
  rwa [← toAlgHom_mul, ← toAlgHom_mul, mul_one] at key

include hOP in
theorem redPt_pow {w : ℕ} {f : H.Point ℚbar w} (hf : RedPt P H f) (m : ℕ) : RedPt P H (f ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact redPt_one w
  | succ m ih => rw [pow_succ]; exact redPt_mul hOP ih hf

include hOP in

theorem redPt_inv {w : ℕ} {f : H.Point ℚbar w} (hf : RedPt P H f) : RedPt P H f⁻¹ := by
  rw [redPt_iff] at hf ⊢
  intro a
  have h1 : ∀ b, P.valuation (PDivisibleGroup.Point.toAlgHom f⁻¹ b -
      PDivisibleGroup.Point.toAlgHom f⁻¹ b) < 1 := fun b => by
    rw [sub_self, Valuation.map_zero]; exact zero_lt_one
  have h2 : ∀ b, P.valuation (PDivisibleGroup.Point.toAlgHom (1 : H.Point ℚbar w) b -
      PDivisibleGroup.Point.toAlgHom f b) < 1 := fun b => by
    rw [← Valuation.map_neg, neg_sub]; exact hf b
  have key := valuation_mul_sub_mul_lt_one P hOP _ _ _ _ h1 h2 a
  rwa [← toAlgHom_mul, ← toAlgHom_mul, mul_one, inv_mul_cancel] at key

include hOP in
theorem redPt_div {w : ℕ} {f g : H.Point ℚbar w} (hf : RedPt P H f) (hg : RedPt P H g) :
    RedPt P H (f / g) := by
  rw [div_eq_mul_inv]; exact redPt_mul hOP hf (redPt_inv hOP hg)

theorem redPt_pointIncl {w : ℕ} {f : H.Point ℚbar w} (hf : RedPt P H f) :
    RedPt P H (H.pointIncl ℚbar w f) := fun a => by
  rw [PDivisibleGroup.pointIncl_apply, ← H.counit_transition w a]
  exact hf _

theorem redPt_pointInclLE {v w : ℕ} (hvw : v ≤ w) {f : H.Point ℚbar v} (hf : RedPt P H f) :
    RedPt P H (H.pointInclLE ℚbar hvw f) := by
  induction hvw with
  | refl => rwa [H.pointInclLE_self]
  | step hvw ih => rw [H.pointInclLE_succ hvw]; exact redPt_pointIncl ih

include hOP in

theorem redPt_pointMap_div (τ' : ℚbar ≃ₐ[O] ℚbar) (hτ : ∀ x ∈ P, P.valuation (τ' x - x) < 1)
    {w : ℕ} (f : H.Point ℚbar w) : RedPt P H (H.pointMap (τ' : ℚbar →ₐ[O] ℚbar) w f / f) := by
  rw [redPt_iff]
  intro a
  have h1 : ∀ b, P.valuation (PDivisibleGroup.Point.toAlgHom (H.pointMap (τ' : ℚbar →ₐ[O] ℚbar) w f) b -
      PDivisibleGroup.Point.toAlgHom f b) < 1 := fun b => by
    rw [PDivisibleGroup.toAlgHom_pointMap, AlgHom.comp_apply]
    exact hτ _ (apply_mem P hOP _ b)
  have h2 : ∀ b, P.valuation (PDivisibleGroup.Point.toAlgHom f⁻¹ b -
      PDivisibleGroup.Point.toAlgHom f⁻¹ b) < 1 := fun b => by
    rw [sub_self, Valuation.map_zero]; exact zero_lt_one
  have key := valuation_mul_sub_mul_lt_one P hOP _ _ _ _ h1 h2 a
  rwa [← toAlgHom_mul, ← toAlgHom_mul, mul_inv_cancel, ← div_eq_mul_inv] at key

variable (P H) in

def RedId (y : TateModule p (H.Points ℚbar)) : Prop :=
  ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point ℚbar w),
    H.pointsMkAdd ℚbar w (Additive.ofMul f) = (y : ℕ → H.Points ℚbar) n ∧
    ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
      algebraMap O ℚbar (Coalgebra.counit a)) < 1

theorem redId_zero : RedId P H 0 := fun n =>
  ⟨0, 1, by rw [ofMul_one, map_zero]; rfl, redPt_one 0⟩

include hOP in
theorem redId_add {x y : TateModule p (H.Points ℚbar)} (hx : RedId P H x) (hy : RedId P H y) :
    RedId P H (x + y) := by
  intro n
  obtain ⟨w, f, hf, hfr⟩ := hx n
  obtain ⟨w', g, hg, hgr⟩ := hy n
  refine ⟨max w w', H.pointInclLE ℚbar (le_max_left w w') f * H.pointInclLE ℚbar (le_max_right w w') g,
    ?_, redPt_mul hOP (redPt_pointInclLE _ hfr) (redPt_pointInclLE _ hgr)⟩
  rw [ofMul_mul, map_add, H.pointsMkAdd_pointInclLE, H.pointsMkAdd_pointInclLE, hf, hg,
    TateModule.coe_add, Pi.add_apply]

include hOP in
theorem redId_smul (a : ℤ_[p]) {x : TateModule p (H.Points ℚbar)} (hx : RedId P H x) :
    RedId P H (a • x) := by
  intro n
  obtain ⟨w, f, hf, hfr⟩ := hx n
  refine ⟨w, f ^ (a.appr n), ?_, redPt_pow hOP hfr _⟩
  rw [ofMul_pow, map_nsmul, hf, TateModule.smul_apply, natCast_zsmul]

theorem redId_of_p_smul {x : TateModule p (H.Points ℚbar)} (hx : RedId P H ((p : ℤ_[p]) • x)) :
    RedId P H x := by
  intro n
  obtain ⟨w, f, hf, hfr⟩ := hx (n + 1)
  refine ⟨w, f, ?_, hfr⟩
  rw [hf, TateModule.natCast_padicInt_smul_apply]
  exact TateModule.compat x n

variable (P H) in

def kerRed (hOP : ∀ x : O, algebraMap O ℚbar x ∈ P) : Submodule ℤ_[p] (TateModule p (H.Points ℚbar)) where
  carrier := {y | RedId P H y}
  add_mem' hx hy := redId_add hOP hx hy
  zero_mem' := redId_zero
  smul_mem' a x hx := redId_smul hOP a hx

theorem valuation_sub_lt_one_of_mem_inertiaSubgroupIn {τ : ℚbar ≃ₐ[ℚ] ℚbar}
    (hτ : τ ∈ P.inertiaSubgroupIn ℚ) (x : ℚbar) (hx : x ∈ P) : P.valuation (τ x - x) < 1 := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hτ
  have hker : MulSemiringAction.toRingAut (P.decompositionSubgroup ℚ) (IsLocalRing.ResidueField P) d = 1 :=
    hd
  have h1 : d • IsLocalRing.residue P ⟨x, hx⟩ = IsLocalRing.residue P ⟨x, hx⟩ := by
    have h := DFunLike.congr_fun hker (IsLocalRing.residue P ⟨x, hx⟩)
    exact h
  rw [← IsLocalRing.ResidueField.residue_smul] at h1
  have h2 : d • (⟨x, hx⟩ : P) - ⟨x, hx⟩ ∈ IsLocalRing.maximalIdeal P :=
    (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal P)).1 h1
  rw [ValuationSubring.valuation_lt_one_iff] at h2
  exact h2

include hOP in
theorem redId_rep_sub (τ : ℚbar ≃ₐ[ℚ] ℚbar) (τ' : ℚbar ≃ₐ[O] ℚbar) (hττ' : ∀ x, τ' x = τ x)
    (hτ : τ ∈ P.inertiaSubgroupIn ℚ) (x : TateModule p (H.Points ℚbar)) :
    RedId P H (H.tateModuleRep ℚbar τ' x - x) := by
  have hτ' : ∀ y ∈ P, P.valuation (τ' y - y) < 1 := fun y hy => by
    rw [hττ']; exact valuation_sub_lt_one_of_mem_inertiaSubgroupIn hτ y hy
  intro n
  obtain ⟨w, f, hf⟩ := PDivisibleGroup.Points.exists_mkAdd H ((x : ℕ → H.Points ℚbar) n)
  refine ⟨w, H.pointMap (τ' : ℚbar →ₐ[O] ℚbar) w f / f, ?_, redPt_pointMap_div hOP τ' hτ' f⟩
  rw [ofMul_div, map_sub, hf, TateModule.coe_sub, Pi.sub_apply, PDivisibleGroup.tateModuleRep_apply,
    ← hf, PDivisibleGroup.Points.smul_pointsMkAdd]

end PDivisibleGroup.KerRed

open PDivisibleGroup.KerRed in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} (H : PDivisibleGroup O p h) :
    (∃ S : Submodule ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))),
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S ↔
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧
      ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), (p : ℤ_[p]) • y ∈ S → y ∈ S) ∧
    ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → τ ∈ P.inertiaSubgroupIn ℚ →
      ∀ x : TateModule p (H.Points (AlgebraicClosure ℚ)),
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            ((H.tateModuleRep (AlgebraicClosure ℚ) τ' x - x :
              TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1 :=
  ⟨⟨kerRed P H hOP, fun _ => Iff.rfl, fun _ hy => redId_of_p_smul hy⟩,
    fun τ τ' hττ' hτ x => redId_rep_sub hOP τ τ' hττ' hτ x⟩

end S_PDivisibleGroup_exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_PDivisibleGroup_exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn (solution)
