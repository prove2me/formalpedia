-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0c44a0a5-5a28-5116-a39b-c640400cc02e

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_TateModule_nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "CartierDuality Point Point.toAlgHom Point.one_apply pointIncl toAlgHom_pointIncl pointIncl_apply pointInclLE pointInclLE_self pointInclLE_succ exists_pointInclLE_eq_of_pow_eq_one Points pointsMkAdd pointsMkAdd_pointInclLE pointsMkAdd_injective pointMap toAlgHom_pointMap Points.smul_pointsMkAdd tateModuleRep tateModuleRep_apply counit_transition transition_surjective transition level"
namespace MultFrob
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

theorem convMul_apply_eq_sum (φ ψ : A →ₐ[O] ℚbar) (a : A) {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr O a ι𝓡) :
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

include hOP in
theorem redPt_div_of_forall {w : ℕ} (f g : H.Point ℚbar w)
    (hfg : ∀ b, P.valuation (PDivisibleGroup.Point.toAlgHom f b - PDivisibleGroup.Point.toAlgHom g b) < 1) :
    RedPt P H (f / g) := by
  rw [redPt_iff]
  intro a
  have h2 : ∀ b, P.valuation (PDivisibleGroup.Point.toAlgHom g⁻¹ b -
      PDivisibleGroup.Point.toAlgHom g⁻¹ b) < 1 := fun b => by
    rw [sub_self, Valuation.map_zero]; exact zero_lt_one
  have key := valuation_mul_sub_mul_lt_one P hOP _ _ _ _ hfg h2 a
  rwa [← toAlgHom_mul, ← toAlgHom_mul, mul_inv_cancel, ← div_eq_mul_inv] at key

theorem apply_mem_of_decomp (d : P.decompositionSubgroup ℚ) (t : ℚbar) (ht : t ∈ P) :
    (d : ℚbar ≃ₐ[ℚ] ℚbar) t ∈ P :=
  (d • (⟨t, ht⟩ : P)).2

theorem valuation_apply_lt_one_of_decomp (d : P.decompositionSubgroup ℚ) (t : ℚbar) (ht : t ∈ P)
    (hv : P.valuation t < 1) : P.valuation ((d : ℚbar ≃ₐ[ℚ] ℚbar) t) < 1 := by
  have h1 : (⟨t, ht⟩ : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [ValuationSubring.valuation_lt_one_iff]; exact hv
  have h2 : d • (⟨t, ht⟩ : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    intro hu
    apply h1
    have hu' := hu.map (MulSemiringAction.toRingEquiv _ P d).symm
    rwa [show d • (⟨t, ht⟩ : P) = MulSemiringAction.toRingEquiv _ P d ⟨t, ht⟩ from rfl,
      RingEquiv.symm_apply_apply] at hu'
  rw [ValuationSubring.valuation_lt_one_iff] at h2
  exact h2

theorem valuation_frob_sub_pow_lt_one {φ : ℚbar ≃ₐ[ℚ] ℚbar} (hφ : P.IsFrobeniusAt φ p)
    (t : ℚbar) (ht : t ∈ P) : P.valuation (φ t - t ^ p) < 1 := by
  have h1 := hφ.smul_residue_eq (IsLocalRing.residue P ⟨t, ht⟩)
  rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow] at h1
  have h2 : (⟨φ, hφ.mem_decompositionSubgroup⟩ : P.decompositionSubgroup ℚ) • (⟨t, ht⟩ : P) - ⟨t, ht⟩ ^ p ∈
      IsLocalRing.maximalIdeal P :=
    (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal P)).1 h1
  rw [ValuationSubring.valuation_lt_one_iff] at h2
  exact h2

end PDivisibleGroup.MultFrob

open PDivisibleGroup.MultFrob in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} {H H' : PDivisibleGroup O p h} (D : H.CartierDuality H')

    (ε : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hεtr : ∀ v : ℕ, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))

    (horth : ∀ (v : ℕ) (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
      (∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (PDivisibleGroup.Point.toAlgHom f).comp (ε v : H.level v →ₐ[O] H.level v) =
        PDivisibleGroup.Point.toAlgHom f →
      (∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      D.pair (AlgebraicClosure ℚ) v f ψ = 1)

    (B : TateModule p (H.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]]
      TateModule p (H'.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (Additive (AlgebraicClosure ℚ)ˣ))
    (hB : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (y : TateModule p (H'.Points (AlgebraicClosure ℚ)))
        (v : ℕ) (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
        H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) v →
        H'.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) v →
        ((Additive.toMul ((B x y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ) = D.pair (AlgebraicClosure ℚ) v f ψ)
    (hBσ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ) (x : TateModule p (H.Points (AlgebraicClosure ℚ)))
        (y : TateModule p (H'.Points (AlgebraicClosure ℚ))) (v : ℕ),
        ((Additive.toMul ((B (H.tateModuleRep (AlgebraicClosure ℚ) σ x)
            (H'.tateModuleRep (AlgebraicClosure ℚ) σ y) : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) :
            (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
          σ (((Additive.toMul ((B x y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) :
            AlgebraicClosure ℚ)))

    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (φ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ)
    (hφφ' : ∀ t : AlgebraicClosure ℚ, φ' t = φ t) (hφ : P.IsFrobeniusAt φ p)

    (x : TateModule p (H.Points (AlgebraicClosure ℚ)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      (∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧
      (PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w) =
        PDivisibleGroup.Point.toAlgHom f)

    (y z : TateModule p (H'.Points (AlgebraicClosure ℚ)))
    (hyz : ∀ n : ℕ, ∃ (w : ℕ) (ψ χ : H'.Point (AlgebraicClosure ℚ) w),
      H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
      H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul χ) = (z : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
      (∀ a : H'.level w, PDivisibleGroup.Point.toAlgHom ψ a ∈ P) ∧
      ∀ a : H'.level w, P.valuation (PDivisibleGroup.Point.toAlgHom χ a -
        PDivisibleGroup.Point.toAlgHom ψ a ^ p) < 1) :
    B (H.tateModuleRep (AlgebraicClosure ℚ) φ' x) z =
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • B x y := by
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

  have hsup : ∀ (w : ℕ) (g : H.Point (AlgebraicClosure ℚ) w),
      (PDivisibleGroup.Point.toAlgHom g).comp (ε w : H.level w →ₐ[O] H.level w) = PDivisibleGroup.Point.toAlgHom g →
      (PDivisibleGroup.Point.toAlgHom (H.pointIncl (AlgebraicClosure ℚ) w g)).comp
          (ε (w + 1) : H.level (w + 1) →ₐ[O] H.level (w + 1)) =
        PDivisibleGroup.Point.toAlgHom (H.pointIncl (AlgebraicClosure ℚ) w g) := by
    intro w g hg
    apply AlgHom.ext; intro a
    rw [AlgHom.comp_apply, PDivisibleGroup.toAlgHom_pointIncl, AlgHom.comp_apply, AlgHom.comp_apply]
    have h1 : (H.transition w : H.level (w + 1) →ₐ[O] H.level w) ((ε (w + 1) : H.level (w + 1) →ₐ[O] H.level (w + 1)) a) =
        (ε w : H.level w →ₐ[O] H.level w) ((H.transition w : H.level (w + 1) →ₐ[O] H.level w) a) := by
      have := DFunLike.congr_fun (hεtr w) a
      simp only [BialgHom.comp_apply] at this
      exact this
    rw [h1, ← AlgHom.comp_apply (PDivisibleGroup.Point.toAlgHom g), hg]
  have hsdown : ∀ (w : ℕ) (g : H.Point (AlgebraicClosure ℚ) w),
      (PDivisibleGroup.Point.toAlgHom (H.pointIncl (AlgebraicClosure ℚ) w g)).comp
          (ε (w + 1) : H.level (w + 1) →ₐ[O] H.level (w + 1)) =
        PDivisibleGroup.Point.toAlgHom (H.pointIncl (AlgebraicClosure ℚ) w g) →
      (PDivisibleGroup.Point.toAlgHom g).comp (ε w : H.level w →ₐ[O] H.level w) = PDivisibleGroup.Point.toAlgHom g := by
    intro w g hg
    apply AlgHom.ext; intro a
    obtain ⟨b, rfl⟩ := H.transition_surjective w a
    have := DFunLike.congr_fun hg b
    rw [AlgHom.comp_apply, PDivisibleGroup.toAlgHom_pointIncl, AlgHom.comp_apply, AlgHom.comp_apply] at this
    have h1 : (H.transition w : H.level (w + 1) →ₐ[O] H.level w) ((ε (w + 1) : H.level (w + 1) →ₐ[O] H.level (w + 1)) b) =
        (ε w : H.level w →ₐ[O] H.level w) ((H.transition w : H.level (w + 1) →ₐ[O] H.level w) b) := by
      have := DFunLike.congr_fun (hεtr w) b
      simp only [BialgHom.comp_apply] at this
      exact this
    rw [h1] at this
    rw [AlgHom.comp_apply]
    exact this
  have hlevelε : ∀ (s : TateModule p (H.Points (AlgebraicClosure ℚ))),
      (∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (s : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
        (∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧
        (PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w) = PDivisibleGroup.Point.toAlgHom f) →
      ∀ v : ℕ, ∃ f : H.Point (AlgebraicClosure ℚ) v,
        H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul f) = (s : ℕ → H.Points (AlgebraicClosure ℚ)) v ∧
        (∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧
        (PDivisibleGroup.Point.toAlgHom f).comp (ε v : H.level v →ₐ[O] H.level v) = PDivisibleGroup.Point.toAlgHom f := by
    intro s hs v
    obtain ⟨w, f, hf, hff, hfε⟩ := hs v
    rcases le_total w v with hwv | hvw
    · refine ⟨H.pointInclLE (AlgebraicClosure ℚ) hwv f, by rw [H.pointsMkAdd_pointInclLE]; exact hf, ?_⟩
      clear hf
      induction hwv with
      | refl => rw [H.pointInclLE_self]; exact ⟨hff, hfε⟩
      | step hle ih =>
        rw [H.pointInclLE_succ hle]
        exact ⟨hup H _ _ ih.1, hsup _ _ ih.2⟩
    · have hpow : f ^ (p ^ v) = 1 := by
        have ht := TateModule.torsion s v
        rw [← hf, natCast_zsmul, ← map_nsmul, ← ofMul_pow] at ht
        exact Additive.ofMul.injective (H.pointsMkAdd_injective w (ht.trans (map_zero _).symm))
      obtain ⟨f', rfl⟩ := H.exists_pointInclLE_eq_of_pow_eq_one hvw f hpow
      refine ⟨f', by rw [← hf, H.pointsMkAdd_pointInclLE], ?_⟩
      clear hf hpow
      induction hvw with
      | refl => rw [H.pointInclLE_self] at hff hfε; exact ⟨hff, hfε⟩
      | step hle ih =>
        rw [H.pointInclLE_succ hle] at hff hfε
        exact ih (hdown H _ _ hff) (hsdown _ _ hfε)

  let d : P.decompositionSubgroup ℚ := ⟨φ, hφ.mem_decompositionSubgroup⟩
  have hdφ : ∀ t, (d : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) t = φ t := fun t => rfl
  have hφP : ∀ t ∈ P, φ' t ∈ P := fun t ht => by
    rw [hφφ']; exact apply_mem_of_decomp d t ht
  have hφm : ∀ t ∈ P, P.valuation t < 1 → P.valuation (φ' t) < 1 := fun t ht hv => by
    rw [hφφ']; exact valuation_apply_lt_one_of_decomp d t ht hv

  have hφx : ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
        ((H.tateModuleRep (AlgebraicClosure ℚ) φ' x : TateModule p (H.Points (AlgebraicClosure ℚ))) :
          ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      (∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧
      (PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w) = PDivisibleGroup.Point.toAlgHom f := by
    intro n
    obtain ⟨w, f, hf, hff, hfε⟩ := hx n
    refine ⟨w, H.pointMap (φ' : AlgebraicClosure ℚ →ₐ[O] AlgebraicClosure ℚ) w f, ?_, fun a => ?_, ?_⟩
    · rw [PDivisibleGroup.tateModuleRep_apply, ← hf, PDivisibleGroup.Points.smul_pointsMkAdd]
    rotate_right
    · rw [PDivisibleGroup.toAlgHom_pointMap, AlgHom.comp_assoc, hfε]
    · rw [PDivisibleGroup.toAlgHom_pointMap, AlgHom.comp_apply]
      have e1 : (φ' : AlgebraicClosure ℚ →ₐ[O] AlgebraicClosure ℚ) (PDivisibleGroup.Point.toAlgHom f a) -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a) =
          φ' (PDivisibleGroup.Point.toAlgHom f a - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) := by
        rw [map_sub, AlgEquiv.commutes]; rfl
      rw [e1]
      exact hφm _ (P.sub_mem (apply_mem P hOP _ a) (hOP _)) (hff a)

  have hzy : ∀ n : ℕ, ∃ (w : ℕ) (g : H'.Point (AlgebraicClosure ℚ) w),
      H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul g) =
        ((z - H'.tateModuleRep (AlgebraicClosure ℚ) φ' y : TateModule p (H'.Points (AlgebraicClosure ℚ))) :
          ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
      ∀ a : H'.level w, P.valuation (PDivisibleGroup.Point.toAlgHom g a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1 := by
    intro n
    obtain ⟨w, ψ, χ, hψ, hχ, hint, hfrob⟩ := hyz n
    refine ⟨w, χ / H'.pointMap (φ' : AlgebraicClosure ℚ →ₐ[O] AlgebraicClosure ℚ) w ψ, ?_, ?_⟩
    · rw [ofMul_div, map_sub, hχ, TateModule.coe_sub, Pi.sub_apply, PDivisibleGroup.tateModuleRep_apply, ← hψ,
        PDivisibleGroup.Points.smul_pointsMkAdd]
    · refine redPt_div_of_forall hOP χ _ fun b => ?_
      rw [PDivisibleGroup.toAlgHom_pointMap, AlgHom.comp_apply]
      rw [show (φ' : AlgebraicClosure ℚ →ₐ[O] AlgebraicClosure ℚ) (PDivisibleGroup.Point.toAlgHom ψ b) =
        φ (PDivisibleGroup.Point.toAlgHom ψ b) from hφφ' _]
      have hsplit : PDivisibleGroup.Point.toAlgHom χ b - φ (PDivisibleGroup.Point.toAlgHom ψ b) =
          (PDivisibleGroup.Point.toAlgHom χ b - PDivisibleGroup.Point.toAlgHom ψ b ^ p) +
            -(φ (PDivisibleGroup.Point.toAlgHom ψ b) - PDivisibleGroup.Point.toAlgHom ψ b ^ p) := by ring
      rw [hsplit]
      refine Valuation.map_add_lt _ (hfrob b) ?_
      rw [Valuation.map_neg]
      exact valuation_frob_sub_pow_lt_one hφ _ (hint b)

  have horthT : ∀ (s : TateModule p (H.Points (AlgebraicClosure ℚ))) (s' : TateModule p (H'.Points (AlgebraicClosure ℚ))),
      (∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (s : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
        (∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧
        (PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w) = PDivisibleGroup.Point.toAlgHom f) →
      (∀ n : ℕ, ∃ (w : ℕ) (f : H'.Point (AlgebraicClosure ℚ) w),
        H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (s' : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
        ∀ a : H'.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      B s s' = 0 := by
    intro s s' hs hs'
    refine Subtype.ext (funext fun v => ?_)
    obtain ⟨f, hf, hff, hfε⟩ := hlevelε s hs v
    obtain ⟨ψ, hψ, hψf⟩ := hlevel H' s' hs' v
    have hv := hB s s' v f ψ hf hψ
    rw [horth v f ψ hff hfε hψf] at hv
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
      B (H.tateModuleRep (AlgebraicClosure ℚ) φ' s) (H'.tateModuleRep (AlgebraicClosure ℚ) φ' y) =
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • B s y := by
    intro s y
    apply hιinj
    rw [map_smul]
    refine (TateModule.nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq p (AlgebraicClosure ℚ) Unit).2
      φ.toRingEquiv _ _ fun v _ => ?_
    change ((Additive.toMul ((B (H.tateModuleRep (AlgebraicClosure ℚ) φ' s) (H'.tateModuleRep (AlgebraicClosure ℚ) φ' y) :
        ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      φ.toRingEquiv (((Additive.toMul ((B s y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    rw [hBσ φ' s y v]
    exact hφφ' _

  have hsplit : z = H'.tateModuleRep (AlgebraicClosure ℚ) φ' y + (z - H'.tateModuleRep (AlgebraicClosure ℚ) φ' y) := by
    abel
  rw [hsplit, map_add, hχ x y, horthT _ _ hφx hzy, add_zero]

end S_PDivisibleGroup_CartierDuality_tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one (solution)
