-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1e091e12-9419-56c7-bf95-488141e059b3

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate Quaternion

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk Affine.Point.some Affine.degree_polynomial Affine.Point.some.inj map_id toAffine Affine.Point Affine.nonsingular_neg Affine.monic_polynomial baseChange j b₄ evalEvalBC rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet exists_isDualPair_of_mem_rationalHomSet card_torsion_of_isAlgClosed exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq"
namespace HomSeparatesTorsion
p2m_open "WeierstrassCurve"

section Helper

variable {k : Type*} [Field k]

theorem exists_eq_some' {W : WeierstrassCurve k} {P : W.toAffine.Point} {u v u' v' : k}
    {h₀ : W.toAffine.Nonsingular u v} (hP : P = .some u v h₀) (hu : u = u') (hv : v = v') :
    ∃ h'', P = .some u' v' h'' := by
  subst hu hv
  exact ⟨h₀, hP⟩

theorem exists_nonsingular [IsAlgClosed k] (W : WeierstrassCurve k) [W.IsElliptic] (x : k) :
    ∃ y : k, W.toAffine.Nonsingular x y := by
  have hdeg : (W.toAffine.polynomial.map (Polynomial.evalRingHom x)).degree ≠ 0 := by
    rw [WeierstrassCurve.Affine.monic_polynomial.degree_map, WeierstrassCurve.Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, (W.toAffine.equation_iff_nonsingular).mp ?_⟩
  rw [Polynomial.IsRoot.def, Polynomial.map_evalRingHom_eval] at hy
  exact hy

scoped instance instIsEllipticBaseChangeSelf (W : WeierstrassCurve k) [W.IsElliptic] : (W.baseChange k).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap k k)).IsElliptic)

end Helper

section HomSet

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero.WeierstrassCurve"

variable {κ : Type*} [Field κ] [DecidableEq κ]

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve κ}
    {α : (W₁.baseChange κ).toAffine.Point →+ (W₂.baseChange κ).toAffine.Point} (hα : α ∈ rationalHomSet κ W₁ W₂) :
    -α ∈ rationalHomSet κ W₁ W₂ := by
  rcases hα with rfl | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · rw [neg_zero]; exact zero_mem_rationalHomSet κ W₁ W₂
  refine Or.inr ⟨nX, dX, -(nY * dX) - C (C W₂.a₁) * nX * dY - C (C W₂.a₃) * dX * dY, dY * dX, B, hB, ?_⟩
  intro x y h hx
  obtain ⟨hdX, hdY, h', hP⟩ := hrep x y h hx
  have hbc : ∀ q : κ[X][Y], evalEvalBC (F := κ) κ q x y = q.evalEval x y := by
    intro q; simp [evalEvalBC, Polynomial.map_id]
  refine ⟨hdX, by rw [hbc, evalEval_mul]; rw [hbc] at hdX hdY; exact mul_ne_zero hdY hdX, ?_⟩
  have hneg : (-α) (.some x y h) =
      .some (evalEvalBC (F := κ) κ nX x y / evalEvalBC (F := κ) κ dX x y)
        ((W₂.baseChange κ).toAffine.negY (evalEvalBC (F := κ) κ nX x y / evalEvalBC (F := κ) κ dX x y)
          (evalEvalBC (F := κ) κ nY x y / evalEvalBC (F := κ) κ dY x y))
        ((Affine.nonsingular_neg ..).mpr h') := by
    rw [AddMonoidHom.neg_apply, hP]; rfl
  refine exists_eq_some' hneg rfl ?_
  simp only [hbc] at hdX hdY ⊢
  simp only [Affine.negY, evalEval_sub, evalEval_neg, evalEval_mul, evalEval_C, eval_C]
  change -(nY.evalEval x y / dY.evalEval x y) - W₂.a₁ * (nX.evalEval x y / dX.evalEval x y) - W₂.a₃ = _
  field_simp

theorem nsmul_mem_rationalHomSet [IsAlgClosed κ] {W₁ W₂ : WeierstrassCurve κ} [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange κ).toAffine.Point →+ (W₂.baseChange κ).toAffine.Point} (hα : α ∈ rationalHomSet κ W₁ W₂)
    (n : ℕ) : n • α ∈ rationalHomSet κ W₁ W₂ := by
  induction n with
  | zero => rw [zero_nsmul]; exact zero_mem_rationalHomSet κ W₁ W₂
  | succ n ih => rw [succ_nsmul]; exact add_mem_rationalHomSet κ W₁ W₂ ih hα

theorem zsmul_mem_rationalHomSet [IsAlgClosed κ] {W₁ W₂ : WeierstrassCurve κ} [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange κ).toAffine.Point →+ (W₂.baseChange κ).toAffine.Point} (hα : α ∈ rationalHomSet κ W₁ W₂)
    (c : ℤ) : c • α ∈ rationalHomSet κ W₁ W₂ := by
  induction c using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet κ W₁ W₂
  | succ n ih => rw [add_zsmul, one_zsmul]; exact add_mem_rationalHomSet κ W₁ W₂ ih hα
  | pred n ih =>
    rw [sub_zsmul, one_zsmul]
    exact add_mem_rationalHomSet κ W₁ W₂ ih (neg_mem_rationalHomSet hα)

theorem mem_rationalHomSet_of_mem_rationalEndSubring [IsAlgClosed κ] {W : WeierstrassCurve κ} [W.IsElliptic]
    {f : AddMonoid.End (W.baseChange κ).toAffine.Point} (hf : f ∈ rationalEndSubring κ W) :
    (f : (W.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point) ∈ rationalHomSet κ W W := by
  induction hf using Subring.closure_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem_rationalHomSet κ W W
  | one => exact id_mem_rationalHomSet κ W
  | add x y _ _ hx hy => exact add_mem_rationalHomSet κ W W hx hy
  | neg x _ hx => exact neg_mem_rationalHomSet hx
  | mul x y _ _ hx hy => exact comp_mem_rationalHomSet κ W W W hy hx

omit [DecidableEq κ] in
theorem infinite_point [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] :
    Infinite (W.baseChange κ).toAffine.Point := by
  choose f hf using exists_nonsingular (W.baseChange κ)
  refine Infinite.of_injective (fun x : κ => (Affine.Point.some x (f x) (hf x) : (W.baseChange κ).toAffine.Point)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

theorem exists_nsmul_ne_zero [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (hW : ∀ P : (W.baseChange κ).toAffine.Point, p • P = 0 → P = 0) {N : ℕ} (hN : N ≠ 0) :
    ∃ P : (W.baseChange κ).toAffine.Point, N • P ≠ 0 := by
  obtain ⟨k, m, hm, hNkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p (Fact.out : p.Prime).ne_one
  have hstrip : ∀ (j : ℕ) (P : (W.baseChange κ).toAffine.Point), (p ^ j) • P = 0 → P = 0 := by
    intro j
    induction j with
    | zero => intro P hP; simpa using hP
    | succ j ih =>
      intro P hP
      rw [pow_succ, mul_smul] at hP
      exact hW P (ih _ hP)
  by_contra hall
  push Not at hall
  have hm0 : m ≠ 0 := by rintro rfl; simp at hNkm; exact hN hNkm
  have hmκ : ((m : ℕ) : κ) ≠ 0 := fun h => hm ((CharP.cast_eq_zero_iff κ p m).mp h)
  have htors : ∀ P : (W.baseChange κ).toAffine.Point, P ∈ Submodule.torsionBy ℤ _ (m : ℤ) := by
    intro P
    rw [Submodule.mem_torsionBy_iff]
    have h1 : (p ^ k) • (m • P) = 0 := by
      rw [← mul_smul, ← hNkm]
      exact hall P
    have h2 := hstrip k _ h1
    rw [natCast_zsmul]
    exact h2
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W (n := m) hmκ
  haveI : Finite ↥(Submodule.torsionBy ℤ (W.baseChange κ).toAffine.Point (m : ℤ)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact pow_ne_zero 2 hm0
  haveI := infinite_point W
  haveI : Finite (W.baseChange κ).toAffine.Point :=
    Finite.of_injective (fun P => (⟨P, htors P⟩ : ↥(Submodule.torsionBy ℤ _ (m : ℤ))))
      (fun P Q h => congrArg Subtype.val h)
  exact not_finite (W.baseChange κ).toAffine.Point

end HomSet

section Lattice

open QuaternionAlgebra

variable {a b : ℚ}

scoped instance instIsAddTorsionFree : IsAddTorsionFree ℍ[ℚ, a, b] where
  nsmul_right_injective n hn x y hxy := by
    have : (n : ℚ) • x = (n : ℚ) • y := by rwa [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hn) this

theorem finrank_eq_four_of_isOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) :
    haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛ.fg
    Module.finrank ℤ Λ = 4 := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛ.fg
  let bΛ := Module.Free.chooseBasis ℤ Λ
  set v : Module.Free.ChooseBasisIndex ℤ Λ → ℍ[ℚ, a, b] := fun i => (bΛ i : ℍ[ℚ, a, b]) with hv
  have hli : LinearIndependent ℤ v := bΛ.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)
  have hliQ : LinearIndependent ℚ v := hli.localization ℚ (nonZeroDivisors ℤ)
  have hspan : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    rw [← hΛ.spanTop]
    apply Submodule.span_le.mpr
    intro z hz
    have hz' : (⟨z, hz⟩ : Λ) ∈ Submodule.span ℤ (Set.range bΛ) := by rw [bΛ.span_eq]; trivial
    have := Submodule.apply_mem_span_image_of_mem_span (Λ.subtype) hz'
    rw [← Set.range_comp] at this
    exact Submodule.span_le_restrictScalars ℤ ℚ _ this
  let bQ : Module.Basis _ ℚ ℍ[ℚ, a, b] := Module.Basis.mk hliQ hspan
  rw [Module.finrank_eq_card_chooseBasisIndex, ← QuaternionAlgebra.finrank_eq_four (R := ℚ) (c₁ := a) (c₂ := (0:ℚ)) (c₃ := b),
    Module.finrank_eq_card_basis bQ]

set_option synthInstance.maxHeartbeats 800000 in

theorem exists_incongruent (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (L : Submodule ℤ ℍ[ℚ, a, b]) (hL : L ≤ Λ)
    {n : ℤ} (hn : n ≠ 0) (hnL : ∀ z ∈ Λ, n • z ∈ L) (ℓ : ℕ) [NeZero ℓ] :
    ∃ x : (Fin 4 → ZMod ℓ) → ℍ[ℚ, a, b], (∀ d, x d ∈ L) ∧
      ∀ d d', (∃ y ∈ L, x d - x d' = (ℓ : ℤ) • y) → d = d' := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛ.fg
  have hΛ4 := finrank_eq_four_of_isOrder Λ hΛ
  let LΛ : Submodule ℤ Λ := L.comap Λ.subtype

  let f : Λ →ₗ[ℤ] Λ := n • LinearMap.id
  have hf : Function.Injective f := by
    intro z z' h
    apply Subtype.ext
    have h' : (n : ℚ) • (z : ℍ[ℚ, a, b]) = (n : ℚ) • (z' : ℍ[ℚ, a, b]) := by
      have := congrArg Subtype.val h
      simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul, Int.cast_smul_eq_zsmul] using this
    exact smul_right_injective _ (Int.cast_ne_zero.mpr hn) h'
  have hfL : LinearMap.range f ≤ LΛ := by
    rintro _ ⟨z, rfl⟩
    show Λ.subtype (n • z) ∈ L
    rw [map_zsmul]
    exact hnL z z.2
  have h4 : Module.finrank ℤ LΛ = 4 := by
    refine le_antisymm ?_ ?_
    · exact (Submodule.finrank_le LΛ).trans hΛ4.le
    · calc 4 = Module.finrank ℤ Λ := hΛ4.symm
        _ = Module.finrank ℤ (LinearMap.range f) := (LinearMap.finrank_range_of_inj hf).symm
        _ ≤ Module.finrank ℤ LΛ := Submodule.finrank_mono hfL
  let bL := Module.finBasisOfFinrankEq ℤ LΛ h4
  let Xd : (Fin 4 → ZMod ℓ) → LΛ := fun d => ∑ i, ((d i).val : ℤ) • bL i
  refine ⟨fun d => ((Xd d : Λ) : ℍ[ℚ, a, b]), fun d => (Xd d).2, ?_⟩
  rintro d d' ⟨y, hy, hxy⟩
  let yΛ : LΛ := ⟨⟨y, hL hy⟩, hy⟩
  have hX : Xd d - Xd d' = (ℓ : ℤ) • yΛ := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hxy
  funext i
  have hi := congrArg (fun z => bL.repr z i) hX
  simp only [Xd] at hi
  rw [map_sub, map_zsmul, Finsupp.sub_apply, Finsupp.smul_apply,
    Module.Basis.repr_sum_self, Module.Basis.repr_sum_self, smul_eq_mul] at hi

  apply ZMod.val_injective
  have h1 : ((d i).val : ℤ) < ℓ := by exact_mod_cast (d i).val_lt
  have h2 : ((d' i).val : ℤ) < ℓ := by exact_mod_cast (d' i).val_lt
  have hdvd : (ℓ : ℤ) ∣ ((d i).val : ℤ) - ((d' i).val : ℤ) := ⟨_, hi⟩
  have := Int.eq_of_sub_eq_zero (Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega))
  exact_mod_cast this

end Lattice

section TorsionLinAlg

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem exists_spanning_pair (v : ZMod ℓ × ZMod ℓ) (hv : v ≠ 0) :
    ∃ w : ZMod ℓ × ZMod ℓ, ∀ u : ZMod ℓ × ZMod ℓ, ∃ α β : ZMod ℓ, u = α • v + β • w := by
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := by
      intro h2; apply hv; ext <;> assumption
    refine ⟨(1, 0), fun u => ⟨u.2 / v.2, u.1, ?_⟩⟩
    ext
    · simp [h1]
    · simp [div_mul_cancel₀ _ h2]
  · refine ⟨(0, 1), fun u => ⟨u.1 / v.1, u.2 - u.1 / v.1 * v.2, ?_⟩⟩
    ext
    · simp [div_mul_cancel₀ _ h1]
    · simp

end TorsionLinAlg

section Main

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero.WeierstrassCurve QuaternionAlgebra"

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

abbrev Pt (W : WeierstrassCurve κ) := (W.baseChange κ).toAffine.Point

theorem main (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic]
    (a b : ℚ) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (_hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (χ : Pt X₀ →+ Pt W) (hχ : χ ∈ rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q')
    (Q : Pt W) (hQ : ℓ • Q = 0) (hQ0 : Q ≠ 0) :
    ∃ ρ ∈ rationalHomSet κ W X₀, ρ Q ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓκ : (ℓ : κ) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff κ q' ℓ).mp h
    exact hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q'.Prime) hℓ).mp this).symm
  by_contra hall
  push Not at hall

  let toEnd : ∀ ρ : Pt W →+ Pt X₀, ρ ∈ rationalHomSet κ W X₀ → rationalEndSubring κ X₀ := fun ρ hρ =>
    ⟨ρ.comp χ, Subring.subset_closure (WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W X₀ hχ hρ)⟩
  have toEnd_add : ∀ ρ ρ' hρ hρ', toEnd (ρ + ρ') (add_mem_rationalHomSet κ W X₀ hρ hρ') = toEnd ρ hρ + toEnd ρ' hρ' :=
    fun _ _ _ _ => Subtype.ext (AddMonoidHom.add_comp _ _ _)
  have toEnd_zsmul : ∀ (c : ℤ) ρ hρ, toEnd (c • ρ) (zsmul_mem_rationalHomSet hρ c) = c • toEnd ρ hρ :=
    fun _ _ _ => Subtype.ext (AddMonoidHom.ext fun _ => rfl)

  let L : Submodule ℤ ℍ[ℚ, a, b] :=
    { carrier := {z | ∃ ρ, ∃ hρ : ρ ∈ rationalHomSet κ W X₀, θ (toEnd ρ hρ) = z}
      add_mem' := by
        rintro _ _ ⟨ρ, hρ, rfl⟩ ⟨ρ', hρ', rfl⟩
        exact ⟨ρ + ρ', add_mem_rationalHomSet κ W X₀ hρ hρ', by rw [toEnd_add ρ ρ' hρ hρ', map_add]⟩
      zero_mem' := ⟨0, zero_mem_rationalHomSet κ W X₀, by
        rw [show toEnd 0 (zero_mem_rationalHomSet κ W X₀) = 0 from Subtype.ext (AddMonoidHom.zero_comp χ), map_zero]⟩
      smul_mem' := by
        rintro c _ ⟨ρ, hρ, rfl⟩
        exact ⟨c • ρ, zsmul_mem_rationalHomSet hρ c, by rw [toEnd_zsmul c ρ hρ, map_zsmul]⟩ }
  have hLmem : ∀ ρ hρ, θ (toEnd ρ hρ) ∈ L := fun ρ hρ => ⟨ρ, hρ, rfl⟩
  have hLΛ : L ≤ Λ := by
    rintro _ ⟨ρ, hρ, rfl⟩
    show θ (toEnd ρ hρ) ∈ (Λ : Set ℍ[ℚ, a, b])
    rw [← hθΛ]
    exact ⟨_, rfl⟩

  obtain ⟨σ, hσ, n, hn, hdual⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₀ W hχ hχ0
  have hnL : ∀ z ∈ Λ, n • z ∈ L := by
    intro z hz
    have hz' : z ∈ Set.range θ := by rw [hθΛ]; exact hz
    obtain ⟨e, rfl⟩ := hz'
    have he : ((e : AddMonoid.End (Pt X₀)) : Pt X₀ →+ Pt X₀) ∈ rationalHomSet κ X₀ X₀ :=
      mem_rationalHomSet_of_mem_rationalEndSubring e.2
    have hρ : ((e : AddMonoid.End (Pt X₀)) : Pt X₀ →+ Pt X₀).comp σ ∈ rationalHomSet κ W X₀ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ W X₀ X₀ hσ he
    refine ⟨_, hρ, ?_⟩
    have key : toEnd _ hρ = (n : rationalEndSubring κ X₀) * e := by
      apply Subtype.ext
      rw [Subring.coe_mul, SubringClass.coe_intCast]
      apply AddMonoidHom.ext
      intro P
      show (e : AddMonoid.End (Pt X₀)) (σ (χ P)) = ((n : AddMonoid.End (Pt X₀)) * (e : AddMonoid.End (Pt X₀))) P
      rw [hdual.comp_left P, map_zsmul]
      rfl
    rw [key, map_mul, map_intCast, zsmul_eq_mul]

  obtain ⟨x, hxL, hxinj⟩ := exists_incongruent Λ hΛ L hLΛ hn.ne' hnL ℓ
  choose ρ hρ hρx using fun d => (hxL d)

  have hdist : ∀ d d', (∀ P : Pt W, ℓ • P = 0 → ρ d P = ρ d' P) → d = d' := by
    intro d d' hP
    have hδ : ρ d - ρ d' ∈ rationalHomSet κ W X₀ :=
      sub_eq_add_neg (ρ d) (ρ d') ▸ add_mem_rationalHomSet κ W X₀ (hρ d) (neg_mem_rationalHomSet (hρ d'))
    obtain ⟨β, hβ, hβδ⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W X₀ hℓκ hδ
      (fun P hP0 => by
        rw [AddMonoidHom.sub_apply, sub_eq_zero]
        exact hP P (by rwa [natCast_zsmul] at hP0))
    refine hxinj d d' ⟨θ (toEnd β hβ), hLmem β hβ, ?_⟩
    rw [← hρx d, ← hρx d', ← map_zsmul, ← toEnd_zsmul (ℓ : ℤ) β hβ, ← map_sub]
    congr 1
    rw [sub_eq_iff_eq_add, ← toEnd_add _ _ (zsmul_mem_rationalHomSet hβ ℓ) (hρ d')]
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    show ρ d (χ P) = ((ℓ : ℤ) • β) (χ P) + ρ d' (χ P)
    rw [AddMonoidHom.smul_apply, ← hβδ, AddMonoidHom.sub_apply, sub_add_cancel]

  have hcardW : Nat.card {P : Pt W // ℓ • P = 0} = ℓ ^ 2 := by
    rw [← WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W (n := ℓ) hℓκ]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun P => by rw [Submodule.mem_torsionBy_iff, natCast_zsmul])
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq (Ω := κ) W ℓ hℓκ hcardW
  have hQt : Q ∈ Submodule.torsionBy ℤ (Pt W) ℓ := by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hQ
  set v := eT.symm ⟨Q, hQt⟩ with hv
  have hv0 : v ≠ 0 := by
    intro h0
    apply hQ0
    have : eT v = ⟨Q, hQt⟩ := by rw [hv, AddEquiv.apply_symm_apply]
    rw [h0, map_zero] at this
    exact (congrArg Subtype.val this).symm
  obtain ⟨w, hvw⟩ := exists_spanning_pair v hv0

  have hgen : ∀ P : Pt W, ℓ • P = 0 → ∃ α β : ℕ, P = α • Q + β • ((eT w : Submodule.torsionBy ℤ (Pt W) ℓ) : Pt W) := by
    intro P hP
    have hPt : P ∈ Submodule.torsionBy ℤ (Pt W) ℓ := by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hP
    obtain ⟨α, β, hu⟩ := hvw (eT.symm ⟨P, hPt⟩)
    refine ⟨α.val, β.val, ?_⟩
    have h1 : eT (eT.symm ⟨P, hPt⟩) = eT (α • v + β • w) := by rw [hu]
    rw [AddEquiv.apply_symm_apply, map_add, ← ZMod.natCast_zmod_val α, ← ZMod.natCast_zmod_val β,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul, map_nsmul, hv, AddEquiv.apply_symm_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_add, AddSubmonoidClass.coe_nsmul, AddSubmonoidClass.coe_nsmul] at h2
    exact h2

  set R : Pt W := ((eT w : Submodule.torsionBy ℤ (Pt W) ℓ) : Pt W) with hR
  have hRℓ : ℓ • R = 0 := by
    have := (eT w).2
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at this
    exact this
  let F : (Fin 4 → ZMod ℓ) → {P : Pt X₀ // ℓ • P = 0} := fun d => ⟨ρ d R, by rw [← map_nsmul, hRℓ, map_zero]⟩
  have hF : Function.Injective F := by
    intro d d' h
    have h' : ρ d R = ρ d' R := congrArg Subtype.val h
    refine hdist d d' fun P hP => ?_
    obtain ⟨α, β, rfl⟩ := hgen P hP
    rw [map_add, map_add, map_nsmul, map_nsmul, map_nsmul, map_nsmul, hall _ (hρ d), hall _ (hρ d'), h']
  have hcardX : Nat.card {P : Pt X₀ // ℓ • P = 0} = ℓ ^ 2 := by
    rw [← WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) X₀ (n := ℓ) hℓκ]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun P => by rw [Submodule.mem_torsionBy_iff, natCast_zsmul])
  haveI : Finite {P : Pt X₀ // ℓ • P = 0} := Nat.finite_of_card_ne_zero (by rw [hcardX]; exact pow_ne_zero 2 hℓ.ne_zero)
  have hle := Nat.card_le_card_of_injective F hF
  rw [hcardX, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  have h2 : 2 ≤ ℓ := hℓ.two_le
  have : ℓ ^ 2 < ℓ ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

end Main

end WeierstrassCurve.HomSeparatesTorsion
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero.WeierstrassCurve.HomSeparatesTorsion"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero.WeierstrassCurve"

open scoped Quaternion in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic]
    (a b : ℚ) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q')
    (Q : (W.baseChange κ).toAffine.Point) (hQ : ℓ • Q = 0) (hQ0 : Q ≠ 0) :
    ∃ ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀, ρ Q ≠ 0 :=
  WeierstrassCurve.HomSeparatesTorsion.main q' X₀ a b Λ hΛ θ hθ hθΛ W χ hχ hχ0 ℓ hℓ hℓq Q hQ hQ0

end S_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_ne_zero_of_prime_nsmul_eq_zero (solution)
