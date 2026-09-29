-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c9c00031-2bc4-5e3b-8382-f250246392bb

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.CoordinateRing.smul_basis_eq_zero a₃ a₁ map Affine.CoordinateRing.norm_smul_basis Affine.CoordinateRing Affine.CoordinateRing.smul variableChange_a₃ mk a₄ a₂ a₆ Affine.Point.some variableChange_a₆ Affine.degree_polynomial Affine.Point.some.inj Affine.map_polynomial variableChange_a₂ toAffine Affine.Point Affine.monic_polynomial Affine.CoordinateRing.degree_norm_smul_basis variableChange_a₁ variableChange_a₄ VariableChange Affine.equation_iff baseChange evalEvalBC IsRationallyRepresented rationalHomSet exists_polynomial_rep_of_injective_of_mem_rationalHomSet"
namespace RationalHomInverse
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing"

section Subst

variable {S : Type*} [CommRing S]

noncomputable def substXY (P Q : S[X][Y]) : S[X][Y] →+* S[X][Y] :=
  eval₂RingHom (eval₂RingHom (C.comp C) P) Q

@[scoped simp] theorem substXY_CC (P Q : S[X][Y]) (c : S) : substXY P Q (C (C c)) = C (C c) := by
  simp [substXY]

@[scoped simp] theorem substXY_CX (P Q : S[X][Y]) : substXY P Q (C X) = P := by
  simp [substXY]

@[scoped simp] theorem substXY_Y (P Q : S[X][Y]) : substXY P Q Y = Q := by
  simp [substXY]

theorem ringHom_ext_CXY {T : Type*} [Semiring T] {φ ψ : S[X][Y] →+* T}
    (hC : ∀ c, φ (C (C c)) = ψ (C (C c))) (hX : φ (C X) = ψ (C X)) (hY : φ Y = ψ Y) : φ = ψ :=
  Polynomial.ringHom_ext (fun p => by
    have : φ.comp C = ψ.comp C :=
      Polynomial.ringHom_ext (fun c => by simpa using hC c) (by simpa using hX)
    exact RingHom.congr_fun this p) hY

theorem evalEval_substXY (P Q G : S[X][Y]) (x y : S) :
    (substXY P Q G).evalEval x y = G.evalEval (P.evalEval x y) (Q.evalEval x y) := by
  have : (evalEvalRingHom x y).comp (substXY P Q) =
      evalEvalRingHom (P.evalEval x y) (Q.evalEval x y) :=
    ringHom_ext_CXY (fun c => by simp) (by simp) (by simp)
  exact RingHom.congr_fun this G

noncomputable def lin (p q : S[X]) : S[X][Y] := C p + C q * Y

theorem evalEval_lin (p q : S[X]) (x y : S) : (lin p q).evalEval x y = p.eval x + q.eval x * y := by
  rw [lin, evalEval_add, evalEval_mul, evalEval_C, evalEval_C, evalEval_X]

end Subst

section OverK

variable {k : Type*} [Field k]

theorem eq_zero_of_norm_eq_zero (E : Affine k) {p q : k[X]}
    (h : p ^ 2 - p * q * (C E.a₁ * X + C E.a₃) -
      q ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) = 0) : p = 0 ∧ q = 0 := by
  classical
  have key : Algebra.norm k[X] (p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y) = 0 := by
    rw [Affine.CoordinateRing.norm_smul_basis]; exact h
  haveI : Module.Free k[X] E.CoordinateRing := Module.Free.of_basis (CoordinateRing.basis E)
  haveI : Module.Finite k[X] E.CoordinateRing := Module.Finite.of_basis (CoordinateRing.basis E)
  rw [Algebra.norm_eq_zero_iff] at key
  exact Affine.CoordinateRing.smul_basis_eq_zero key

theorem smul_basis_ne_zero (E : Affine k) {p q : k[X]} (h : p ≠ 0 ∨ q ≠ 0) :
    p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y ≠ 0 := by
  intro h0
  obtain ⟨hp, hq⟩ := Affine.CoordinateRing.smul_basis_eq_zero h0
  rcases h with h | h
  · exact h hp
  · exact h hq

theorem natDegree_norm_smul_basis (E : Affine k) (p : k[X]) {q : k[X]} (hq : q ≠ 0) :
    (Algebra.norm k[X] (p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y)).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  classical
  have hn0 : Algebra.norm k[X] (p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y) ≠ 0 := by
    intro h0
    rw [Affine.CoordinateRing.norm_smul_basis] at h0
    exact hq (eq_zero_of_norm_eq_zero E h0).right
  have hdeg := Affine.CoordinateRing.degree_norm_smul_basis (W' := E) p q
  rw [degree_eq_natDegree hn0, degree_eq_natDegree hq] at hdeg
  by_cases hp : p = 0
  · subst hp
    rw [degree_zero, two_nsmul, WithBot.bot_add, max_bot_left] at hdeg
    rw [natDegree_zero, mul_zero, Nat.zero_max]
    have h' : ((Algebra.norm k[X] ((0 : k[X]) • (1 : E.CoordinateRing) +
        q • CoordinateRing.mk E Y)).natDegree : WithBot ℕ) = ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) := by
      rw [hdeg]; norm_cast
    exact_mod_cast h'
  · rw [degree_eq_natDegree hp] at hdeg
    have h' : ((Algebra.norm k[X] (p • (1 : E.CoordinateRing) +
        q • CoordinateRing.mk E Y)).natDegree : WithBot ℕ) =
        max ((2 * p.natDegree : ℕ) : WithBot ℕ) ((2 * q.natDegree + 3 : ℕ)) := by
      rw [hdeg]; norm_cast
    simp only [Nat.cast_withBot] at h'
    rw [← WithBot.coe_max] at h'
    exact_mod_cast h'

theorem natDegree_norm_smul_basis_zero (E : Affine k) (p : k[X]) :
    (Algebra.norm k[X] (p • (1 : E.CoordinateRing) + (0 : k[X]) • CoordinateRing.mk E Y)).natDegree =
      2 * p.natDegree := by
  rw [Affine.CoordinateRing.norm_smul_basis]
  simp [natDegree_pow]

theorem shape_of_natDegree_norm_eq_two (E : Affine k) {p q : k[X]}
    (h : (Algebra.norm k[X] (p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y)).natDegree = 2) :
    q = 0 ∧ p.natDegree = 1 := by
  by_cases hq : q = 0
  · subst hq
    rw [natDegree_norm_smul_basis_zero] at h
    exact ⟨rfl, by omega⟩
  · rw [natDegree_norm_smul_basis E p hq] at h
    omega

theorem shape_of_natDegree_norm_eq_three (E : Affine k) {p q : k[X]}
    (h : (Algebra.norm k[X] (p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y)).natDegree = 3) :
    q ≠ 0 ∧ q.natDegree = 0 ∧ p.natDegree ≤ 1 := by
  by_cases hq : q = 0
  · subst hq
    rw [natDegree_norm_smul_basis_zero] at h
    omega
  · rw [natDegree_norm_smul_basis E p hq] at h
    exact ⟨hq, by omega, by omega⟩

theorem exists_nonsingular (E : Affine k) [IsAlgClosed k] [E.IsElliptic] (x : k) :
    ∃ y, E.Nonsingular x y := by
  have hdeg : (E.polynomial.map (evalRingHom x)).degree ≠ 0 := by
    rw [Affine.monic_polynomial.degree_map, Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, (E.equation_iff_nonsingular).mp ?_⟩
  rw [IsRoot.def, map_evalRingHom_eval] at hy
  exact hy

theorem norm_eval_eq_zero (E : Affine k) {p q : k[X]} {x y : k} (hxy : E.Equation x y)
    (h0 : p.eval x + q.eval x * y = 0) :
    (p ^ 2 - p * q * (C E.a₁ * X + C E.a₃) -
      q ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)).eval x = 0 := by
  rw [Affine.equation_iff] at hxy
  simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X]
  linear_combination (q.eval x) ^ 2 * hxy +
    (p.eval x - q.eval x * y - q.eval x * (E.a₁ * x + E.a₃)) * h0

theorem eq_zero_of_eval_eq_zero (E : Affine k) [IsAlgClosed k] [E.IsElliptic] {p q : k[X]}
    {B : Set k} (hB : B.Finite)
    (hf : ∀ x y, E.Nonsingular x y → x ∉ B → p.eval x + q.eval x * y = 0) :
    p = 0 ∧ q = 0 := by
  refine eq_zero_of_norm_eq_zero E ?_
  by_contra hN
  refine hB.infinite_compl ((Polynomial.finite_setOf_isRoot hN).subset fun x hx => ?_)
  obtain ⟨y, hy⟩ := exists_nonsingular E x
  exact norm_eval_eq_zero E hy.left (hf x y hy hx)

theorem mk_eq_zero_of_evalEval (E : Affine k) [IsAlgClosed k] [E.IsElliptic] {G : k[X][Y]}
    {B : Set k} (hB : B.Finite) (hG : ∀ x y, E.Nonsingular x y → x ∉ B → G.evalEval x y = 0) :
    CoordinateRing.mk E G = 0 := by
  set r : k[X][Y] := G %ₘ E.polynomial with hr_def
  have hne1 : E.polynomial ≠ 1 := by
    intro h
    have := E.natDegree_polynomial
    rw [h, natDegree_one] at this
    exact absurd this (by norm_num)
  have hr : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt G E.monic_polynomial hne1
    rw [E.natDegree_polynomial] at this
    exact Nat.lt_succ_iff.mp this
  have hGr : r + E.polynomial * (G /ₘ E.polynomial) = G := modByMonic_add_div G E.polynomial
  have hreq : r = C (r.coeff 1) * Y + C (r.coeff 0) := eq_X_add_C_of_natDegree_le_one hr
  have hpq : ∀ x y : k, E.Equation x y →
      G.evalEval x y = (r.coeff 0).eval x + (r.coeff 1).eval x * y := by
    intro x y hxy
    have h0 : E.polynomial.evalEval x y = 0 := hxy
    have hr_eval : r.evalEval x y = (r.coeff 0).eval x + (r.coeff 1).eval x * y := by
      conv_lhs => rw [hreq]
      rw [evalEval_add, evalEval_mul, evalEval_C, evalEval_C, evalEval_X]
      ring
    rw [← hGr, evalEval_add, evalEval_mul, h0, zero_mul, add_zero, hr_eval]
  have hG' : CoordinateRing.mk E G = CoordinateRing.mk E r := by
    rw [← hGr, map_add, map_mul]
    change _ + AdjoinRoot.mk E.polynomial E.polynomial * _ = _
    rw [AdjoinRoot.mk_self, zero_mul, add_zero]
  obtain ⟨h0, h1⟩ := eq_zero_of_eval_eq_zero E hB (fun x y hxy hx => by
    rw [← hpq x y hxy.left]; exact hG x y hxy hx)
  rw [hG', hreq, h0, h1]
  simp

section Comap

variable (E E' : Affine k) (ΦX ΦY : k[X][Y])

noncomputable def comap (h₁ : CoordinateRing.mk E (substXY ΦX ΦY E'.polynomial) = 0) :
    E'.CoordinateRing →+* E.CoordinateRing :=
  AdjoinRoot.lift ((CoordinateRing.mk E).comp (eval₂RingHom (C.comp C) ΦX))
    (CoordinateRing.mk E ΦY) (by rwa [substXY, coe_eval₂RingHom, hom_eval₂] at h₁)

variable {E E' ΦX ΦY}

theorem comap_mk (h₁ : CoordinateRing.mk E (substXY ΦX ΦY E'.polynomial) = 0) (G : k[X][Y]) :
    comap E E' ΦX ΦY h₁ (CoordinateRing.mk E' G) = CoordinateRing.mk E (substXY ΦX ΦY G) := by
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk _ G) = _
  rw [AdjoinRoot.lift_mk, substXY, coe_eval₂RingHom, hom_eval₂]

theorem comap_algebraMap (h₁ : CoordinateRing.mk E (substXY ΦX ΦY E'.polynomial) = 0) (c : k) :
    comap E E' ΦX ΦY h₁ (algebraMap k E'.CoordinateRing c) = algebraMap k E.CoordinateRing c := by
  have h1 : algebraMap k E'.CoordinateRing c = CoordinateRing.mk E' (C (C c)) := rfl
  have h2 : algebraMap k E.CoordinateRing c = CoordinateRing.mk E (C (C c)) := rfl
  rw [h1, h2, comap_mk, substXY_CC]

theorem comap_comp_comap {ΦX' ΦY' : k[X][Y]}
    (h₁ : CoordinateRing.mk E (substXY ΦX ΦY E'.polynomial) = 0)
    (h₁' : CoordinateRing.mk E' (substXY ΦX' ΦY' E.polynomial) = 0)
    (h₂ : CoordinateRing.mk E' (substXY ΦX' ΦY' ΦX) = CoordinateRing.mk E' (C X))
    (h₃ : CoordinateRing.mk E' (substXY ΦX' ΦY' ΦY) = CoordinateRing.mk E' Y) :
    (comap E' E ΦX' ΦY' h₁').comp (comap E E' ΦX ΦY h₁) = RingHom.id _ := by
  have key : ((comap E' E ΦX' ΦY' h₁').comp (comap E E' ΦX ΦY h₁)).comp (CoordinateRing.mk E') =
      (RingHom.id _).comp (CoordinateRing.mk E') := by
    refine ringHom_ext_CXY (fun c => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, comap_mk, substXY_CC, RingHom.id_apply]
    · simp only [RingHom.comp_apply, comap_mk, substXY_CX, RingHom.id_apply, h₂]
    · simp only [RingHom.comp_apply, comap_mk, substXY_Y, RingHom.id_apply, h₃]
  refine RingHom.ext fun z => ?_
  obtain ⟨G, rfl⟩ := AdjoinRoot.mk_surjective z
  exact RingHom.congr_fun key G

noncomputable def algEquivOfSubst {ΦX' ΦY' : k[X][Y]}
    (h₁ : CoordinateRing.mk E (substXY ΦX ΦY E'.polynomial) = 0)
    (h₁' : CoordinateRing.mk E' (substXY ΦX' ΦY' E.polynomial) = 0)
    (h₂ : CoordinateRing.mk E' (substXY ΦX' ΦY' ΦX) = CoordinateRing.mk E' (C X))
    (h₃ : CoordinateRing.mk E' (substXY ΦX' ΦY' ΦY) = CoordinateRing.mk E' Y)
    (h₂' : CoordinateRing.mk E (substXY ΦX ΦY ΦX') = CoordinateRing.mk E (C X))
    (h₃' : CoordinateRing.mk E (substXY ΦX ΦY ΦY') = CoordinateRing.mk E Y) :
    E'.CoordinateRing ≃ₐ[k] E.CoordinateRing :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (comap E E' ΦX ΦY h₁) (comap E' E ΦX' ΦY' h₁')
    (comap_comp_comap h₁' h₁ h₂' h₃') (comap_comp_comap h₁ h₁' h₂ h₃))
    (fun c => comap_algebraMap h₁ c)

theorem algEquivOfSubst_apply {ΦX' ΦY' : k[X][Y]}
    (h₁ : CoordinateRing.mk E (substXY ΦX ΦY E'.polynomial) = 0)
    (h₁' : CoordinateRing.mk E' (substXY ΦX' ΦY' E.polynomial) = 0)
    (h₂ : CoordinateRing.mk E' (substXY ΦX' ΦY' ΦX) = CoordinateRing.mk E' (C X))
    (h₃ : CoordinateRing.mk E' (substXY ΦX' ΦY' ΦY) = CoordinateRing.mk E' Y)
    (h₂' : CoordinateRing.mk E (substXY ΦX ΦY ΦX') = CoordinateRing.mk E (C X))
    (h₃' : CoordinateRing.mk E (substXY ΦX ΦY ΦY') = CoordinateRing.mk E Y) (G : k[X][Y]) :
    algEquivOfSubst h₁ h₁' h₂ h₃ h₂' h₃' (CoordinateRing.mk E' G) =
      CoordinateRing.mk E (substXY ΦX ΦY G) :=
  comap_mk h₁ G

end Comap

section Transport

variable {E E' : Affine k}

theorem natDegree_norm_algEquiv (Θ : E'.CoordinateRing ≃ₐ[k] E.CoordinateRing)
    {f : E'.CoordinateRing} (hf : f ≠ 0) :
    (Algebra.norm k[X] (Θ f)).natDegree = (Algebra.norm k[X] f).natDegree := by
  classical
  have hΘf : Θ f ≠ 0 := by simpa using hf
  rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis E) hΘf,
    ← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis E') hf]
  refine (Ideal.quotientEquivAlg (Ideal.span {f}) (Ideal.span {Θ f}) Θ
    ?_).toLinearEquiv.finrank_eq.symm
  rw [Ideal.map_span, Set.image_singleton]; rfl

theorem mk_CX_eq_smul (E : Affine k) : CoordinateRing.mk E (C X) =
    (X : k[X]) • (1 : E.CoordinateRing) + (0 : k[X]) • CoordinateRing.mk E Y := by
  rw [zero_smul, add_zero, Affine.CoordinateRing.smul, mul_one]

theorem mk_Y_eq_smul (E : Affine k) : CoordinateRing.mk E Y =
    (0 : k[X]) • (1 : E.CoordinateRing) + (1 : k[X]) • CoordinateRing.mk E Y := by
  rw [zero_smul, zero_add, one_smul]

theorem mk_lin (E : Affine k) (p q : k[X]) :
    CoordinateRing.mk E (lin p q) = p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y := by
  rw [lin, map_add, map_mul, Affine.CoordinateRing.smul, Affine.CoordinateRing.smul, mul_one]

theorem natDegree_norm_mk_CX (E : Affine k) :
    (Algebra.norm k[X] (CoordinateRing.mk E (C X))).natDegree = 2 := by
  rw [mk_CX_eq_smul, natDegree_norm_smul_basis_zero, natDegree_X]

theorem natDegree_norm_mk_Y (E : Affine k) :
    (Algebra.norm k[X] (CoordinateRing.mk E Y)).natDegree = 3 := by
  rw [mk_Y_eq_smul, natDegree_norm_smul_basis E _ one_ne_zero, natDegree_zero, natDegree_one]
  norm_num

theorem mk_CX_ne_zero (E : Affine k) : CoordinateRing.mk E (C X) ≠ 0 := by
  rw [mk_CX_eq_smul]; exact smul_basis_ne_zero E (Or.inl X_ne_zero)

theorem mk_Y_ne_zero (E : Affine k) : CoordinateRing.mk E Y ≠ 0 := by
  rw [mk_Y_eq_smul]; exact smul_basis_ne_zero E (Or.inr one_ne_zero)

end Transport

theorem coeffs_eq_zero_of_eq_zero {m₃ m₂ m₁ m₀ l₁ l₀ : k}
    (hp : (C m₃ * X ^ 3 + C m₂ * X ^ 2 + C m₁ * X + C m₀ : k[X]) = 0)
    (hq : (C l₁ * X + C l₀ : k[X]) = 0) :
    m₃ = 0 ∧ m₂ = 0 ∧ m₁ = 0 ∧ m₀ = 0 ∧ l₁ = 0 ∧ l₀ = 0 := by
  have e3 := congrArg (fun f : k[X] => f.coeff 3) hp
  have e2 := congrArg (fun f : k[X] => f.coeff 2) hp
  have e1 := congrArg (fun f : k[X] => f.coeff 1) hp
  have e0 := congrArg (fun f : k[X] => f.coeff 0) hp
  have f1 := congrArg (fun f : k[X] => f.coeff 1) hq
  have f0 := congrArg (fun f : k[X] => f.coeff 0) hq
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at e3 e2 e1 e0 f1 f0
  norm_num at e3 e2 e1 e0 f1 f0
  exact ⟨e3, e2, e1, e0, f1, f0⟩

theorem eval_eq_of_natDegree_le_one {p : k[X]} (hp : p.natDegree ≤ 1) (x : k) :
    p.eval x = p.coeff 1 * x + p.coeff 0 := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp]
  rw [eval_add, eval_mul, eval_C, eval_X, eval_C]

end OverK

section OverF

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

local notation "ι" => algebraMap F k

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k p x y = bc x y p := rfl

theorem bc_apply (x y : k) (p : F[X][Y]) :
    bc x y p = (p.map (mapRingHom (algebraMap F k))).evalEval x y := rfl

@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by simp [bc]
@[scoped simp] theorem bc_CX (x y : k) : bc x y (C X : F[X][Y]) = x := by simp [bc]
@[scoped simp] theorem bc_Y (x y : k) : bc x y (Y : F[X][Y]) = y := by simp [bc]

theorem bc_C (x y : k) (p : F[X]) : bc x y (C p) = (p.map ι).eval x := by
  simp [bc]

section BaseChange

variable (W : WeierstrassCurve F)

theorem baseChange_a₁ : (W.baseChange k).a₁ = ι W.a₁ := rfl
theorem baseChange_a₂ : (W.baseChange k).a₂ = ι W.a₂ := rfl
theorem baseChange_a₃ : (W.baseChange k).a₃ = ι W.a₃ := rfl
theorem baseChange_a₄ : (W.baseChange k).a₄ = ι W.a₄ := rfl
theorem baseChange_a₆ : (W.baseChange k).a₆ = ι W.a₆ := rfl

theorem baseChange_polynomial :
    (W.baseChange k).toAffine.polynomial = W.toAffine.polynomial.map (mapRingHom ι) :=
  Affine.map_polynomial W.toAffine (algebraMap F k)

theorem bc_polynomial {x y : k} (hxy : (W.baseChange k).toAffine.Equation x y) :
    bc x y W.toAffine.polynomial = 0 := by
  rw [bc_apply, ← baseChange_polynomial (k := k) W]; exact hxy

theorem equation_iff_bc (x y : k) : (W.baseChange k).toAffine.Equation x y ↔
    y ^ 2 + ι W.a₁ * x * y + ι W.a₃ * y = x ^ 3 + ι W.a₂ * x ^ 2 + ι W.a₄ * x + ι W.a₆ := by
  rw [Affine.equation_iff]; rfl

theorem exists_bc_eq_linear (G : F[X][Y]) :
    ∃ p q : F[X], ∀ x y : k, (W.baseChange k).toAffine.Equation x y →
      bc x y G = (p.map ι).eval x + (q.map ι).eval x * y := by
  set r : F[X][Y] := G %ₘ W.toAffine.polynomial with hr_def
  have hne1 : W.toAffine.polynomial ≠ 1 := by
    intro h
    have := W.toAffine.natDegree_polynomial
    rw [h, natDegree_one] at this
    exact absurd this (by norm_num)
  have hr : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt G W.toAffine.monic_polynomial hne1
    rw [W.toAffine.natDegree_polynomial] at this
    exact Nat.lt_succ_iff.mp this
  refine ⟨r.coeff 0, r.coeff 1, fun x y hxy => ?_⟩
  have hG : r + W.toAffine.polynomial * (G /ₘ W.toAffine.polynomial) = G :=
    modByMonic_add_div G W.toAffine.polynomial
  have hreq : r = C (r.coeff 1) * Y + C (r.coeff 0) := eq_X_add_C_of_natDegree_le_one hr
  have hr_eval : bc x y r = ((r.coeff 0).map ι).eval x + ((r.coeff 1).map ι).eval x * y := by
    conv_lhs => rw [hreq]
    rw [map_add, map_mul, bc_C, bc_C, bc_Y]
    ring
  rw [← hG, map_add, map_mul, bc_polynomial W hxy, zero_mul, add_zero, hr_eval]

theorem descent [IsAlgClosed k] [W.IsElliptic]
    {p q : k[X]} {n d : F[X][Y]} {B : Set k} (hB : B.Finite)
    (h : ∀ x y, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B →
      bc x y d ≠ 0 ∧ bc x y n = (p.eval x + q.eval x * y) * bc x y d) :
    (∃ p₀ : F[X], p = p₀.map ι) ∧ (∃ q₀ : F[X], q = q₀.map ι) := by
  haveI : (W.baseChange k).IsElliptic := (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  obtain ⟨e₀, e₁, he⟩ := exists_bc_eq_linear (k := k) W d
  obtain ⟨m₀, m₁, hm⟩ := exists_bc_eq_linear (k := k) W n
  have hℓ : ∀ x : k, ((C W.a₁ * X + C W.a₃ : F[X]).map ι).eval x =
      (W.baseChange k).toAffine.a₁ * x + (W.baseChange k).toAffine.a₃ := by
    intro x
    simp [Polynomial.map_add, Polynomial.map_mul]
  have hc : ∀ x : k, ((X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X]).map ι).eval x =
      x ^ 3 + (W.baseChange k).toAffine.a₂ * x ^ 2 + (W.baseChange k).toAffine.a₄ * x
        + (W.baseChange k).toAffine.a₆ := by
    intro x
    simp [Polynomial.map_add, Polynomial.map_mul]

  have hPQ := eq_zero_of_eval_eq_zero (W.baseChange k).toAffine hB
    (p := m₀.map ι - p * e₀.map ι - q * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X]).map ι
      * e₁.map ι)
    (q := m₁.map ι - p * e₁.map ι - q * (e₀.map ι - (C W.a₁ * X + C W.a₃ : F[X]).map ι * e₁.map ι))
    (fun x y hxy hx => by
      obtain ⟨hd, hn⟩ := h x y hxy hx
      have hE : y ^ 2 + (W.baseChange k).toAffine.a₁ * x * y + (W.baseChange k).toAffine.a₃ * y
          = x ^ 3 + (W.baseChange k).toAffine.a₂ * x ^ 2 + (W.baseChange k).toAffine.a₄ * x
            + (W.baseChange k).toAffine.a₆ := (Affine.equation_iff ..).mp hxy.left
      rw [he x y hxy.left] at hn
      rw [hm x y hxy.left] at hn
      simp only [eval_sub, eval_mul, hℓ, hc]
      linear_combination hn + q.eval x * (e₁.map ι).eval x * hE)
  obtain ⟨hP, hQ⟩ := hPQ

  have hνp : (e₀ ^ 2 - e₀ * e₁ * (C W.a₁ * X + C W.a₃) -
      e₁ ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)).map ι * p =
      (m₀ * (e₀ - (C W.a₁ * X + C W.a₃) * e₁) -
        (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) * e₁ * m₁).map ι := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]
    linear_combination (-(e₀.map ι - (C W.a₁ * X + C W.a₃ : F[X]).map ι * e₁.map ι)) * hP
      + (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X]).map ι * e₁.map ι * hQ
  have hνq : (e₀ ^ 2 - e₀ * e₁ * (C W.a₁ * X + C W.a₃) -
      e₁ ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)).map ι * q =
      (e₀ * m₁ - e₁ * m₀).map ι := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]
    linear_combination e₁.map ι * hP - e₀.map ι * hQ
  have hν : (e₀ ^ 2 - e₀ * e₁ * (C W.a₁ * X + C W.a₃) -
      e₁ ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) ≠ 0 := by
    intro h0
    obtain ⟨h0', h1'⟩ := eq_zero_of_norm_eq_zero W.toAffine h0
    obtain ⟨x, hx⟩ := hB.infinite_compl.nonempty
    obtain ⟨y, hy⟩ := exists_nonsingular (W.baseChange k).toAffine x
    refine (h x y hy hx).1 ?_
    rw [he x y hy.left, h0', h1']
    simp
  have hνk := (Polynomial.map_ne_zero_iff (algebraMap F k).injective).mpr hν
  refine ⟨⟨(m₀ * (e₀ - (C W.a₁ * X + C W.a₃) * e₁) -
        (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) * e₁ * m₁) /
      (e₀ ^ 2 - e₀ * e₁ * (C W.a₁ * X + C W.a₃) -
        e₁ ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)), ?_⟩,
    ⟨(e₀ * m₁ - e₁ * m₀) / (e₀ ^ 2 - e₀ * e₁ * (C W.a₁ * X + C W.a₃) -
        e₁ ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)), ?_⟩⟩
  · rw [Polynomial.map_div, ← hνp, mul_div_cancel_left₀ _ hνk]
  · rw [Polynomial.map_div, ← hνq, mul_div_cancel_left₀ _ hνk]

end BaseChange

theorem exists_variableChange_of_relations (W W' : WeierstrassCurve F) {α β μ r σ t : F}
    (hμ : μ ≠ 0) (hα : α = μ ^ 2) (hβ : β = μ ^ 3)
    (L1 : 2 * β * σ + W'.a₁ * α * β - β ^ 2 * W.a₁ = 0)
    (L0 : 2 * β * t + W'.a₁ * r * β + W'.a₃ * β - β ^ 2 * W.a₃ = 0)
    (M2 : σ ^ 2 + W'.a₁ * α * σ - 3 * α ^ 2 * r - W'.a₂ * α ^ 2 + β ^ 2 * W.a₂ = 0)
    (M1 : 2 * σ * t + W'.a₁ * (α * t + r * σ) + W'.a₃ * σ - 3 * α * r ^ 2 - 2 * W'.a₂ * α * r
      - W'.a₄ * α + β ^ 2 * W.a₄ = 0)
    (M0 : t ^ 2 + W'.a₁ * r * t + W'.a₃ * t - r ^ 3 - W'.a₂ * r ^ 2 - W'.a₄ * r - W'.a₆
      + β ^ 2 * W.a₆ = 0) :
    ∃ γ : VariableChange F, γ • W = W' := by
  subst hα hβ
  have h3 : μ ^ 3 ≠ 0 := pow_ne_zero 3 hμ
  have L1' : 2 * σ + W'.a₁ * μ ^ 2 - μ ^ 3 * W.a₁ = 0 := by
    apply mul_left_cancel₀ h3
    linear_combination L1
  have L0' : 2 * t + W'.a₁ * r + W'.a₃ - μ ^ 3 * W.a₃ = 0 := by
    apply mul_left_cancel₀ h3
    linear_combination L0
  refine ⟨⟨(Units.mk0 μ hμ)⁻¹, -r / μ ^ 2, -σ / μ ^ 3, (σ * r - μ ^ 2 * t) / μ ^ 5⟩, ?_⟩
  have hu : (((Units.mk0 μ hμ)⁻¹)⁻¹ : Fˣ) = (μ : F) := by
    rw [inv_inv, Units.val_mk0]
  ext
  · simp only [variableChange_a₁, hu]
    field_simp
    linear_combination (-1 : F) * L1'
  · simp only [variableChange_a₂, hu]
    field_simp
    linear_combination M2 - σ * L1'
  · simp only [variableChange_a₃, hu]
    field_simp
    linear_combination -μ ^ 2 * L0' + r * L1'
  · simp only [variableChange_a₄, hu]
    field_simp
    linear_combination μ ^ 2 * M1 - 2 * r * M2 - σ * μ ^ 2 * L0' - (μ ^ 2 * t - 2 * r * σ) * L1'
  · simp only [variableChange_a₆, hu]
    field_simp
    linear_combination μ ^ 4 * M0 - μ ^ 2 * r * M1 + r ^ 2 * M2
      + r * (μ ^ 2 * t - σ * r) * L1' - μ ^ 2 * (μ ^ 2 * t - σ * r) * L0'

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

section Points

variable (W : WeierstrassCurve F)

def Good (B : Set k) (P : Pt k W) : Prop :=
  ∃ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B

theorem finite_setOf_equation (x : k) :
    {y : k | (W.baseChange k).toAffine.Equation x y}.Finite := by
  have hne : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

theorem finite_not_good {B : Set k} (hB : B.Finite) : {P : Pt k W | ¬ Good W B P}.Finite := by
  have hfin : (insert (0 : Pt k W) (⋃ x ∈ B, ⋃ y ∈ {y : k | (W.baseChange k).toAffine.Equation x y},
      {P : Pt k W | ∃ h : (W.baseChange k).toAffine.Nonsingular x y, P = .some x y h})).Finite := by
    refine Set.Finite.insert _ (Set.Finite.biUnion hB fun x _ => ?_)
    refine Set.Finite.biUnion (finite_setOf_equation (k := k) W x) fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq, Good, not_exists, not_and, not_not] at hP
  rcases P with _ | ⟨x, y, h⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨x, hP x y h rfl, y, h.left, h, rfl⟩

theorem infinite_point [IsAlgClosed k] [W.IsElliptic] : Infinite (Pt k W) := by
  haveI : (W.baseChange k).IsElliptic :=
    (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  choose f hf using exists_nonsingular (W.baseChange k).toAffine
  refine Infinite.of_injective (fun x : k => (Affine.Point.some x (f x) (hf x) : Pt k W)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

def absc : Pt k W → k
  | .zero => 0
  | .some x _ _ => x

end Points

section Pair

variable [IsAlgClosed k] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]

def PolyRep (u : Pt k W → Pt k W') (pX qX pY qY : k[X]) (B : Set k) : Prop :=
  ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
    ∃ h', u (.some x y h) = .some (pX.eval x + qX.eval x * y) (pY.eval x + qY.eval x * y) h'

variable {u : Pt k W → Pt k W'} {u' : Pt k W' → Pt k W}
  {pX qX pY qY : k[X]} {B : Set k} {pX' qX' pY' qY' : k[X]} {B' : Set k}

omit [W.IsElliptic] [W'.IsElliptic] [IsAlgClosed k] in
theorem PolyRep.eval_lin (hrep : PolyRep u pX qX pY qY B) {x y : k}
    (h : (W.baseChange k).toAffine.Nonsingular x y) (hx : x ∉ B) :
    ∃ h', u (.some x y h) = .some ((lin pX qX).evalEval x y) ((lin pY qY).evalEval x y) h' := by
  rw [evalEval_lin, evalEval_lin]; exact hrep x y h hx

omit [W'.IsElliptic] in

theorem mk_subst_polynomial (hB : B.Finite) (hrep : PolyRep u pX qX pY qY B) :
    CoordinateRing.mk (W.baseChange k).toAffine
      (substXY (lin pX qX) (lin pY qY) (W'.baseChange k).toAffine.polynomial) = 0 := by
  haveI : (W.baseChange k).IsElliptic := (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  refine mk_eq_zero_of_evalEval _ hB fun x y hxy hx => ?_
  obtain ⟨h', -⟩ := hrep.eval_lin hxy hx
  rw [evalEval_substXY]
  exact h'.left

def badSet (u : Pt k W → Pt k W') (B B' : Set k) : Set k :=
  B ∪ absc W '' (u ⁻¹' {Q : Pt k W' | ¬ Good W' B' Q})

omit [W.IsElliptic] [W'.IsElliptic] [IsAlgClosed k] in
theorem badSet_finite (hinj : Function.Injective u) (hB : B.Finite) (hB' : B'.Finite) :
    (badSet u B B').Finite :=
  hB.union ((Set.Finite.preimage hinj.injOn (finite_not_good W' hB')).image _)

omit [W'.IsElliptic] in

theorem mk_subst_lin (hinj : Function.Injective u) (hc : ∀ P, u' (u P) = P)
    (hB : B.Finite) (hrep : PolyRep u pX qX pY qY B)
    (hB' : B'.Finite) (hrep' : PolyRep u' pX' qX' pY' qY' B') :
    CoordinateRing.mk (W.baseChange k).toAffine (substXY (lin pX qX) (lin pY qY) (lin pX' qX')) =
        CoordinateRing.mk (W.baseChange k).toAffine (C X) ∧
      CoordinateRing.mk (W.baseChange k).toAffine (substXY (lin pX qX) (lin pY qY) (lin pY' qY')) =
        CoordinateRing.mk (W.baseChange k).toAffine Y := by
  haveI : (W.baseChange k).IsElliptic := (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  have key : ∀ x y, (W.baseChange k).toAffine.Nonsingular x y → x ∉ badSet u B B' →
      (lin pX' qX').evalEval ((lin pX qX).evalEval x y) ((lin pY qY).evalEval x y) = x ∧
        (lin pY' qY').evalEval ((lin pX qX).evalEval x y) ((lin pY qY).evalEval x y) = y := by
    intro x y hxy hx
    simp only [badSet, Set.mem_union, Set.mem_image, Set.mem_preimage, Set.mem_setOf_eq,
      not_or, not_exists, not_and] at hx
    obtain ⟨hxB, hx2⟩ := hx
    obtain ⟨h', hu⟩ := hrep.eval_lin hxy hxB
    have hgood : Good W' B' (u (.some x y hxy)) := by
      by_contra hng
      exact hx2 (.some x y hxy) hng rfl
    obtain ⟨x₂, y₂, h₂, hu₂, hx₂⟩ := hgood
    rw [hu] at hu₂
    obtain ⟨hxx, hyy⟩ := Affine.Point.some.inj hu₂
    have hX'B : (lin pX qX).evalEval x y ∉ B' := hxx ▸ hx₂
    obtain ⟨h'', hu'⟩ := hrep'.eval_lin h' hX'B
    have hcomp := hc (.some x y hxy)
    rw [hu, hu'] at hcomp
    exact Affine.Point.some.inj hcomp
  have hfin := badSet_finite (B := B) (B' := B') hinj hB hB'
  constructor
  · rw [← sub_eq_zero, ← map_sub]
    refine mk_eq_zero_of_evalEval _ hfin fun x y hxy hx => ?_
    rw [evalEval_sub, evalEval_substXY, (key x y hxy hx).1, evalEval_C, eval_X, sub_self]
  · rw [← sub_eq_zero, ← map_sub]
    refine mk_eq_zero_of_evalEval _ hfin fun x y hxy hx => ?_
    rw [evalEval_sub, evalEval_substXY, (key x y hxy hx).2, evalEval_X, sub_self]

theorem shapes (hinj : Function.Injective u) (hinj' : Function.Injective u')
    (hc : ∀ P, u' (u P) = P) (hc' : ∀ Q, u (u' Q) = Q)
    (hB : B.Finite) (hrep : PolyRep u pX qX pY qY B)
    (hB' : B'.Finite) (hrep' : PolyRep u' pX' qX' pY' qY' B') :
    qX = 0 ∧ pX.natDegree = 1 ∧ qY ≠ 0 ∧ qY.natDegree = 0 ∧ pY.natDegree ≤ 1 := by
  have I1 := mk_subst_polynomial hB hrep
  have I1' := mk_subst_polynomial hB' hrep'
  obtain ⟨I2, I3⟩ := mk_subst_lin hinj hc hB hrep hB' hrep'
  obtain ⟨I2', I3'⟩ := mk_subst_lin hinj' hc' hB' hrep' hB hrep
  let Θ := algEquivOfSubst I1 I1' I2' I3' I2 I3
  have hX := natDegree_norm_algEquiv Θ (mk_CX_ne_zero (W'.baseChange k).toAffine)
  have hY := natDegree_norm_algEquiv Θ (mk_Y_ne_zero (W'.baseChange k).toAffine)
  rw [natDegree_norm_mk_CX] at hX
  rw [natDegree_norm_mk_Y] at hY
  change (Algebra.norm k[X] (algEquivOfSubst I1 I1' I2' I3' I2 I3
    (CoordinateRing.mk _ (C X)))).natDegree = 2 at hX
  change (Algebra.norm k[X] (algEquivOfSubst I1 I1' I2' I3' I2 I3
    (CoordinateRing.mk _ Y))).natDegree = 3 at hY
  rw [algEquivOfSubst_apply, substXY_CX, mk_lin] at hX
  rw [algEquivOfSubst_apply, substXY_Y, mk_lin] at hY
  obtain ⟨hqX, hpX⟩ := shape_of_natDegree_norm_eq_two _ hX
  obtain ⟨hqY, hqY0, hpY⟩ := shape_of_natDegree_norm_eq_three _ hY
  exact ⟨hqX, hpX, hqY, hqY0, hpY⟩

end Pair

section Main

variable [IsAlgClosed k] [DecidableEq k] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]

omit [W'.IsElliptic] in

theorem polyRep_descent {u : Pt k W →+ Pt k W'} {pX qX pY qY : k[X]} {B : Set k}
    (hB : B.Finite) (hrep : PolyRep u pX qX pY qY B)
    (hu : WeierstrassCurve.IsRationallyRepresented k W W' u) :
    ((∃ p₀ : F[X], pX = p₀.map ι) ∧ (∃ q₀ : F[X], qX = q₀.map ι)) ∧
      ((∃ p₀ : F[X], pY = p₀.map ι) ∧ (∃ q₀ : F[X], qY = q₀.map ι)) := by
  obtain ⟨nX, dX, nY, dY, BF, hBF, hF⟩ := hu
  have hfin : (B ∪ BF).Finite := hB.union hBF
  have key : ∀ x y, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B ∪ BF →
      (bc x y dX ≠ 0 ∧ bc x y nX = (pX.eval x + qX.eval x * y) * bc x y dX) ∧
      (bc x y dY ≠ 0 ∧ bc x y nY = (pY.eval x + qY.eval x * y) * bc x y dY) := by
    intro x y hxy hx
    rw [Set.mem_union, not_or] at hx
    obtain ⟨hdX, hdY, h'', huF⟩ := hF x y hxy hx.2
    obtain ⟨h', hu⟩ := hrep x y hxy hx.1
    rw [hu] at huF
    obtain ⟨hxx, hyy⟩ := Affine.Point.some.inj huF
    simp only [evalEvalBC_eq] at hxx hyy hdX hdY
    refine ⟨⟨hdX, ?_⟩, ⟨hdY, ?_⟩⟩
    · rw [hxx, div_mul_cancel₀ _ hdX]
    · rw [hyy, div_mul_cancel₀ _ hdY]
  exact ⟨descent W hfin fun x y hxy hx => (key x y hxy hx).1,
    descent W hfin fun x y hxy hx => (key x y hxy hx).2⟩

theorem exists_variableChange
    (u : Pt k W →+ Pt k W') (hu : u ∈ WeierstrassCurve.rationalHomSet k W W')
    (u' : Pt k W' →+ Pt k W) (hu' : u' ∈ WeierstrassCurve.rationalHomSet k W' W)
    (h : u'.comp u = AddMonoidHom.id _) (h' : u.comp u' = AddMonoidHom.id _) :
    ∃ γ : VariableChange F, γ • W = W' := by
  haveI : (W.baseChange k).IsElliptic := (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  haveI : (W'.baseChange k).IsElliptic := (inferInstance : (W'.map (algebraMap F k)).IsElliptic)

  have hc : ∀ P, u' (u P) = P := fun P => DFunLike.congr_fun h P
  have hc' : ∀ Q, u (u' Q) = Q := fun Q => DFunLike.congr_fun h' Q
  have hinj : Function.Injective u := Function.LeftInverse.injective hc
  have hinj' : Function.Injective u' := Function.LeftInverse.injective hc'

  have huR : WeierstrassCurve.IsRationallyRepresented k W W' u := by
    rcases hu with hu0 | huR
    · exfalso
      haveI := infinite_point (k := k) W
      obtain ⟨P, hP⟩ := exists_ne (0 : Pt k W)
      exact hP (hinj (by rw [hu0]; rfl))
    · exact huR

  obtain ⟨pX, qX, pY, qY, B, hB, hrep⟩ :=
    WeierstrassCurve.exists_polynomial_rep_of_injective_of_mem_rationalHomSet k W W' u hu hinj
  obtain ⟨pX', qX', pY', qY', B', hB', hrep'⟩ :=
    WeierstrassCurve.exists_polynomial_rep_of_injective_of_mem_rationalHomSet k W' W u' hu' hinj'

  obtain ⟨hqX, hpX, hqY, hqY0, hpY⟩ :=
    shapes (u := u) (u' := u') hinj hinj' hc hc' hB hrep hB' hrep'

  obtain ⟨⟨⟨pX₀, hpX₀⟩, -⟩, ⟨⟨pY₀, hpY₀⟩, ⟨qY₀, hqY₀⟩⟩⟩ := polyRep_descent hB hrep huR

  have hpX₀d : pX₀.natDegree = 1 := by
    rw [← hpX, hpX₀, natDegree_map_eq_of_injective (algebraMap F k).injective]
  have hpY₀d : pY₀.natDegree ≤ 1 := by
    rw [← natDegree_map_eq_of_injective (algebraMap F k).injective, ← hpY₀]; exact hpY
  have hqY₀d : qY₀.natDegree = 0 := by
    rw [← hqY0, hqY₀, natDegree_map_eq_of_injective (algebraMap F k).injective]
  set α₀ : F := pX₀.coeff 1 with hα₀_def
  set r₀ : F := pX₀.coeff 0 with hr₀_def
  set β₀ : F := qY₀.coeff 0 with hβ₀_def
  set σ₀ : F := pY₀.coeff 1 with hσ₀_def
  set t₀ : F := pY₀.coeff 0 with ht₀_def
  have hα₀ : α₀ ≠ 0 := by
    intro h0
    have : pX₀.leadingCoeff = 0 := by rw [leadingCoeff, hpX₀d]; exact h0
    rw [leadingCoeff_eq_zero] at this
    rw [this, natDegree_zero] at hpX₀d
    exact zero_ne_one hpX₀d
  have hβ₀ : β₀ ≠ 0 := by
    intro h0
    apply hqY
    rw [hqY₀, eq_C_of_natDegree_eq_zero hqY₀d, ← hβ₀_def, h0, map_zero, Polynomial.map_zero]
  have hXev : ∀ x y : k, pX.eval x + qX.eval x * y = ι α₀ * x + ι r₀ := by
    intro x y
    rw [hqX, eval_zero, zero_mul, add_zero, hpX₀, eval_eq_of_natDegree_le_one, coeff_map,
      coeff_map]
    rw [natDegree_map_eq_of_injective (algebraMap F k).injective]; exact hpX₀d.le
  have hYev : ∀ x y : k, pY.eval x + qY.eval x * y = ι β₀ * y + ι σ₀ * x + ι t₀ := by
    intro x y
    have h1 : pY.eval x = ι σ₀ * x + ι t₀ := by
      rw [hpY₀, eval_eq_of_natDegree_le_one, coeff_map, coeff_map]
      rw [natDegree_map_eq_of_injective (algebraMap F k).injective]; exact hpY₀d
    have h2 : qY.eval x = ι β₀ := by
      rw [hqY₀, eq_C_of_natDegree_eq_zero hqY₀d, map_C, eval_C]
    rw [h1, h2]; ring

  have hrel := eq_zero_of_eval_eq_zero (W.baseChange k).toAffine hB
    (p := C (ι β₀ ^ 2 - ι α₀ ^ 3) * X ^ 3
      + C (ι σ₀ ^ 2 + ι W'.a₁ * ι α₀ * ι σ₀ - 3 * ι α₀ ^ 2 * ι r₀ - ι W'.a₂ * ι α₀ ^ 2
          + ι β₀ ^ 2 * ι W.a₂) * X ^ 2
      + C (2 * ι σ₀ * ι t₀ + ι W'.a₁ * (ι α₀ * ι t₀ + ι r₀ * ι σ₀) + ι W'.a₃ * ι σ₀
          - 3 * ι α₀ * ι r₀ ^ 2 - 2 * ι W'.a₂ * ι α₀ * ι r₀ - ι W'.a₄ * ι α₀
          + ι β₀ ^ 2 * ι W.a₄) * X
      + C (ι t₀ ^ 2 + ι W'.a₁ * ι r₀ * ι t₀ + ι W'.a₃ * ι t₀ - ι r₀ ^ 3 - ι W'.a₂ * ι r₀ ^ 2
          - ι W'.a₄ * ι r₀ - ι W'.a₆ + ι β₀ ^ 2 * ι W.a₆))
    (q := C (2 * ι β₀ * ι σ₀ + ι W'.a₁ * ι α₀ * ι β₀ - ι β₀ ^ 2 * ι W.a₁) * X
      + C (2 * ι β₀ * ι t₀ + ι W'.a₁ * ι r₀ * ι β₀ + ι W'.a₃ * ι β₀ - ι β₀ ^ 2 * ι W.a₃))
    (fun x y hxy hx => by
      obtain ⟨h', -⟩ := hrep x y hxy hx
      have hE' := (equation_iff_bc W' _ _).mp h'.left
      rw [hXev, hYev] at hE'
      have hE := (equation_iff_bc W _ _).mp hxy.left
      simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
      linear_combination hE' - (ι β₀) ^ 2 * hE)
  obtain ⟨M3, M2, M1, M0, L1, L0⟩ := coeffs_eq_zero_of_eq_zero hrel.1 hrel.2

  have hI : Function.Injective (algebraMap F k) := (algebraMap F k).injective
  have M3F : β₀ ^ 2 - α₀ ^ 3 = 0 := hI (by
    simp only [map_sub, map_pow, map_zero]; linear_combination M3)
  have M2F : σ₀ ^ 2 + W'.a₁ * α₀ * σ₀ - 3 * α₀ ^ 2 * r₀ - W'.a₂ * α₀ ^ 2 + β₀ ^ 2 * W.a₂ = 0 :=
    hI (by simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero]; linear_combination M2)
  have M1F : 2 * σ₀ * t₀ + W'.a₁ * (α₀ * t₀ + r₀ * σ₀) + W'.a₃ * σ₀ - 3 * α₀ * r₀ ^ 2
      - 2 * W'.a₂ * α₀ * r₀ - W'.a₄ * α₀ + β₀ ^ 2 * W.a₄ = 0 :=
    hI (by simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero]; linear_combination M1)
  have M0F : t₀ ^ 2 + W'.a₁ * r₀ * t₀ + W'.a₃ * t₀ - r₀ ^ 3 - W'.a₂ * r₀ ^ 2 - W'.a₄ * r₀ - W'.a₆
      + β₀ ^ 2 * W.a₆ = 0 :=
    hI (by simp only [map_add, map_sub, map_mul, map_pow, map_zero]; linear_combination M0)
  have L1F : 2 * β₀ * σ₀ + W'.a₁ * α₀ * β₀ - β₀ ^ 2 * W.a₁ = 0 :=
    hI (by simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero]; linear_combination L1)
  have L0F : 2 * β₀ * t₀ + W'.a₁ * r₀ * β₀ + W'.a₃ * β₀ - β₀ ^ 2 * W.a₃ = 0 :=
    hI (by simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero]; linear_combination L0)

  have hμ : β₀ / α₀ ≠ 0 := div_ne_zero hβ₀ hα₀
  have hαμ : α₀ = (β₀ / α₀) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hα₀)]
    linear_combination (-1 : F) * M3F
  have hβμ : β₀ = (β₀ / α₀) ^ 3 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 3 hα₀)]
    linear_combination (-(β₀ : F)) * M3F
  exact exists_variableChange_of_relations W W' hμ hαμ hβμ L1F L0F M2F M1F M0F

end Main

end OverF

end WeierstrassCurve.RationalHomInverse
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet.WeierstrassCurve.RationalHomInverse"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet.WeierstrassCurve"

theorem solution {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (u : (W.baseChange k).toAffine.Point →+ (W'.baseChange k).toAffine.Point) (hu : u ∈ WeierstrassCurve.rationalHomSet k W W') (u' : (W'.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) (hu' : u' ∈ WeierstrassCurve.rationalHomSet k W' W) (h : u'.comp u = AddMonoidHom.id ((W.baseChange k).toAffine.Point)) (h' : u.comp u' = AddMonoidHom.id ((W'.baseChange k).toAffine.Point)) : ∃ γ : WeierstrassCurve.VariableChange F, γ • W = W' :=
  WeierstrassCurve.RationalHomInverse.exists_variableChange u hu u' hu' h h'

end S_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet (solution)
