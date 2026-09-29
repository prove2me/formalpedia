-- Prove2me | solution 1 for WeierstrassCurve.finite_rationalHomSet_units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d89f8e4d-a6d3-5011-bec6-f2ec3abaca3b

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_finite_stabilizer_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_finite_rationalHomSet_units

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.CoordinateRing.smul_basis_eq_zero a₃ a₁ VariableChange.u map Affine.CoordinateRing.norm_smul_basis Affine.CoordinateRing Affine.CoordinateRing.smul variableChange_a₃ mk a₄ a₂ a₆ Affine.Point.some variableChange_a₆ Affine.degree_polynomial Affine.Point.some.inj VariableChange.t variableChange_a₂ toAffine Affine.Point VariableChange.s VariableChange.r Affine.monic_polynomial Affine.CoordinateRing.degree_norm_smul_basis variableChange_a₁ variableChange_a₄ VariableChange Affine.equation_iff baseChange rationalHomSet exists_polynomial_rep_of_injective_of_mem_rationalHomSet finite_stabilizer_variableChange"
namespace RationalHomUnits
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_finite_rationalHomSet_units.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing"

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

section VC

noncomputable def toVC (q : kˣ × k × k × k) : VariableChange k :=
  ⟨q.1⁻¹, -q.2.1 / (q.1 : k) ^ 2, -q.2.2.1 / (q.1 : k) ^ 3,
    (q.2.2.1 * q.2.1 - (q.1 : k) ^ 2 * q.2.2.2) / (q.1 : k) ^ 5⟩

theorem toVC_injective : Function.Injective (toVC (k := k)) := by
  rintro ⟨μ, r, σ, t⟩ ⟨μ', r', σ', t'⟩ h
  have hu : μ⁻¹ = μ'⁻¹ := congrArg VariableChange.u h
  have hμ : μ = μ' := inv_injective hu
  subst hμ
  have h0 : (μ : k) ≠ 0 := μ.ne_zero
  have hr : -r / (μ : k) ^ 2 = -r' / (μ : k) ^ 2 := congrArg VariableChange.r h
  have hs : -σ / (μ : k) ^ 3 = -σ' / (μ : k) ^ 3 := congrArg VariableChange.s h
  have ht : (σ * r - (μ : k) ^ 2 * t) / (μ : k) ^ 5 =
      (σ' * r' - (μ : k) ^ 2 * t') / (μ : k) ^ 5 := congrArg VariableChange.t h
  rw [div_left_inj' (pow_ne_zero _ h0), neg_inj] at hr hs
  subst hr hs
  rw [div_left_inj' (pow_ne_zero _ h0), sub_right_inj] at ht
  have htt : t = t' := mul_left_cancel₀ (pow_ne_zero 2 h0) ht
  subst htt
  rfl

theorem toVC_smul_eq_of_relations (E : Affine k) {α β μ r σ t : k}
    (hμ : μ ≠ 0) (hα : α = μ ^ 2) (hβ : β = μ ^ 3)
    (L1 : 2 * β * σ + E.a₁ * α * β - β ^ 2 * E.a₁ = 0)
    (L0 : 2 * β * t + E.a₁ * r * β + E.a₃ * β - β ^ 2 * E.a₃ = 0)
    (M2 : σ ^ 2 + E.a₁ * α * σ - 3 * α ^ 2 * r - E.a₂ * α ^ 2 + β ^ 2 * E.a₂ = 0)
    (M1 : 2 * σ * t + E.a₁ * (α * t + r * σ) + E.a₃ * σ - 3 * α * r ^ 2 - 2 * E.a₂ * α * r
      - E.a₄ * α + β ^ 2 * E.a₄ = 0)
    (M0 : t ^ 2 + E.a₁ * r * t + E.a₃ * t - r ^ 3 - E.a₂ * r ^ 2 - E.a₄ * r - E.a₆
      + β ^ 2 * E.a₆ = 0) :
    toVC (Units.mk0 μ hμ, r, σ, t) • (E : WeierstrassCurve k) = E := by
  subst hα hβ
  have h3 : μ ^ 3 ≠ 0 := pow_ne_zero 3 hμ
  have L1' : 2 * σ + E.a₁ * μ ^ 2 - μ ^ 3 * E.a₁ = 0 := by
    apply mul_left_cancel₀ h3
    linear_combination L1
  have L0' : 2 * t + E.a₁ * r + E.a₃ - μ ^ 3 * E.a₃ = 0 := by
    apply mul_left_cancel₀ h3
    linear_combination L0
  have hu : (((Units.mk0 μ hμ)⁻¹)⁻¹ : kˣ) = (μ : k) := by
    rw [inv_inv, Units.val_mk0]
  show (⟨(Units.mk0 μ hμ)⁻¹, -r / μ ^ 2, -σ / μ ^ 3, (σ * r - μ ^ 2 * t) / μ ^ 5⟩ :
    VariableChange k) • (E : WeierstrassCurve k) = E
  ext
  · simp only [variableChange_a₁, hu]
    field_simp
    linear_combination (-1 : k) * L1'
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

end VC

section Points

variable (E : Affine k)

def Good (B : Set k) (P : E.Point) : Prop :=
  ∃ (x y : k) (h : E.Nonsingular x y), P = .some x y h ∧ x ∉ B

theorem finite_setOf_equation (x : k) : {y : k | E.Equation x y}.Finite := by
  have hne : (E.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

theorem finite_not_good {B : Set k} (hB : B.Finite) : {P : E.Point | ¬ Good E B P}.Finite := by
  have hfin : (insert (0 : E.Point) (⋃ x ∈ B, ⋃ y ∈ {y : k | E.Equation x y},
      {P : E.Point | ∃ h : E.Nonsingular x y, P = .some x y h})).Finite := by
    refine Set.Finite.insert _ (Set.Finite.biUnion hB fun x _ => ?_)
    refine Set.Finite.biUnion (finite_setOf_equation E x) fun y _ => ?_
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

theorem infinite_point [IsAlgClosed k] [E.IsElliptic] : Infinite E.Point := by
  choose f hf using exists_nonsingular E
  refine Infinite.of_injective (fun x : k => (Affine.Point.some x (f x) (hf x) : E.Point)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

def absc : E.Point → k
  | .zero => 0
  | .some x _ _ => x

variable {E} in
theorem some_eq_some {x y x' y' : k} (h : E.Nonsingular x y) (hx : x = x') (hy : y = y') :
    ∃ h', Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  subst hx hy
  exact ⟨h, rfl⟩

end Points

theorem addMonoidHom_eq_of_finite {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Infinite G]
    {f g : G →+ H} (hfin : {P | f P ≠ g P}.Finite) : f = g := by
  by_contra hne
  obtain ⟨P₀, hP₀⟩ : ∃ P, f P ≠ g P := by
    by_contra h
    exact hne (AddMonoidHom.ext fun P => not_not.mp (not_exists.mp h P))
  have hinf : {P | f P = g P}.Infinite := by
    have := hfin.infinite_compl
    convert this using 1
    ext P
    simp
  refine hinf ((hfin.subset ?_).of_finite_image (add_right_injective P₀).injOn)
  rintro _ ⟨P, hP, rfl⟩
  simp only [Set.mem_setOf_eq] at hP ⊢
  rw [map_add, map_add, hP]
  intro h
  exact hP₀ (add_right_cancel h)

section Pair

variable [IsAlgClosed k] {E E' : Affine k} [E.IsElliptic] [E'.IsElliptic]

def PolyRep (u : E.Point → E'.Point) (pX qX pY qY : k[X]) (B : Set k) : Prop :=
  ∀ (x y : k) (h : E.Nonsingular x y), x ∉ B →
    ∃ h', u (.some x y h) = .some (pX.eval x + qX.eval x * y) (pY.eval x + qY.eval x * y) h'

variable {u : E.Point → E'.Point} {u' : E'.Point → E.Point}
  {pX qX pY qY : k[X]} {B : Set k} {pX' qX' pY' qY' : k[X]} {B' : Set k}

omit [E.IsElliptic] [E'.IsElliptic] [IsAlgClosed k] in
theorem PolyRep.eval_lin (hrep : PolyRep u pX qX pY qY B) {x y : k}
    (h : E.Nonsingular x y) (hx : x ∉ B) :
    ∃ h', u (.some x y h) = .some ((lin pX qX).evalEval x y) ((lin pY qY).evalEval x y) h' := by
  rw [evalEval_lin, evalEval_lin]; exact hrep x y h hx

omit [E'.IsElliptic] in

theorem mk_subst_polynomial (hB : B.Finite) (hrep : PolyRep u pX qX pY qY B) :
    CoordinateRing.mk E (substXY (lin pX qX) (lin pY qY) E'.polynomial) = 0 := by
  refine mk_eq_zero_of_evalEval _ hB fun x y hxy hx => ?_
  obtain ⟨h', -⟩ := hrep.eval_lin hxy hx
  rw [evalEval_substXY]
  exact h'.left

def badSet (u : E.Point → E'.Point) (B B' : Set k) : Set k :=
  B ∪ absc E '' (u ⁻¹' {Q : E'.Point | ¬ Good E' B' Q})

omit [E.IsElliptic] [E'.IsElliptic] [IsAlgClosed k] in
theorem badSet_finite (hinj : Function.Injective u) (hB : B.Finite) (hB' : B'.Finite) :
    (badSet u B B').Finite :=
  hB.union ((Set.Finite.preimage hinj.injOn (finite_not_good E' hB')).image _)

omit [E'.IsElliptic] in

theorem mk_subst_lin (hinj : Function.Injective u) (hc : ∀ P, u' (u P) = P)
    (hB : B.Finite) (hrep : PolyRep u pX qX pY qY B)
    (hB' : B'.Finite) (hrep' : PolyRep u' pX' qX' pY' qY' B') :
    CoordinateRing.mk E (substXY (lin pX qX) (lin pY qY) (lin pX' qX')) =
        CoordinateRing.mk E (C X) ∧
      CoordinateRing.mk E (substXY (lin pX qX) (lin pY qY) (lin pY' qY')) =
        CoordinateRing.mk E Y := by
  have key : ∀ x y, E.Nonsingular x y → x ∉ badSet u B B' →
      (lin pX' qX').evalEval ((lin pX qX).evalEval x y) ((lin pY qY).evalEval x y) = x ∧
        (lin pY' qY').evalEval ((lin pX qX).evalEval x y) ((lin pY qY).evalEval x y) = y := by
    intro x y hxy hx
    simp only [badSet, Set.mem_union, Set.mem_image, Set.mem_preimage, Set.mem_setOf_eq,
      not_or, not_exists, not_and] at hx
    obtain ⟨hxB, hx2⟩ := hx
    obtain ⟨h', hu⟩ := hrep.eval_lin hxy hxB
    have hgood : Good E' B' (u (.some x y hxy)) := by
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
  have hX := natDegree_norm_algEquiv Θ (mk_CX_ne_zero E')
  have hY := natDegree_norm_algEquiv Θ (mk_Y_ne_zero E')
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

theorem exists_toVC {u u' : E.Point → E.Point} (hinj : Function.Injective u)
    (hinj' : Function.Injective u') (hc : ∀ P, u' (u P) = P) (hc' : ∀ Q, u (u' Q) = Q)
    (hB : B.Finite) (hrep : PolyRep u pX qX pY qY B)
    (hB' : B'.Finite) (hrep' : PolyRep u' pX' qX' pY' qY' B') :
    ∃ q : kˣ × k × k × k, toVC q • (E : WeierstrassCurve k) = E ∧
      ∀ (x y : k) (h : E.Nonsingular x y), x ∉ B →
        ∃ h', u (.some x y h) =
          .some ((q.1 : k) ^ 2 * x + q.2.1) ((q.1 : k) ^ 3 * y + q.2.2.1 * x + q.2.2.2) h' := by
  obtain ⟨hqX, hpX, hqY, hqY0, hpY⟩ := shapes hinj hinj' hc hc' hB hrep hB' hrep'

  obtain ⟨α, r, hα, hXev⟩ :
      ∃ α r : k, α ≠ 0 ∧ ∀ x y : k, pX.eval x + qX.eval x * y = α * x + r := by
    refine ⟨pX.coeff 1, pX.coeff 0, fun h0 => ?_, fun x y => ?_⟩
    · have : pX.leadingCoeff = 0 := by rw [leadingCoeff, hpX]; exact h0
      rw [leadingCoeff_eq_zero] at this
      rw [this, natDegree_zero] at hpX
      exact zero_ne_one hpX
    · rw [hqX, eval_zero, zero_mul, add_zero, eval_eq_of_natDegree_le_one hpX.le]
  obtain ⟨β, σ, t, hβ, hYev⟩ :
      ∃ β σ t : k, β ≠ 0 ∧ ∀ x y : k, pY.eval x + qY.eval x * y = β * y + σ * x + t := by
    have hq : qY = C (qY.coeff 0) := eq_C_of_natDegree_eq_zero hqY0
    refine ⟨qY.coeff 0, pY.coeff 1, pY.coeff 0, fun h0 => hqY ?_, fun x y => ?_⟩
    · rw [hq, h0, map_zero]
    · have h2 : qY.eval x = qY.coeff 0 := by
        conv_lhs => rw [hq, eval_C]
      rw [eval_eq_of_natDegree_le_one hpY, h2]
      ring

  have hrel := eq_zero_of_eval_eq_zero E hB
    (p := C (β ^ 2 - α ^ 3) * X ^ 3
      + C (σ ^ 2 + E.a₁ * α * σ - 3 * α ^ 2 * r - E.a₂ * α ^ 2 + β ^ 2 * E.a₂) * X ^ 2
      + C (2 * σ * t + E.a₁ * (α * t + r * σ) + E.a₃ * σ - 3 * α * r ^ 2 - 2 * E.a₂ * α * r
          - E.a₄ * α + β ^ 2 * E.a₄) * X
      + C (t ^ 2 + E.a₁ * r * t + E.a₃ * t - r ^ 3 - E.a₂ * r ^ 2 - E.a₄ * r - E.a₆
          + β ^ 2 * E.a₆))
    (q := C (2 * β * σ + E.a₁ * α * β - β ^ 2 * E.a₁) * X
      + C (2 * β * t + E.a₁ * r * β + E.a₃ * β - β ^ 2 * E.a₃))
    (fun x y hxy hx => by
      obtain ⟨h', -⟩ := hrep x y hxy hx
      have hE' := (Affine.equation_iff ..).mp h'.left
      rw [hXev, hYev] at hE'
      have hE := (Affine.equation_iff ..).mp hxy.left
      simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
      linear_combination hE' - β ^ 2 * hE)
  obtain ⟨M3, M2, M1, M0, L1, L0⟩ := coeffs_eq_zero_of_eq_zero hrel.1 hrel.2

  have hμ : β / α ≠ 0 := div_ne_zero hβ hα
  have hαμ : α = (β / α) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hα)]
    linear_combination (-1 : k) * M3
  have hβμ : β = (β / α) ^ 3 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 3 hα)]
    linear_combination (-(β : k)) * M3
  refine ⟨(Units.mk0 (β / α) hμ, r, σ, t),
    toVC_smul_eq_of_relations E hμ hαμ hβμ L1 L0 M2 M1 M0, fun x y h hx => ?_⟩
  obtain ⟨h', hu⟩ := hrep x y h hx
  have hA : pX.eval x + qX.eval x * y = ((Units.mk0 (β / α) hμ : kˣ) : k) ^ 2 * x + r := by
    rw [hXev, Units.val_mk0, ← hαμ]
  have hB : pY.eval x + qY.eval x * y =
      ((Units.mk0 (β / α) hμ : kˣ) : k) ^ 3 * y + σ * x + t := by
    rw [hYev, Units.val_mk0, ← hβμ]
  obtain ⟨h'', e⟩ := some_eq_some h' hA hB
  exact ⟨h'', hu.trans e⟩

end Pair

section Aff

variable [IsAlgClosed k] [DecidableEq k] (E : Affine k) [E.IsElliptic]

def affSet (q : kˣ × k × k × k) : Set (E.Point →+ E.Point) :=
  {u | ∃ B : Set k, B.Finite ∧ ∀ (x y : k) (h : E.Nonsingular x y), x ∉ B →
    ∃ h', u (.some x y h) =
      .some ((q.1 : k) ^ 2 * x + q.2.1) ((q.1 : k) ^ 3 * y + q.2.2.1 * x + q.2.2.2) h'}

theorem affSet_subsingleton (q : kˣ × k × k × k) : (affSet E q).Subsingleton := by
  rintro u ⟨B, hB, hu⟩ v ⟨B', hB', hv⟩
  haveI := infinite_point E
  refine addMonoidHom_eq_of_finite ((finite_not_good E (hB.union hB')).subset ?_)
  intro P hP
  simp only [Set.mem_setOf_eq] at hP ⊢
  intro hgood
  obtain ⟨x, y, h, rfl, hx⟩ := hgood
  rw [Set.mem_union, not_or] at hx
  obtain ⟨h1, e1⟩ := hu x y h hx.1
  obtain ⟨h2, e2⟩ := hv x y h hx.2
  exact hP (by rw [e1, e2])

end Aff

end OverK

section OverF

variable {F : Type*} [Field F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k]
  (W : WeierstrassCurve F) [W.IsElliptic]

theorem exists_mem_affSet
    (u : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point)
    (hu : u ∈ WeierstrassCurve.rationalHomSet k W W)
    (v : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point)
    (hv : v ∈ WeierstrassCurve.rationalHomSet k W W)
    (h₁ : u.comp v = AddMonoidHom.id _) (h₂ : v.comp u = AddMonoidHom.id _) :
    ∃ q : kˣ × k × k × k,
      toVC q ∈ MulAction.stabilizer (VariableChange k) (W.baseChange k) ∧
        u ∈ affSet (W.baseChange k).toAffine q := by
  haveI : (W.baseChange k).IsElliptic := (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  have hc : ∀ P, v (u P) = P := fun P => DFunLike.congr_fun h₂ P
  have hc' : ∀ Q, u (v Q) = Q := fun Q => DFunLike.congr_fun h₁ Q
  have hinj : Function.Injective u := Function.LeftInverse.injective hc
  have hinj' : Function.Injective v := Function.LeftInverse.injective hc'

  obtain ⟨pX, qX, pY, qY, B, hB, hrep⟩ :=
    WeierstrassCurve.exists_polynomial_rep_of_injective_of_mem_rationalHomSet k W W u hu hinj
  obtain ⟨pX', qX', pY', qY', B', hB', hrep'⟩ :=
    WeierstrassCurve.exists_polynomial_rep_of_injective_of_mem_rationalHomSet k W W v hv hinj'
  obtain ⟨q, hq, huq⟩ := exists_toVC (E := (W.baseChange k).toAffine) (u := u) (u' := v)
    hinj hinj' hc hc' hB hrep hB' hrep'
  exact ⟨q, MulAction.mem_stabilizer_iff.mpr hq, B, hB, huq⟩

theorem finite_units :
    {u : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point |
      u ∈ WeierstrassCurve.rationalHomSet k W W ∧
        ∃ v ∈ WeierstrassCurve.rationalHomSet k W W,
          u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _}.Finite := by
  haveI : (W.baseChange k).IsElliptic := (inferInstance : (W.map (algebraMap F k)).IsElliptic)

  have hI : (toVC ⁻¹' (MulAction.stabilizer (VariableChange k) (W.baseChange k) :
      Set (VariableChange k))).Finite := by
    haveI := WeierstrassCurve.finite_stabilizer_variableChange k (W.baseChange k)
    exact (Set.toFinite _).preimage toVC_injective.injOn
  refine (hI.biUnion fun q _ =>
    (affSet_subsingleton (W.baseChange k).toAffine q).finite).subset ?_
  rintro u ⟨hu, v, hv, h₁, h₂⟩
  obtain ⟨q, hq, hA⟩ := exists_mem_affSet k W u hu v hv h₁ h₂
  exact Set.mem_biUnion hq hA

end OverF

end WeierstrassCurve.RationalHomUnits
p2m_reactivate "P2MW.S_WeierstrassCurve_finite_rationalHomSet_units.WeierstrassCurve P2MW.S_WeierstrassCurve_finite_rationalHomSet_units.WeierstrassCurve.RationalHomUnits"
p2m_reactivate "P2MW.S_WeierstrassCurve_finite_rationalHomSet_units.WeierstrassCurve"

theorem solution {F : Type*} [Field F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] : {u : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point | u ∈ WeierstrassCurve.rationalHomSet k W W ∧ ∃ v ∈ WeierstrassCurve.rationalHomSet k W W, u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _}.Finite :=
  WeierstrassCurve.RationalHomUnits.finite_units k W

end S_WeierstrassCurve_finite_rationalHomSet_units
end P2MW
export P2MW.S_WeierstrassCurve_finite_rationalHomSet_units (solution)
