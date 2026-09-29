-- Prove2me | solution 1 for WeierstrassCurve.add_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/31c83bc2-90cc-5c68-904f-7ea42f9eea17

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_add_mem_rationalHomSet

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.CoordinateRing.smul_basis_eq_zero Affine.slope_of_X_ne a₃ a₁ map Affine.CoordinateRing.norm_smul_basis Affine.CoordinateRing a₄ a₂ a₆ Affine.Point.some Affine.Point.X_eq_iff Affine.degree_polynomial Affine.Point.some.inj Affine.Point.add_self_of_Y_eq Affine.negAddY Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.monic_polynomial Affine.CoordinateRing.basis Affine.addY Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.add_self_of_Y_ne baseChange evalEvalBC IsRationallyRepresented rationalHomSet"
namespace RationalHomAdd
p2m_open "WeierstrassCurve"

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k p x y = bc x y p := rfl

theorem bc_apply (x y : k) (p : F[X][Y]) :
    bc x y p = (p.map (mapRingHom (algebraMap F k))).evalEval x y := rfl

@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by
  simp [bc]

@[scoped simp] theorem bc_CX (x y : k) : bc x y (C X : F[X][Y]) = x := by
  simp [bc]

@[scoped simp] theorem bc_Y (x y : k) : bc x y (Y : F[X][Y]) = y := by
  simp [bc]

section Dichotomy

variable (W' : Affine k)

theorem exists_evalEval_eq_linear (G : k[X][Y]) :
    ∃ p q : k[X], ∀ x y : k, W'.Equation x y → G.evalEval x y = p.eval x + q.eval x * y := by
  set r : k[X][Y] := G %ₘ W'.polynomial with hr_def
  have hne1 : W'.polynomial ≠ 1 := by
    intro h
    have := W'.natDegree_polynomial
    rw [h, natDegree_one] at this
    exact absurd this (by norm_num)
  have hr : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt G W'.monic_polynomial hne1
    rw [W'.natDegree_polynomial] at this
    exact Nat.lt_succ_iff.mp this
  refine ⟨r.coeff 0, r.coeff 1, fun x y hxy => ?_⟩
  have hG : r + W'.polynomial * (G /ₘ W'.polynomial) = G := modByMonic_add_div G W'.polynomial
  have hreq : r = C (r.coeff 1) * Y + C (r.coeff 0) := eq_X_add_C_of_natDegree_le_one hr
  have h0 : W'.polynomial.evalEval x y = 0 := hxy
  have hr_eval : r.evalEval x y = (r.coeff 0).eval x + (r.coeff 1).eval x * y := by
    conv_lhs => rw [hreq]
    rw [evalEval_add, evalEval_mul, evalEval_C, evalEval_C, evalEval_X]
    ring
  rw [← hG, evalEval_add, evalEval_mul, h0, zero_mul, add_zero, hr_eval]

theorem norm_eval_eq_zero {p q : k[X]} {x y : k} (hxy : W'.Equation x y)
    (h0 : p.eval x + q.eval x * y = 0) :
    (p ^ 2 - p * q * (C W'.a₁ * X + C W'.a₃) -
      q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)).eval x = 0 := by
  rw [Affine.equation_iff] at hxy
  simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X]
  linear_combination (q.eval x) ^ 2 * hxy +
    (p.eval x - q.eval x * y - q.eval x * (W'.a₁ * x + W'.a₃)) * h0

theorem eq_zero_of_norm_eq_zero {p q : k[X]}
    (hN : p ^ 2 - p * q * (C W'.a₁ * X + C W'.a₃) -
      q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) = 0) : p = 0 ∧ q = 0 := by
  classical
  haveI : Module.Free k[X] W'.CoordinateRing :=
    Module.Free.of_basis (Affine.CoordinateRing.basis W')
  haveI : Module.Finite k[X] W'.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis W')
  rw [← Affine.CoordinateRing.norm_smul_basis, Algebra.norm_eq_zero_iff] at hN
  exact Affine.CoordinateRing.smul_basis_eq_zero hN

end Dichotomy

theorem dichotomy (W : WeierstrassCurve F) (G : F[X][Y]) :
    (∀ x y : k, (W.baseChange k).toAffine.Equation x y → bc x y G = 0) ∨
      {x : k | ∃ y : k, (W.baseChange k).toAffine.Equation x y ∧ bc x y G = 0}.Finite := by
  obtain ⟨p, q, hpq⟩ :=
    exists_evalEval_eq_linear (W.baseChange k).toAffine (G.map (mapRingHom (algebraMap F k)))
  by_cases hN : p ^ 2 - p * q * (C (W.baseChange k).toAffine.a₁ * X + C (W.baseChange k).toAffine.a₃)
      - q ^ 2 * (X ^ 3 + C (W.baseChange k).toAffine.a₂ * X ^ 2 +
        C (W.baseChange k).toAffine.a₄ * X + C (W.baseChange k).toAffine.a₆) = 0
  · left
    intro x y hxy
    obtain ⟨rfl, rfl⟩ := eq_zero_of_norm_eq_zero (W.baseChange k).toAffine hN
    rw [bc_apply, hpq x y hxy]
    simp
  · right
    refine (Polynomial.finite_setOf_isRoot hN).subset ?_
    rintro x ⟨y, hxy, h0⟩
    exact norm_eval_eq_zero (W.baseChange k).toAffine hxy (by rw [← hpq x y hxy]; exact h0)

section GroupLemma

variable {G G' : Type*} [AddCommGroup G] [AddCommGroup G']

theorem eq_top_of_finite_compl [Infinite G] (H : AddSubgroup G) (hH : ((H : Set G)ᶜ).Finite) :
    H = ⊤ := by
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, a ∉ H := by
    by_contra hall
    push Not at hall
    exact hne ((AddSubgroup.eq_top_iff' H).mpr hall)
  have hsub : (fun h : G => a + h) '' (H : Set G) ⊆ (H : Set G)ᶜ := by
    rintro _ ⟨h, hh, rfl⟩ hah
    have : a + h - h ∈ H := H.sub_mem hah hh
    exact ha (by simpa using this)
  have hHfin : (H : Set G).Finite :=
    (hH.subset hsub).of_finite_image (add_right_injective a).injOn
  have huniv : (Set.univ : Set G).Finite := by
    rw [← Set.union_compl_self (H : Set G)]
    exact hHfin.union hH
  exact Set.infinite_univ huniv

theorem zero_or_zero_of_cofinite [Infinite G] (φ ψ : G →+ G') (S : Set G) (hS : Sᶜ.Finite)
    (h : ∀ P ∈ S, φ P = 0 ∨ ψ P = 0) : φ = 0 ∨ ψ = 0 := by
  classical
  by_cases hφ : φ = 0
  · exact Or.inl hφ
  right
  suffices hk : ((ψ.ker : Set G)ᶜ).Finite by
    have htop := eq_top_of_finite_compl ψ.ker hk
    ext P
    have hP : P ∈ ψ.ker := htop ▸ AddSubgroup.mem_top P
    simpa using hP
  by_cases hfin : (φ.ker : Set G).Finite
  · refine (hS.union hfin).subset ?_
    intro P hP
    by_contra hP'
    simp only [Set.mem_union, Set.mem_compl_iff, SetLike.mem_coe, AddMonoidHom.mem_ker,
      not_or, not_not] at hP'
    rcases h P hP'.1 with h1 | h2
    · exact hP'.2 h1
    · exact hP (by simpa using h2)
  · obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hφ (AddMonoidHom.ext hall)

    have hker : ∀ h₀, φ h₀ = 0 → ψ h₀ = 0 := by
      intro h₀ hh₀
      have hinf : (φ.ker : Set G).Infinite := hfin
      have hbad : ({t : G | g + t ∈ Sᶜ} ∪ {t : G | g + t - h₀ ∈ Sᶜ}).Finite := by
        refine (hS.preimage (f := fun t => g + t) ?_).union (hS.preimage (f := fun t => g + t - h₀) ?_)
        · exact fun a _ b _ hab => add_left_cancel hab
        · exact fun a _ b _ hab => add_left_cancel (sub_left_injective hab)
      obtain ⟨t, ht, htbad⟩ := (hinf.diff hbad).nonempty
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, not_or, not_not] at htbad
      have ht' : φ t = 0 := ht
      have h1 : ψ (g + t) = 0 := by
        rcases h _ htbad.1 with h1 | h1
        · exact absurd (by simpa [map_add, ht'] using h1) hg
        · exact h1
      have h2 : ψ (g + t - h₀) = 0 := by
        rcases h _ htbad.2 with h2 | h2
        · exact absurd (by simpa [map_add, map_sub, ht', hh₀] using h2) hg
        · exact h2
      have : ψ h₀ = ψ (g + t) - ψ (g + t - h₀) := by
        rw [← map_sub]; congr 1; abel
      rw [this, h1, h2, sub_zero]
    refine hS.subset ?_
    intro P hP
    by_contra hPS
    simp only [Set.mem_compl_iff, not_not] at hPS
    rcases h P hPS with h1 | h2
    · exact hP (hker P h1)
    · exact hP h2

end GroupLemma

variable [DecidableEq k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

section Generic

variable (W : WeierstrassCurve F)

def Good (B : Set k) (P : Pt k W) : Prop :=
  ∃ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B

omit [DecidableEq k] in
theorem exists_some_of_eq {Q : Pt k W} {x₁ y₁ : k}
    {h₁ : (W.baseChange k).toAffine.Nonsingular x₁ y₁}
    (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

omit [DecidableEq k] in
theorem finite_setOf_equation (x : k) :
    {y : k | (W.baseChange k).toAffine.Equation x y}.Finite := by
  have hne : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

omit [DecidableEq k] in
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

omit [DecidableEq k] in
theorem infinite_point [IsAlgClosed k] [W.IsElliptic] : Infinite (Pt k W) := by
  haveI : (W.baseChange k).IsElliptic :=
    (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  have hy : ∀ x : k, ∃ y : k, (W.baseChange k).toAffine.Nonsingular x y := by
    intro x
    have hdeg : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
      rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
        WeierstrassCurve.Affine.degree_polynomial]
      norm_num
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, ((W.baseChange k).toAffine.equation_iff_nonsingular).mp ?_⟩
    rw [IsRoot.def, map_evalRingHom_eval] at hy
    exact hy
  choose f hf using hy
  refine Infinite.of_injective (fun x : k => (Affine.Point.some x (f x) (hf x) : Pt k W)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

def IsRat (f : k → k → k) : Prop :=
  ∃ (n d : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ x y : k, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B →
      bc x y d ≠ 0 ∧ f x y = bc x y n / bc x y d

namespace IsRat

variable {W}
variable {f g : k → k → k}

omit [DecidableEq k] in
theorem of_eq (hf : IsRat W f) (hfg : ∀ x y, g x y = f x y) : IsRat W g := by
  obtain ⟨n, d, B, hB, h⟩ := hf
  exact ⟨n, d, B, hB, fun x y hxy hx => ⟨(h x y hxy hx).1, (hfg x y).trans (h x y hxy hx).2⟩⟩

omit [DecidableEq k] in
theorem const (a : F) : IsRat W (fun _ _ => algebraMap F k a) :=
  ⟨C (C a), 1, ∅, Set.finite_empty, fun x y _ _ => by simp⟩

omit [DecidableEq k] in
theorem natCast (n : ℕ) : IsRat W (fun _ _ => (n : k)) :=
  (const (W := W) (n : F)).of_eq fun _ _ => by simp

omit [DecidableEq k] in
theorem fst : IsRat W (fun (x : k) (_ : k) => x) :=
  ⟨C X, 1, ∅, Set.finite_empty, fun x y _ _ => by simp⟩

omit [DecidableEq k] in
theorem snd : IsRat W (fun (_ : k) (y : k) => y) :=
  ⟨Y, 1, ∅, Set.finite_empty, fun x y _ _ => by simp⟩

omit [DecidableEq k] in
theorem add (hf : IsRat W f) (hg : IsRat W g) : IsRat W (fun x y => f x y + g x y) := by
  obtain ⟨n₁, d₁, B₁, hB₁, h₁⟩ := hf
  obtain ⟨n₂, d₂, B₂, hB₂, h₂⟩ := hg
  refine ⟨n₁ * d₂ + n₂ * d₁, d₁ * d₂, B₁ ∪ B₂, hB₁.union hB₂, fun x y hxy hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1
  obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.2
  refine ⟨by simp [hd₁, hd₂], ?_⟩
  beta_reduce
  rw [hf₁, hf₂, map_add, map_mul, map_mul, map_mul]
  field_simp

omit [DecidableEq k] in
theorem neg (hf : IsRat W f) : IsRat W (fun x y => -f x y) := by
  obtain ⟨n, d, B, hB, h⟩ := hf
  refine ⟨-n, d, B, hB, fun x y hxy hx => ?_⟩
  obtain ⟨hd, hf⟩ := h x y hxy hx
  exact ⟨hd, by beta_reduce; rw [hf, map_neg, neg_div]⟩

omit [DecidableEq k] in
theorem sub (hf : IsRat W f) (hg : IsRat W g) : IsRat W (fun x y => f x y - g x y) :=
  (hf.add hg.neg).of_eq fun x y => by ring

omit [DecidableEq k] in
theorem mul (hf : IsRat W f) (hg : IsRat W g) : IsRat W (fun x y => f x y * g x y) := by
  obtain ⟨n₁, d₁, B₁, hB₁, h₁⟩ := hf
  obtain ⟨n₂, d₂, B₂, hB₂, h₂⟩ := hg
  refine ⟨n₁ * n₂, d₁ * d₂, B₁ ∪ B₂, hB₁.union hB₂, fun x y hxy hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1
  obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.2
  refine ⟨by simp [hd₁, hd₂], ?_⟩
  beta_reduce
  rw [hf₁, hf₂, map_mul, map_mul]
  field_simp

omit [DecidableEq k] in
theorem pow (hf : IsRat W f) (n : ℕ) : IsRat W (fun x y => f x y ^ n) := by
  induction n with
  | zero => exact (natCast (W := W) 1).of_eq fun x y => by simp
  | succ n ih => exact (ih.mul hf).of_eq fun x y => by ring

omit [DecidableEq k] in

theorem div (hf : IsRat W f) (hg : IsRat W g) {B₀ : Set k} (hB₀ : B₀.Finite)
    (hne : ∀ x y, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B₀ → g x y ≠ 0) :
    IsRat W (fun x y => f x y / g x y) := by
  obtain ⟨n₁, d₁, B₁, hB₁, h₁⟩ := hf
  obtain ⟨n₂, d₂, B₂, hB₂, h₂⟩ := hg
  refine ⟨n₁ * d₂, d₁ * n₂, B₀ ∪ B₁ ∪ B₂, (hB₀.union hB₁).union hB₂, fun x y hxy hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1.2
  obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.2
  have hg0 := hne x y hxy hx.1.1
  rw [hf₂] at hg0
  have hn₂ : bc x y n₂ ≠ 0 := fun h0 => hg0 (by rw [h0, zero_div])
  refine ⟨by simp [hd₁, hn₂], ?_⟩
  beta_reduce
  rw [hf₁, hf₂, map_mul, map_mul]
  field_simp

end IsRat

theorem isRationallyRepresented_of_isRat {W₁ W₂ : WeierstrassCurve F}
    (γ : Pt k W₁ →+ Pt k W₂) {fX fY : k → k → k} (hX : IsRat W₁ fX) (hY : IsRat W₁ fY)
    {B₀ : Set k} (hB₀ : B₀.Finite)
    (hγ : ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B₀ →
      ∃ h', γ (.some x y h) = .some (fX x y) (fY x y) h') :
    IsRationallyRepresented k W₁ W₂ γ := by
  obtain ⟨nX, dX, BX, hBX, hX⟩ := hX
  obtain ⟨nY, dY, BY, hBY, hY⟩ := hY
  refine ⟨nX, dX, nY, dY, B₀ ∪ BX ∪ BY, (hB₀.union hBX).union hBY, fun x y h hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hdX, hfX⟩ := hX x y h hx.1.2
  obtain ⟨hdY, hfY⟩ := hY x y h hx.2
  obtain ⟨h', hγ'⟩ := hγ x y h hx.1.1
  refine ⟨hdX, hdY, ?_⟩
  simp only [evalEvalBC_eq]
  exact exists_some_of_eq W₂ hγ' hfX hfY

end Generic

variable {W₁ W₂ : WeierstrassCurve F}

theorem exists_isRat_of_isRationallyRepresented {α : Pt k W₁ →+ Pt k W₂}
    (hα : IsRationallyRepresented k W₁ W₂ α) :
    ∃ (fX fY : k → k → k) (B : Set k), IsRat W₁ fX ∧ IsRat W₁ fY ∧ B.Finite ∧
      ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
        ∃ h', α (.some x y h) = .some (fX x y) (fY x y) h' := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine ⟨fun x y => bc x y nX / bc x y dX, fun x y => bc x y nY / bc x y dY, B,
    ⟨nX, dX, B, hB, fun x y h hx => ⟨(hrep x y h hx).1, rfl⟩⟩,
    ⟨nY, dY, B, hB, fun x y h hx => ⟨(hrep x y h hx).2.1, rfl⟩⟩, hB, fun x y h hx => ?_⟩
  obtain ⟨-, -, h', hP⟩ := hrep x y h hx
  exact ⟨h', hP⟩

omit [DecidableEq k] in

theorem isRat_dichotomy {f g : k → k → k} (hf : IsRat W₁ f) (hg : IsRat W₁ g) :
    (∃ B : Set k, B.Finite ∧ ∀ (x y : k), (W₁.baseChange k).toAffine.Nonsingular x y → x ∉ B →
        f x y = g x y) ∨
      (∃ B : Set k, B.Finite ∧ ∀ (x y : k), (W₁.baseChange k).toAffine.Nonsingular x y → x ∉ B →
        f x y ≠ g x y) := by
  obtain ⟨n₁, d₁, B₁, hB₁, h₁⟩ := hf
  obtain ⟨n₂, d₂, B₂, hB₂, h₂⟩ := hg
  rcases dichotomy (k := k) W₁ (n₁ * d₂ - n₂ * d₁) with hall | hfin
  · left
    refine ⟨B₁ ∪ B₂, hB₁.union hB₂, fun x y hxy hx => ?_⟩
    simp only [Set.mem_union, not_or] at hx
    obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1
    obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.2
    have h0 := hall x y hxy.1
    rw [map_sub, map_mul, map_mul] at h0
    rw [hf₁, hf₂, div_eq_div_iff hd₁ hd₂]
    linear_combination h0
  · right
    refine ⟨B₁ ∪ B₂ ∪ _, (hB₁.union hB₂).union hfin, fun x y hxy hx => ?_⟩
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_exists, not_and] at hx
    obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1.1
    obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.1.2
    intro hfg
    refine hx.2 y hxy.1 ?_
    rw [hf₁, hf₂, div_eq_div_iff hd₁ hd₂] at hfg
    rw [map_sub, map_mul, map_mul]
    linear_combination hfg

theorem isRationallyRepresented_add_of_X_ne {α β : Pt k W₁ →+ Pt k W₂}
    {fX fY gX gY : k → k → k} (hfX : IsRat W₁ fX) (hfY : IsRat W₁ fY) (hgX : IsRat W₁ gX)
    (hgY : IsRat W₁ gY) {B : Set k} (hB : B.Finite)
    (hα : ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
        ∃ h', α (.some x y h) = .some (fX x y) (fY x y) h')
    (hβ : ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
        ∃ h', β (.some x y h) = .some (gX x y) (gY x y) h')
    (hne : ∀ (x y : k), (W₁.baseChange k).toAffine.Nonsingular x y → x ∉ B → fX x y ≠ gX x y) :
    IsRationallyRepresented k W₁ W₂ (α + β) := by

  set L : k → k → k := fun x y => (fY x y - gY x y) / (fX x y - gX x y) with hL
  have hLr : IsRat W₁ L := (hfY.sub hgY).div (hfX.sub hgX) hB
    (fun x y hxy hx => sub_ne_zero.mpr (hne x y hxy hx))
  set X₃ : k → k → k := fun x y => (W₂.baseChange k).toAffine.addX (fX x y) (gX x y) (L x y)
    with hX₃
  set Y₃ : k → k → k := fun x y => (W₂.baseChange k).toAffine.addY (fX x y) (gX x y) (fY x y) (L x y)
    with hY₃
  have hX₃r : IsRat W₁ X₃ := by
    refine ((((hLr.pow 2).add ((IsRat.const W₂.a₁).mul hLr)).sub (IsRat.const W₂.a₂)).sub
      hfX).sub hgX |>.of_eq fun x y => ?_
    simp [X₃, Affine.addX]
  have hY₃r : IsRat W₁ Y₃ := by
    refine ((((hLr.mul (hX₃r.sub hfX)).add hfY).neg.sub ((IsRat.const W₂.a₁).mul hX₃r)).sub
      (IsRat.const W₂.a₃)).of_eq fun x y => ?_
    simp [Y₃, X₃, Affine.addY, Affine.negAddY, Affine.negY]
  refine isRationallyRepresented_of_isRat (α + β) hX₃r hY₃r hB fun x y h hx => ?_
  obtain ⟨h₁, hαP⟩ := hα x y h hx
  obtain ⟨h₂, hβP⟩ := hβ x y h hx
  have hne' := hne x y h hx
  refine exists_some_of_eq W₂ (x₁ := (W₂.baseChange k).toAffine.addX (fX x y) (gX x y)
      ((W₂.baseChange k).toAffine.slope (fX x y) (gX x y) (fY x y) (gY x y)))
    (y₁ := (W₂.baseChange k).toAffine.addY (fX x y) (gX x y) (fY x y)
      ((W₂.baseChange k).toAffine.slope (fX x y) (gX x y) (fY x y) (gY x y)))
    (h₁ := Affine.nonsingular_add h₁ h₂ fun hxy => hne' hxy.left) ?_ ?_ ?_
  · rw [AddMonoidHom.add_apply, hαP, hβP, Affine.Point.add_of_X_ne hne']
  · rw [Affine.slope_of_X_ne hne']
  · rw [Affine.slope_of_X_ne hne']

theorem add_self_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] {α : Pt k W₁ →+ Pt k W₂}
    (hα : IsRationallyRepresented k W₁ W₂ α) : α + α ∈ rationalHomSet k W₁ W₂ := by
  obtain ⟨fX, fY, B, hfX, hfY, hB, hαP⟩ := exists_isRat_of_isRationallyRepresented hα

  have hNr : IsRat W₁ (fun x y => (W₂.baseChange k).toAffine.negY (fX x y) (fY x y)) := by
    refine ((hfY.neg.sub ((IsRat.const W₂.a₁).mul hfX)).sub (IsRat.const W₂.a₃)).of_eq
      fun x y => ?_
    simp [Affine.negY]
  have hDr : IsRat W₁ (fun x y => fY x y - (W₂.baseChange k).toAffine.negY (fX x y) (fY x y)) :=
    hfY.sub hNr
  rcases isRat_dichotomy hfY hNr with ⟨B', hB', hall⟩ | ⟨B', hB', hne⟩
  ·
    left
    haveI := infinite_point (k := k) W₁
    have hcof : ∀ P ∈ {P : Pt k W₁ | Good W₁ (B ∪ B') P}, (α + α) P = 0 ∨ (α + α) P = 0 := by
      rintro P ⟨x, y, h, rfl, hx⟩
      simp only [Set.mem_union, not_or] at hx
      obtain ⟨h', hP⟩ := hαP x y h hx.1
      left
      rw [AddMonoidHom.add_apply, hP]
      exact Affine.Point.add_self_of_Y_eq (hall x y h hx.2)
    have hS : ({P : Pt k W₁ | Good W₁ (B ∪ B') P}ᶜ).Finite := by
      simpa [Set.compl_setOf] using finite_not_good (k := k) W₁ (hB.union hB')
    exact (zero_or_zero_of_cofinite _ _ _ hS hcof).elim id id
  ·
    right
    set L : k → k → k := fun x y =>
      (3 * fX x y ^ 2 + 2 * (W₂.baseChange k).toAffine.a₂ * fX x y + (W₂.baseChange k).toAffine.a₄
        - (W₂.baseChange k).toAffine.a₁ * fY x y) /
        (fY x y - (W₂.baseChange k).toAffine.negY (fX x y) (fY x y)) with hL
    have hLr : IsRat W₁ L := by
      refine (((((IsRat.natCast 3).mul (hfX.pow 2)).add (((IsRat.natCast 2).mul
        (IsRat.const W₂.a₂)).mul hfX)).add (IsRat.const W₂.a₄)).sub
        ((IsRat.const W₂.a₁).mul hfY)).div hDr hB' (fun x y hxy hx => sub_ne_zero.mpr
          (hne x y hxy hx)) |>.of_eq fun x y => ?_
      simp [L]
    set X₃ : k → k → k := fun x y => (W₂.baseChange k).toAffine.addX (fX x y) (fX x y) (L x y)
      with hX₃
    set Y₃ : k → k → k := fun x y =>
      (W₂.baseChange k).toAffine.addY (fX x y) (fX x y) (fY x y) (L x y) with hY₃
    have hX₃r : IsRat W₁ X₃ := by
      refine ((((hLr.pow 2).add ((IsRat.const W₂.a₁).mul hLr)).sub (IsRat.const W₂.a₂)).sub
        hfX).sub hfX |>.of_eq fun x y => ?_
      simp [X₃, Affine.addX]
    have hY₃r : IsRat W₁ Y₃ := by
      refine ((((hLr.mul (hX₃r.sub hfX)).add hfY).neg.sub ((IsRat.const W₂.a₁).mul hX₃r)).sub
        (IsRat.const W₂.a₃)).of_eq fun x y => ?_
      simp [Y₃, X₃, Affine.addY, Affine.negAddY, Affine.negY]
    refine isRationallyRepresented_of_isRat (α + α) hX₃r hY₃r (hB.union hB') fun x y h hx => ?_
    simp only [Set.mem_union, not_or] at hx
    obtain ⟨h₁, hP⟩ := hαP x y h hx.1
    have hne' := hne x y h hx.2
    refine exists_some_of_eq W₂ (x₁ := (W₂.baseChange k).toAffine.addX (fX x y) (fX x y)
        ((W₂.baseChange k).toAffine.slope (fX x y) (fX x y) (fY x y) (fY x y)))
      (y₁ := (W₂.baseChange k).toAffine.addY (fX x y) (fX x y) (fY x y)
        ((W₂.baseChange k).toAffine.slope (fX x y) (fX x y) (fY x y) (fY x y)))
      (h₁ := Affine.nonsingular_add h₁ h₁ fun hxy => hne' hxy.right) ?_ ?_ ?_
    · rw [AddMonoidHom.add_apply, hP, Affine.Point.add_self_of_Y_ne hne']
    · rw [Affine.slope_of_Y_ne rfl hne']
    · rw [Affine.slope_of_Y_ne rfl hne']

theorem add_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂)
    (hβ : β ∈ rationalHomSet k W₁ W₂) : α + β ∈ rationalHomSet k W₁ W₂ := by
  rcases hα with rfl | hα
  · simpa using hβ
  rcases hβ with rfl | hβ
  · have h__af := (Or.inr hα : α ∈ rationalHomSet k W₁ W₂)
    simp at h__af ⊢
    exact h__af
  obtain ⟨fX, fY, Ba, hfX, hfY, hBa, hαP⟩ := exists_isRat_of_isRationallyRepresented hα
  obtain ⟨gX, gY, Bb, hgX, hgY, hBb, hβP⟩ := exists_isRat_of_isRationallyRepresented hβ
  rcases isRat_dichotomy hfX hgX with ⟨B', hB', hall⟩ | ⟨B', hB', hne⟩
  ·
    haveI := infinite_point (k := k) W₁
    have hcof : ∀ P ∈ {P : Pt k W₁ | Good W₁ (Ba ∪ Bb ∪ B') P},
        (α - β) P = 0 ∨ (α + β) P = 0 := by
      rintro P ⟨x, y, h, rfl, hx⟩
      simp only [Set.mem_union, not_or] at hx
      obtain ⟨h₁, hP₁⟩ := hαP x y h hx.1.1
      obtain ⟨h₂, hP₂⟩ := hβP x y h hx.1.2
      have hxx := hall x y h hx.2
      rcases (Affine.Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp hxx with heq | heq
      · left
        rw [AddMonoidHom.sub_apply, hP₁, hP₂, heq, sub_self]
      · right
        rw [AddMonoidHom.add_apply, hP₁, hP₂, heq, neg_add_cancel]
    have hS : ({P : Pt k W₁ | Good W₁ (Ba ∪ Bb ∪ B') P}ᶜ).Finite := by
      simpa [Set.compl_setOf] using finite_not_good (k := k) W₁ ((hBa.union hBb).union hB')
    rcases zero_or_zero_of_cofinite _ _ _ hS hcof with h0 | h0
    · have hαβ : α = β := eq_of_sub_eq_zero h0
      subst hαβ
      exact add_self_mem_rationalHomSet hα
    · exact Or.inl h0
  ·
    right
    refine isRationallyRepresented_add_of_X_ne hfX hfY hgX hgY ((hBa.union hBb).union hB')
      (fun x y h hx => hαP x y h ?_) (fun x y h hx => hβP x y h ?_) (fun x y h hx => hne x y h ?_)
    all_goals simp only [Set.mem_union, not_or] at hx
    · exact hx.1.1
    · exact hx.1.2
    · exact hx.2

end WeierstrassCurve.RationalHomAdd
p2m_reactivate "P2MW.S_WeierstrassCurve_add_mem_rationalHomSet.WeierstrassCurve P2MW.S_WeierstrassCurve_add_mem_rationalHomSet.WeierstrassCurve.RationalHomAdd"
p2m_reactivate "P2MW.S_WeierstrassCurve_add_mem_rationalHomSet.WeierstrassCurve"

theorem solution {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {α β : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) : α + β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂ :=
  WeierstrassCurve.RationalHomAdd.add_mem_rationalHomSet hα hβ

end S_WeierstrassCurve_add_mem_rationalHomSet
end P2MW
export P2MW.S_WeierstrassCurve_add_mem_rationalHomSet (solution)
