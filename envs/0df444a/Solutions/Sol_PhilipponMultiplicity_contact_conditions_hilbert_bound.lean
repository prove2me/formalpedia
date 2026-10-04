-- Prove2me | solution 1 for PhilipponMultiplicity.contact_conditions_hilbert_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:36:56.380097+00:00
-- url     : https://prove2.me/submissions/e1dcab22-fe59-45bc-8849-bd9076d77320

import Mathlib
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic

set_option autoImplicit false

noncomputable section

namespace Cex2ca8

open PhilipponMultiplicity MvPolynomial

/-! ### Hilbert function of the zero ideal of `K[x0,x1]` (one projective factor `P^1`). -/

abbrev N1 : Fin 1 → ℕ := fun _ => 1
abbrev Var1 := Sigma fun i : Fin 1 => Fin (N1 i + 1)

theorem weight_eq (m : Var1 →₀ ℕ) :
    Finsupp.weight (Hilbert.blockWeight 1 N1) m = fun _ => m ⟨0, 0⟩ + m ⟨0, 1⟩ := by
  funext i
  fin_cases i
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Hilbert.blockWeight, Fintype.sum_sigma,
    Fin.sum_univ_succ]

def monoEquiv (d : Fin 1 → ℕ) :
    {m : Var1 →₀ ℕ | Finsupp.weight (Hilbert.blockWeight 1 N1) m = d} ≃ Fin (d 0 + 1) where
  toFun m := ⟨m.1 ⟨0, 1⟩, by
    have h := congrFun m.2 0
    rw [weight_eq] at h
    simp only at h
    omega⟩
  invFun k := ⟨Finsupp.single ⟨0, 0⟩ (d 0 - k.1) + Finsupp.single ⟨0, 1⟩ k.1, by
    show Finsupp.weight _ _ = d
    rw [weight_eq]
    funext i
    fin_cases i
    have := k.2
    simp [Finsupp.single_apply]
    omega⟩
  left_inv m := by
    obtain ⟨m, hm⟩ := m
    have h := congrFun hm 0
    rw [weight_eq] at h
    simp only at h
    apply Subtype.ext
    ext ⟨i, j⟩
    fin_cases i
    fin_cases j
    · simp [Finsupp.single_apply]
      omega
    · simp [Finsupp.single_apply]
  right_inv k := by
    apply Fin.ext
    simp [Finsupp.single_apply]

theorem finrank_degreePiece (d : Fin 1 → ℕ) :
    Module.finrank ℂ (Hilbert.degreePiece ℂ 1 N1 d) = d 0 + 1 := by
  unfold Hilbert.degreePiece
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have e1 := AddMonoidAlgebra.supportedEquivFinsupp (R := ℂ) (S := ℂ)
    {m : Var1 →₀ ℕ | Finsupp.weight (Hilbert.blockWeight 1 N1) m = d}
  have e2 := Finsupp.domLCongr (M := ℂ) (R := ℂ) (monoEquiv d)
  rw [(e1.trans e2).finrank_eq, Module.finrank_finsupp_self, Fintype.card_fin]

theorem hilbertFunction_bot (d : Fin 1 → ℕ) :
    Hilbert.hilbertFunction ℂ 1 N1 ⊥ d = d 0 + 1 := by
  unfold Hilbert.hilbertFunction Hilbert.quotientPiece
  have hinj : Function.Injective (Ideal.Quotient.mkₐ ℂ (⊥ : Ideal (Hilbert.CoordinateRing ℂ 1 N1))).toLinearMap := by
    intro a b hab
    have : Ideal.Quotient.mk (⊥ : Ideal (Hilbert.CoordinateRing ℂ 1 N1)) a =
        Ideal.Quotient.mk ⊥ b := hab
    rw [Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at this
    exact this
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_degreePiece]

theorem hilbertPolynomial_bot :
    Hilbert.hilbertPolynomial ℂ 1 N1 ⊥ = X 0 + 1 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, fun d _ => ?_⟩
  rw [hilbertFunction_bot]
  simp

theorem totalDegree_X_add_one : (X 0 + 1 : MvPolynomial (Fin 1) ℚ).totalDegree = 1 := by
  apply le_antisymm
  · refine (totalDegree_add _ _).trans ?_
    simp
  · have hmem : (Finsupp.single (0 : Fin 1) 1) ∈ (X 0 + 1 : MvPolynomial (Fin 1) ℚ).support := by
      rw [mem_support_iff, coeff_add, coeff_X, coeff_one,
        if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm]
      norm_num
    have := le_totalDegree hmem
    simpa using this

theorem degreeValue_bot_zero : Hilbert.degreeValue ℂ 1 N1 ⊥ 0 = 0 := by
  unfold Hilbert.degreeValue Hilbert.degreeForm
  simp only
  rw [hilbertPolynomial_bot, totalDegree_X_add_one]
  simp [constantCoeff_eq, coeff_homogeneousComponent]

/-! ### Projective-point representatives -/

theorem rep_mk_eq (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ (Projectivization.mk ℂ v hv).rep = a • v := by
  have h := Projectivization.mk_rep (Projectivization.mk ℂ v hv)
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_, ha.symm⟩
  rintro rfl
  rw [zero_smul] at ha
  exact Projectivization.rep_nonzero _ ha.symm

theorem eval_smul_homog (P : MvPolynomial Var1 ℂ) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j : Fin 2, m ⟨0, j⟩ = d) (a : ℂ) (x : Var1 → ℂ) :
    eval (a • x) P = a ^ d * eval x P := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hsum : ∑ i : Var1, m i = d := by
    rw [Fintype.sum_sigma, Fin.sum_univ_one]
    exact hP m hm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hsum]
  ring

theorem eq_zero_of_vanish (P : MvPolynomial Var1 ℂ) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j : Fin 2, m ⟨0, j⟩ = d)
    (hv : ∀ x : Projectivization ℂ (Fin 2 → ℂ), x.rep 0 ≠ 0 →
      eval (fun w : Var1 => x.rep w.2) P = 0) : P = 0 := by
  have hQ : X ⟨0, 0⟩ * P = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_mul, eval_X, map_zero]
    by_cases hx : x ⟨0, 0⟩ = 0
    · simp [hx]
    · let v : Fin 2 → ℂ := fun j => x ⟨0, j⟩
      have hv0 : v ≠ 0 := fun h => hx (congrFun h 0)
      obtain ⟨a, ha, hrep⟩ := rep_mk_eq v hv0
      have hmem : (Projectivization.mk ℂ v hv0).rep 0 ≠ 0 := by
        rw [hrep]
        simp [v, ha, hx]
      have h1 := hv (Projectivization.mk ℂ v hv0) hmem
      have hcoord : (fun w : Var1 => (Projectivization.mk ℂ v hv0).rep w.2) = a • x := by
        funext w
        obtain ⟨i, j⟩ := w
        fin_cases i
        rw [hrep]
        rfl
      rw [hcoord, eval_smul_homog P d hP] at h1
      have : eval x P = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd (pow_eq_zero_iff'.mp h).1 ha
        · exact h
      simp [this]
  rcases mul_eq_zero.mp hQ with h | h
  · exact absurd h (X_ne_zero _)
  · exact h

/-! ### The additive group `G_a` as the open chart `x0 ≠ 0` of `P^1` -/

def C1 : Set (Projectivization ℂ (Fin (1 + 1) → ℂ)) := {x | x.rep 0 ≠ 0}

def vec (t : ℂ) : Fin 2 → ℂ := ![1, t]

theorem vec_ne (t : ℂ) : vec t ≠ 0 := fun h => by simpa [vec] using congrFun h 0

def pt (t : ℂ) : Projectivization ℂ (Fin (1 + 1) → ℂ) := Projectivization.mk ℂ (vec t) (vec_ne t)

theorem pt_rep (t : ℂ) : ∃ a : ℂ, a ≠ 0 ∧ (pt t).rep = a • vec t := rep_mk_eq _ (vec_ne t)

theorem pt_mem (t : ℂ) : pt t ∈ C1 := by
  obtain ⟨a, ha, h⟩ := pt_rep t
  show (pt t).rep 0 ≠ 0
  rw [h]
  simpa [vec] using ha

theorem pt_coord (x : Projectivization ℂ (Fin (1 + 1) → ℂ)) (hx : x ∈ C1) :
    pt (x.rep 1 / x.rep 0) = x := by
  have hx' : x.rep 0 ≠ 0 := hx
  conv_rhs => rw [← Projectivization.mk_rep x]
  unfold pt
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨(x.rep 0)⁻¹, ?_⟩
  funext j
  fin_cases j
  · simp [vec, hx']
  · simp [vec]
    field_simp

theorem pt_inv (t : ℂ) : (pt t).rep 1 / (pt t).rep 0 = t := by
  obtain ⟨a, ha, h⟩ := pt_rep t
  rw [h]
  simp [vec]
  field_simp

def phi : ℂ ≃ C1 where
  toFun t := ⟨pt t, pt_mem t⟩
  invFun x := x.1.rep 1 / x.1.rep 0
  left_inv t := pt_inv t
  right_inv x := Subtype.ext (pt_coord x.1 x.2)

instance grp : AddCommGroup C1 := phi.symm.addCommGroup

theorem rep_of (x : C1) : ∃ a : ℂ, a ≠ 0 ∧ x.1.rep = a • vec (phi.symm x) := by
  have : x.1 = pt (phi.symm x) := by
    conv_lhs => rw [← phi.apply_symm_apply x]
    rfl
  rw [this]
  exact pt_rep _

theorem add_val (x y : C1) : (x + y).1 = pt (phi.symm x + phi.symm y) := rfl

theorem neg_val (x : C1) : (-x).1 = pt (-(phi.symm x)) := rfl


/-! ### Regularity of addition and negation -/

theorem supp_XX {σ : Type} [DecidableEq σ] (a b : σ) :
    (X a * X b : MvPolynomial σ ℂ).support = {Finsupp.single a 1 + Finsupp.single b 1} := by
  classical
  rw [X, X, monomial_mul, one_mul, support_monomial, if_neg one_ne_zero]

abbrev Sq := Σ _ : Fin 2, Fin 2

def p0 : MvPolynomial Sq ℂ := X ⟨0, 0⟩ * X ⟨1, 0⟩
def p1 : MvPolynomial Sq ℂ := X ⟨0, 0⟩ * X ⟨1, 1⟩ + X ⟨0, 1⟩ * X ⟨1, 0⟩

theorem homog_pair (ja jb : Fin 2) :
    ∀ i : Fin 2, ∑ j : Fin 2,
      ((Finsupp.single (⟨0, ja⟩ : Sq) 1 + Finsupp.single (⟨1, jb⟩ : Sq) 1 : Sq →₀ ℕ) ⟨i, j⟩) = 1 := by
  intro i
  fin_cases i <;> fin_cases ja <;> fin_cases jb <;>
    simp +decide [Finsupp.single_apply, Fin.sum_univ_succ]

theorem homog_p0' : ∀ m ∈ p0.support, ∀ i : Fin 2, ∑ j : Fin 2, m ⟨i, j⟩ = 1 := by
  intro m hm i
  rw [p0, supp_XX, Finset.mem_singleton] at hm
  subst hm
  exact homog_pair 0 0 i

theorem homog_p0 : (projectiveSquare ℂ 1).IsHomogeneous p0 (fun _ => 1) := homog_p0'

theorem homog_p1' : ∀ m ∈ p1.support, ∀ i : Fin 2, ∑ j : Fin 2, m ⟨i, j⟩ = 1 := by
  classical
  intro m hm i
  have := support_add hm
  rw [Finset.mem_union, supp_XX, supp_XX, Finset.mem_singleton, Finset.mem_singleton] at this
  rcases this with rfl | rfl
  · exact homog_pair 0 1 i
  · exact homog_pair 1 0 i

theorem homog_p1 : (projectiveSquare ℂ 1).IsHomogeneous p1 (fun _ => 1) := homog_p1'

theorem add_reg : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 1) (projectiveSpace ℂ 1)
    (fun xy : C1 × C1 => fun i => if i.val = 0 then xy.1.val else xy.2.val)
    (fun xy : C1 × C1 => fun _ => (xy.1 + xy.2).val) := by
  intro xy b
  refine ⟨Set.univ, @isOpen_univ _ (projectiveSquare ℂ 1).zariskiTopology, trivial, fun _ => 1,
    ![p0, p1], fun j => by fin_cases j; exacts [homog_p0, homog_p1], ?_⟩
  intro y _
  obtain ⟨a, ha, h1⟩ := rep_of y.1
  obtain ⟨b', hb, h2⟩ := rep_of y.2
  have h1' : ∀ j, y.1.1.rep j = a * vec (phi.symm y.1) j := fun j => by rw [h1]; rfl
  have h2' : ∀ j, y.2.1.rep j = b' * vec (phi.symm y.2) j := fun j => by rw [h2]; rfl
  have hvec : (fun j : Fin 2 => MvPolynomial.eval
      (fun v : Sq => (if v.1.val = 0 then y.1.val else y.2.val).rep v.2) (![p0, p1] j)) =
      (a * b') • vec (phi.symm y.1 + phi.symm y.2) := by
    funext j
    fin_cases j
    · (simp [p0, h1', h2', vec]) <;> ring
    · (simp [p1, h1', h2', vec]) <;> ring
  have hne : (fun j : Fin 2 => MvPolynomial.eval
      (fun v : Sq => (if v.1.val = 0 then y.1.val else y.2.val).rep v.2) (![p0, p1] j)) ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero (mul_ne_zero ha hb) (vec_ne _)
  exact ⟨hne, (Projectivization.mk_eq_mk_iff' ℂ _ (vec (phi.symm y.1 + phi.symm y.2)) hne
    (vec_ne _)).mpr ⟨a * b', hvec.symm⟩⟩

def q0 : MvPolynomial Var1 ℂ := X ⟨0, 0⟩
def q1 : MvPolynomial Var1 ℂ := -X ⟨0, 1⟩

theorem homog_single (j : Fin 2) :
    ∀ i : Fin 1, ∑ k : Fin 2, (Finsupp.single (⟨0, j⟩ : Var1) 1) ⟨i, k⟩ = 1 := by
  intro i
  fin_cases i <;> fin_cases j <;> simp +decide [Finsupp.single_apply, Fin.sum_univ_succ]

theorem homog_q0' : ∀ m ∈ q0.support, ∀ i : Fin 1, ∑ j : Fin 2, m ⟨i, j⟩ = 1 := by
  intro m hm i
  rw [q0, support_X, Finset.mem_singleton] at hm
  subst hm
  exact homog_single 0 i

theorem homog_q1' : ∀ m ∈ q1.support, ∀ i : Fin 1, ∑ j : Fin 2, m ⟨i, j⟩ = 1 := by
  intro m hm i
  rw [q1, support_neg, support_X, Finset.mem_singleton] at hm
  subst hm
  exact homog_single 1 i

theorem homog_q0 : (projectiveSpace ℂ 1).IsHomogeneous q0 (fun _ => 1) := homog_q0'

theorem homog_q1 : (projectiveSpace ℂ 1).IsHomogeneous q1 (fun _ => 1) := homog_q1'

theorem neg_reg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 1) (projectiveSpace ℂ 1)
    (fun x : C1 => fun _ => x.val) (fun x : C1 => fun _ => (-x).val) := by
  intro x b
  refine ⟨Set.univ, @isOpen_univ _ (projectiveSpace ℂ 1).zariskiTopology, trivial, fun _ => 1,
    ![q0, q1], fun j => by fin_cases j; exacts [homog_q0, homog_q1], ?_⟩
  intro y _
  obtain ⟨a, ha, h1⟩ := rep_of y
  have h1' : ∀ j, y.1.rep j = a * vec (phi.symm y) j := fun j => by rw [h1]; rfl
  have hvec : (fun j : Fin 2 => MvPolynomial.eval (fun v : Var1 => y.1.rep v.2) (![q0, q1] j)) =
      a • vec (-(phi.symm y)) := by
    funext j
    fin_cases j
    · simp [q0, h1', vec]
    · simp [q1, h1', vec]
  have hne : (fun j : Fin 2 => MvPolynomial.eval (fun v : Var1 => y.1.rep v.2)
      (![q0, q1] j)) ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero ha (vec_ne _)
  exact ⟨hne, (Projectivization.mk_eq_mk_iff' ℂ _ (vec (-(phi.symm y))) hne
    (vec_ne _)).mpr ⟨a, hvec.symm⟩⟩

theorem lc_pre : (fun (x : Projectivization ℂ (Fin (1 + 1) → ℂ)) =>
    (fun _ => x : (projectiveSpace ℂ 1).Point)) ⁻¹' {x | (projectiveSpace ℂ 1).eval q0 x ≠ 0} = C1 := by
  have h : ∀ x : Projectivization ℂ (Fin (1 + 1) → ℂ),
      (projectiveSpace ℂ 1).eval q0 (fun _ => x) = x.rep 0 := fun x => MvPolynomial.eval_X _
  ext x
  show (projectiveSpace ℂ 1).eval q0 (fun _ => x) ≠ 0 ↔ x.rep 0 ≠ 0
  rw [h x]

theorem lc : @IsLocallyClosed _ (TopologicalSpace.induced
    (fun (x : Projectivization ℂ (Fin (1 + 1) → ℂ)) => (fun _ => x : (projectiveSpace ℂ 1).Point))
    (projectiveSpace ℂ 1).zariskiTopology) C1 := by
  letI : TopologicalSpace (Projectivization ℂ (Fin (1 + 1) → ℂ)) := TopologicalSpace.induced
    (fun (x : Projectivization ℂ (Fin (1 + 1) → ℂ)) => (fun _ => x : (projectiveSpace ℂ 1).Point))
    (projectiveSpace ℂ 1).zariskiTopology
  apply IsOpen.isLocallyClosed
  exact ⟨{x | (projectiveSpace ℂ 1).eval q0 x ≠ 0},
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨q0, fun _ => 1, homog_q0, rfl⟩, lc_pre⟩

def E : EmbeddedCommutativeGroup ℂ where
  ambientDimension := 1
  carrier := C1
  group := grp
  locallyClosed := lc
  addition_regular := add_reg
  negation_regular := neg_reg

def G : EmbeddedGroupProduct ℂ := ⟨1, one_pos, fun _ => E⟩

/-! ### Vanishing ideals are zero -/

theorem vIE : (projectiveSpace ℂ 1).vanishingIdeal ((fun x => fun _ => x) '' C1) = ⊥ := by
  unfold MultiProjectiveSpace.vanishingIdeal
  rw [Ideal.span_eq_bot]
  rintro P ⟨⟨D, hD⟩, hvan⟩
  exact eq_zero_of_vanish P (D ⟨0, Nat.one_pos⟩) (fun m hm => hD m hm ⟨0, Nat.one_pos⟩)
    (fun x hx => hvan (fun _ => x) ⟨x, hx, rfl⟩)

theorem vIG : G.vanishingIdeal Set.univ = ⊥ := by
  unfold EmbeddedGroupProduct.vanishingIdeal MultiProjectiveSpace.vanishingIdeal
  rw [Ideal.span_eq_bot]
  rintro P ⟨⟨D, hD⟩, hvan⟩
  exact eq_zero_of_vanish P (D ⟨0, Nat.one_pos⟩) (fun m hm => hD m hm ⟨0, Nat.one_pos⟩)
    (fun x hx => hvan (G.embedding (fun _ => (⟨x, hx⟩ : C1))) ⟨fun _ => (⟨x, hx⟩ : C1), trivial, rfl⟩)

theorem hp_eq (I : Ideal (Hilbert.CoordinateRing ℂ 1 N1)) (hI : I = ⊥) :
    Hilbert.hilbertPolynomial ℂ 1 N1 I = X 0 + 1 := by
  subst hI
  exact hilbertPolynomial_bot

theorem dv_eq (I : Ideal (Hilbert.CoordinateRing ℂ 1 N1)) (hI : I = ⊥) :
    Hilbert.degreeValue ℂ 1 N1 I 0 = 0 := by
  subst hI
  exact degreeValue_bot_zero

theorem dimE : E.dimension = 1 := by
  have h := hp_eq _ vIE
  unfold EmbeddedCommutativeGroup.dimension
  exact (congrArg MvPolynomial.totalDegree h).trans totalDegree_X_add_one

theorem dimG : 0 < G.dimension := by
  show 0 < ∑ i : Fin 1, (G.factor i).dimension
  rw [Fin.sum_univ_one]
  show 0 < E.dimension
  rw [dimE]
  exact one_pos

/-! ### A (constant) analytic subgroup -/

def A : AnalyticSubgroup G where
  parameterDimension := 1
  parameterDimension_pos := one_pos
  radius := 1
  radius_pos := one_pos
  domain := Metric.ball 0 1
  domain_eq_ball := rfl
  domain_open := Metric.isOpen_ball
  zero_mem := Metric.mem_ball_self one_pos
  map := fun _ => 0
  map_zero := rfl
  map_add := fun _ _ _ => (add_zero 0).symm
  lift := fun g _ v => G.ambient.coordinate (G.embedding g) v
  lift_analytic := fun _ _ => analyticAt_const
  base_series := fun _ => ⟨constFormalMultilinearSeries ℂ (Fin 1 → ℂ) _,
    hasFPowerSeriesOnBall_const.mono (by simp) le_top⟩
  base_represents := fun _ i =>
    ⟨Projectivization.rep_nonzero (G.embedding 0 i), Projectivization.mk_rep _⟩
  lift_represents := fun g => by
    filter_upwards [Metric.ball_mem_nhds (0 : Fin 1 → ℂ) one_pos] with z hz
    refine ⟨hz, fun i => ⟨Projectivization.rep_nonzero (G.embedding g i), ?_⟩⟩
    show _ = G.embedding (g + 0) i
    rw [add_zero]
    exact Projectivization.mk_rep (G.embedding g i)

def H : AlgebraicSubgroup G :=
  ⟨⊤, by rw [AddSubgroup.coe_top]; exact @isClosed_univ _ G.zariskiTopology⟩

theorem pullback_C (c : ℂ) (g : G.Point) : A.pullback (C c) g = fun _ => c := by
  funext z
  simp [AnalyticSubgroup.pullback]

theorem vo_C_ne (c : ℂ) (hc : c ≠ 0) (x : G.Point) : vanishingOrder A (C c) x = 0 := by
  unfold vanishingOrder
  rw [pullback_C]
  apply le_antisymm _ zero_le
  apply sInf_le
  refine ⟨0, ?_, rfl⟩
  show iteratedFDeriv ℂ 0 (fun _ : Fin 1 → ℂ => c) 0 ≠ 0
  rw [Ne, ← norm_eq_zero, norm_iteratedFDeriv_zero]
  simpa using hc

theorem vo_zero (x : G.Point) : vanishingOrder A 0 x = ⊤ := by
  unfold vanishingOrder
  have : A.pullback 0 x = fun _ => 0 := by
    funext z
    simp [AnalyticSubgroup.pullback]
  rw [this]
  simp [iteratedFDeriv_fun_zero]

theorem hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P 0 →
    (P ∈ (⊥ : Ideal G.CoordinateRing) ↔ ∀ g ∈ ({0} : Finset G.Point), ∀ h ∈ H.carrier,
      ((0 + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)) := by
  intro P hP
  have hPC : P = C (coeff 0 P) := by
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [hm]
    · by_contra hne
      have hmem : m ∈ P.support := mem_support_iff.mpr hne
      have hs := hP m hmem ⟨0, Nat.one_pos⟩
      apply hm
      ext w
      obtain ⟨⟨i, hi⟩, j⟩ := w
      have hi0 : i = 0 := by
        change i < 1 at hi
        omega
      subst hi0
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      exact (Finset.sum_eq_zero_iff.mp hs j (Finset.mem_univ _)).symm
  rw [hPC]
  generalize coeff 0 P = c
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero]
    simp only [Submodule.zero_mem, true_iff]
    intro g _ h _
    rw [vo_zero]
    exact le_top
  · constructor
    · intro hmem
      exact absurd (C_eq_zero.mp ((Ideal.mem_bot).mp hmem)) hc
    · intro hall
      have := hall 0 (Finset.mem_singleton_self 0) 0 H.toAddSubgroup.zero_mem
      rw [vo_C_ne c hc] at this
      simp at this

theorem lhs_one :
    ((Hilbert.hilbertFunction ℂ G.factorCount G.ambient.ambientDimension
      (⊥ : Ideal G.CoordinateRing) 0 : ℕ) : ℝ) = 1 := by
  show ((Hilbert.hilbertFunction ℂ 1 N1 ⊥ 0 : ℕ) : ℝ) = 1
  rw [hilbertFunction_bot]
  simp

theorem hdf_zero : hilbertDegreeForm G H.carrier 0 = 0 := by
  have hc : H.carrier = Set.univ := AddSubgroup.coe_top
  rw [hc]
  show ((Hilbert.degreeValue ℂ 1 N1 (G.vanishingIdeal Set.univ) 0 : ℚ) : ℝ) = 0
  rw [dv_eq _ vIG]
  simp

theorem hK : IsPhilipponBaseField ℂ := Or.inl ⟨RingEquiv.refl ℂ, fun _ _ => rfl⟩

end Cex2ca8

open PhilipponMultiplicity in
theorem solution : ¬ (∀ (K : Type) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (H : AlgebraicSubgroup G)
    (J : Ideal G.CoordinateRing)
    (hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h))),
    (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D : ℝ) ≤
      (Nat.choose (T + analyticCodimension A H.carrier)
        (analyticCodimension A H.carrier) : ℝ) *
        (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D) := by
  intro h
  have key := h ℂ Cex2ca8.hK Cex2ca8.G Cex2ca8.dimG Cex2ca8.A {0} (Finset.mem_singleton_self 0)
    0 0 Cex2ca8.H ⊥ Cex2ca8.hJ
  have h1 : (1 : ℝ) ≤ 0 := by
    calc (1 : ℝ) = _ := Cex2ca8.lhs_one.symm
      _ ≤ _ := key
      _ = 0 := by rw [Cex2ca8.hdf_zero, mul_zero]
  norm_num at h1
