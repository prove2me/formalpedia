-- Prove2me | solution 1 for PhilipponMultiplicity.lemma_3_1_zero_degree_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T08:25:59.270988+00:00
-- url     : https://prove2.me/submissions/5cbd4ec4-4630-4e7b-9405-e8a9916a937f

import Definitions.Def_PhilipponMultiplicity_Hilbert
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Mathlib.RingTheory.MvPolynomial.Ideal


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MonomialQuotientCount
variable {K σ Γ : Type*} [Field K] [AddCommMonoid Γ]

/-- Count a homogeneous quotient using its actual monomial ideal membership
criterion. The proof projects onto the complementary monomial support. -/
theorem finrank_piece (w : σ → Γ) (I : Ideal (MvPolynomial σ K))
    (U : Set (σ →₀ ℕ))
    (hI : ∀ f, f ∈ I ↔ ∀ m ∈ f.support, m ∈ U) (d : Γ) :
    Module.finrank K ((weightedHomogeneousSubmodule K w d).map
      (Ideal.Quotient.mkₐ K I).toLinearMap) =
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m = d ∧ m ∉ U} := by
  classical
  let S : Set (σ →₀ ℕ) := {m | Finsupp.weight w m = d ∧ m ∉ U}
  let V := restrictSupport K S
  let W := (weightedHomogeneousSubmodule K w d).map (Ideal.Quotient.mkₐ K I).toLinearMap
  have memV (f : MvPolynomial σ K) : f ∈ V ↔ ∀ m ∈ f.support, m ∈ S := Iff.rfl
  have homog {f : MvPolynomial σ K} (hf : f ∈ V) : f.IsWeightedHomogeneous w d := by
    intro m hm
    exact ((memV f).mp hf m (mem_support_iff.mpr hm)).1
  let q : V →ₗ[K] W :=
    { toFun := fun f => ⟨Ideal.Quotient.mk I f.val, ⟨f.val, homog f.property, rfl⟩⟩
      map_add' := by intro f g; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c f; apply Subtype.ext; exact (Ideal.Quotient.mkₐ K I).toLinearMap.map_smul c f.val }
  have hqinj : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro f hf
    have hfI : f.val ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hf)
    have hf0 : f.val = 0 := by
      apply MvPolynomial.ext
      intro m
      rw [coeff_zero]
      by_contra hn
      have hm := mem_support_iff.mpr hn
      exact ((memV f.val).mp f.property m hm).2 ((hI f.val).mp hfI m hm)
    exact Subtype.ext hf0
  have hqsurj : Function.Surjective q := by
    rintro ⟨z, f, hf, rfl⟩
    let r : MvPolynomial σ K := AddMonoidAlgebra.ofCoeff
      (Finsupp.filter (fun m => m ∉ U) (AddMonoidAlgebra.coeff f))
    have hr : r ∈ V := by
      intro m hm
      have hm' : m ∈ f.support ∧ m ∉ U := Finset.mem_filter.mp hm
      exact ⟨hf (mem_support_iff.mp hm'.1), hm'.2⟩
    refine ⟨⟨r, hr⟩, Subtype.ext (Ideal.Quotient.eq.mpr ?_)⟩
    rw [hI]
    intro m hm
    by_contra hmU
    have hc := mem_support_iff.mp hm
    apply hc
    change coeff m r - coeff m f = 0
    simp [r, MvPolynomial.coeff, Finsupp.filter_apply, hmU]
  let e := LinearEquiv.ofBijective q ⟨hqinj, hqsurj⟩
  rw [← e.finrank_eq]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K S)

end PhilipponMultiplicity.MonomialQuotientCount
end


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThree.ZeroDegreeBoundary

abbrev V := ambient.Variable
abbrev x (j : Fin 3) : V :=
  ⟨(0 : Fin 2), ⟨j.val, by simpa [ambient] using j.isLt⟩⟩
abbrev y (j : Fin 2) : V :=
  ⟨(1 : Fin 2), ⟨j.val, by simpa [ambient] using j.isLt⟩⟩

theorem single_pair_le (a b : V) (hab : a ≠ b) (m : V →₀ ℕ) :
    Finsupp.single a 1 + Finsupp.single b 1 ≤ m ↔ m a ≠ 0 ∧ m b ≠ 0 := by
  constructor
  · intro h
    have ha := h a
    have hb := h b
    simp [Finsupp.single_apply, hab, Ne.symm hab] at ha hb
    omega
  · rintro ⟨ha, hb⟩ z
    by_cases hza : z = a
    · subst z; simp [Finsupp.single_apply, hab, Ne.symm hab]; omega
    by_cases hzb : z = b
    · subst z; simp [Finsupp.single_apply, hab, Ne.symm hab]; omega
    simp [Finsupp.single_apply, Ne.symm hza, Ne.symm hzb]

theorem mem_ideal_iff (f : ambient.CoordinateRing) :
    f ∈ ideal ↔ ∀ m ∈ f.support, m (y 1) ≠ 0 ∧ (m (x 1) ≠ 0 ∨ m (x 2) ≠ 0) := by
  have h := @mem_ideal_span_monomial_image V ℂ _ f
    {Finsupp.single (y 1) 1 + Finsupp.single (x 1) 1,
      Finsupp.single (y 1) 1 + Finsupp.single (x 2) 1}
  have h1 : y 1 ≠ x 1 := by decide
  have h2 : y 1 ≠ x 2 := by decide
  have hm (a b : V) : monomial (Finsupp.single a 1 + Finsupp.single b 1) (1 : ℂ) = X a * X b := by
    simp only [X, monomial_mul, one_mul]
  simpa only [Set.image_pair, hm,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left,
    single_pair_le _ _ h1, single_pair_le _ _ h2, and_or_left,
    ideal, firstCoordinate, secondCoordinate] using h

theorem mem_yIdeal (f : ambient.CoordinateRing) :
    f ∈ Ideal.span {secondCoordinate 1} ↔ ∀ m ∈ f.support, m (y 1) ≠ 0 := by
  simpa only [Set.image_singleton, Set.mem_singleton_iff, exists_eq_left,
    secondCoordinate] using (@mem_ideal_span_X_image V ℂ _ f {y 1})

theorem mem_xIdeal (f : ambient.CoordinateRing) :
    f ∈ Ideal.span {firstCoordinate 1, firstCoordinate 2} ↔
      ∀ m ∈ f.support, m (x 1) ≠ 0 ∨ m (x 2) ≠ 0 := by
  simpa only [Set.image_pair, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, firstCoordinate] using
    (@mem_ideal_span_X_image V ℂ _ f {x 1, x 2})

theorem ideal_intersection : ideal = Ideal.span {secondCoordinate 1} ⊓
    Ideal.span {firstCoordinate 1, firstCoordinate 2} := by
  ext f
  simp only [Ideal.mem_inf, mem_ideal_iff, mem_yIdeal, mem_xIdeal]
  simp only [forall_and]

theorem ideal_homogeneous : IsMultihomogeneousIdeal ambient ideal := by
  classical
  intro f hf d
  rw [mem_ideal_iff] at hf ⊢
  intro m hm
  rw [support_weightedHomogeneousComponent] at hm
  exact hf m (Finset.mem_filter.mp hm).1

theorem ideal_regular : IsRegular (Ideal.Quotient.mk ideal polynomial) := by
  apply (Commute.isRegular_iff (fun b => Commute.all _ b)).mpr
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq.mpr
  have hz : polynomial * (a - b) ∈ ideal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [map_mul, map_sub, mul_sub, hab, sub_self]
  rw [mem_ideal_iff] at hz ⊢
  intro m hm
  have hc : (a - b).coeff m ≠ 0 := mem_support_iff.mp hm
  have hm' : m + Finsupp.single (y 0) 1 ∈ (polynomial * (a - b)).support := by
    rw [mem_support_iff]
    simpa [polynomial, secondCoordinate, mul_comm, coeff_mul_X] using hc
  simpa [Finsupp.single_apply] using hz _ hm'

theorem polynomial_homogeneous : ambient.IsHomogeneous polynomial equationDegrees := by
  intro m hm i
  have hm' : m = Finsupp.single (y 0) 1 := by
    simpa [polynomial, secondCoordinate, x, y, mem_support_iff, coeff_X, eq_comm] using hm
  subst m
  fin_cases i <;> simp [ambient, equationDegrees, x, y, Fin.sum_univ_two, Fin.sum_univ_succ,
    Finsupp.single_apply]

def exponent (a b c d e : ℕ) : V →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v =>
    if v.1 = (0 : Fin 2) then if v.2.val = 0 then a else if v.2.val = 1 then b else c
    else if v.2.val = 0 then d else e)

@[simp] theorem exponent_x0 (a b c d e : ℕ) : exponent a b c d e (x 0) = a := rfl
@[simp] theorem exponent_x1 (a b c d e : ℕ) : exponent a b c d e (x 1) = b := rfl
@[simp] theorem exponent_x2 (a b c d e : ℕ) : exponent a b c d e (x 2) = c := rfl
@[simp] theorem exponent_y0 (a b c d e : ℕ) : exponent a b c d e (y 0) = d := rfl
@[simp] theorem exponent_y1 (a b c d e : ℕ) : exponent a b c d e (y 1) = e := rfl

theorem exponent_ext {m n : V →₀ ℕ}
    (h0 : m (x 0) = n (x 0)) (h1 : m (x 1) = n (x 1)) (h2 : m (x 2) = n (x 2))
    (h3 : m (y 0) = n (y 0)) (h4 : m (y 1) = n (y 1)) : m = n := by
  ext ⟨i, j⟩
  fin_cases i
  · change Fin 3 at j
    fin_cases j <;> assumption
  · change Fin 2 at j
    fin_cases j <;> assumption

theorem weight_eq_iff (m : V →₀ ℕ) (d : Fin 2 → ℕ) :
    Finsupp.weight (Hilbert.blockWeight ambient.factorCount ambient.ambientDimension) m = d ↔
      m (x 0) + m (x 1) + m (x 2) = d 0 ∧ m (y 0) + m (y 1) = d 1 := by
  have hw : Finsupp.weight (Hilbert.blockWeight ambient.factorCount ambient.ambientDimension) m =
      ![m (x 0) + m (x 1) + m (x 2), m (y 0) + m (y 1)] := by
    ext i
    fin_cases i <;>
      simp [Finsupp.weight_eq_sum, Hilbert.blockWeight, Fintype.sum_sigma,
        ambient, Fin.sum_univ_succ, x, y, add_assoc] <;> rfl
  rw [hw]
  simp [_root_.funext_iff, Fin.forall_fin_two]

abbrev Triangle (n : ℕ) := (k : Fin (n + 1)) × Fin (k.val + 1)

theorem triangle_card (n : ℕ) : Nat.card (Triangle n) = (n + 2).choose 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ k : Fin (n + 1), (fun j : ℕ => j + 1) k.val) = _
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => j + 1) (n + 1)).trans
    (by simpa using Nat.sum_range_add_choose n 1)

abbrev Standard (d : Fin 2 → ℕ) :=
  {m : V →₀ ℕ //
    (m (x 0) + m (x 1) + m (x 2) = d 0 ∧ m (y 0) + m (y 1) = d 1) ∧
      (m (y 1) = 0 ∨ m (x 1) = 0 ∧ m (x 2) = 0)}

def standardEquiv (d : Fin 2 → ℕ) : Standard d ≃ Triangle (d 0) ⊕ Fin (d 1) where
  toFun m := if h : m.val (y 1) = 0 then
      Sum.inl ⟨⟨m.val (x 1) + m.val (x 2), by have := m.property.1.1; omega⟩,
        ⟨m.val (x 2), by dsimp; omega⟩⟩
    else Sum.inr ⟨m.val (y 1) - 1, by have := m.property.1.2; omega⟩
  invFun s := match s with
    | Sum.inl k => ⟨exponent (d 0 - k.1.val) (k.1.val - k.2.val) k.2.val (d 1) 0, by
        change ((d 0 - k.1.val) + (k.1.val - k.2.val) + k.2.val = d 0 ∧ d 1 + 0 = d 1) ∧
          (0 = 0 ∨ _)
        refine ⟨⟨?_, by omega⟩, Or.inl rfl⟩
        have := k.1.isLt
        have := k.2.isLt
        omega⟩
    | Sum.inr k => ⟨exponent (d 0) 0 0 (d 1 - (k.val + 1)) (k.val + 1), by
        change (d 0 + 0 + 0 = d 0 ∧ d 1 - (k.val + 1) + (k.val + 1) = d 1) ∧
          (_ ∨ 0 = 0 ∧ 0 = 0)
        refine ⟨⟨by omega, ?_⟩, Or.inr ⟨rfl, rfl⟩⟩
        have := k.isLt
        omega⟩
  left_inv m := by
    dsimp only
    split_ifs with h
    · apply Subtype.ext
      apply exponent_ext <;> simp only [exponent_x0, exponent_x1, exponent_x2, exponent_y0, exponent_y1]
      all_goals have := m.property.1.1; have := m.property.1.2; omega
    · have hm := m.property.2.resolve_left h
      apply Subtype.ext
      apply exponent_ext <;> simp only [exponent_x0, exponent_x1, exponent_x2, exponent_y0, exponent_y1]
      all_goals have := m.property.1.1; have := m.property.1.2; omega
  right_inv s := by
    rcases s with k | k
    · simp only [exponent_y1, dite_true, exponent_x1, exponent_x2]
      congr 1
      apply Sigma.ext
      · apply Fin.ext
        dsimp
        have := k.2.isLt
        omega
      · apply (Fin.heq_ext_iff (by dsimp; have := k.2.isLt; omega)).mpr
        rfl
    · simp only [exponent_y1, Nat.add_sub_cancel, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, dite_false]

theorem ideal_hilbertFunction (d : Fin 2 → ℕ) :
    Hilbert.hilbertFunction ℂ ambient.factorCount ambient.ambientDimension ideal d =
      (d 0 + 2).choose 2 + d 1 := by
  classical
  rw [Hilbert.hilbertFunction, Hilbert.quotientPiece, Hilbert.degreePiece,
    MonomialQuotientCount.finrank_piece _ ideal
      {m | m (y 1) ≠ 0 ∧ (m (x 1) ≠ 0 ∨ m (x 2) ≠ 0)} mem_ideal_iff]
  calc
    _ = Nat.card (Standard d) := Nat.card_congr (Equiv.subtypeEquivRight (by
      intro m
      simp only [weight_eq_iff, Set.mem_setOf_eq]
      tauto))
    _ = Nat.card (Triangle (d 0) ⊕ Fin (d 1)) := Nat.card_congr (standardEquiv d)
    _ = _ := by rw [Nat.card_sum, triangle_card, Nat.card_fin]

theorem section_mem_iff (f : ambient.CoordinateRing) :
    f ∈ ideal ⊔ Ideal.span {polynomial} ↔
      ∀ m ∈ f.support, (m (y 1) ≠ 0 ∧ (m (x 1) ≠ 0 ∨ m (x 2) ≠ 0)) ∨ m (y 0) ≠ 0 := by
  have h := @mem_ideal_span_monomial_image V ℂ _ f
    {Finsupp.single (y 1) 1 + Finsupp.single (x 1) 1,
      Finsupp.single (y 1) 1 + Finsupp.single (x 2) 1, Finsupp.single (y 0) 1}
  have h1 : y 1 ≠ x 1 := by decide
  have h2 : y 1 ≠ x 2 := by decide
  have hm (a b : V) : monomial (Finsupp.single a 1 + Finsupp.single b 1) (1 : ℂ) = X a * X b := by
    simp only [X, monomial_mul, one_mul]
  have hx (a : V) : monomial (Finsupp.single a 1) (1 : ℂ) = X a := rfl
  simpa only [Set.image_insert_eq, Set.image_singleton, hm, hx,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left,
    single_pair_le _ _ h1, single_pair_le _ _ h2, Finsupp.single_le_iff,
    Nat.one_le_iff_ne_zero, ideal, polynomial, firstCoordinate, secondCoordinate,
    Ideal.span_insert, sup_assoc, or_assoc, and_or_left] using h

theorem section_hilbertFunction (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    Hilbert.hilbertFunction ℂ ambient.factorCount ambient.ambientDimension
      (ideal ⊔ Ideal.span {polynomial}) d = 1 := by
  classical
  rw [Hilbert.hilbertFunction, Hilbert.quotientPiece, Hilbert.degreePiece,
    MonomialQuotientCount.finrank_piece _ _
      {m | (m (y 1) ≠ 0 ∧ (m (x 1) ≠ 0 ∨ m (x 2) ≠ 0)) ∨ m (y 0) ≠ 0} section_mem_iff]
  let E := {m : V →₀ ℕ //
    Finsupp.weight (Hilbert.blockWeight ambient.factorCount ambient.ambientDimension) m = d ∧
      ¬ ((m (y 1) ≠ 0 ∧ (m (x 1) ≠ 0 ∨ m (x 2) ≠ 0)) ∨ m (y 0) ≠ 0)}
  have he (m : E) : m.val = exponent (d 0) 0 0 0 (d 1) := by
    have hw := (weight_eq_iff m.val d).mp m.property.1
    have ha := m.property.2
    push_neg at ha
    apply exponent_ext <;> simp only [exponent_x0, exponent_x1, exponent_x2, exponent_y0, exponent_y1]
    all_goals omega
  let e : E := ⟨exponent (d 0) 0 0 0 (d 1), by simp [weight_eq_iff]⟩
  let eqv : E ≃ Unit := Equiv.ofBijective (fun _ => ()) ⟨by
      intro m n _
      exact Subtype.ext ((he m).trans (he n).symm), by
      intro u
      exact ⟨e, Subsingleton.elim _ _⟩⟩
  exact (Nat.card_congr eqv).trans (by simp)

theorem ideal_hilbertPolynomial :
    Hilbert.hilbertPolynomial ℂ ambient.factorCount ambient.ambientDimension ideal =
      expectedHilbertPolynomial := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, fun d _ => ?_⟩
  change Fin 2 → ℕ at d
  rw [ideal_hilbertFunction]
  have hc : (((d 0 + 2).choose 2 : ℕ) : ℚ) = ((d 0 : ℚ) + 2) * ((d 0 : ℚ) + 1) / 2 := by
    have he : 2 * (d 0 + 2).choose 2 = (d 0 + 2) * (d 0 + 1) := by
      have h := Nat.add_one_mul_choose_eq (d 0 + 1) 1
      simpa [Nat.choose_one_right, mul_comm] using h.symm
    have he' := congrArg (fun n : ℕ => (n : ℚ)) he
    push_cast at he'
    linarith
  change MvPolynomial.eval (fun i : Fin 2 => (d i : ℚ)) expectedHilbertPolynomial = _
  simp only [expectedHilbertPolynomial, map_add, map_mul, map_pow, map_one,
    eval_C, eval_X, Nat.cast_add, hc]
  ring

theorem section_hilbertPolynomial :
    Hilbert.hilbertPolynomial ℂ ambient.factorCount ambient.ambientDimension
      (ideal ⊔ Ideal.span {polynomial}) = 1 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => 1, fun d hd => ?_⟩
  change Fin 2 → ℕ at d
  have hd1 : 1 ≤ d 1 := hd (1 : Fin 2)
  rw [section_hilbertFunction d (by omega)]
  simp

theorem ideal_nontrivial : IsNontrivialIdeal ambient ideal := by
  classical
  let v : V → ℂ := fun j => if j = x 0 ∨ j = y 0 then 1 else 0
  have hi : ideal ≤ RingHom.ker (MvPolynomial.eval v) := by
    rw [ideal, Ideal.span_le]
    intro f hf
    rcases hf with rfl | rfl <;>
      simp [RingHom.mem_ker, firstCoordinate, secondCoordinate, v, x, y]
  have hq : firstCoordinate 0 * secondCoordinate 0 ∈
      Hilbert.irrelevantIdeal ℂ ambient.factorCount ambient.ambientDimension := by
    rw [Hilbert.irrelevantIdeal, Ideal.mem_iInf]
    intro i
    change Fin 2 at i
    fin_cases i
    · apply Ideal.mul_mem_right
      apply Ideal.subset_span
      exact ⟨0, rfl⟩
    · apply Ideal.mul_mem_left
      apply Ideal.subset_span
      exact ⟨0, rfl⟩
  intro h
  obtain ⟨n, hn⟩ := h hq
  have hz := hi hn
  change MvPolynomial.eval v ((firstCoordinate 0 * secondCoordinate 0) ^ n) = 0 at hz
  simpa [firstCoordinate, secondCoordinate, v, x, y] using hz

theorem expected_dimension : expectedHilbertPolynomial.totalDegree = 2 := by
  have ha : (C (1 / 2 : ℚ) * (X (0 : Fin 2)) ^ 2).totalDegree = 2 :=
    (isHomogeneous_C_mul_X_pow _ _ _).totalDegree (by
      apply mul_ne_zero
      · simpa using (show (1 / 2 : ℚ) ≠ 0 by norm_num)
      · exact pow_ne_zero _ (X_ne_zero _))
  have hb : (C (3 / 2 : ℚ) * (X (0 : Fin 2))).totalDegree = 1 :=
    (isHomogeneous_C_mul_X _ _).totalDegree (by
      apply mul_ne_zero
      · simpa using (show (3 / 2 : ℚ) ≠ 0 by norm_num)
      · exact X_ne_zero _)
  have hab : (C (1 / 2 : ℚ) * X (0 : Fin 2) ^ 2 + C (3 / 2 : ℚ) * X 0).totalDegree = 2 :=
    (totalDegree_add_eq_left_of_totalDegree_lt (by rw [hb, ha]; omega)).trans ha
  have habc : (C (1 / 2 : ℚ) * X (0 : Fin 2) ^ 2 + C (3 / 2 : ℚ) * X 0 + 1).totalDegree = 2 :=
    (totalDegree_add_eq_left_of_totalDegree_lt (by rw [totalDegree_one, hab]; omega)).trans hab
  exact (totalDegree_add_eq_left_of_totalDegree_lt
    (by rw [totalDegree_X, habc]; omega)).trans habc

theorem expected_top : homogeneousComponent 2 expectedHilbertPolynomial =
    C (1 / 2 : ℚ) * X (0 : Fin 2) ^ 2 := by
  simp only [expectedHilbertPolynomial, map_add,
    homogeneousComponent_of_mem (isHomogeneous_C_mul_X_pow (1 / 2 : ℚ) (0 : Fin 2) 2),
    homogeneousComponent_of_mem (isHomogeneous_C_mul_X (3 / 2 : ℚ) (0 : Fin 2)),
    homogeneousComponent_of_mem (isHomogeneous_one (σ := Fin 2) ℚ),
    homogeneousComponent_of_mem (isHomogeneous_X ℚ (1 : Fin 2))]
  norm_num

theorem ideal_dimension : idealDimension ambient ideal = 2 := by
  rw [idealDimension, ideal_hilbertPolynomial, expected_dimension]

theorem ideal_degree (d : ambient.FactorIndex → ℕ) :
    idealDegreeValue ambient ideal d = (d (0 : Fin 2) : ℚ) ^ 2 := by
  unfold idealDegreeValue Hilbert.degreeValue Hilbert.degreeForm
  rw [ideal_hilbertPolynomial]
  change eval (fun i : Fin 2 => (d i : ℚ))
    ((expectedHilbertPolynomial.totalDegree.factorial : ℚ) •
      homogeneousComponent expectedHilbertPolynomial.totalDegree expectedHilbertPolynomial) = _
  rw [expected_dimension, expected_top]
  change eval (fun i : Fin 2 => (d i : ℚ))
    ((Nat.factorial 2 : ℚ) • (C (1 / 2 : ℚ) * X (0 : Fin 2) ^ 2)) = _
  simp

theorem section_degree (d : ambient.FactorIndex → ℕ) :
    idealDegreeValue ambient (ideal ⊔ Ideal.span {polynomial}) d = 1 := by
  unfold idealDegreeValue Hilbert.degreeValue Hilbert.degreeForm
  rw [section_hilbertPolynomial]
  simp

theorem coefficient_sum_zero :
    hypersurfaceCoefficientSum ambient ideal equationDegrees (fun _ => 1) = 0 := by
  classical
  unfold hypersurfaceCoefficientSum
  dsimp only
  rw [ideal_dimension]
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with ha
  · by_cases ha1 : (a (1 : Fin 2)).val = 0
    · have hs : (∑ i : ambient.FactorIndex,
          ((a i).val : ℚ) * (equationDegrees i : ℚ) / ((fun _ => 1) i : ℕ)) = 0 := by
        change (∑ i : Fin 2, ((a i).val : ℚ) * (equationDegrees i : ℚ) / 1) = 0
        simp [Fin.sum_univ_two, equationDegrees, ha1]
      rw [hs]
      simp
    · let e : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
      have he : e.degree = 2 := by
        change (∑ i : Fin 2, (a i).val) = 2 at ha
        simpa [e, Finsupp.degree_eq_sum] using ha
      have hne : Finsupp.single (0 : Fin 2) 2 ≠ e := by
        intro heq
        have hv := congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq
        exact ha1 (by simpa [e] using hv.symm)
      have hc : expectedHilbertPolynomial.coeff e = 0 := by
        have hh := coeff_homogeneousComponent 2 expectedHilbertPolynomial e
        rw [he, if_pos rfl, expected_top, C_mul_X_pow_eq_monomial, coeff_monomial,
          if_neg hne] at hh
        exact hh.symm
      have hm : idealMixedDegree ambient ideal (fun i => (a i).val) = 0 := by
        rw [idealMixedDegree, ideal_dimension, if_pos ha, ideal_hilbertPolynomial]
        change expectedHilbertPolynomial.coeff e * _ = 0
        rw [hc, zero_mul]
      rw [hm]
      simp
  · rfl

end PhilipponMultiplicity.SectionThree.ZeroDegreeBoundary
end

open PhilipponMultiplicity
open SectionThree

theorem solution :
    let M := ZeroDegreeBoundary.ambient
    let I := ZeroDegreeBoundary.ideal
    let P := ZeroDegreeBoundary.polynomial
    let D := ZeroDegreeBoundary.equationDegrees
    let J := I ⊔ Ideal.span {P}
    I = Ideal.span {ZeroDegreeBoundary.secondCoordinate 1} ⊓
      Ideal.span {ZeroDegreeBoundary.firstCoordinate 1, ZeroDegreeBoundary.firstCoordinate 2} ∧
    IsMultihomogeneousIdeal M I ∧ IsNontrivialIdeal M I ∧
    M.IsHomogeneous P D ∧ IsRegular (Ideal.Quotient.mk I P) ∧
    idealDimension M I = 2 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I =
      ZeroDegreeBoundary.expectedHilbertPolynomial ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension J = 1 ∧
    (∀ d : M.FactorIndex → ℕ, idealDegreeValue M I d = (d (0 : Fin 2) : ℚ) ^ 2) ∧
    (∀ d : M.FactorIndex → ℕ, idealDegreeValue M J d = 1) ∧
    hypersurfaceCoefficientSum M I D (fun _ => 1) = 0 ∧
    idealDegreeValue M J (fun _ => 1) ≠ hypersurfaceCoefficientSum M I D (fun _ => 1) ∧
    idealDegreeValue M J D ≠ idealDegreeValue M I D  := by
  dsimp only
  refine ⟨ZeroDegreeBoundary.ideal_intersection, ZeroDegreeBoundary.ideal_homogeneous,
    ZeroDegreeBoundary.ideal_nontrivial, ZeroDegreeBoundary.polynomial_homogeneous,
    ZeroDegreeBoundary.ideal_regular, ZeroDegreeBoundary.ideal_dimension,
    ZeroDegreeBoundary.ideal_hilbertPolynomial, ZeroDegreeBoundary.section_hilbertPolynomial,
    ZeroDegreeBoundary.ideal_degree, ZeroDegreeBoundary.section_degree,
    ZeroDegreeBoundary.coefficient_sum_zero, ?_, ?_⟩
  · rw [ZeroDegreeBoundary.section_degree, ZeroDegreeBoundary.coefficient_sum_zero]
    norm_num
  · rw [ZeroDegreeBoundary.section_degree, ZeroDegreeBoundary.ideal_degree]
    norm_num [ZeroDegreeBoundary.equationDegrees]

