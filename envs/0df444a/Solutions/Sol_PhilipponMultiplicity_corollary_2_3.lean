-- Prove2me | solution 1 for PhilipponMultiplicity.corollary_2_3
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T09:32:13.555973+00:00
-- url     : https://prove2.me/submissions/a6292df8-70df-4868-af42-dc97fe5d256c

import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Theorems.Thm_PhilipponMultiplicity_lemma_3_4
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.Submodule
import Theorems.Thm_PhilipponMultiplicity_theorem_2_1
import Definitions.Def_PhilipponMultiplicity_Corollaries
import Theorems.Thm_PhilipponMultiplicity_corollary_2_3_zero_degree_boundary


set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ProductDegree

theorem top_mul {σ : Type*} (P Q : MvPolynomial σ ℚ) (a b : ℕ)
    (hP : P.totalDegree ≤ a) (hQ : Q.totalDegree ≤ b) :
    homogeneousComponent (a + b) (P * Q) =
      homogeneousComponent a P * homogeneousComponent b Q := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases hd : d.degree = a + b
  · rw [if_pos hd]
    apply Finset.sum_congr rfl
    rintro ⟨e, f⟩ hef
    have hef' : e + f = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases he : coeff e P = 0
    · simp [he]
    by_cases hf : coeff f Q = 0
    · simp [hf]
    have he' : e.degree ≤ a := (le_totalDegree (mem_support_iff.mpr he)).trans hP
    have hf' : f.degree ≤ b := (le_totalDegree (mem_support_iff.mpr hf)).trans hQ
    have hsum : e.degree + f.degree = a + b := by
      rw [← map_add, hef', hd]
    have hea : e.degree = a := by omega
    have hfb : f.degree = b := by omega
    simp [hea, hfb]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨e, f⟩ hef
    have hef' : e + f = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases he : e.degree = a
    · by_cases hf : f.degree = b
      · exfalso
        apply hd
        rw [← hef', map_add, he, hf]
      · simp [hf]
    · simp [he]

theorem top_prod {σ ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℚ)
    (hP : ∀ i ∈ s, P i ≠ 0) :
    (∏ i ∈ s, P i).totalDegree = ∑ i ∈ s, (P i).totalDegree ∧
    homogeneousComponent (∏ i ∈ s, P i).totalDegree (∏ i ∈ s, P i) =
      ∏ i ∈ s, homogeneousComponent (P i).totalDegree (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hpi := hP i (Finset.mem_insert_self i s)
    have hps : ∀ j ∈ s, P j ≠ 0 := fun j hj => hP j (Finset.mem_insert_of_mem hj)
    obtain ⟨hdeg, htop⟩ := ih hps
    have hprod : ∏ j ∈ s, P j ≠ 0 := Finset.prod_ne_zero_iff.mpr hps
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [totalDegree_mul_of_isDomain hpi hprod]
    constructor
    · rw [hdeg]
    · rw [top_mul _ _ _ _ le_rfl le_rfl, htop]

theorem degree_fin_one (d : Fin 1 →₀ ℕ) : d.degree = d 0 := by
  simp [Finsupp.degree_eq_sum]

theorem top_fin_one (P : MvPolynomial (Fin 1) ℚ) :
    homogeneousComponent P.totalDegree P =
      monomial (Finsupp.single 0 P.totalDegree) (coeff (Finsupp.single 0 P.totalDegree) P) := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_monomial]
  have hd : d.degree = P.totalDegree ↔ Finsupp.single 0 P.totalDegree = d := by
    rw [degree_fin_one]
    constructor
    · intro h
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa using h.symm
    · intro h
      rw [← h, Finsupp.single_eq_same]
  by_cases h : d.degree = P.totalDegree
  · rw [if_pos h, if_pos (hd.mp h), ← hd.mp h]
  · rw [if_neg h, if_neg (mt hd.mpr h)]

theorem degree_rename_single {ι : Type*} (i : ι) (P : MvPolynomial (Fin 1) ℚ) :
    (rename (fun _ => i) P).totalDegree = P.totalDegree := by
  have h := (weightedTotalDegree_rename_of_injective
      (w := (1 : ι → ℕ)) (P := P)
      (show Function.Injective (fun _ : Fin 1 => i) from fun _ _ _ => Subsingleton.elim _ _))
  change weightedTotalDegree 1 _ = weightedTotalDegree 1 _ at h
  simpa only [weightedTotalDegree_one] using h

theorem eval_top_fin_one (P : MvPolynomial (Fin 1) ℚ) (d : Fin 1 → ℚ) :
    eval d (homogeneousComponent P.totalDegree P) =
      coeff (Finsupp.single 0 P.totalDegree) P * d 0 ^ P.totalDegree := by
  conv_lhs => rw [top_fin_one P]
  rw [eval_monomial, Finsupp.prod_single_index]
  simp

/-- Philippon's factorial normalization for a product of polynomials in separate
variables. Zero factors are included, so no nonemptiness premise is needed. -/
theorem normalized_product {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial (Fin 1) ℚ) (d : ι → ℚ) :
    let Q := ∏ i, rename (fun _ : Fin 1 => i) (P i)
    eval d ((Q.totalDegree.factorial : ℚ) • homogeneousComponent Q.totalDegree Q) =
      (Q.totalDegree.factorial : ℚ) / (∏ i, ((P i).totalDegree.factorial : ℚ)) *
        (∏ i, eval (fun _ => 1)
          (((P i).totalDegree.factorial : ℚ) •
            homogeneousComponent (P i).totalDegree (P i))) *
        ∏ i, d i ^ (P i).totalDegree := by
  classical
  dsimp only
  by_cases hP : ∀ i, P i ≠ 0
  · have hrename (i : ι) : rename (fun _ : Fin 1 => i) (P i) ≠ 0 := by
      exact fun h => hP i ((rename_injective _ (fun _ _ _ => Subsingleton.elim _ _)) h)
    have htop := (top_prod Finset.univ
      (fun i => rename (fun _ : Fin 1 => i) (P i)) (fun i _ => hrename i)).2
    rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, htop, map_prod]
    simp_rw [degree_rename_single, ← rename_homogeneousComponent, eval_rename,
      eval_top_fin_one, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_top_fin_one]
    simp only [Function.comp_apply, one_pow, mul_one, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hfact : (∏ i, ((P i).totalDegree.factorial : ℚ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact_mod_cast Nat.factorial_ne_zero (P i).totalDegree
    field_simp
  · push Not at hP
    obtain ⟨i, hi⟩ := hP
    have hprod : (∏ j, rename (fun _ : Fin 1 => j) (P j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hi, map_zero]
    have hprod' : (∏ j, eval (fun _ => (1 : ℚ))
        (((P j).totalDegree.factorial : ℚ) •
          homogeneousComponent (P j).totalDegree (P j))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [hprod, hprod']
    simp

end PhilipponMultiplicity.ProductDegree


namespace PhilipponMultiplicity
open SectionThree

/-- The product Hilbert polynomial identity supplies exactly the geometric input
to Lemma 3.4. The remaining factorial and leading-term calculation is proved here. -/
theorem lemma_3_4_of_product_hilbertPolynomial
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (hprod : Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) =
      ∏ i, MvPolynomial.rename (fun _ : Fin 1 => i)
        (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor)))
    (d : M.FactorIndex → ℕ) :
    locusDegreeValue M (productCarrier M V) d =
      ((locusDimension M (productCarrier M V)).factorial : ℚ) /
        (∏ i, ((V i).dimension.factorial : ℚ)) *
        (∏ i, (V i).degree) * ∏ i, (d i : ℚ) ^ (V i).dimension := by
  unfold locusDegreeValue locusDimension idealDegreeValue idealDimension
    ProjectiveSubvariety.dimension ProjectiveSubvariety.degree
    idealDegreeValue idealDimension Hilbert.degreeValue Hilbert.degreeForm
  rw [hprod]
  exact ProductDegree.normalized_product _ _

end PhilipponMultiplicity

end


set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.BinomialPolynomial

def oneVariable (q a : ℕ) : MvPolynomial (Fin 1) ℚ :=
  (uniqueAlgEquiv ℚ (Fin 1)).symm (Polynomial.preHilbertPoly ℚ q a)

theorem oneVariable_coeff (q a : ℕ) (b : Fin 1 →₀ ℕ) :
    coeff b (oneVariable q a) = (Polynomial.preHilbertPoly ℚ q a).coeff (b 0) :=
  coeff_uniqueAlgEquiv_symm ℚ _ _

theorem oneVariable_degree (q a : ℕ) : (oneVariable q a).totalDegree = q := by
  classical
  apply le_antisymm
  · change (oneVariable q a).support.sup (fun b : Fin 1 →₀ ℕ => b.sum (fun _ e => e)) ≤ q
    apply Finset.sup_le
    intro b hb
    have h := mem_support_iff.mp hb
    rw [oneVariable_coeff] at h
    have ht := Polynomial.le_natDegree_of_ne_zero h
    rw [Polynomial.natDegree_preHilbertPoly] at ht
    simpa [Finsupp.sum_fintype] using ht
  · have hcoeff : coeff (Finsupp.single 0 q) (oneVariable q a) ≠ 0 := by
      rw [oneVariable_coeff, Finsupp.single_eq_same, Polynomial.coeff_preHilbertPoly_self]
      exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero q)
    simpa using le_totalDegree (mem_support_iff.mpr hcoeff)

theorem oneVariable_top (q a : ℕ) :
    homogeneousComponent q (oneVariable q a) =
      monomial (Finsupp.single 0 q) (q.factorial : ℚ)⁻¹ := by
  have h := ProductDegree.top_fin_one (oneVariable q a)
  simpa only [oneVariable_degree, oneVariable_coeff, Finsupp.single_eq_same,
    Polynomial.coeff_preHilbertPoly_self] using h

def block {ι : Type*} (i : ι) (q a : ℕ) : MvPolynomial ι ℚ :=
  rename (fun _ : Fin 1 => i) (oneVariable q a)

theorem block_degree {ι : Type*} (i : ι) (q a : ℕ) : (block i q a).totalDegree = q := by
  rw [block, ProductDegree.degree_rename_single, oneVariable_degree]

theorem block_top {ι : Type*} (i : ι) (q a : ℕ) :
    homogeneousComponent q (block i q a) =
      monomial (Finsupp.single i q) (q.factorial : ℚ)⁻¹ := by
  rw [block, ← rename_homogeneousComponent, oneVariable_top, rename_monomial]
  simp

theorem block_ne_zero {ι : Type*} (i : ι) (q a : ℕ) : block i q a ≠ 0 := by
  intro h
  have hh := block_top i q a
  rw [h, map_zero] at hh
  have hn : (monomial (Finsupp.single i q) (q.factorial : ℚ)⁻¹ : MvPolynomial ι ℚ) ≠ 0 := by
    simp [Nat.factorial_ne_zero]
  exact hn hh.symm

theorem block_eval {ι : Type*} (i : ι) (q a : ℕ) (d : ι → ℕ) (ha : a ≤ d i) :
    eval (fun i => (d i : ℚ)) (block i q a) = ((d i - a + q).choose q : ℚ) := by
  rw [block, eval_rename]
  change MvPolynomial.eval₂ (RingHom.id ℚ) _
    ((uniqueAlgEquiv ℚ (Fin 1)).symm _) = _
  rw [eval₂_uniqueAlgEquiv_symm]
  exact Polynomial.preHilbertPoly_eq_choose_sub_add ℚ q ha

def product {ι : Type*} [Fintype ι] (q a : ι → ℕ) : MvPolynomial ι ℚ :=
  ∏ i, block i (q i) (a i)

def exponent {ι : Type*} [Fintype ι] (q : ι → ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm q

theorem prod_monomial {ι σ : Type*} (s : Finset ι) (e : ι → σ →₀ ℕ) (c : ι → ℚ) :
    (∏ i ∈ s, monomial (e i) (c i) : MvPolynomial σ ℚ) =
      monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, monomial_mul]

theorem product_degree {ι : Type*} [Fintype ι] (q a : ι → ℕ) :
    (product q a).totalDegree = ∑ i, q i := by
  have h := (ProductDegree.top_prod Finset.univ
    (fun i => block i (q i) (a i)) (fun i _ => block_ne_zero i _ _)).1
  simpa only [product, block_degree] using h

theorem product_top {ι : Type*} [Fintype ι] (q a : ι → ℕ) :
    homogeneousComponent (∑ i, q i) (product q a) =
      monomial (exponent q) (∏ i, (q i |>.factorial : ℚ)⁻¹) := by
  classical
  rw [← product_degree q a]
  have h := (ProductDegree.top_prod Finset.univ
    (fun i => block i (q i) (a i)) (fun i _ => block_ne_zero i _ _)).2
  simp only [block_degree, block_top] at h
  change homogeneousComponent (product q a).totalDegree (product q a) = _ at h
  rw [h, prod_monomial]
  have he : (∑ i, Finsupp.single i (q i)) = exponent q := by
    ext i
    simp [exponent, Finsupp.single_apply]
  rw [he]

theorem product_eval {ι : Type*} [Fintype ι] (q a d : ι → ℕ) (ha : ∀ i, a i ≤ d i) :
    eval (fun i => (d i : ℚ)) (product q a) =
      (∏ i, (d i - a i + q i).choose (q i) : ℕ) := by
  classical
  simp only [product, map_prod, Nat.cast_prod]
  exact Finset.prod_congr rfl (fun i _ => block_eval i _ _ _ (ha i))

/-- Positive leading monomials cannot cancel in a finite sum. -/
theorem sum_top_coefficients {ι J : Type*} [Fintype ι] [Fintype J]
    (q a : J → ι → ℕ) (N : ι → ℕ) (hq : ∀ j i, q j i ≤ N i) :
    let F := ∑ j, product (q j) (a j)
    (∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) ∧
    (∀ b : ι →₀ ℕ, (∃ i, N i < b i) →
      coeff b (homogeneousComponent F.totalDegree F) = 0) := by
  classical
  let F := ∑ j, product (q j) (a j)
  change (∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) ∧ _
  cases isEmpty_or_nonempty J with
  | inl h => simp [F]
  | inr h =>
    let n := Finset.univ.sup (fun j : J => ∑ i, q j i)
    have hqn (j : J) : (∑ i, q j i) ≤ n :=
      Finset.le_sup (f := fun j : J => ∑ i, q j i) (Finset.mem_univ j)
    have hpn (j : J) : (product (q j) (a j)).totalDegree ≤ n := by
      rw [product_degree]
      exact hqn j
    have hc (j : J) : 0 < ∏ i, ((q j i).factorial : ℚ)⁻¹ := by
      apply Finset.prod_pos
      intro i _
      exact inv_pos.mpr (by exact_mod_cast Nat.factorial_pos (q j i))
    have hpart (j : J) : homogeneousComponent n (product (q j) (a j)) =
        if (∑ i, q j i) = n then
          monomial (exponent (q j)) (∏ i, ((q j i).factorial : ℚ)⁻¹) else 0 := by
      split_ifs with he
      · rw [← he, product_top]
      · apply homogeneousComponent_eq_zero
        rw [product_degree]
        exact lt_of_le_of_ne (hqn j) he
    have hnn (j : J) (b : ι →₀ ℕ) :
        0 ≤ coeff b (homogeneousComponent n (product (q j) (a j))) := by
      rw [hpart]
      split_ifs
      · rw [coeff_monomial]
        split_ifs
        · exact (hc j).le
        · rfl
      · simp
    have hcoeff (b : ι →₀ ℕ) : coeff b (homogeneousComponent n F) =
        ∑ j, coeff b (homogeneousComponent n (product (q j) (a j))) := by
      simp only [F, map_sum, coeff_sum]
    have hFle : F.totalDegree ≤ n := totalDegree_finsetSum_le (fun j _ => hpn j)
    obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun j : J => ∑ i, q j i)
    have hjn' : (∑ i, q j i) = n := hjn.symm
    have hp : 0 < coeff (exponent (q j)) (homogeneousComponent n F) := by
      rw [hcoeff]
      have hpos : 0 < coeff (exponent (q j))
          (homogeneousComponent n (product (q j) (a j))) := by
        rw [hpart, if_pos hjn', coeff_monomial, if_pos rfl]
        exact hc j
      exact hpos.trans_le (Finset.single_le_sum (fun k _ => hnn k _) hj)
    have hFge : n ≤ F.totalDegree := by
      by_contra! hlt
      rw [homogeneousComponent_eq_zero n F hlt, coeff_zero] at hp
      exact (lt_irrefl 0) hp
    have hFn : F.totalDegree = n := le_antisymm hFle hFge
    change (∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) ∧
      (∀ b : ι →₀ ℕ, (∃ i, N i < b i) →
        coeff b (homogeneousComponent F.totalDegree F) = 0)
    rw [hFn]
    constructor
    · intro b
      rw [hcoeff]
      exact Finset.sum_nonneg (fun j _ => hnn j b)
    · intro b hb
      obtain ⟨i, hi⟩ := hb
      rw [hcoeff]
      apply Finset.sum_eq_zero
      intro j _
      rw [hpart]
      split_ifs
      · rw [coeff_monomial, if_neg]
        intro he
        have hiq : q j i = b i := congrArg (fun e : ι →₀ ℕ => e i) he
        have hqi := hq j i
        omega
      · simp

end PhilipponMultiplicity.BinomialPolynomial

end


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.StandardMonomials

variable {K σ Γ : Type*} [Field K] [AddCommMonoid Γ]

def initialExponents (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :
    Set (σ →₀ ℕ) :=
  {e | ∃ f ∈ I, f ≠ 0 ∧ m.degree f = e}

theorem initialExponents_upper (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :
    IsUpperSet (initialExponents m I) := by
  classical
  intro a b hab ha
  obtain ⟨f, hf, hf0, rfl⟩ := ha
  refine ⟨monomial (b - m.degree f) (1 : K) * f, I.mul_mem_left _ hf,
    mul_ne_zero (by simp) hf0, ?_⟩
  rw [m.degree_mul (by simp) hf0, m.degree_monomial]
  simpa using tsub_add_cancel_of_le hab

theorem normal_representative (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) :
    ∃ r : MvPolynomial σ K, f - r ∈ I ∧
      ∀ e ∈ r.support, e ∉ initialExponents m I := by
  classical
  let B := {g : MvPolynomial σ K // g ∈ I ∧ g ≠ 0}
  obtain ⟨g, r, heq, _, hr⟩ := m.div
    (b := fun b : B => b.val)
    (fun b => isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr b.property.2)) f
  refine ⟨r, ?_, ?_⟩
  · rw [heq, add_sub_cancel_right]
    change g.sum (fun b c => c * b.val) ∈ I
    exact I.sum_mem (fun b _ => I.mul_mem_left _ b.property.1)
  · intro e he ⟨b, hb, hb0, hbe⟩
    exact hr e he ⟨b, hb, hb0⟩ (le_of_eq hbe)

theorem weighted_normal_representative (m : MonomialOrder σ)
    (w : σ → Γ) (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ d, weightedHomogeneousComponent w d f ∈ I)
    (d : Γ) (f : MvPolynomial σ K) (hf : f.IsWeightedHomogeneous w d) :
    ∃ r : MvPolynomial σ K, f - r ∈ I ∧ r.IsWeightedHomogeneous w d ∧
      ∀ e ∈ r.support, e ∉ initialExponents m I := by
  classical
  obtain ⟨r, hfr, hr⟩ := normal_representative m I f
  refine ⟨weightedHomogeneousComponent w d r, ?_,
    weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  · have h := hI (f - r) hfr d
    simpa only [map_sub, weightedHomogeneousComponent_of_mem hf, if_true] using h
  · intro e he
    rw [support_weightedHomogeneousComponent] at he
    exact hr e (Finset.mem_filter.mp he).1

theorem normal_piece_equiv (m : MonomialOrder σ) (w : σ → Γ)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ d, weightedHomogeneousComponent w d f ∈ I) (d : Γ) :
    Nonempty ((restrictSupport K {e | Finsupp.weight w e = d ∧
        e ∉ initialExponents m I}) ≃ₗ[K]
      ((weightedHomogeneousSubmodule K w d).map
        (Ideal.Quotient.mkₐ K I).toLinearMap)) := by
  classical
  let S : Set (σ →₀ ℕ) := {e | Finsupp.weight w e = d ∧ e ∉ initialExponents m I}
  let V := restrictSupport K S
  let W := (weightedHomogeneousSubmodule K w d).map (Ideal.Quotient.mkₐ K I).toLinearMap
  have memV (f : MvPolynomial σ K) : f ∈ V ↔ ∀ e ∈ f.support, e ∈ S := Iff.rfl
  have homog {f : MvPolynomial σ K} (hf : f ∈ V) : f.IsWeightedHomogeneous w d := by
    intro e he
    exact ((memV f).mp hf e (mem_support_iff.mpr he)).1
  let q : V →ₗ[K] W :=
    { toFun := fun f => ⟨Ideal.Quotient.mk I f.val, ⟨f.val, homog f.property, rfl⟩⟩
      map_add' := by intro f g; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c f; apply Subtype.ext; exact (Ideal.Quotient.mkₐ K I).toLinearMap.map_smul c f.val }
  have hqinj : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro f hf
    have hIf : f.val ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact congrArg Subtype.val hf
    have hf0 : f.val = 0 := by
      by_contra hn
      exact ((memV f.val).mp f.property (m.degree f.val)
        ((m.degree_mem_support_iff f.val).mpr hn)).2 ⟨f.val, hIf, hn, rfl⟩
    exact Subtype.ext hf0
  have hqsurj : Function.Surjective q := by
    rintro ⟨x, f, hf, rfl⟩
    obtain ⟨r, hfr, hr, hs⟩ := weighted_normal_representative m w I hI d f hf
    refine ⟨⟨r, (memV r).mpr (fun e he => ⟨hr (mem_support_iff.mp he), hs e he⟩)⟩, ?_⟩
    apply Subtype.ext
    exact (Ideal.Quotient.eq.mpr hfr).symm
  exact ⟨LinearEquiv.ofBijective q ⟨hqinj, hqsurj⟩⟩

theorem weighted_finrank_eq (m : MonomialOrder σ) (w : σ → Γ)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ d, weightedHomogeneousComponent w d f ∈ I) (d : Γ) :
    Module.finrank K ((weightedHomogeneousSubmodule K w d).map
      (Ideal.Quotient.mkₐ K I).toLinearMap) =
      Nat.card {e : σ →₀ ℕ // Finsupp.weight w e = d ∧ e ∉ initialExponents m I} := by
  obtain ⟨e⟩ := normal_piece_equiv m w I hI d
  rw [← e.finrank_eq]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

/-- Dickson's lemma supplies finitely many forbidden monomial divisors. -/
theorem upperSet_finite_generators [Finite σ] (U : Set (σ →₀ ℕ)) (hU : IsUpperSet U) :
    ∃ s : Finset (σ →₀ ℕ), ∀ e, e ∈ U ↔ ∃ a ∈ s, a ≤ e := by
  classical
  have hp : U.IsPWO := Set.isPWO_of_wellQuasiOrderedLE U
  have ha : IsAntichain (· ≤ ·) {a | Minimal (· ∈ U) a} := by
    intro a ha b hb hab hle
    exact hab (le_antisymm hle (hb.2 ha.1 hle))
  have hs := ha.finite_of_partiallyWellOrderedOn
    (Set.isPWO_of_wellQuasiOrderedLE {a | Minimal (· ∈ U) a})
  refine ⟨hs.toFinset, fun e => ⟨?_, ?_⟩⟩
  · intro he
    obtain ⟨a, hae, ha⟩ := hp.exists_le_minimal he
    exact ⟨a, hs.mem_toFinset.mpr ha, hae⟩
  · rintro ⟨a, ha, hae⟩
    exact hU hae (hs.mem_toFinset.mp ha).1

end PhilipponMultiplicity.StandardMonomials

namespace PhilipponMultiplicity

/-- Every actual multigraded quotient piece is counted by standard monomials
avoiding finitely many forbidden divisors. No radicality assumption is used. -/
theorem multigraded_hilbert_function_standard_monomials
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    ∃ s : Finset (M.Variable →₀ ℕ), ∀ d : M.FactorIndex → ℕ,
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension I d =
        Nat.card {e : M.Variable →₀ ℕ //
          Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) e = d ∧
          ∀ a ∈ s, ¬ a ≤ e} := by
  classical
  obtain ⟨instOrder, instWF⟩ := exists_wellFoundedGT M.Variable
  let m : MonomialOrder M.Variable := MonomialOrder.lex
  obtain ⟨s, hs⟩ := StandardMonomials.upperSet_finite_generators
    (StandardMonomials.initialExponents m I) (StandardMonomials.initialExponents_upper m I)
  refine ⟨s, fun d => ?_⟩
  rw [Hilbert.hilbertFunction, Hilbert.quotientPiece, Hilbert.degreePiece,
    StandardMonomials.weighted_finrank_eq m _ I hI d]
  simp only [hs, not_exists, not_and]

end PhilipponMultiplicity

end


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MonomialCells

variable {α : Type*} [Fintype α]

abbrev Free (B : ℕ) (b : α → Fin (B + 1)) := {x : α // (b x : ℕ) = B}

def Cell (B : ℕ) (b : α → Fin (B + 1)) :=
  {f : α → ℕ // ∀ x, min (f x) B = (b x : ℕ)}

def cellEquiv (B : ℕ) (b : α → Fin (B + 1)) : Cell B b ≃ (Free B b → ℕ) where
  toFun f x := f.val x.val - B
  invFun u := ⟨fun x => (b x : ℕ) + if h : (b x : ℕ) = B then u ⟨x,h⟩ else 0, by
    intro x
    have hbx := (b x).isLt
    dsimp only
    split_ifs with h
    · omega
    · omega⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    have hx := f.property x
    have hbx := (b x).isLt
    dsimp
    split_ifs with h
    · omega
    · omega
  right_inv u := by
    funext x
    simp [x.property]

theorem cellEquiv_symm_sum (B : ℕ) (b : α → Fin (B + 1)) (u : Free B b → ℕ) :
    ∑ x, ((cellEquiv B b).symm u).val x =
      (∑ x, (b x : ℕ)) + ∑ x, u x := by
  classical
  change (∑ x, ((b x : ℕ) + if h : (b x : ℕ) = B then u ⟨x,h⟩ else 0)) = _
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr_set {x | (b x : ℕ) = B} _ u
    (fun x hx => by simp only [Set.mem_setOf_eq] at hx; simp [hx])
    (fun x hx => by simp only [Set.mem_setOf_eq] at hx; simp [hx])

def degreeCellEquiv (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ)
    (hd : (∑ x, (b x : ℕ)) ≤ d) :
    {f : Cell B b // ∑ x, f.val x = d} ≃
      {u : Free B b → ℕ // ∑ x, u x = d - ∑ x, (b x : ℕ)} where
  toFun f := ⟨cellEquiv B b f.val, by
    have h := cellEquiv_symm_sum B b (cellEquiv B b f.val)
    rw [Equiv.symm_apply_apply, f.property] at h
    omega⟩
  invFun u := ⟨(cellEquiv B b).symm u.val, by
    rw [cellEquiv_symm_sum, u.property]
    omega⟩
  left_inv f := by apply Subtype.ext; exact (cellEquiv B b).symm_apply_apply f.val
  right_inv u := by apply Subtype.ext; exact (cellEquiv B b).apply_symm_apply u.val

instance degreeCell_finite (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ) :
    Finite {f : Cell B b // ∑ x, f.val x = d} := by
  classical
  haveI : Finite {f : α → ℕ // ∑ x, f x = d} :=
    Finite.of_equiv (Sym α d) (Sym.equivNatSumOfFintype α d)
  apply Finite.of_injective
    (fun f : {f : Cell B b // ∑ x, f.val x = d} =>
      (⟨f.val.val, f.property⟩ : {f : α → ℕ // ∑ x, f x = d}))
  intro f g h
  have hh : f.val.val = g.val.val :=
    congrArg (fun x : {f : α → ℕ // ∑ x, f x = d} => x.val) h
  exact Subtype.ext (Subtype.ext hh)

def flatCellEquiv (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ) :
    {f : α → ℕ // (∀ x, min (f x) B = (b x : ℕ)) ∧ ∑ x, f x = d} ≃
      {f : Cell B b // ∑ x, f.val x = d} where
  toFun f := ⟨⟨f.val, f.property.1⟩, f.property.2⟩
  invFun f := ⟨f.val.val, f.val.property, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance flatCell_finite (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ) :
    Finite {f : α → ℕ // (∀ x, min (f x) B = (b x : ℕ)) ∧ ∑ x, f x = d} :=
  Finite.of_equiv _ (flatCellEquiv B b d).symm

theorem degreeCell_card (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ)
    (hd : (∑ x, (b x : ℕ)) ≤ d) :
    Nat.card {f : Cell B b // ∑ x, f.val x = d} =
      (Nat.card (Free B b)).multichoose (d - ∑ x, (b x : ℕ)) := by
  classical
  rw [Nat.card_congr (degreeCellEquiv B b d hd)]
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Free B b) _)]
  exact Sym.natCard_sym_eq_multichoose _ _

theorem degreeCell_card_pos (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ)
    (hd : (∑ x, (b x : ℕ)) ≤ d) (hr : 0 < Nat.card (Free B b)) :
    Nat.card {f : Cell B b // ∑ x, f.val x = d} =
      (d - (∑ x, (b x : ℕ)) + (Nat.card (Free B b) - 1)).choose
        (Nat.card (Free B b) - 1) := by
  rw [degreeCell_card B b d hd, Nat.multichoose_eq]
  have hh : Nat.card (Free B b) + (d - ∑ x, (b x : ℕ)) - 1 =
      d - (∑ x, (b x : ℕ)) + (Nat.card (Free B b) - 1) := by omega
  rw [hh, ← Nat.choose_symm (show d - (∑ x, (b x : ℕ)) ≤
    d - (∑ x, (b x : ℕ)) + (Nat.card (Free B b) - 1) by omega)]
  simp

theorem degreeCell_card_zero (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ)
    (hd : (∑ x, (b x : ℕ)) < d) (hr : Nat.card (Free B b) = 0) :
    Nat.card {f : Cell B b // ∑ x, f.val x = d} = 0 := by
  rw [degreeCell_card B b d hd.le, hr]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show d - ∑ x, (b x : ℕ) ≠ 0 by omega)
  rw [hn]
  exact Nat.multichoose_zero_succ n

end PhilipponMultiplicity.MonomialCells

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MonomialCells

variable (p : ℕ) (N : Fin p → ℕ)

abbrev Var := Sigma fun i : Fin p => Fin (N i + 1)
abbrev Pattern (B : ℕ) := ∀ i : Fin p, Fin (N i + 1) → Fin (B + 1)

def Avoid (s : Finset (Var p N →₀ ℕ)) (f : Var p N → ℕ) : Prop :=
  ∀ a ∈ s, ¬ ∀ v, a v ≤ f v

theorem weight_apply (e : Var p N →₀ ℕ) (i : Fin p) :
    Finsupp.weight (Hilbert.blockWeight p N) e i = ∑ j, e ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : Fin p, ∑ j : Fin (N b + 1),
    e ⟨b,j⟩ • Hilbert.blockWeight p N ⟨b,j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem exists_bound (s : Finset (Var p N →₀ ℕ)) :
    ∃ B : ℕ, ∀ a ∈ s, ∀ v, a v ≤ B := by
  classical
  refine ⟨s.sup (fun a => Finset.univ.sup a), ?_⟩
  intro a ha v
  exact (Finset.le_sup (f := a) (Finset.mem_univ v)).trans
    (Finset.le_sup (f := fun a : Var p N →₀ ℕ => Finset.univ.sup a) ha)

theorem avoid_cap (s : Finset (Var p N →₀ ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, ∀ v, a v ≤ B) (f : Var p N → ℕ) :
    Avoid p N s (fun v => min (f v) B) ↔ Avoid p N s f := by
  constructor
  · intro h a ha hle
    exact h a ha (fun v => le_min (hle v) (hB a ha v))
  · intro h a ha hle
    exact h a ha (fun v => (hle v).trans (min_le_left _ _))

abbrev GoodPattern (s : Finset (Var p N →₀ ℕ)) (B : ℕ) :=
  {b : Pattern p N B // Avoid p N s (fun v => (b v.1 v.2 : ℕ))}

instance goodPatternFintype (s : Finset (Var p N →₀ ℕ)) (B : ℕ) :
    Fintype (GoodPattern p N s B) := by classical exact Subtype.fintype _

abbrev DegreeCellProduct (B : ℕ) (b : Pattern p N B) (d : Fin p → ℕ) :=
  ∀ i : Fin p, {f : Fin (N i + 1) → ℕ //
    (∀ j, min (f j) B = (b i j : ℕ)) ∧ ∑ j, f j = d i}

def partitionEquiv (s : Finset (Var p N →₀ ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, ∀ v, a v ≤ B) (d : Fin p → ℕ) :
    {e : Var p N →₀ ℕ // Finsupp.weight (Hilbert.blockWeight p N) e = d ∧
      ∀ a ∈ s, ¬ a ≤ e} ≃
    Σ b : GoodPattern p N s B, DegreeCellProduct p N B b.val d where
  toFun e :=
    ⟨⟨fun i j => ⟨min (e.val ⟨i,j⟩) B, Nat.lt_succ_of_le (min_le_right _ _)⟩,
      (avoid_cap p N s B hB e.val).mpr e.property.2⟩,
      fun i => ⟨fun j => e.val ⟨i,j⟩, (fun j => rfl), by
        rw [← weight_apply p N e.val i, e.property.1]⟩⟩
  invFun q :=
    ⟨Finsupp.equivFunOnFinite.symm (fun v => (q.2 v.1).val v.2), by
      constructor
      · funext i
        rw [weight_apply]
        exact (q.2 i).property.2
      · intro a ha hae
        apply q.1.property a ha
        intro v
        have h := (q.2 v.1).property.1 v.2
        change a v ≤ (q.1.val v.1 v.2 : ℕ)
        rw [← h]
        exact le_min (hae v) (hB a ha v)⟩
  left_inv e := by
    apply Subtype.ext
    ext v
    rfl
  right_inv q := by
    apply Sigma.ext
    · apply Subtype.ext
      funext i j
      apply Fin.ext
      exact (q.2 i).property.1 j
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      apply (Subtype.heq_iff_coe_eq ?_).mpr
      · rfl
      intro f
      change ((∀ j, min (f j) B = min ((q.2 i).val j) B) ∧ ∑ j, f j = d i) ↔
        ((∀ j, min (f j) B = (q.1.val i j : ℕ)) ∧ ∑ j, f j = d i)
      simp only [(q.2 i).property.1]

theorem partition_card (s : Finset (Var p N →₀ ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, ∀ v, a v ≤ B) (d : Fin p → ℕ) :
    Nat.card {e : Var p N →₀ ℕ // Finsupp.weight (Hilbert.blockWeight p N) e = d ∧
      ∀ a ∈ s, ¬ a ≤ e} =
    ∑ b : GoodPattern p N s B, ∏ i : Fin p,
      Nat.card {f : Cell B (b.val i) // ∑ j, f.val j = d i} := by
  classical
  rw [Nat.card_congr (partitionEquiv p N s B hB d), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [DegreeCellProduct, Nat.card_pi]
  exact Finset.prod_congr rfl (fun i _ => Nat.card_congr (flatCellEquiv B (b.val i) (d i)))

abbrev Active (s : Finset (Var p N →₀ ℕ)) (B : ℕ) :=
  {b : GoodPattern p N s B // ∀ i, 0 < Nat.card (Free B (b.val i))}

instance activeFintype (s : Finset (Var p N →₀ ℕ)) (B : ℕ) :
    Fintype (Active p N s B) := by classical exact Subtype.fintype _

theorem pattern_sum_bound (B : ℕ) (b : Pattern p N B) (i : Fin p) :
    (∑ j, (b i j : ℕ)) ≤ (N i + 1) * B := by
  calc
    _ ≤ ∑ _j : Fin (N i + 1), B := Finset.sum_le_sum (fun j _ => Nat.le_of_lt_succ (b i j).isLt)
    _ = _ := by simp

theorem eventual_partition_count (s : Finset (Var p N →₀ ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, ∀ v, a v ≤ B) (d : Fin p → ℕ)
    (hd : ∀ i, (N i + 1) * B < d i) :
    Nat.card {e : Var p N →₀ ℕ // Finsupp.weight (Hilbert.blockWeight p N) e = d ∧
      ∀ a ∈ s, ¬ a ≤ e} =
    ∑ b : Active p N s B, ∏ i : Fin p,
      (d i - (∑ j, (b.val.val i j : ℕ)) +
          (Nat.card (Free B (b.val.val i)) - 1)).choose
        (Nat.card (Free B (b.val.val i)) - 1) := by
  classical
  rw [partition_card p N s B hB d]
  calc
    _ = ∑ b : Active p N s B, ∏ i : Fin p,
        Nat.card {f : Cell B (b.val.val i) // ∑ j, f.val j = d i} := by
      apply Finset.sum_congr_set
        {b : GoodPattern p N s B | ∀ i, 0 < Nat.card (Free B (b.val i))}
      · intro b hb
        rfl
      · intro b hb
        simp only [Set.mem_setOf_eq, not_forall, Nat.not_lt, Nat.le_zero] at hb
        obtain ⟨i, hi⟩ := hb
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact degreeCell_card_zero B (b.val i) (d i)
          ((pattern_sum_bound p N B b.val i).trans_lt (hd i)) hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.prod_congr rfl
      intro i _
      exact degreeCell_card_pos B (b.val.val i) (d i)
        ((pattern_sum_bound p N B b.val.val i).trans (hd i).le) (b.property i)

end PhilipponMultiplicity.MonomialCells

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.BinomialPolynomial

/-- Positive leading coefficients prevent cancellation at the largest cell degree. -/
theorem sum_product_degree {ι J : Type*} [Fintype ι] [Fintype J]
    (q a : J → ι → ℕ) :
    (∑ j, product (q j) (a j)).totalDegree =
      Finset.univ.sup (fun j : J => ∑ i, q j i) := by
  classical
  cases isEmpty_or_nonempty J with
  | inl h => simp
  | inr h =>
    let F := ∑ j, product (q j) (a j)
    let n := Finset.univ.sup (fun j : J => ∑ i, q j i)
    have hqn (j : J) : (∑ i, q j i) ≤ n :=
      Finset.le_sup (f := fun j : J => ∑ i, q j i) (Finset.mem_univ j)
    have hpn (j : J) : (product (q j) (a j)).totalDegree ≤ n := by
      rw [product_degree]
      exact hqn j
    have hc (j : J) : 0 < ∏ i, ((q j i).factorial : ℚ)⁻¹ := by
      apply Finset.prod_pos
      intro i _
      exact inv_pos.mpr (by exact_mod_cast Nat.factorial_pos (q j i))
    have hpart (j : J) : homogeneousComponent n (product (q j) (a j)) =
        if (∑ i, q j i) = n then
          monomial (exponent (q j)) (∏ i, ((q j i).factorial : ℚ)⁻¹) else 0 := by
      split_ifs with he
      · rw [← he, product_top]
      · apply homogeneousComponent_eq_zero
        rw [product_degree]
        exact lt_of_le_of_ne (hqn j) he
    have hnn (j : J) (b : ι →₀ ℕ) :
        0 ≤ coeff b (homogeneousComponent n (product (q j) (a j))) := by
      rw [hpart]
      split_ifs
      · rw [coeff_monomial]
        split_ifs
        · exact (hc j).le
        · rfl
      · simp
    have hcoeff (b : ι →₀ ℕ) : coeff b (homogeneousComponent n F) =
        ∑ j, coeff b (homogeneousComponent n (product (q j) (a j))) := by
      simp only [F, map_sum, coeff_sum]
    have hFle : F.totalDegree ≤ n := totalDegree_finsetSum_le (fun j _ => hpn j)
    obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun j : J => ∑ i, q j i)
    have hjn' : (∑ i, q j i) = n := hjn.symm
    have hp : 0 < coeff (exponent (q j)) (homogeneousComponent n F) := by
      rw [hcoeff]
      have hpos : 0 < coeff (exponent (q j))
          (homogeneousComponent n (product (q j) (a j))) := by
        rw [hpart, if_pos hjn', coeff_monomial, if_pos rfl]
        exact hc j
      exact hpos.trans_le (Finset.single_le_sum (fun k _ => hnn k _) hj)
    have hFge : n ≤ F.totalDegree := by
      by_contra! hlt
      rw [homogeneousComponent_eq_zero n F hlt, coeff_zero] at hp
      exact (lt_irrefl 0) hp
    exact le_antisymm hFle hFge

/-- After factorial normalization, a top coefficient counts the cells with that exponent. -/
theorem sum_product_top_normalized {ι J : Type*} [Fintype ι] [Fintype J]
    (q a : J → ι → ℕ) (α : ι → ℕ)
    (hα : ∑ i, α i = (∑ j, product (q j) (a j)).totalDegree) :
    coeff (exponent α) (∑ j, product (q j) (a j)) *
      (∏ i, ((α i).factorial : ℚ)) =
        ((Finset.univ.filter (fun j : J => q j = α)).card : ℚ) := by
  classical
  let F := ∑ j, product (q j) (a j)
  let n := F.totalDegree
  have hqn (j : J) : (∑ i, q j i) ≤ n := by
    dsimp [n, F]
    rw [sum_product_degree]
    exact Finset.le_sup (f := fun j : J => ∑ i, q j i) (Finset.mem_univ j)
  have hexp : (exponent α).sum (fun _ e => e) = n := by
    simpa [exponent, Finsupp.sum_fintype] using hα
  have htop : coeff (exponent α) F = coeff (exponent α) (homogeneousComponent n F) := by
    have hd : (exponent α).degree = n := hexp
    simp [coeff_homogeneousComponent, hd]
  change coeff (exponent α) F * _ = _
  rw [htop]
  simp only [F, map_sum, coeff_sum, Finset.sum_mul]
  have hterm (j : J) :
      coeff (exponent α) (homogeneousComponent n (product (q j) (a j))) *
        (∏ i, ((α i).factorial : ℚ)) = if q j = α then 1 else 0 := by
    by_cases he : (∑ i, q j i) = n
    · rw [← he, product_top, coeff_monomial]
      by_cases hq : q j = α
      · rw [hq, if_pos rfl, if_pos rfl]
        rw [Finset.prod_inv_distrib, inv_mul_cancel₀]
        exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero (α i))
      · have hne : exponent (q j) ≠ exponent α := by
          intro h
          apply hq
          exact Finsupp.equivFunOnFinite.symm.injective h
        simp [hne, hq]
    · have hlt : (product (q j) (a j)).totalDegree < n := by
        rw [product_degree]
        exact lt_of_le_of_ne (hqn j) he
      rw [homogeneousComponent_eq_zero n _ hlt]
      have hq : q j ≠ α := by
        intro h
        apply he
        simpa [h] using hα
      simp [hq]
  simp_rw [hterm]
  simp

end PhilipponMultiplicity.BinomialPolynomial

namespace PhilipponMultiplicity

/-- The normalized mixed degrees are actual natural-number cell counts. -/
theorem idealMixedDegree_integral
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (α : M.FactorIndex → ℕ) : ∃ n : ℕ, SectionThree.idealMixedDegree M I α = (n : ℚ) := by
  classical
  obtain ⟨s, hs⟩ := multigraded_hilbert_function_standard_monomials K M I hI
  obtain ⟨B, hB⟩ := MonomialCells.exists_bound M.factorCount M.ambientDimension s
  let J := MonomialCells.Active M.factorCount M.ambientDimension s B
  let q (b : J) (i : M.FactorIndex) := Nat.card (MonomialCells.Free B (b.val.val i)) - 1
  let a (b : J) (i : M.FactorIndex) := ∑ j, (b.val.val i j : ℕ)
  let F := ∑ b : J, BinomialPolynomial.product (q b) (a b)
  have hF : Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I F := by
    refine ⟨fun i => (M.ambientDimension i + 1) * B + 1, ?_⟩
    intro d hd
    have hd' (i : M.FactorIndex) : (M.ambientDimension i + 1) * B < d i :=
      Nat.lt_of_succ_le (hd i)
    have ha (b : J) (i : M.FactorIndex) : a b i ≤ d i :=
      (MonomialCells.pattern_sum_bound M.factorCount M.ambientDimension B b.val.val i).trans
        (hd' i).le
    change eval (fun i => (d i : ℚ)) (∑ b : J, BinomialPolynomial.product (q b) (a b)) = _
    rw [map_sum, hs d, MonomialCells.eventual_partition_count
      M.factorCount M.ambientDimension s B hB d hd', Nat.cast_sum]
    exact Finset.sum_congr rfl (fun b _ => BinomialPolynomial.product_eval (q b) (a b) d (ha b))
  have hpoly := Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
    K M.factorCount M.ambientDimension I hF
  unfold SectionThree.idealMixedDegree
  split_ifs with hα
  · refine ⟨(Finset.univ.filter (fun b : J => q b = α)).card, ?_⟩
    rw [hpoly]
    apply BinomialPolynomial.sum_product_top_normalized q a α
    simpa only [SectionThree.idealDimension, hpoly] using hα
  · exact ⟨0, rfl⟩

end PhilipponMultiplicity

end


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity
noncomputable section
namespace PhilipponMultiplicity.CountingProof

-- Reuse the homogeneous-span argument from PhilipponProjectiveHilbertExistence.
theorem block_weight_apply {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (e : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) e) i =
      ∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex, ∑ j : Fin (M.ambientDimension b + 1),
    e ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem vanishing_homogeneous {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  let := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [block_weight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

theorem eval_nonneg {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℚ) (hF : ∀ b, 0 ≤ coeff b F) (D : ι → ℕ) :
    0 ≤ eval (fun i => (D i : ℚ)) F := by
  classical
  rw [eval_eq']
  exact Finset.sum_nonneg fun b _ => mul_nonneg (hF b)
    (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)

theorem term_le_eval {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℚ) (hF : ∀ b, 0 ≤ coeff b F)
    (D : ι → ℕ) (b : ι →₀ ℕ) :
    coeff b F * (∏ i, (D i : ℚ) ^ b i) ≤ eval (fun i => (D i : ℚ)) F := by
  classical
  by_cases hb : b ∈ F.support
  · rw [eval_eq']
    exact Finset.single_le_sum (fun e _ => mul_nonneg (hF e)
      (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)) hb
  · have hz : coeff b F = 0 := by simpa only [mem_support_iff, not_not] using hb
    rw [hz, zero_mul]
    exact eval_nonneg F hF D

/-- The complementary exponents have exactly the subgroup's Hilbert dimension. -/
theorem complement_sum {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} {H : AlgebraicSubgroup G}
    (r : SourceMixedCodimensionIndex G H) :
    ∑ i, r.complementIndex i = varietyDimension G H.carrier := by
  classical
  change (∑ i, ((G.factor i).dimension - r.exponent i)) = _
  rw [Finset.sum_tsub_distrib _ (fun i _ => r.bounded i)]
  change G.dimension - (∑ i, r.exponent i) = varietyDimension G H.carrier
  rw [← r.sum_eq, Nat.add_sub_cancel_left]

theorem degree_fin_one (d : Fin 1 →₀ ℕ) : d.degree = d 0 := by
  simp [Finsupp.degree_eq_sum]

theorem top_fin_one (P : MvPolynomial (Fin 1) ℚ) :
    homogeneousComponent P.totalDegree P =
      monomial (Finsupp.single 0 P.totalDegree) (coeff (Finsupp.single 0 P.totalDegree) P) := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_monomial]
  have hd : d.degree = P.totalDegree ↔ Finsupp.single 0 P.totalDegree = d := by
    rw [degree_fin_one]
    constructor
    · intro h
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa using h.symm
    · intro h
      rw [← h, Finsupp.single_eq_same]
  by_cases h : d.degree = P.totalDegree
  · rw [if_pos h, if_pos (hd.mp h), ← hd.mp h]
  · rw [if_neg h, if_neg (mt hd.mpr h)]

theorem eval_top_fin_one (P : MvPolynomial (Fin 1) ℚ) (d : Fin 1 → ℚ) :
    eval d (homogeneousComponent P.totalDegree P) =
      coeff (Finsupp.single 0 P.totalDegree) P * d 0 ^ P.totalDegree := by
  conv_lhs => rw [top_fin_one P]
  rw [eval_monomial, Finsupp.prod_single_index]
  simp

end PhilipponMultiplicity.CountingProof
namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i

theorem exists_form_nonzero_at (p : M.Point) (D : M.FactorIndex → ℕ) :
    ∃ Q : M.CoordinateRing, M.IsHomogeneous Q D ∧ M.eval Q p ≠ 0 := by
  classical
  have hj (i : M.FactorIndex) : ∃ j, (p i).rep j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using
      (Projectivization.rep_nonzero (p i))
  choose j hj using hj
  let d : M.Variable →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun v => if v.2 = j v.1 then D v.1 else 0)
  refine ⟨monomial d 1, ?_, ?_⟩
  · intro m hm i
    have hm' : m = d := Finset.mem_singleton.mp (support_monomial_subset hm)
    subst m
    simp [d]
  · change MvPolynomial.eval (M.coordinate p) (monomial d 1) ≠ 0
    rw [eval_monomial]
    simp only [one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    dsimp [d]
    split_ifs with h
    · apply pow_ne_zero
      change (p v.1).rep v.2 ≠ 0
      rw [h]
      exact hj v.1
    · simp

theorem homogeneous_total {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : P.IsHomogeneous (∑ i, D i) := by
  intro a ha
  change (Finsupp.weight (fun _ : M.Variable => (1 : ℕ))) a = _
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => hP a (mem_support_iff.mpr ha) i)

instance degreePiece_finite (D : M.FactorIndex → ℕ) :
    Module.Finite K (Hilbert.degreePiece K M.factorCount M.ambientDimension D) := by
  let W := MvPolynomial.homogeneousSubmodule M.Variable K (∑ i, D i)
  letI : Module.Finite K W := Module.Finite.of_fg
    (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  have hle : Hilbert.degreePiece K M.factorCount M.ambientDimension D ≤ W := by
    intro P hP
    exact M.homogeneous_total ((M.degreePiece_iff P D).mp hP)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

theorem hilbertFunction_pos {S : Set M.Point} (hS : S.Nonempty)
    (D : M.FactorIndex → ℕ) :
    0 < Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) D := by
  classical
  obtain ⟨x, hx⟩ := hS
  obtain ⟨Q, hQ, hQx⟩ := M.exists_form_nonzero_at x D
  let I := M.vanishingIdeal S
  let W := Hilbert.quotientPiece K M.factorCount M.ambientDimension I D
  let q : W := ⟨Ideal.Quotient.mk I Q,
    ⟨Q, (M.degreePiece_iff Q D).mpr hQ, rfl⟩⟩
  have hq : q ≠ 0 := by
    intro h
    have hz : Ideal.Quotient.mk I Q = 0 := congrArg Subtype.val h
    have hm : Q ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact hQx (M.eval_eq_zero_of_mem_vanishingIdeal hm hx)
  letI : Nontrivial W := nontrivial_of_ne q 0 hq
  letI : Module.Finite K W := by
    dsimp [W, Hilbert.quotientPiece]
    infer_instance
  exact Module.finrank_pos

end PhilipponMultiplicity.MultiProjectiveSpace
namespace PhilipponMultiplicity.CountingProof

/-- A nonempty multiprojective locus has a nonzero Hilbert polynomial. -/
theorem hilbertPolynomial_ne_zero {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) (hne : S.Nonempty) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S) ≠ 0 := by
  intro hz
  obtain ⟨b,hb⟩ := Hilbert.hilbertPolynomial_spec K M.factorCount M.ambientDimension
    (M.vanishingIdeal S) (multigraded_hilbert_polynomial_exists K M _
      (vanishing_homogeneous M S))
  have heq := hb b (fun _ => le_rfl)
  rw [hz,map_zero] at heq
  have hzero : Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) b = 0 := by exact_mod_cast heq.symm
  exact (Nat.ne_of_gt (M.hilbertFunction_pos hne b)) hzero

/-- The lower binomial estimate includes zero codimension and zero contact. -/
theorem binomial_lower (T s : ℕ) :
    ((T+1 : ℕ) : ℝ)^s / (s.factorial : ℝ) ≤ ((T+s).choose s : ℝ) := by
  simpa [show T+s+1-s = T+1 by omega] using (Nat.pow_le_choose (α := ℝ) s (T+s))

/-- A single nonnegative top Hilbert monomial is bounded by the whole form. -/
theorem mixed_lower {K : Type*} [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (r : SourceMixedCodimensionIndex G H) (D : G.FactorIndex → ℕ) :
    mixedDegree G H.carrier r.complementIndex *
      (Nat.factorial (varietyDimension G H.carrier) : ℝ) /
      (∏ i, (Nat.factorial (r.complementIndex i) : ℝ)) *
      (∏ i, (D i : ℝ)^r.complementIndex i) ≤ hilbertDegreeForm G H.carrier D := by
  classical
  let F := Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
    (G.vanishingIdeal H.carrier)
  let b : G.FactorIndex →₀ ℕ := Finsupp.equivFunOnFinite.symm r.complementIndex
  let Q := homogeneousComponent F.totalDegree F
  have hb : b.degree = F.totalDegree := by
    simpa [b, F, Finsupp.degree_eq_sum, varietyDimension] using complement_sum r
  have hcoeff : coeff b Q = coeff b F := by simp [Q, coeff_homogeneousComponent, hb]
  have hQ := (multigraded_hilbert_polynomial_top_coefficients K G.ambient
    (G.vanishingIdeal H.carrier)
    (vanishing_homogeneous G.ambient (G.embedding '' H.carrier))).1
  change ∀ e, 0 ≤ coeff e Q at hQ
  have hterm := mul_le_mul_of_nonneg_left (term_le_eval Q hQ D b)
    (Nat.cast_nonneg F.totalDegree.factorial : (0:ℚ) ≤ _)
  have hterm' : (F.totalDegree.factorial : ℚ) * coeff b F *
      (∏ i, (D i : ℚ)^r.complementIndex i) ≤
      Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal H.carrier) D := by
    change _ ≤ eval (fun i => (D i : ℚ)) ((F.totalDegree.factorial : ℚ) • Q)
    rw [smul_eq_C_mul, map_mul, eval_C]
    simpa [hcoeff, b, mul_assoc] using hterm
  have htermR : (F.totalDegree.factorial : ℝ) * ((coeff b F : ℚ) : ℝ) *
      (∏ i, (D i : ℝ)^r.complementIndex i) ≤ hilbertDegreeForm G H.carrier D := by
    unfold hilbertDegreeForm
    exact_mod_cast hterm'
  have hfac : (∏ i, ((r.complementIndex i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero _)
  rw [mixedDegree, if_pos (complement_sum r)]
  change (((coeff b F : ℚ) : ℝ) * _) * _ / _ * _ ≤ _
  change (((coeff b F : ℚ) : ℝ) * _) * (F.totalDegree.factorial : ℝ) / _ * _ ≤ _
  convert htermR using 1 <;> field_simp <;> ring

/-- A nonempty projective locus has degree at least one and bounded dimension. -/
theorem single_factor_degree {K : Type*} [Field K] {N : ℕ}
    (V : SectionThree.ProjectiveSubvariety K N) (hne : V.carrier.Nonempty) :
    1 ≤ V.degree ∧ V.dimension ≤ N := by
  classical
  let M := projectiveSpace K N
  let I := M.vanishingIdeal V.carrierInSingleFactor
  let F := Hilbert.hilbertPolynomial K 1 (fun _ => N) I
  let e : Fin 1 →₀ ℕ := Finsupp.single 0 F.totalDegree
  have hF : F ≠ 0 := hilbertPolynomial_ne_zero M _ (hne.image (fun x => fun _ => x))
  have hce : coeff e F ≠ 0 := by
    intro hz
    have ht : homogeneousComponent F.totalDegree F = 0 := by rw [top_fin_one, hz, monomial_zero]
    obtain ⟨b, hb, hd⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF) Finsupp.degree
    have hd' : b.degree = F.totalDegree := hd.symm
    have hc := congrArg (coeff b) ht
    rw [coeff_homogeneousComponent, if_pos hd', coeff_zero] at hc
    exact (mem_support_iff.mp hb) hc
  have het : e.degree = F.totalDegree := by simp [e, degree_fin_one]
  have hI := vanishing_homogeneous M V.carrierInSingleFactor
  have htop := multigraded_hilbert_polynomial_top_coefficients K M I hI
  have hdegree : V.degree = (F.totalDegree.factorial : ℚ) * coeff e F := by
    change eval (fun _ => (1:ℚ)) ((F.totalDegree.factorial : ℚ) •
      homogeneousComponent F.totalDegree F) = _
    rw [smul_eq_C_mul,map_mul,eval_C,eval_top_fin_one]
    simp [e]
  have hpos : 0 < V.degree := by
    rw [hdegree]
    apply mul_pos (by exact_mod_cast Nat.factorial_pos F.totalDegree)
    have hc := htop.1 e
    change 0 ≤ coeff e (homogeneousComponent F.totalDegree F) at hc
    rw [coeff_homogeneousComponent, if_pos het] at hc
    exact lt_of_le_of_ne hc (Ne.symm hce)
  obtain ⟨n,hn⟩ := idealMixedDegree_integral M I hI (fun _ => F.totalDegree)
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => F.totalDegree) = e := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp [e]
  have hn' : V.degree = (n:ℚ) := by
    change (if (∑ _ : Fin 1, F.totalDegree) = F.totalDegree then
      coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => F.totalDegree)) F *
        (∏ _ : Fin 1, (F.totalDegree.factorial : ℚ)) else 0) = (n:ℚ) at hn
    simpa [he, hdegree, mul_comm] using hn
  refine ⟨?_, ?_⟩
  · rw [hn'] at hpos ⊢
    exact_mod_cast Nat.succ_le_of_lt (show 0<n by exact_mod_cast hpos)
  · by_contra h
    have hN : N < e 0 := by
      change ¬ F.totalDegree ≤ N at h
      simpa [e] using Nat.lt_of_not_ge h
    have hz := htop.2 e ⟨(0 : Fin 1),hN⟩
    change coeff e (homogeneousComponent F.totalDegree F) = 0 at hz
    rw [coeff_homogeneousComponent, if_pos het] at hz
    exact hce hz

/-- Uniform lower degree bound for a product of nonempty projective loci. -/
theorem product_degree_lower {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, SectionThree.ProjectiveSubvariety K (M.ambientDimension i))
    (hne : ∀ i, (V i).carrier.Nonempty) (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    0 < SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D ∧
    (∏ i, (D i : ℚ)^(V i).dimension) ≤
      (∏ i, ((M.ambientDimension i).factorial : ℚ)) *
        SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D := by
  classical
  have hV := fun i => single_factor_degree (V i) (hne i)
  have hfac : (∏ i, ((V i).dimension.factorial : ℚ)) > 0 :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  have hdeg : (1:ℚ) ≤ ∏ i, (V i).degree := Finset.one_le_prod fun i _ => (hV i).1
  have hdim : (1:ℚ) ≤ ((SectionThree.locusDimension M
      (SectionThree.productCarrier M V)).factorial : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
  have hmon : 0 < ∏ i, (D i : ℚ)^(V i).dimension :=
    Finset.prod_pos fun i _ => pow_pos (by exact_mod_cast hD i) _
  have hform := lemma_3_4 K hK M V D hD
  have hpos : 0 < SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D := by
    rw [hform]
    exact mul_pos (mul_pos (div_pos (lt_of_lt_of_le zero_lt_one hdim) hfac)
      (lt_of_lt_of_le zero_lt_one hdeg)) hmon
  refine ⟨hpos, ?_⟩
  have hscale : (∏ i, ((V i).dimension.factorial : ℚ)) ≤
      ∏ i, ((M.ambientDimension i).factorial : ℚ) :=
    Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => by
      exact_mod_cast Nat.factorial_le (hV i).2)
  have heq : (∏ i, ((V i).dimension.factorial : ℚ)) *
      SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D =
      ((SectionThree.locusDimension M (SectionThree.productCarrier M V)).factorial : ℚ) *
        (∏ i, (V i).degree) * (∏ i, (D i : ℚ)^(V i).dimension) := by
    rw [hform]
    field_simp
  calc
    (∏ i, (D i : ℚ)^(V i).dimension) ≤
      (∏ i, ((V i).dimension.factorial : ℚ)) *
        SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D := by
          rw [heq]
          exact le_mul_of_one_le_left hmon.le (one_le_mul_of_one_le_of_one_le hdim hdeg)
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hpos.le

/-- A closed factor projection is locally closed in its projective space. -/
theorem projection_locallyClosed {K : Type*} [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K) (hdisjoint : HasDisjointFactors G)
    (H : AlgebraicSubgroup G) (i : G.FactorIndex) :
    @IsLocallyClosed _ (TopologicalSpace.induced (fun x _ => x)
      (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology)
      (Subtype.val '' factorProjection G H i) := by
  letI : TopologicalSpace (G.factor i).Point := factorTopology (G.factor i)
  letI : TopologicalSpace (Projectivization K (Fin ((G.factor i).ambientDimension + 1) → K)) :=
    TopologicalSpace.induced (fun x _ => x)
      (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology
  have he : Topology.IsInducing (Subtype.val : (G.factor i).Point → _) := by
    constructor
    change TopologicalSpace.induced (fun x : (G.factor i).Point => fun _ : Fin 1 => x.val)
      (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology =
      TopologicalSpace.induced Subtype.val (TopologicalSpace.induced
        (fun x : Projectivization K (Fin ((G.factor i).ambientDimension + 1) → K) =>
          fun _ : Fin 1 => x) (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology)
    rw [induced_compose]
    rfl
  apply ((hdisjoint H).2 i).isLocallyClosed.image he
  simpa only [Subtype.range_coe] using (G.factor i).locallyClosed

/-- The uniform degree-ratio estimate uses only the genuine product property.
Ambient factorials bound every subgroup's denominator in Lemma 3.4. -/
theorem disjoint_degree_ratio {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) (G : EmbeddedGroupProduct K)
    (hdisjoint : HasDisjointFactors G) :
    ∃ c : ℝ, 0 < c ∧ ∀ (H : AlgebraicSubgroup G) (D : G.FactorIndex → ℕ),
      (∀ i, 1 ≤ D i) → 0 < hilbertDegreeForm G H.carrier D ∧
      hilbertDegreeForm G Set.univ D / hilbertDegreeForm G H.carrier D ≤
        c * ∏ i, (D i : ℝ)^factorCodimension G H i := by
  classical
  let F : ℝ := ∏ i, ((G.ambient.ambientDimension i).factorial : ℝ)
  let B : ℝ := hilbertDegreeForm G Set.univ (fun _ => 1)
  have hF : 0 < F := Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  refine ⟨(|B|+1)*F, mul_pos (by positivity) hF, ?_⟩
  intro H D hD
  let V (i : G.ambient.FactorIndex) : SectionThree.ProjectiveSubvariety K
      (G.ambient.ambientDimension i) :=
    ⟨Subtype.val '' factorProjection G H i, projection_locallyClosed G hdisjoint H i⟩
  have hV (i : G.FactorIndex) : (V i).carrier.Nonempty :=
    ⟨((0 : G.Point) i).val, ⟨(0 : G.Point) i, ⟨0,H.toAddSubgroup.zero_mem,rfl⟩,rfl⟩⟩
  have hcarrier : G.embedding '' H.carrier = SectionThree.productCarrier G.ambient V := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩ i
      exact ⟨y i,⟨y,hy,rfl⟩,rfl⟩
    · intro hx
      choose y hy heq using hx
      have hm : (fun i => y i) ∈ H.carrier := (hdisjoint H).1 _ |>.mpr hy
      exact ⟨y,hm,funext heq⟩
  have hcod (i : G.FactorIndex) : factorCodimension G H i =
      (G.factor i).dimension - (V i).dimension := by
    unfold factorCodimension SectionThree.ProjectiveSubvariety.dimension
      SectionThree.idealDimension SectionThree.ProjectiveSubvariety.carrierInSingleFactor
    simp only [V, Set.image_image, Function.comp_def]
    rfl
  obtain ⟨hpos,hlower⟩ := product_degree_lower hK G.ambient V hV D hD
  have hform : hilbertDegreeForm G H.carrier D =
      (SectionThree.locusDegreeValue G.ambient (SectionThree.productCarrier G.ambient V) D : ℝ) := by
    unfold hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
    rw [hcarrier]
    rfl
  have hposR : 0 < hilbertDegreeForm G H.carrier D := by rw [hform]; exact_mod_cast hpos
  have hlowR : (∏ i, (D i : ℝ)^(V i).dimension) ≤ F * hilbertDegreeForm G H.carrier D := by
    rw [hform]
    dsimp only [F]
    exact_mod_cast hlower
  refine ⟨hposR, (div_le_iff₀ hposR).mpr ?_⟩
  let W : ∀ i : G.ambient.FactorIndex,
      SectionThree.ProjectiveSubvariety K (G.ambient.ambientDimension i) :=
    fun i => ⟨(G.factor i).carrier,(G.factor i).locallyClosed⟩
  have hfull : G.embedding '' Set.univ = SectionThree.productCarrier G.ambient W := by
    ext x
    constructor
    · rintro ⟨y,_,rfl⟩ i
      exact (y i).property
    · intro hx
      exact ⟨fun i => ⟨x i,hx i⟩,Set.mem_univ _,rfl⟩
  have hmain : hilbertDegreeForm G Set.univ D = B *
      ∏ i, (D i : ℝ)^(G.factor i).dimension := by
    have hd := lemma_3_4 K hK G.ambient W D hD
    have h1 := lemma_3_4 K hK G.ambient W (fun _ => 1) (fun _ => le_rfl)
    have heq : SectionThree.locusDegreeValue G.ambient (SectionThree.productCarrier G.ambient W) D =
        SectionThree.locusDegreeValue G.ambient (SectionThree.productCarrier G.ambient W) (fun _ => 1) *
          ∏ i, (D i : ℚ)^(G.factor i).dimension := by
      rw [hd,h1]
      simp only [Nat.cast_one,one_pow,Finset.prod_const_one,mul_one]
      rfl
    unfold B hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
    rw [hfull]
    exact_mod_cast heq
  have hmon : (∏ i, (D i : ℝ)^(G.factor i).dimension) ≤
      (∏ i, (D i : ℝ)^factorCodimension G H i) *
        (∏ i, (D i : ℝ)^(V i).dimension) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun i _ => pow_nonneg (Nat.cast_nonneg _) _)
    intro i _
    rw [hcod,← pow_add]
    exact pow_le_pow_right₀ (by exact_mod_cast hD i) (by omega)
  have hc : 0 ≤ ∏ i, (D i : ℝ)^factorCodimension G H i := by positivity
  calc
    hilbertDegreeForm G Set.univ D = B * ∏ i, (D i : ℝ)^(G.factor i).dimension := hmain
    _ ≤ (|B|+1) * ∏ i, (D i : ℝ)^(G.factor i).dimension :=
      mul_le_mul_of_nonneg_right (le_trans (le_abs_self B) (by linarith)) (by positivity)
    _ ≤ (|B|+1) * ((∏ i, (D i : ℝ)^factorCodimension G H i) *
        (∏ i, (D i : ℝ)^(V i).dimension)) := mul_le_mul_of_nonneg_left hmon (by positivity)
    _ ≤ (|B|+1) * ((∏ i, (D i : ℝ)^factorCodimension G H i) *
        (F * hilbertDegreeForm G H.carrier D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlowR hc) (by positivity)
    _ = _ := by ring

end PhilipponMultiplicity.CountingProof
end


set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
open Submodule
noncomputable section
namespace PhilipponMultiplicity.CountingProof

/-- A finite generating family contains as many independent elements as its rank,
even when its integer span has torsion. -/
theorem independent_subfamily {M : Type*} [AddCommGroup M] {m : ℕ}
    (v : Fin m → M) :
    ∃ s : Finset (Fin m), s.card = Module.finrank ℤ (span ℤ (Set.range v)) ∧
      LinearIndependent ℤ (fun i : s => v i) := by
  classical
  let N := span ℤ (Set.range v)
  let w (i : Fin m) : N := ⟨v i,subset_span (Set.mem_range_self i)⟩
  letI : Module.Finite ℤ N := Module.Finite.span_of_finite ℤ (Set.finite_range v)
  have hw : span ℤ (Set.range w) = ⊤ :=
    (span_range_subtype_eq_top_iff N (fun i => subset_span (Set.mem_range_self i))).mpr rfl
  obtain ⟨s,hs,hmax⟩ := exists_maximal_linearIndepOn ℤ w
  letI : Fintype s := Fintype.ofFinite s
  let L := span ℤ (w '' s)
  have htor : Module.IsTorsion ℤ (N ⧸ L) := by
    have hgen (i : Fin m) : L.mkQ (w i) ∈ torsion ℤ (N ⧸ L) := by
      rw [mem_torsion_iff]
      by_cases hi : i ∈ s
      · refine ⟨1, ?_⟩
        simp only [one_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact subset_span (Set.mem_image_of_mem w hi)
      · obtain ⟨a,ha,hmem⟩ := hmax i hi
        refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
        change a • L.mkQ (w i) = 0
        rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hmem
    have hall : (⊤ : Submodule ℤ N) ≤ (torsion ℤ (N ⧸ L)).comap L.mkQ := by
      rw [← hw]
      apply span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hgen i
    intro q
    obtain ⟨x,rfl⟩ := L.mkQ_surjective q
    exact hall (show x ∈ (⊤ : Submodule ℤ N) from trivial)
  have hrank : Module.finrank ℤ L = Module.finrank ℤ N := by
    have h := L.finrank_quotient_add_finrank
    rw [htor.finrank_eq_zero,zero_add] at h
    exact h
  have hind : LinearIndependent ℤ (fun i : s => w i) := hs
  have hcard : Module.finrank ℤ L = Fintype.card s := by
    have hspan : span ℤ (Set.range (fun i : s => w i)) = L := by
      congr 1
      ext x
      simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]
    rw [← hspan]
    exact Module.finrank_eq_card_basis (Module.Basis.span hind)
  refine ⟨s.toFinite.toFinset, ?_, ?_⟩
  · simpa only [Set.toFinite_toFinset, Set.toFinset_card] using hcard.symm.trans hrank
  · have h := hind.map' N.subtype (ker_subtype N)
    have hh : LinearIndepOn ℤ v s := h
    change LinearIndepOn ℤ v (↑s.toFinite.toFinset : Set (Fin m))
    simpa only [Set.Finite.coe_toFinset] using hh

/-- Natural-coefficient grid in an arbitrary abelian group. -/
def nonnegativeGrid {M : Type*} [AddCommGroup M] {m : ℕ}
    (v : Fin m → M) (S : ℝ) : Set M :=
  {x | ∃ a : Fin m → ℕ, (∀ i, (a i : ℝ) ≤ S) ∧ x = ∑ i, a i • v i}

theorem nonnegativeGrid_finite {M : Type*} [AddCommGroup M] {m : ℕ}
    (v : Fin m → M) (S : ℝ) (hS : 0 ≤ S) : (nonnegativeGrid v S).Finite := by
  let f (a : Fin m → Fin (⌊S⌋₊+1)) : M := ∑ i, (a i).val • v i
  have heq : nonnegativeGrid v S = Set.range f := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨fun i => ⟨a i,Nat.lt_succ_of_le ((Nat.le_floor_iff hS).mpr (ha i))⟩,rfl⟩
    · rintro ⟨a,rfl⟩
      refine ⟨fun i => (a i).val, ?_,rfl⟩
      intro i
      exact (Nat.le_floor_iff hS).mp (Nat.le_of_lt_succ (a i).isLt)
  rw [heq]
  exact Set.finite_range f

/-- A rank-sized independent subfamily gives an injective integer cube in the grid. -/
theorem nonnegativeGrid_card_lower {M : Type*} [AddCommGroup M] {m : ℕ}
    (v : Fin m → M) (S : ℝ) (hS : 0 ≤ S) :
    S ^ Module.finrank ℤ (span ℤ (Set.range v)) ≤ ((nonnegativeGrid v S).ncard : ℝ) := by
  classical
  obtain ⟨s,hcard,hlin⟩ := independent_subfamily v
  let f (a : s → Fin (⌊S⌋₊+1)) : M := ∑ i, (a i).val • v i
  have hf : Function.Injective f := by
    intro a b hab
    have h := hlin.fintypeLinearCombination_injective (a₁ := fun i => ((a i).val : ℤ))
      (a₂ := fun i => ((b i).val : ℤ)) (by
        simpa only [Fintype.linearCombination_apply,natCast_zsmul,f] using hab)
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  have hsub : Set.range f ⊆ nonnegativeGrid v S := by
    rintro _ ⟨a,rfl⟩
    let b (i : Fin m) : ℕ := if hi : i ∈ s then (a ⟨i,hi⟩).val else 0
    refine ⟨b,?_,?_⟩
    · intro i
      dsimp only [b]
      split_ifs with hi
      · exact (Nat.le_floor_iff hS).mp (Nat.le_of_lt_succ (a ⟨i,hi⟩).isLt)
      · simpa using hS
    · change (∑ i : s, (a i).val • v i) = ∑ i : Fin m, b i • v i
      have heq : (∑ i : Fin m, b i • v i) = ∑ i ∈ s, b i • v i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _ hi
        simp [b,hi]
      rw [heq, Finset.sum_subtype s (fun _ => Iff.rfl)]
      apply Finset.sum_congr rfl
      intro i _
      simp [b,i.property]
  have hnat : (⌊S⌋₊+1)^s.card ≤ (nonnegativeGrid v S).ncard := by
    have h := Set.ncard_le_ncard hsub (nonnegativeGrid_finite v S hS)
    rw [Set.ncard_range_of_injective hf] at h
    simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using h
  rw [← hcard]
  calc
    S^s.card ≤ ((⌊S⌋₊+1 : ℕ) : ℝ)^s.card :=
      pow_le_pow_left₀ hS (by exact_mod_cast (Nat.lt_floor_add_one S).le) _
    _ ≤ _ := by exact_mod_cast hnat

theorem nonnegativeGrid_map {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {m : ℕ} (f : M →+ N) (v : Fin m → M) (S : ℝ) :
    f '' nonnegativeGrid v S = nonnegativeGrid (fun i => f (v i)) S := by
  ext x
  constructor
  · rintro ⟨y,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,by simp⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨∑ i, a i • v i,⟨a,ha,rfl⟩,by simp⟩

/-- The quotient grid and the set of translated subgroup carriers have equal cardinality. -/
theorem coset_grid_card_lower {M : Type*} [AddCommGroup M] {m : ℕ}
    (H : AddSubgroup M) (v : Fin m → M) (S : ℝ) (hS : 0 ≤ S) :
    S ^ Module.finrank ℤ (span ℤ (Set.range (fun i => QuotientAddGroup.mk' H (v i)))) ≤
      (((fun x => (fun y => x+y) '' (H : Set M)) '' nonnegativeGrid v S).ncard : ℝ) := by
  classical
  let q := QuotientAddGroup.mk' H
  let fiber (z : M ⧸ H) : Set M := q ⁻¹' {z}
  have hf : Function.Injective fiber := by
    intro x y h
    obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective x
    have ha : a ∈ fiber (q a) := rfl
    change fiber (q a) = fiber y at h
    rw [h] at ha
    exact ha
  have hcoset (x : M) : (fun y => x+y) '' (H : Set M) = fiber (q x) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change q (x+z) = q x
      rw [map_add, show q z = 0 from (QuotientAddGroup.eq_zero_iff z).mpr hz,add_zero]
    · intro hy
      have hz : y-x ∈ H := (QuotientAddGroup.eq_zero_iff (y-x)).mp (by
        change q (y-x) = 0
        rw [map_sub, show q y = q x from hy,sub_self])
      exact ⟨y-x,hz,by abel⟩
  have heq : (fun x => (fun y => x+y) '' (H : Set M)) '' nonnegativeGrid v S =
      fiber '' nonnegativeGrid (fun i => q (v i)) S := by
    simp_rw [hcoset]
    rw [← nonnegativeGrid_map q,Set.image_image]
  rw [heq, Set.ncard_image_of_injective _ hf]
  exact nonnegativeGrid_card_lower (fun i => q (v i)) S hS

end PhilipponMultiplicity.CountingProof

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Corollary23Proof

private theorem complete_base {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

/-- A uniform bound uses the rank of the joint homogeneous-coordinate lift,
so redundant analytic parameters do not affect the constant. -/
theorem codimension_le_coordinates {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) {G : EmbeddedGroupProduct K}
    (A : AnalyticSubgroup G) (V : Set G.Point) :
    analyticCodimension A V ≤ Fintype.card G.ambient.Variable := by
  classical
  letI : CompleteSpace K := complete_base hK
  let L := A.lift 0
  let d : A.ParameterSpace →ₗ[K] (G.ambient.Variable → K) := (fderiv K L 0).toLinearMap
  have hL : DifferentiableAt K L 0 :=
    differentiableAt_pi.mpr (fun i => (A.lift_analytic 0 i).differentiableAt)
  have hker : LinearMap.ker d ≤ A.tangentKernel V := by
    apply le_iInf
    intro P v hv
    change (fderiv K (A.pullback P.val 0) 0) v = 0
    have hP : DifferentiableAt K (fun x : G.ambient.Variable → K => eval x P.val) (L 0) :=
      (AnalyticOnNhd.eval_continuousLinearMap
        (ContinuousLinearMap.id K (G.ambient.Variable → K)) P.val (L 0)
        (Set.mem_univ _)).differentiableAt
    change (fderiv K ((fun x : G.ambient.Variable → K => eval x P.val) ∘ L) 0) v = 0
    rw [fderiv_comp 0 hP hL, ContinuousLinearMap.comp_apply]
    change (fderiv K (fun x : G.ambient.Variable → K => eval x P.val) (L 0)) (d v) = 0
    rw [show d v = 0 from hv, map_zero]
  have hrank := d.finrank_range_add_finrank_ker
  have hmono := Submodule.finrank_mono hker
  have hbound := Submodule.finrank_le (LinearMap.range d)
  have hdom : Module.finrank K A.ParameterSpace = A.parameterDimension := by simp
  have hcod : Module.finrank K (G.ambient.Variable → K) = Fintype.card G.ambient.Variable := by simp
  rw [hdom] at hrank
  rw [hcod] at hbound
  unfold analyticCodimension
  omega

theorem zero_mem_grid {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} {l : ℕ} (γ : Fin l → G.Point)
    {S : ℝ} (hS : 0 ≤ S) : 0 ∈ samplingGrid γ S := by
  exact ⟨fun _ => 0, fun _ => by simpa using hS, by simp⟩

/-- Adding n points of the S-grid gives a point of the nS-grid. -/
theorem sumset_grid {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} {l : ℕ} (γ : Fin l → G.Point)
    (S : ℝ) (hS : 0 ≤ S) (n : ℕ) :
    ↑(sumset (CountingProof.nonnegativeGrid_finite γ S hS).toFinset n) ⊆
      samplingGrid γ ((n : ℝ) * S) := by
  classical
  intro x hx
  simp only [sumset, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨v, rfl⟩ := hx
  have hv (j : Fin n) : ∃ a : Fin l → ℕ,
      (∀ i, (a i : ℝ) ≤ S) ∧ (v j).val = ∑ i, a i • γ i := by
    exact (CountingProof.nonnegativeGrid_finite γ S hS).mem_toFinset.mp (v j).property
  choose a ha heq using hv
  refine ⟨fun i => ∑ j, a j i, ?_, ?_⟩
  · intro i
    push_cast
    calc
      ∑ j, (a j i : ℝ) ≤ ∑ _j : Fin n, S := Finset.sum_le_sum (fun j _ => ha j i)
      _ = (n : ℝ) * S := by simp
  · calc
      (∑ j, (v j).val) = ∑ j, ∑ i, a j i • γ i := Finset.sum_congr rfl (fun j _ => heq j)
      _ = ∑ i, ∑ j, a j i • γ i := Finset.sum_comm
      _ = ∑ i, (∑ j, a j i) • γ i := by simp only [Finset.sum_smul]

theorem product_degree_scaling {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) (G : EmbeddedGroupProduct K)
    (c D : G.FactorIndex → ℕ) (hc : ∀ i, 1 ≤ c i) (hD : ∀ i, 1 ≤ D i) :
    hilbertDegreeForm G Set.univ (fun i => c i * D i) =
      hilbertDegreeForm G Set.univ D * ∏ i, (c i : ℝ) ^ (G.factor i).dimension := by
  classical
  let V : ∀ i : G.ambient.FactorIndex,
      SectionThree.ProjectiveSubvariety K (G.ambient.ambientDimension i) :=
    fun i => ⟨(G.factor i).carrier, (G.factor i).locallyClosed⟩
  have hcarrier : G.embedding '' Set.univ = SectionThree.productCarrier G.ambient V := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩ i
      exact (y i).property
    · intro hx
      exact ⟨fun i => ⟨x i, hx i⟩, Set.mem_univ _, rfl⟩
  have hmul := lemma_3_4 K hK G.ambient V (fun i => c i * D i)
    (fun i => Nat.mul_pos (hc i) (hD i))
  have hbase := lemma_3_4 K hK G.ambient V D hD
  have heq : SectionThree.locusDegreeValue G.ambient
      (SectionThree.productCarrier G.ambient V) (fun i => c i * D i) =
      SectionThree.locusDegreeValue G.ambient (SectionThree.productCarrier G.ambient V) D *
        ∏ i, (c i : ℚ) ^ (G.factor i).dimension := by
    rw [hmul, hbase]
    simp only [Nat.cast_mul, mul_pow, Finset.prod_mul_distrib]
    exact (mul_assoc _ _ _).symm.trans (mul_right_comm _ _ _)
  unfold hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
  rw [hcarrier]
  exact_mod_cast heq

theorem positive_degrees
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hdisjoint : HasDisjointFactors G) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : AnalyticSubgroup G) (l : ℕ) (γ : Fin l → G.Point)
        (S : ℝ), 0 ≤ S →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        (∀ i, 1 ≤ D i) →
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ samplingGrid γ ((G.dimension : ℝ) * S),
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        (∀ r : G.FactorIndex → ℕ, (∀ i, r i ≤ (G.factor i).dimension) →
          c * (∏ i, (D i : ℝ) ^ r i) ≤
            ((T + 1 : ℕ) : ℝ) ^ analyticCodimensionMinimum A r *
              S ^ samplingRankMinimum A γ r) →
        ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P := by
  classical
  obtain ⟨c, hc, hmain⟩ := theorem_2_1 K hK
  obtain ⟨b, hb, hratio⟩ := CountingProof.disjoint_degree_ratio hK G hdisjoint
  let C : ℝ := ∏ i, (c (G.factor i) : ℝ) ^ (G.factor i).dimension
  let F : ℝ := (Fintype.card G.ambient.Variable).factorial
  have hC : 0 < C := Finset.prod_pos fun i _ => pow_pos (by exact_mod_cast hc (G.factor i)) _
  have hF : 0 < F := by dsimp [F]; exact_mod_cast Nat.factorial_pos (Fintype.card G.ambient.Variable)
  refine ⟨F * C * b + 1, by positivity, ?_⟩
  intro A l γ S hS T D P hD hP hhom hcontact hlarge
  let sample : Finset G.Point := (CountingProof.nonnegativeGrid_finite γ S hS).toFinset
  have hzero : 0 ∈ sample :=
    (CountingProof.nonnegativeGrid_finite γ S hS).mem_toFinset.mpr (zero_mem_grid γ hS)
  have hcontact' : ∀ g ∈ sumset sample G.dimension,
      ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g :=
    fun g hg => hcontact g (sumset_grid γ S hS G.dimension hg)
  obtain ⟨H, _, _, ⟨g, hg⟩, hbound⟩ := hmain G A sample hzero T D P hP hhom hcontact'
  have hAH : A.carrier ⊆ H.carrier := by
    by_contra hnot
    let r := factorCodimension G H
    let s := analyticCodimension A H.carrier
    let N : ℝ := cosetCount sample H.carrier
    let W : ℝ := ((T+s).choose s : ℝ) * N
    let M : ℝ := ∏ i, (D i : ℝ)^r i
    have hM : 0 < M := Finset.prod_pos fun i _ => pow_pos (by exact_mod_cast hD i) _
    have hN : 1 ≤ N := by
      have hp : 0 < cosetCount sample H.carrier := Finset.card_pos.mpr
        ⟨translate 0 H.carrier, Finset.mem_image.mpr ⟨0, hzero, rfl⟩⟩
      dsimp [N]
      exact_mod_cast Nat.succ_le_of_lt hp
    have hsmin : analyticCodimensionMinimum A r ≤ s :=
      Nat.sInf_le ⟨H, ⟨hnot, fun _ => le_rfl⟩, rfl⟩
    have hqmin : samplingRankMinimum A γ r ≤ samplingQuotientRank γ H :=
      Nat.sInf_le ⟨H, ⟨hnot, fun _ => le_rfl⟩, rfl⟩
    have hSbound : S ^ samplingRankMinimum A γ r ≤ N := by
      by_cases hSone : S ≤ 1
      · exact (pow_le_one₀ hS hSone).trans hN
      · have hgrid := CountingProof.coset_grid_card_lower H.toAddSubgroup γ S hS
        have heq : ((fun x => (fun y => x+y) '' (H.toAddSubgroup : Set G.Point)) ''
            CountingProof.nonnegativeGrid γ S).ncard = cosetCount sample H.carrier := by
          rw [cosetCount, ← Set.ncard_coe_finset, Finset.coe_image]
          simp only [sample, Set.Finite.coe_toFinset]
          rfl
        rw [heq] at hgrid
        exact (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hSone)) hqmin).trans hgrid
    have hTbound : ((T+1 : ℕ) : ℝ)^analyticCodimensionMinimum A r ≤
        F * ((T+s).choose s : ℝ) := by
      have hs : s ≤ Fintype.card G.ambient.Variable := codimension_le_coordinates hK A H.carrier
      have hsf : 0 < (s.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos s
      have hfac : (s.factorial : ℝ) ≤ F := by dsimp [F]; exact_mod_cast Nat.factorial_le hs
      calc
        _ ≤ ((T+1 : ℕ) : ℝ)^s := pow_le_pow_right₀ (by exact_mod_cast Nat.le_add_left 1 T) hsmin
        _ ≤ ((T+s).choose s : ℝ) * (s.factorial : ℝ) :=
          (div_le_iff₀ hsf).mp (CountingProof.binomial_lower T s)
        _ ≤ ((T+s).choose s : ℝ) * F := mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = _ := mul_comm _ _
    have hlow : (F*C*b+1) * M ≤ F * W := by
      calc
        _ ≤ ((T+1 : ℕ) : ℝ)^analyticCodimensionMinimum A r *
            S^samplingRankMinimum A γ r := hlarge r (fun i => Nat.sub_le _ _)
        _ ≤ (F * ((T+s).choose s : ℝ)) * N :=
          mul_le_mul hTbound hSbound (pow_nonneg hS _) (by positivity)
        _ = _ := by dsimp [W]; ring
    obtain ⟨hH, hratioD⟩ := hratio H D hD
    have hscale := product_degree_scaling hK G (fun i => c (G.factor i)) D
      (fun i => hc (G.factor i)) hD
    have hupper : W * hilbertDegreeForm G H.carrier D ≤ (C*b*M) * hilbertDegreeForm G H.carrier D := by
      calc
        W * hilbertDegreeForm G H.carrier D ≤ hilbertDegreeForm G Set.univ D * C := by
          simpa only [hscale] using hbound
        _ ≤ (b * M * hilbertDegreeForm G H.carrier D) * C :=
          mul_le_mul_of_nonneg_right ((div_le_iff₀ hH).mp hratioD) hC.le
        _ = _ := by ring
    have hW : W ≤ C*b*M := (mul_le_mul_iff_of_pos_right hH).mp hupper
    have hlast := hlow.trans (mul_le_mul_of_nonneg_left hW hF.le)
    nlinarith only [hlast, hM]
  refine ⟨-g, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨z, hz, hza⟩ := hg (hAH ha)
  have hx : -g + a = z := by rw [← hza]; simp
  change -g + a ∈ zeroLocusOnGroup G P
  rw [hx]
  exact hz

end PhilipponMultiplicity.Corollary23Proof

end

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace PhilipponMultiplicity.Corollary23Proof

/-- A maximum of the two uniform constants handles every natural multidegree. -/
theorem combine_cases {K : Type*} [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K)
    (hpositive :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : AnalyticSubgroup G) (l : ℕ) (γ : Fin l → G.Point)
        (S : ℝ), 0 ≤ S →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        (∀ i, 1 ≤ D i) →
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ samplingGrid γ ((G.dimension : ℝ) * S),
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        (∀ r : G.FactorIndex → ℕ, (∀ i, r i ≤ (G.factor i).dimension) →
          c * (∏ i, (D i : ℝ) ^ r i) ≤
            ((T + 1 : ℕ) : ℝ) ^ analyticCodimensionMinimum A r *
              S ^ samplingRankMinimum A γ r) →
        ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P)
    (hboundary :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : AnalyticSubgroup G) (l : ℕ) (γ : Fin l → G.Point)
        (S : ℝ), 0 ≤ S →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        (∃ i, D i = 0) →
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ samplingGrid γ ((G.dimension : ℝ) * S),
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        (∀ r : G.FactorIndex → ℕ, (∀ i, r i ≤ (G.factor i).dimension) →
          c * (∏ i, (D i : ℝ) ^ r i) ≤
            ((T + 1 : ℕ) : ℝ) ^ analyticCodimensionMinimum A r *
              S ^ samplingRankMinimum A γ r) →
        ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : AnalyticSubgroup G) (l : ℕ) (γ : Fin l → G.Point)
        (S : ℝ), 0 ≤ S →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ samplingGrid γ ((G.dimension : ℝ) * S),
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        (∀ r : G.FactorIndex → ℕ, (∀ i, r i ≤ (G.factor i).dimension) →
          c * (∏ i, (D i : ℝ) ^ r i) ≤
            ((T + 1 : ℕ) : ℝ) ^ analyticCodimensionMinimum A r *
              S ^ samplingRankMinimum A γ r) →
        ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P := by
  classical
  obtain ⟨cp, hcp, hp⟩ := hpositive
  obtain ⟨cz, hcz, hz⟩ := hboundary
  refine ⟨max cp cz, lt_of_lt_of_le hcp (le_max_left _ _), ?_⟩
  intro A l γ S hS T D P hP hhom hcontact hlarge
  by_cases hD : ∀ i, 1 ≤ D i
  · apply hp A l γ S hS T D P hD hP hhom hcontact
    intro r hr
    exact (mul_le_mul_of_nonneg_right (le_max_left cp cz) (by positivity)).trans (hlarge r hr)
  · have hzero : ∃ i, D i = 0 := by
      push Not at hD
      obtain ⟨i, hi⟩ := hD
      exact ⟨i, by omega⟩
    apply hz A l γ S hS T D P hzero hP hhom hcontact
    intro r hr
    exact (mul_le_mul_of_nonneg_right (le_max_right cp cz) (by positivity)).trans (hlarge r hr)

end PhilipponMultiplicity.Corollary23Proof
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hdisjoint : HasDisjointFactors G) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : AnalyticSubgroup G) (l : ℕ) (γ : Fin l → G.Point)
        (S : ℝ), 0 ≤ S →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ samplingGrid γ ((G.dimension : ℝ) * S),
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        (∀ r : G.FactorIndex → ℕ, (∀ i, r i ≤ (G.factor i).dimension) →
          c * (∏ i, (D i : ℝ) ^ r i) ≤
            ((T + 1 : ℕ) : ℝ) ^ analyticCodimensionMinimum A r *
              S ^ samplingRankMinimum A γ r) →
        ∃ g : G.Point, PhilipponMultiplicity.translate g A.carrier ⊆ zeroLocusOnGroup G P  := by
  exact Corollary23Proof.combine_cases G
    (Corollary23Proof.positive_degrees K hK G hdisjoint)
    (corollary_2_3_zero_degree_boundary K hK G hdisjoint)

