-- Prove2me | solution 1 for PhilipponMultiplicity.normalized_affine_chart_domain_and_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T10:24:01.763695+00:00
-- url     : https://prove2.me/submissions/69792994-6814-48df-b40f-4311cce81112

import Theorems.Thm_PhilipponMultiplicity_normalized_affine_chart_dimension
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Mathlib


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

theorem isHomogeneous_zero (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) :
    M.IsHomogeneous 0 D := by simp [IsHomogeneous]

theorem isHomogeneous_sum (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) D) :
    M.IsHomogeneous (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_zero D
  | @insert i s hi ih =>
    simp only [Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).add M (ih (fun j hj => hP j (by simp [hj])))

theorem isHomogeneous_prod (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : ι → M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) (D i)) :
    M.IsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_one
  | @insert i s hi ih =>
    simp only [Finset.prod_insert, Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).mul M (ih (fun j hj => hP j (by simp [hj])))

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


end PhilipponMultiplicity.MultiProjectiveSpace
namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem prime_of_homogeneous_products (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hne : I ≠ ⊤)
    (hmul : ∀ P Q : M.CoordinateRing, (∃ D, M.IsHomogeneous P D) →
      (∃ E, M.IsHomogeneous Q E) → P * Q ∈ I → P ∈ I ∨ Q ∈ I) : I.IsPrime := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply]
    have heq : weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (ofLex d) f := by
      ext e
      simp only [coeff_weightedHomogeneousComponent]
      rfl
    rw [heq]
    exact hI f hf (ofLex d)
  apply hIg.isPrime_of_homogeneous_mem_or_mem hne
  rintro P Q ⟨D, hP⟩ ⟨E, hQ⟩ hPQ
  apply hmul P Q _ _ hPQ
  · exact ⟨ofLex D, (M.degreePiece_iff P (ofLex D)).mp hP⟩
  · exact ⟨ofLex E, (M.degreePiece_iff Q (ofLex E)).mp hQ⟩


end PhilipponMultiplicity.Hilbert
namespace PhilipponMultiplicity

theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [M.blockWeight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

variable {K : Type*} [Field K]

theorem MultiProjectiveSpace.vanishingIdeal_isPrime_of_isIrreducible
    (M : MultiProjectiveSpace K) (S : Set M.Point)
    (hS : @IsIrreducible _ M.zariskiTopology S) : (M.vanishingIdeal S).IsPrime := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  apply Hilbert.prime_of_homogeneous_products M _ (vanishingIdeal_multihomogeneous K M S)
  · intro htop
    obtain ⟨x,hx⟩ := hS.nonempty
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal
      (show (1 : M.CoordinateRing) ∈ M.vanishingIdeal S by rw [htop]; trivial) hx
    exact one_ne_zero (by simpa only [MultiProjectiveSpace.eval,map_one] using hz)
  · rintro P Q ⟨D,hP⟩ ⟨E,hQ⟩ hPQ
    by_contra! hn
    have hnzero (R : M.CoordinateRing) (d : M.FactorIndex → ℕ)
        (hR : M.IsHomogeneous R d) (hRI : R ∉ M.vanishingIdeal S) :
        (S ∩ {x | M.eval R x ≠ 0}).Nonempty := by
      by_contra hz
      apply hRI
      exact Ideal.subset_span ⟨⟨d,hR⟩,fun x hx => by
        by_contra hxR
        exact hz ⟨x,hx,hxR⟩⟩
    obtain ⟨x,hx,hxP,hxQ⟩ := hS.2 _ _ (M.isOpen_basic P D hP)
      (M.isOpen_basic Q E hQ) (hnzero P D hP hn.1) (hnzero Q E hQ hn.2)
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal hPQ hx
    exact (mul_ne_zero hxP hxQ) (by simpa only [MultiProjectiveSpace.eval,map_mul] using hz)


end PhilipponMultiplicity

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AffineChartDomain
universe u v
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)

/-- Homogeneous scaling works over an arbitrary coefficient extension. -/
theorem eval₂_block_scale {A : Type v} [CommRing A] (f : K →+* A)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → A) (a : M.FactorIndex → A) :
    eval₂Hom f (fun j => a j.1 * v j) P =
      (∏ i, a i ^ D i) * eval₂Hom f v P := by
  classical
  simp only [coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i,j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring

/-- Padding by pivot powers gives equality in every normalized algebra,
including the chart quotient itself, not just on field-valued points. -/
theorem exists_homogenization
    (P : M.CoordinateRing) (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) :
    ∃ H : M.CoordinateRing, ∃ D : M.FactorIndex → ℕ, M.IsHomogeneous H D ∧
      ∀ (A : Type u) [CommRing A] (f : M.CoordinateRing →+* A),
        (∀ i, f (X (⟨i,b i⟩ : M.Variable)) = 1) → f H = f P := by
  classical
  let a (m : M.Variable →₀ ℕ) (i : M.FactorIndex) :=
    ∑ k : Fin (M.ambientDimension i + 1), m ⟨i,k⟩
  let D (i : M.FactorIndex) := ∑ m ∈ P.support, a m i
  have hbound (m) (hm : m ∈ P.support) (i) : a m i ≤ D i :=
    Finset.single_le_sum (fun n _ => Nat.zero_le (a n i)) hm
  let T (m : M.Variable →₀ ℕ) : M.CoordinateRing :=
    monomial m (coeff m P) * ∏ i, X (⟨i,b i⟩ : M.Variable) ^ (D i - a m i)
  refine ⟨∑ m ∈ P.support, T m, D, ?_, ?_⟩
  · apply M.isHomogeneous_sum
    intro m hm
    have hmon : M.IsHomogeneous (monomial m (coeff m P)) (a m) := by
      intro n hn i
      have hn' : n = m := Finset.mem_singleton.mp (support_monomial_subset hn)
      subst n
      rfl
    have hpowers := M.isHomogeneous_prod Finset.univ
      (fun i => X (⟨i,b i⟩ : M.Variable) ^ (D i - a m i))
      (fun i k => (D i - a m i) * (if k = i then 1 else 0))
      (fun i _ => (M.isHomogeneous_X ⟨i,b i⟩).pow M (D i - a m i))
    have hdeg : a m + (∑ i : M.FactorIndex,
        fun k => (D i - a m i) * (if k = i then 1 else 0)) = D := by
      funext i
      simp only [Pi.add_apply, Finset.sum_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact Nat.add_sub_of_le (hbound m hm i)
    rw [← hdeg]
    exact hmon.mul M hpowers
  · intro A _ f hf
    rw [map_sum]
    calc
      ∑ m ∈ P.support, f (T m) =
          ∑ m ∈ P.support, f (monomial m (coeff m P)) := by
        apply Finset.sum_congr rfl
        intro m _
        simp [T, map_prod, hf]
      _ = f P := by rw [← map_sum, support_sum_monomial_coeff]

theorem normalization_relations_le_ker {A : Type v} [CommRing A]
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (f : M.CoordinateRing →+* A) (hf : ∀ i, f (X (⟨i,b i⟩ : M.Variable)) = 1) :
    Ideal.span (Set.range (fun i : M.FactorIndex =>
      (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)) ≤ RingHom.ker f := by
  apply Ideal.span_le.mpr
  rintro P ⟨i,rfl⟩
  change f (X (⟨i,b i⟩ : M.Variable) - 1) = 0
  rw [map_sub, map_one, hf i, sub_self]

/-- Normalization embeds a nontrivial chart into the fraction field of the
homogeneous prime quotient. No algebraic-closedness assumption is needed. -/
theorem normalized_chart_isDomain (W : Set M.Point)
    (hirr : @IsIrreducible _ M.zariskiTopology W)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    [Nontrivial (M.CoordinateRing ⧸
      (M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
        (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))))] :
    IsDomain (M.CoordinateRing ⧸
      (M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
        (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)))) := by
  classical
  let I := M.vanishingIdeal W
  let J := I ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
    (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))
  let S := M.CoordinateRing ⧸ J
  let q : M.CoordinateRing →+* S := Ideal.Quotient.mk J
  have hq (i) : q (X (⟨i,b i⟩ : M.Variable)) = 1 := by
    have hz : q ((X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((le_sup_right : Ideal.span _ ≤ J) (Ideal.subset_span ⟨i,rfl⟩))
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  letI : I.IsPrime := M.vanishingIdeal_isPrime_of_isIrreducible W hirr
  let R := M.CoordinateRing ⧸ I
  letI : IsDomain R := inferInstance
  let F := FractionRing R
  letI : Field F := inferInstance
  let f : M.CoordinateRing →+* F := (algebraMap R F).comp (Ideal.Quotient.mk I)
  have hf (P : M.CoordinateRing) : f P = 0 ↔ P ∈ I := by
    change algebraMap R F (Ideal.Quotient.mk I P) = 0 ↔ P ∈ I
    rw [map_eq_zero_iff _ (IsFractionRing.injective R F), Ideal.Quotient.eq_zero_iff_mem]
  have hpivot (i) : f (X (⟨i,b i⟩ : M.Variable)) ≠ 0 := by
    intro hz
    have hzq : q (X (⟨i,b i⟩ : M.Variable)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((le_sup_left : I ≤ J) ((hf _).mp hz))
    exact one_ne_zero ((hq i).symm.trans hzq)
  let a (i : M.FactorIndex) : F := (f (X (⟨i,b i⟩ : M.Variable)))⁻¹
  let φ : M.CoordinateRing →+* F := eval₂Hom (f.comp C) (fun j => a j.1 * f (X j))
  have hself : eval₂Hom (f.comp C) (fun j => f (X j)) = f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro j
      simp
  have hφhom (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
      (hP : M.IsHomogeneous P D) : φ P = (∏ i, a i ^ D i) * f P := by
    have h := eval₂_block_scale M (f.comp C) P D hP (fun j => f (X j)) a
    rw [hself] at h
    exact h
  have hφpivot (i) : φ (X (⟨i,b i⟩ : M.Variable)) = 1 := by
    dsimp only [φ]
    rw [eval₂Hom_X']
    change (f (X (⟨i,b i⟩ : M.Variable)))⁻¹ * f (X (⟨i,b i⟩ : M.Variable)) = 1
    exact inv_mul_cancel₀ (hpivot i)
  have hI : I ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro P ⟨⟨D,hP⟩, hz⟩
    change φ P = 0
    rw [hφhom P D hP, (hf P).mpr (Ideal.subset_span ⟨⟨D,hP⟩,hz⟩), mul_zero]
  have hJ : J ≤ RingHom.ker φ := by
    exact sup_le hI (normalization_relations_le_ker M b φ hφpivot)
  have hker : RingHom.ker φ ≤ J := by
    intro P hP
    change φ P = 0 at hP
    obtain ⟨H,D,hH,heq⟩ := exists_homogenization M P b
    have hφH : φ H = 0 := (heq F φ hφpivot).trans hP
    rw [hφhom H D hH] at hφH
    have ha : (∏ i, a i ^ D i) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact pow_ne_zero _ (inv_ne_zero (hpivot i))
    have hHI : H ∈ I := (hf H).mp ((mul_eq_zero.mp hφH).resolve_left ha)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q P = 0
    rw [← heq S q hq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((le_sup_left : I ≤ J) hHI)
  exact (RingHom.lift_injective_of_ker_le_ideal J (fun P hP => hJ hP) hker).isDomain _

end PhilipponMultiplicity.AffineChartDomain

end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
universe u

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem affine_chart_domain_and_dimension_of_dimension
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hdimension : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        let S := M.CoordinateRing ⧸
          (M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)))
        Nontrivial S → ringKrullDim S = locusDimension M W) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        let S := M.CoordinateRing ⧸
          (M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)))
        Nontrivial S → IsDomain S ∧ ringKrullDim S = locusDimension M W := by
  intro M W hW hirr b
  dsimp only
  intro hnon
  letI := hnon
  exact ⟨AffineChartDomain.normalized_chart_isDomain M W hirr b,
    hdimension M W hW hirr b hnon⟩

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology
attribute [local instance] MvPolynomial.algebraMvPolynomial
universe u

theorem solution
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        let S := M.CoordinateRing ⧸
          (M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)))
        Nontrivial S → IsDomain S ∧ ringKrullDim S = locusDimension M W := by
  exact affine_chart_domain_and_dimension_of_dimension K hK
    (normalized_affine_chart_dimension K hK)
