-- Prove2me | solution 1 for PhilipponMultiplicity.exists_open_preserving_open_mixed_slices
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T15:32:08.48349+00:00
-- url     : https://prove2.me/submissions/d72debca-2c72-453d-9833-243049de9169

import Theorems.Thm_Algebra_exists_open_simultaneous_rational_specialization
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
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

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isClosed_zeroLocus_vanishingIdeal (S : Set M.Point) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus (M.vanishingIdeal S)) := by
  letI := M.zariskiTopology
  have hset : M.zeroLocus (M.vanishingIdeal S) =
      ⋂ P : {P : M.CoordinateRing // (∃ D, M.IsHomogeneous P D) ∧
        ∀ x ∈ S, M.eval P x = 0}, {x | M.eval P.val x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, zeroLocus]
    constructor
    · intro hx P
      exact hx P (Ideal.subset_span P.property)
    · intro hx P hP
      have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
        apply Ideal.span_le.mpr
        intro Q hQ
        exact hx ⟨Q, hQ⟩
      exact hle hP
  rw [hset]
  apply isClosed_iInter
  intro P
  obtain ⟨D, hD⟩ := P.property.1
  exact M.isClosed_zero P.val D hD

/-- The chosen-representative ideal agrees with Zariski closure. -/
theorem zeroLocus_vanishingIdeal_eq_closure (S : Set M.Point) :
    M.zeroLocus (M.vanishingIdeal S) = @closure _ M.zariskiTopology S := by
  letI := M.zariskiTopology
  apply Set.Subset.antisymm
  · intro x hx
    apply M.isTopologicalBasis_basic.mem_closure_iff.mpr
    rintro U ⟨P, D, hP, rfl⟩ hxU
    by_contra hn
    have hPS : ∀ y ∈ S, M.eval P y = 0 := by
      intro y hy
      by_contra hp
      exact hn ⟨y, hp, hy⟩
    exact hxU (hx P (Ideal.subset_span ⟨⟨D, hP⟩, hPS⟩))
  · apply closure_minimal
    · intro x hx P hP
      exact M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact M.isClosed_zeroLocus_vanishingIdeal S


end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
theorem MultiProjectiveSpace.eval_block_scale {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → K) (a : M.FactorIndex → K) :
    MvPolynomial.eval (fun j => a j.1 * v j) P = (∏ i, a i ^ D i) * MvPolynomial.eval v P := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i, j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring

theorem MultiProjectiveSpace.eval_eq_zero_iff_of_lift
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (p : M.Point)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval v P = 0 ↔ M.eval P p = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K))]
  exact mul_eq_zero.trans (or_iff_right hne)

theorem IsPhilipponBaseField.isAlgClosed {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : IsAlgClosed K := by
  have transfer (L : Type) [Field L] [IsAlgClosed L] (e : K ≃+* L) : IsAlgClosed K := by
    apply IsAlgClosed.of_exists_root K
    intro P _ hP
    obtain ⟨x,hx⟩ := IsAlgClosed.exists_eval₂_eq_zero e.toRingHom P
      (ne_of_gt (Polynomial.degree_pos_of_irreducible hP))
    refine ⟨e.symm x,?_⟩
    apply e.injective
    rw [map_zero]
    change e.toRingHom (P.eval (e.symm x)) = 0
    rw [← Polynomial.eval₂_at_apply]
    change P.eval₂ e.toRingHom (e (e.symm x)) = 0
    simpa only [RingEquiv.apply_symm_apply] using hx
  rcases hK with ⟨e,_⟩ | ⟨p,hp,h⟩
  · exact transfer ℂ e
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e,_⟩ := h
    exact transfer (PadicComplex p) e


end PhilipponMultiplicity

namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem rowForm_homogeneous (b : M.FactorIndex) (a : M.Variable → K) :
    M.IsHomogeneous (rowForm M b a) (Pi.single b 1) := by
  classical
  intro m hm i
  change m ∈ (∑ t : Fin (M.ambientDimension b + 1),
    a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)).support at hm
  have hs := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun t : Fin (M.ambientDimension b + 1) =>
      a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)) hm
  obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hs
  have hmX : m ∈ (MvPolynomial.X (⟨b,t⟩ : M.Variable) : M.CoordinateRing).support :=
    MvPolynomial.support_smul ht
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hmX
  subst m
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff, Pi.single_apply]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b,t⟩ : M.Variable) ≠ ⟨i,k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, Pi.single_apply, hi, hn]

theorem polynomial_homogeneous (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (j : Fin l.length) :
    M.IsHomogeneous (polynomial M l c j) (Pi.single l[j] 1) :=
  rowForm_homogeneous M l[j] (c j)


end PhilipponMultiplicity.MixedFlag
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity.MixedFamily
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) (H : M.CoordinateRing)

/-- Original coordinate functions on the universal normalized chart. -/
def coordinate (j : M.Variable) : CoordinateRing M W l b H :=
  Ideal.Quotient.mk (ideal M W l b H) (fixed M l (X j))

theorem coordinate_pivot (i : M.FactorIndex) :
    coordinate M W l b H ⟨i,b i⟩ = 1 := by
  apply sub_eq_zero.mp
  rw [coordinate, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    ← map_one (fixed M l), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_sup_left
  apply Ideal.mem_sup_right
  apply Ideal.mem_map_of_mem
  exact Ideal.subset_span (Set.mem_range_self i)

/-- Evaluation through an arbitrary rational point agrees with polynomial
substitution into its original coordinate functions. -/
theorem eval_coordinate (e : CoordinateRing M W l b H →ₐ[K] K)
    (P : M.CoordinateRing) :
    MvPolynomial.eval (fun j => e (coordinate M W l b H j)) P =
      e (Ideal.Quotient.mk (ideal M W l b H) (fixed M l P)) := by
  have he : MvPolynomial.eval (fun j => e (coordinate M W l b H j)) =
      e.toRingHom.comp ((Ideal.Quotient.mk (ideal M W l b H)).comp (fixed M l)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval_C]
      change a = e (Ideal.Quotient.mk (ideal M W l b H) (fixed M l (C a)))
      have hconst : fixed M l (C a) = algebraMap K (TotalPolynomial M l) a := by
        simp only [fixed, RingHom.comp_apply, MvPolynomial.algebraMap_apply,
          Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
      rw [hconst]
      exact (e.commutes a).symm
    · intro j
      rw [MvPolynomial.eval_X]
      rfl
  exact RingHom.congr_fun he P

theorem eval_coordinate_vanishing (e : CoordinateRing M W l b H →ₐ[K] K)
    (P : M.CoordinateRing) (hP : P ∈ M.vanishingIdeal W) :
    MvPolynomial.eval (fun j => e (coordinate M W l b H j)) P = 0 := by
  rw [eval_coordinate]
  have hmem : fixed M l P ∈ ideal M W l b H :=
    Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_sup_left
      (Ideal.mem_map_of_mem _ hP)))
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]

set_option maxHeartbeats 60000 in
theorem eval_coordinate_row (c : Fin l.length → M.Variable → K)
    (e : CoordinateRing M W l b H →ₐ[K] K)
    (he : ∀ P : ParameterRing M l,
      e (algebraMap (ParameterRing M l) (CoordinateRing M W l b H) P) =
        MvPolynomial.eval (Function.uncurry c) P)
    (j : Fin l.length) :
    MvPolynomial.eval (fun v => e (coordinate M W l b H v))
      (MixedFlag.polynomial M l c j) = 0 := by
  have hmem : row M l j ∈ ideal M W l b H := by
    apply Ideal.mem_sup_left
    apply Ideal.mem_sup_left
    apply Ideal.mem_sup_right
    have hle : Ideal.span {row M l j} ≤
        ⨆ (k : Fin l.length) (_ : k.val < l.length), Ideal.span {row M l k} :=
      le_iSup_of_le j (le_iSup_of_le j.isLt le_rfl)
    exact hle (Ideal.subset_span (Set.mem_singleton _))
  have hz : e (Ideal.Quotient.mk (ideal M W l b H) (row M l j)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  have hpar (v : M.Variable) :
      e (Ideal.Quotient.mk (ideal M W l b H) (MvPolynomial.X (j,v))) = c j v := by
    have hp := he (X (j,v))
    change e (Ideal.Quotient.mk (ideal M W l b H)
      (algebraMap (ParameterRing M l) (TotalPolynomial M l) (X (j,v)))) = _ at hp
    rwa [MvPolynomial.algebraMap_def, MvPolynomial.map_X, MvPolynomial.eval_X] at hp
  change (MvPolynomial.eval (fun v => e (coordinate M W l b H v)))
    (∑ t : Fin (M.ambientDimension l[j] + 1), c j ⟨l[j],t⟩ • (X ⟨l[j],t⟩ : M.CoordinateRing)) = 0
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  simpa only [row, map_sum, map_mul, hpar, coordinate] using hz

/-- A rational point of the original chart gives a point of the actual
projective mixed section, with no radicalization or additional presentation. -/
theorem exists_projective_point (hW : @IsClosed _ M.zariskiTopology W)
    (c : Fin l.length → M.Variable → K)
    (e : CoordinateRing M W l b H →ₐ[K] K)
    (he : ∀ P : ParameterRing M l,
      e (algebraMap (ParameterRing M l) (CoordinateRing M W l b H) P) =
        MvPolynomial.eval (Function.uncurry c) P) :
    ∃ x : M.Point,
      (∀ i, ∃ hn : (fun j => e (coordinate M W l b H ⟨i,j⟩)) ≠ 0,
        Projectivization.mk K (fun j => e (coordinate M W l b H ⟨i,j⟩)) hn = x i) ∧
      x ∈ W ∧ ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0 := by
  letI := M.zariskiTopology
  let v : M.Variable → K := fun j => e (coordinate M W l b H j)
  have hb (i : M.FactorIndex) : v ⟨i,b i⟩ = 1 := by
    simp [v, coordinate_pivot]
  have hn (i : M.FactorIndex) : (fun j => v ⟨i,j⟩) ≠ 0 := by
    intro h
    have := congrFun h (b i)
    simp only [hb, Pi.zero_apply] at this
    exact one_ne_zero this
  let x : M.Point := fun i => Projectivization.mk K (fun j => v ⟨i,j⟩) (hn i)
  have hrep : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i := fun i => ⟨hn i,rfl⟩
  refine ⟨x,hrep,?_,?_⟩
  · have hx : x ∈ M.zeroLocus (M.vanishingIdeal W) := by
      have hle : M.vanishingIdeal W ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
        apply Ideal.span_le.mpr
        rintro P ⟨⟨D,hD⟩,hz⟩
        exact (M.eval_eq_zero_iff_of_lift x v hrep P D hD).mp
          (eval_coordinate_vanishing M W l b H e P (Ideal.subset_span ⟨⟨D,hD⟩,hz⟩))
      exact hle
    rwa [M.zeroLocus_vanishingIdeal_eq_closure, hW.closure_eq] at hx
  · intro j
    exact (M.eval_eq_zero_iff_of_lift x v hrep _ _
      (MixedFlag.polynomial_homogeneous M l c j)).mp
      (eval_coordinate_row M W l b H c e he j)

end PhilipponMultiplicity.MixedFamily
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ConfigurationSeparation
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Proportional representatives have zero two-by-two minors. -/
theorem cross_eq_zero (v w : M.Variable → K) (x y : M.Point)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i)
    (hw : ∀ i, ∃ h : (fun j => w ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => w ⟨i,j⟩) h = y i)
    (hxy : x = y) (i : M.FactorIndex)
    (j k : Fin (M.ambientDimension i + 1)) :
    v ⟨i,j⟩ * w ⟨i,k⟩ - v ⟨i,k⟩ * w ⟨i,j⟩ = 0 := by
  obtain ⟨hv,hev⟩ := hv i
  obtain ⟨hw,hew⟩ := hw i
  have heq := hev.trans ((congrFun hxy i).trans hew.symm)
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ hv hw).mp heq
  have hj : v ⟨i,j⟩ = (a : K) * w ⟨i,j⟩ := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  have hk : v ⟨i,k⟩ = (a : K) * w ⟨i,k⟩ := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm
  rw [hj,hk]
  ring

/-- Distinct multiprojective points differ by a nonzero coordinate minor,
even when their representatives use different normalizing pivots. -/
theorem exists_cross_ne (v w : M.Variable → K) (x y : M.Point)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i)
    (hw : ∀ i, ∃ h : (fun j => w ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => w ⟨i,j⟩) h = y i)
    (hxy : x ≠ y) :
    ∃ i : M.FactorIndex, ∃ j k : Fin (M.ambientDimension i + 1),
      v ⟨i,j⟩ * w ⟨i,k⟩ - v ⟨i,k⟩ * w ⟨i,j⟩ ≠ 0 := by
  classical
  by_contra! h
  apply hxy
  funext i
  obtain ⟨hv,hev⟩ := hv i
  obtain ⟨hw,hew⟩ := hw i
  obtain ⟨k,hk⟩ := Function.ne_iff.mp hw
  change w ⟨i,k⟩ ≠ 0 at hk
  rw [← hev, ← hew]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨v ⟨i,k⟩ / w ⟨i,k⟩, ?_⟩
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hk).mpr
  exact (sub_eq_zero.mp (h i j k)).symm

/-- A single polynomial in a finite family of affine coordinate algebras
certifies pairwise distinctness after every simultaneous specialization. -/
theorem exists_separating_polynomial {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)]
    (z : ∀ i, M.Variable → R i) (e₀ : ∀ i, R i →ₐ[K] K)
    (x : ι ↪ M.Point)
    (hrep : ∀ s i, ∃ h : (fun j => e₀ s (z s ⟨i,j⟩)) ≠ 0,
      Projectivization.mk K (fun j => e₀ s (z s ⟨i,j⟩)) h = x s i) :
    ∃ P : MvPolynomial (Σ i, R i) K,
      MvPolynomial.eval (fun t => e₀ t.1 t.2) P ≠ 0 ∧
      ∀ (e : ∀ i, R i →ₐ[K] K) (y : ι → M.Point),
        (∀ s i, ∃ h : (fun j => e s (z s ⟨i,j⟩)) ≠ 0,
          Projectivization.mk K (fun j => e s (z s ⟨i,j⟩)) h = y s i) →
        MvPolynomial.eval (fun t => e t.1 t.2) P ≠ 0 → Function.Injective y := by
  classical
  letI := Fintype.ofFinite ι
  let Pairs := {p : ι × ι // p.1 ≠ p.2}
  have hsep (p : Pairs) :
      ∃ i : M.FactorIndex, ∃ j k : Fin (M.ambientDimension i + 1),
        e₀ p.val.1 (z p.val.1 ⟨i,j⟩) * e₀ p.val.2 (z p.val.2 ⟨i,k⟩) -
        e₀ p.val.1 (z p.val.1 ⟨i,k⟩) * e₀ p.val.2 (z p.val.2 ⟨i,j⟩) ≠ 0 :=
    exists_cross_ne M (fun v => e₀ p.val.1 (z p.val.1 v))
      (fun v => e₀ p.val.2 (z p.val.2 v)) _ _ (hrep p.val.1) (hrep p.val.2)
      (fun h => p.property (x.injective h))
  choose i j k hne using hsep
  let Q (p : Pairs) : MvPolynomial (Σ s, R s) K :=
    X ⟨p.val.1, z p.val.1 ⟨i p,j p⟩⟩ * X ⟨p.val.2, z p.val.2 ⟨i p,k p⟩⟩ -
    X ⟨p.val.1, z p.val.1 ⟨i p,k p⟩⟩ * X ⟨p.val.2, z p.val.2 ⟨i p,j p⟩⟩
  refine ⟨∏ p : Pairs, Q p, ?_, ?_⟩
  · rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    simpa only [Q, map_sub, map_mul, eval_X] using hne p
  · intro e y hy hP s t hst
    by_contra hne'
    let p : Pairs := ⟨(s,t),hne'⟩
    have hQ : MvPolynomial.eval (fun t => e t.1 t.2) (Q p) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hP)) p (Finset.mem_univ p)
    apply hQ
    simpa only [Q, map_sub, map_mul, eval_X] using
      cross_eq_zero M (fun v => e s (z s v)) (fun v => e t (z t v))
        (y s) (y t) (hy s) (hy t) hst (i p) (j p) (k p)

end PhilipponMultiplicity.ConfigurationSeparation
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport
universe u

theorem mixed_point_persistence_of_simultaneous_specialization
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hspecialize : ∀
    (σ : Type) (ι : Type u) [Finite σ] [Finite ι]
    (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)]
    [∀ i, Algebra (MvPolynomial σ K) (R i)]
    [∀ i, IsScalarTower K (MvPolynomial σ K) (R i)]
    [∀ i, Algebra.FiniteType (MvPolynomial σ K) (R i)]
    (hopen : ∀ i, IsOpenMap
      (PrimeSpectrum.comap (algebraMap (MvPolynomial σ K) (R i))))
    (hquasi : ∀ i, Algebra.QuasiFinite (MvPolynomial σ K) (R i))
    (c₀ : σ → K) (e₀ : ∀ i, R i →ₐ[K] K)
    (h₀ : ∀ i (Q : MvPolynomial σ K),
      e₀ i (algebraMap (MvPolynomial σ K) (R i) Q) = MvPolynomial.eval c₀ Q)
    (P : MvPolynomial (Σ i, R i) K)
    (hP : MvPolynomial.eval (fun t => e₀ t.1 t.2) P ≠ 0),
    ∃ U : Set (PrimeSpectrum (MvPolynomial σ K)), IsOpen U ∧
      MvPolynomial.pointToPoint (k := K) c₀ ∈ U ∧
      ∀ c : σ → K, MvPolynomial.pointToPoint (k := K) c ∈ U →
        ∃ e : ∀ i, R i →ₐ[K] K,
          (∀ i (Q : MvPolynomial σ K),
            e i (algebraMap (MvPolynomial σ K) (R i) Q) = MvPolynomial.eval c Q) ∧
          MvPolynomial.eval (fun t => e t.1 t.2) P ≠ 0) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∃ e : MixedFamily.CoordinateRing M W l b H →ₐ[K] K,
              (∀ P : M.CoordinateRing,
                e (Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (MixedFamily.fixed M l P)) =
                  MvPolynomial.eval v P) ∧
              (∀ P : MixedFamily.ParameterRing M l,
                e (algebraMap (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H) P) =
                  MvPolynomial.eval (Function.uncurry c₀) P) ∧
              ∃ f : MixedFamily.CoordinateRing M W l b H,
                e f ≠ 0 ∧
                IsOpenMap (PrimeSpectrum.comap (algebraMap (MixedFamily.ParameterRing M l)
                  (Localization.Away f))) ∧
                Algebra.QuasiFinite (MixedFamily.ParameterRing M l) (Localization.Away f)) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  classical
  letI : IsAlgClosed K := hK.isAlgClosed
  intro M W hW _ α _ _ l _ c₀ S hS _ hcharts
  letI : Fintype S := hS.fintype
  choose b v hb hrep H a ha e hev hec f hef hopen hquasi using
    (fun x : S => hcharts x.val x.property)
  let R (x : S) := Localization.Away (f x)
  letI : ∀ x : S, CommRing (R x) := fun x => inferInstance
  letI : ∀ x : S, Algebra K (R x) := fun x => inferInstance
  letI : ∀ x : S, Algebra (MixedFamily.ParameterRing M l) (R x) := fun x => inferInstance
  letI : ∀ x : S, IsScalarTower K (MixedFamily.ParameterRing M l) (R x) :=
    fun x => inferInstance
  letI : ∀ x : S, Algebra.FiniteType (MixedFamily.ParameterRing M l) (R x) := by
    intro x
    haveI : Algebra.FiniteType (MixedFamily.ParameterRing M l)
        (MixedFamily.CoordinateRing M W l (b x) (H x)) :=
      Algebra.FiniteType.of_restrictScalars_finiteType K _ _
    dsimp [R]
    infer_instance
  let e₀ (x : S) : R x →ₐ[K] K :=
    IsLocalization.Away.liftAlgHom (f x) (isUnit_iff_ne_zero.mpr (hef x))
  let z (x : S) (j : M.Variable) : R x :=
    algebraMap (MixedFamily.CoordinateRing M W l (b x) (H x)) (R x)
      (MixedFamily.coordinate M W l (b x) (H x) j)
  have hez (x : S) (j : M.Variable) : e₀ x (z x j) = v x j := by
    change IsLocalization.Away.lift (f x) (isUnit_iff_ne_zero.mpr (hef x))
      (algebraMap (MixedFamily.CoordinateRing M W l (b x) (H x)) (R x)
        (MixedFamily.coordinate M W l (b x) (H x) j)) = _
    rw [IsLocalization.Away.lift_eq]
    exact (hev x (MvPolynomial.X j)).trans (MvPolynomial.eval_X _)
  have he₀ (x : S) (Q : MixedFamily.ParameterRing M l) :
      e₀ x (algebraMap (MixedFamily.ParameterRing M l) (R x) Q) =
        MvPolynomial.eval (Function.uncurry c₀) Q := by
    rw [IsScalarTower.algebraMap_apply (MixedFamily.ParameterRing M l)
      (MixedFamily.CoordinateRing M W l (b x) (H x)) (R x)]
    change IsLocalization.Away.lift (f x) (isUnit_iff_ne_zero.mpr (hef x)) (algebraMap _ _ _) = _
    rw [IsLocalization.Away.lift_eq]
    exact hec x Q
  have hrep₀ (x : S) (i : M.FactorIndex) :
      ∃ hn : (fun j => e₀ x (z x ⟨i,j⟩)) ≠ 0,
        Projectivization.mk K (fun j => e₀ x (z x ⟨i,j⟩)) hn = x.val i := by
    simpa only [hez] using hrep x i
  obtain ⟨P,hP,hsep⟩ := ConfigurationSeparation.exists_separating_polynomial
    M R z e₀ (Function.Embedding.subtype S) hrep₀
  obtain ⟨U,hU,h₀,hgood⟩ := hspecialize (Fin l.length × M.Variable) S R
    hopen hquasi (Function.uncurry c₀) e₀ he₀ P hP
  refine ⟨U,hU,h₀,?_⟩
  intro c hc
  obtain ⟨e',he',hP'⟩ := hgood (Function.uncurry c) hc
  let e'' (x : S) : MixedFamily.CoordinateRing M W l (b x) (H x) →ₐ[K] K :=
    (e' x).comp (IsScalarTower.toAlgHom K _ (R x))
  have he'' (x : S) (Q : MixedFamily.ParameterRing M l) :
      e'' x (algebraMap (MixedFamily.ParameterRing M l)
        (MixedFamily.CoordinateRing M W l (b x) (H x)) Q) =
        MvPolynomial.eval (Function.uncurry c) Q := by
    change e' x (algebraMap _ (R x) (algebraMap _ _ Q)) = _
    rw [← IsScalarTower.algebraMap_apply]
    exact he' x Q
  choose y hyrep hyW hycut using fun x : S =>
    MixedFamily.exists_projective_point M W l (b x) (H x) hW c (e'' x) (he'' x)
  have hinj : Function.Injective y := hsep e' y (by
    intro x i
    exact hyrep x i) hP'
  exact ⟨⟨fun x => ⟨y x,hyW x,hycut x⟩, fun x y h => hinj (congrArg Subtype.val h)⟩⟩

end PhilipponMultiplicity
end

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∃ e : MixedFamily.CoordinateRing M W l b H →ₐ[K] K,
              (∀ P : M.CoordinateRing,
                e (Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (MixedFamily.fixed M l P)) =
                  MvPolynomial.eval v P) ∧
              (∀ P : MixedFamily.ParameterRing M l,
                e (algebraMap (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H) P) =
                  MvPolynomial.eval (Function.uncurry c₀) P) ∧
              ∃ f : MixedFamily.CoordinateRing M W l b H,
                e f ≠ 0 ∧
                IsOpenMap (PrimeSpectrum.comap (algebraMap (MixedFamily.ParameterRing M l)
                  (Localization.Away f))) ∧
                Algebra.QuasiFinite (MixedFamily.ParameterRing M l) (Localization.Away f)) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  letI : IsAlgClosed K := hK.isAlgClosed
  exact mixed_point_persistence_of_simultaneous_specialization K hK
    (Algebra.exists_open_simultaneous_rational_specialization K)
