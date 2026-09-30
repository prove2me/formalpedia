-- Prove2me | solution 1 for PhilipponMultiplicity.group_has_regular_homogeneous_representative
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-29T11:14:58.736599+00:00
-- url     : https://prove2.me/submissions/1cfdd692-8690-4858-a5c1-872c98510cf4

import Definitions.Def_P2M_Util
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

section
-- Implementation: Solutions/PhilipponProjectiveGeometry.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

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

theorem vanishingIdeal_antitone {S T : Set M.Point} (h : S ⊆ T) :
    M.vanishingIdeal T ≤ M.vanishingIdeal S := by
  apply Ideal.span_mono
  rintro P ⟨hP, hz⟩
  exact ⟨hP, fun x hx => hz x (h hx)⟩

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

end MultiProjectiveSpace
end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponPointHilbert.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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
end
end


section
-- Implementation: Solutions/PhilipponProjectiveContact.lean


set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

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

end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponAdditiveSubgroups.lean

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

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

end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponProjectiveNullstellensatz.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The multigraded and homogeneous-generator formulations agree. -/
theorem homogeneousIdeal_eq_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : M.IsHomogeneousIdeal I := by
  classical
  apply le_antisymm
  · intro P hP
    let w := Hilbert.blockWeight M.factorCount M.ambientDimension
    rw [← sum_weightedHomogeneousComponent w P,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) P)]
    apply Ideal.sum_mem
    intro D _
    exact Ideal.subset_span ⟨hI P hP D, D,
      (M.degreePiece_iff _ D).mp (weightedHomogeneousComponent_mem w P D)⟩
  · exact Ideal.span_le.mpr (fun _ h => h.1)

theorem homogeneousIdeal_le_vanishingIdeal_zeroLocus (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : I ≤ M.vanishingIdeal (M.zeroLocus I) := by
  nth_rw 1 [M.homogeneousIdeal_eq_span I hI]
  apply Ideal.span_le.mpr
  rintro P ⟨hP, D, hD⟩
  exact Ideal.subset_span ⟨⟨D, hD⟩, fun x hx => hx P hP⟩

theorem mem_zeroLocus_iff_homogeneous (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (x : M.Point) :
    x ∈ M.zeroLocus I ↔
      ∀ P ∈ I, ∀ D, M.IsHomogeneous P D → M.eval P x = 0 := by
  constructor
  · exact fun h P hP _ _ => h P hP
  · intro h
    have hle : I ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
      rw [M.homogeneousIdeal_eq_span I hI]
      exact Ideal.span_le.mpr (by rintro P ⟨hP,D,hD⟩; exact h P hP D hD)
    exact fun P hP => hle hP

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Implementation: Solutions/PhilipponProjectiveHilbertExistence.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

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

end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponGroupReduced.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Radical preserves the actual block multigrading. -/
theorem Hilbert.radical_multihomogeneous (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : IsMultihomogeneousIdeal M I.radical := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (Hilbert.blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hproj (f : M.CoordinateRing) (d : Lex (M.FactorIndex → ℕ)) :
      weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (Hilbert.blockWeight M.factorCount M.ambientDimension)
          (ofLex d) f := by
    ext e
    simp only [coeff_weightedHomogeneousComponent]
    rfl
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply, hproj]
    exact hI f hf (ofLex d)
  intro f hf d
  have h := weightedHomogeneousComponent_mem_of_mem K w hIg.radical hf (toLex d)
  rwa [hproj] at h

/-- The ideal generated by homogeneous equations vanishing on an arbitrary
projective set is radical. No reducedness certificate is added to the model. -/
theorem MultiProjectiveSpace.vanishingIdeal_isRadical (S : Set M.Point) :
    (M.vanishingIdeal S).IsRadical := by
  apply Ideal.radical_eq_iff.mp
  apply le_antisymm ?_ Ideal.le_radical
  rw [M.homogeneousIdeal_eq_span _
    (Hilbert.radical_multihomogeneous M _ (vanishingIdeal_multihomogeneous K M S))]
  apply Ideal.span_le.mpr
  rintro P ⟨hP, D, hD⟩
  obtain ⟨n, hn⟩ := hP
  refine Ideal.subset_span ⟨⟨D, hD⟩, ?_⟩
  intro x hx
  have h := M.eval_eq_zero_of_mem_vanishingIdeal hn hx
  change MvPolynomial.eval (M.coordinate x) (P ^ n) = 0 at h
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponHomogeneousOperations.lean

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Implementation: Solutions/PhilipponRegularMapTopology.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

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

/-- Substituting tuples homogeneous in each source block preserves
multihomogeneity, with the expected linear transformation of degrees. -/
theorem IsHomogeneous.eval₂_blocks (M N : MultiProjectiveSpace K)
    {Q : N.CoordinateRing} {D : N.FactorIndex → ℕ} (hQ : N.IsHomogeneous Q D)
    (P : N.Variable → M.CoordinateRing) (E : N.FactorIndex → M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) (E j.1)) :
    M.IsHomogeneous (eval₂ C P Q) (fun i => ∑ b, D b * E b i) := by
  classical
  rw [eval₂_eq']
  apply M.isHomogeneous_sum
  intro d hd
  have hh := M.isHomogeneous_prod Finset.univ (fun j => P j ^ d j)
    (fun j i => d j * E j.1 i) (fun j _ => (hP j).pow M (d j))
  have he : (∑ j : N.Variable, fun i => d j * E j.1 i) =
      (fun i => ∑ b, D b * E b i) := by
    funext i
    simp only [Finset.sum_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ y, d ⟨b, y⟩ * E b i) = D b * E b i
    rw [← Finset.sum_mul, hQ d hd b]
  rw [he] at hh
  exact hh.C_mul M _

/-- Two projective lifts represent the same point precisely when all their
two-by-two cross products vanish. -/
theorem projectivization_mk_eq_iff_cross {ι : Type*}
    (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔
      ∀ j k, v j * w k = v k * w j := by
  classical
  constructor
  · intro heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp heq
    intro j k
    rw [← ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    change w k ≠ 0 at hk
    apply (Projectivization.mk_eq_mk_iff' K v w hv hw).mpr
    refine ⟨v k / w k, ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    exact h k j

/-- Regular maps into a multiprojective space have a closed equalizer, even
though the Zariski topology on the target is not Hausdorff. -/
theorem IsRegularAlong.isClosed_equalizer
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g) :
    @IsClosed X (TopologicalSpace.induced e M.zariskiTopology) {x | f x = g x} := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hx
  obtain ⟨U, hU, hxU, D, P, hP, hflift⟩ := hf x b
  obtain ⟨V, hV, hxV, E, Q, hQ, hglift⟩ := hg x b
  obtain ⟨hp, hpx⟩ := hflift x hxU
  obtain ⟨hq, hqx⟩ := hglift x hxV
  have hcross : ∃ j k, M.eval (P j * Q k - P k * Q j) (e x) ≠ 0 := by
    by_contra! hn
    apply hb
    rw [← hpx, ← hqx, projectivization_mk_eq_iff_cross]
    intro j k
    simpa only [eval, map_sub, map_mul, sub_eq_zero] using hn j k
  obtain ⟨j, k, hjk⟩ := hcross
  have hhom := ((hP j).mul M (hQ k)).sub M ((hP k).mul M (hQ j))
  let W := U ∩ V ∩ {p | M.eval (P j * Q k - P k * Q j) p ≠ 0}
  have hopen : IsOpen (e ⁻¹' W) :=
    ((hU.inter hV).inter (M.isOpen_basic _ _ hhom)).preimage continuous_induced_dom
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨hxU, hxV⟩, hjk⟩) ?_
  intro y hy heq
  obtain ⟨hpy, hpy'⟩ := hflift y hy.1.1
  obtain ⟨hqy, hqy'⟩ := hglift y hy.1.2
  have hmk := hpy'.trans ((congrFun heq b).trans hqy'.symm)
  have hz := (projectivization_mk_eq_iff_cross _ _ hpy hqy).mp hmk j k
  exact hy.2 (by simpa only [eval, map_sub, map_mul, sub_eq_zero] using hz)

theorem IsRegularAlong.eq_of_dense
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g)
    (A : Set X) (hA : @Dense X (TopologicalSpace.induced e M.zariskiTopology) A)
    (hfg : Set.EqOn f g A) : f = g := by
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  have hh : closure A ⊆ {x | f x = g x} :=
    closure_minimal hfg (hf.isClosed_equalizer M N hg)
  funext x
  exact hh (hA x)

/-- Regular maps are continuous for the actual polynomial Zariski topologies. -/
theorem IsRegularAlong.continuous
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) :
    @Continuous X N.Point (TopologicalSpace.induced e M.zariskiTopology)
      N.zariskiTopology f := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨R, D, hR, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  choose U hU hxU E P hP hlift using hf x
  let pull := eval₂ C (fun j : N.Variable => P j.1 j.2) R
  have hpull : M.IsHomogeneous pull (fun i => ∑ b, D b * E b i) :=
    hR.eval₂_blocks M N _ E (fun j => hP j.1 j.2)
  have heval (y : X) : M.eval pull (e y) =
      MvPolynomial.eval (fun j : N.Variable => M.eval (P j.1 j.2) (e y)) R := by
    dsimp only [eval, pull]
    rw [← eval_assoc]
    rfl
  have hiff (y : X) (hy : ∀ b, e y ∈ U b) :
      M.eval pull (e y) = 0 ↔ N.eval R (f y) = 0 := by
    rw [heval]
    exact N.eval_eq_zero_iff_of_lift (f y) _ (fun b => hlift b y (hy b)) R D hR
  let W : Set M.Point := (⋂ b, U b) ∩ {p | M.eval pull p ≠ 0}
  have hW : IsOpen (e ⁻¹' W) :=
    ((isOpen_iInter_of_finite hU).inter (M.isOpen_basic _ _ hpull)).preimage
      continuous_induced_dom
  have hxW : x ∈ e ⁻¹' W := ⟨Set.mem_iInter.mpr hxU, (hiff x hxU).not.mpr hx⟩
  refine Filter.mem_of_superset (hW.mem_nhds hxW) ?_
  intro y hy
  exact (hiff y (Set.mem_iInter.mp hy.1)).not.mp hy.2

theorem IsRegularAlong.comp_domain
    {X Y : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) (g : Y → X) :
    M.IsRegularAlong N (e ∘ g) (f ∘ g) := by
  intro y b
  obtain ⟨U, hU, hy, D, P, hP, hl⟩ := hf (g y) b
  exact ⟨U, hU, hy, D, P, hP, fun z hz => hl (g z) hz⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Implementation: Solutions/PhilipponProductRegularity.lean


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

theorem MultiProjectiveSpace.projection_regular (M : MultiProjectiveSpace K)
    (i : M.FactorIndex) :
    M.IsRegularAlong (projectiveSpace K (M.ambientDimension i)) id (fun p _ => p i) := by
  let := M.zariskiTopology
  intro x b
  refine ⟨univ, isOpen_univ, mem_univ _, (fun a => if a = i then 1 else 0),
    (fun j => X ⟨i, j⟩), (fun j => M.isHomogeneous_X ⟨i, j⟩), ?_⟩
  intro y _
  simp only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate, id_eq]
  exact ⟨Projectivization.rep_nonzero (y i), Projectivization.mk_rep (y i)⟩

theorem EmbeddedGroupProduct.embedding_injective (G : EmbeddedGroupProduct K) :
    Function.Injective G.embedding := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

theorem EmbeddedGroupProduct.embedding_locallyClosed (G : EmbeddedGroupProduct K) :
    @IsLocallyClosed _ G.ambient.zariskiTopology (range G.embedding) := by
  classical
  let := G.ambient.zariskiTopology
  have hloc (i : G.FactorIndex) : IsLocallyClosed {p : G.ambient.Point | p i ∈ (G.factor i).carrier} := by
    let := (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology
    let := TopologicalSpace.induced
      (fun (x : Projectivization K (Fin ((G.factor i).ambientDimension + 1) → K)) (_ : Fin 1) => x)
      (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology
    apply (G.factor i).locallyClosed.preimage
    apply continuous_induced_rng.mpr
    have h := (G.ambient.projection_regular i).continuous
    rw [induced_id] at h
    exact h
  choose U Z hU hZ hUZ using hloc
  refine ⟨⋂ i, U i, ⋂ i, Z i, isOpen_iInter_of_finite hU, isClosed_iInter hZ, ?_⟩
  have heq : range G.embedding = ⋂ i, {p : G.ambient.Point | p i ∈ (G.factor i).carrier} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_iInter.mpr (fun i => (x i).property)
    · intro hp
      exact ⟨(fun i => ⟨p i, mem_iInter.mp hp i⟩), rfl⟩
  rw [heq]
  simp only [hUZ, iInter_inter_distrib]

end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponGroupOpenLocus.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K]

/-- The open part of the affine coordinate spectrum above a locally closed
projective set: every coordinate block is nonzero and the projective point
belongs to the coborder. -/
def projectiveConeOpen (M : MultiProjectiveSpace K) (S : Set M.Point) :
    Set (PrimeSpectrum M.CoordinateRing) :=
  {q | (∀ i, ∃ j, X ⟨i, j⟩ ∉ q.asIdeal) ∧
    ∃ P D, M.IsHomogeneous P D ∧
      {x | M.eval P x ≠ 0} ⊆ @coborder _ M.zariskiTopology S ∧ P ∉ q.asIdeal}

theorem isOpen_projectiveConeOpen (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsOpen (projectiveConeOpen M S) := by
  classical
  unfold projectiveConeOpen
  simp only [Set.setOf_and, Set.setOf_forall, Set.setOf_exists]
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite (fun i => isOpen_iUnion (fun j =>
      (PrimeSpectrum.basicOpen (X ⟨i,j⟩ : M.CoordinateRing)).isOpen))
  · apply isOpen_iUnion
    intro P
    apply isOpen_iUnion
    intro D
    by_cases h : M.IsHomogeneous P D ∧
        {x | M.eval P x ≠ 0} ⊆ @coborder _ M.zariskiTopology S
    · simp only [h.1, h.2, Set.setOf_true, Set.univ_inter]
      exact (PrimeSpectrum.basicOpen P).isOpen
    · have heq : {q : PrimeSpectrum M.CoordinateRing | M.IsHomogeneous P D} ∩
          ({q | {x | M.eval P x ≠ 0} ⊆ @coborder _ M.zariskiTopology S} ∩
            {q | P ∉ q.asIdeal}) = ∅ := by
        ext q
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        exact fun hP hS _ => h ⟨hP,hS⟩
      rw [heq]
      exact isOpen_empty

theorem groupIdeal_le_representative (G : EmbeddedGroupProduct K)
    (r : GroupHomogeneousRepresentative G) :
    G.vanishingIdeal Set.univ ≤ (representativeMaximalIdeal G r).asIdeal := by
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  exact (G.ambient.eval_eq_zero_iff_of_lift (G.embedding r.point) r.coordinates
    (fun i => ⟨r.nonzero i, r.represents i⟩) P D hD).mpr
      (hP _ ⟨r.point, Set.mem_univ _, rfl⟩)

theorem representative_mem_projectiveConeOpen (G : EmbeddedGroupProduct K)
    (r : GroupHomogeneousRepresentative G) :
    (⟨(representativeMaximalIdeal G r).asIdeal,
      (representativeMaximalIdeal G r).isMaximal.isPrime⟩ : PrimeSpectrum G.CoordinateRing) ∈
      projectiveConeOpen G.ambient (Set.range G.embedding) := by
  classical
  letI := G.ambient.zariskiTopology
  constructor
  · intro i
    have hi := r.nonzero i
    simp only [ne_eq, funext_iff, Pi.zero_apply, not_forall] at hi
    obtain ⟨j,hj⟩ := hi
    exact ⟨j, by simpa [representativeMaximalIdeal, representativeEvaluation] using hj⟩
  · obtain ⟨U,hU,hx,hUS⟩ := G.ambient.isTopologicalBasis_basic.mem_nhds_iff.mp
      (G.embedding_locallyClosed.isOpen_coborder.mem_nhds
        (subset_coborder (Set.mem_range_self r.point)))
    obtain ⟨P,D,hP,rfl⟩ := hU
    refine ⟨P,D,hP,hUS,?_⟩
    change MvPolynomial.eval r.coordinates P ≠ 0
    exact fun hz => hx ((G.ambient.eval_eq_zero_iff_of_lift _ r.coordinates
      (fun i => ⟨r.nonzero i,r.represents i⟩) P D hP).mp hz)

/-- Over an algebraically closed field every closed point in this open
locus lying on the group closure is an actual homogeneous group representative. -/
theorem representative_of_mem_projectiveConeOpen [IsAlgClosed K]
    (G : EmbeddedGroupProduct K) (m : MaximalSpectrum G.CoordinateRing)
    (hG : G.vanishingIdeal Set.univ ≤ m.asIdeal)
    (hm : (⟨m.asIdeal,m.isMaximal.isPrime⟩ : PrimeSpectrum G.CoordinateRing) ∈
      projectiveConeOpen G.ambient (Set.range G.embedding)) :
    ∃ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r = m := by
  classical
  letI := G.ambient.zariskiTopology
  obtain ⟨v,hv⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K m.isMaximal
  have hmem (P : G.CoordinateRing) : P ∈ m.asIdeal ↔ MvPolynomial.eval v P = 0 := by
    rw [hv]
    simp [MvPolynomial.vanishingIdeal]
  have hn (i : G.FactorIndex) : (fun j => v ⟨i,j⟩) ≠ 0 := by
    obtain ⟨j,hj⟩ := hm.1 i
    intro h
    apply hj
    rw [hmem, MvPolynomial.eval_X]
    exact congrFun h j
  let x : G.ambient.Point := fun i => Projectivization.mk K (fun j => v ⟨i,j⟩) (hn i)
  have hrep : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i := fun i => ⟨hn i,rfl⟩
  have hxcl : x ∈ closure (Set.range G.embedding) := by
    rw [← G.ambient.zeroLocus_vanishingIdeal_eq_closure]
    apply (G.ambient.mem_zeroLocus_iff_homogeneous _
      (vanishingIdeal_multihomogeneous K G.ambient _) x).mpr
    intro P hP D hD
    apply (G.ambient.eval_eq_zero_iff_of_lift x v hrep P D hD).mp
    apply (hmem P).mp
    apply hG
    simpa only [EmbeddedGroupProduct.vanishingIdeal, Set.image_univ] using hP
  obtain ⟨P,D,hD,hS,hP⟩ := hm.2
  have hxc : x ∈ coborder (Set.range G.embedding) := by
    apply hS
    intro hz
    exact hP ((hmem P).mpr ((G.ambient.eval_eq_zero_iff_of_lift x v hrep P D hD).mpr hz))
  have hx : x ∈ Set.range G.embedding :=
    (closure_inter_coborder (s := Set.range G.embedding)) ▸ ⟨hxcl,hxc⟩
  obtain ⟨g,hg⟩ := hx
  let r : GroupHomogeneousRepresentative G := ⟨g,v,hn,fun i => congrFun hg.symm i⟩
  refine ⟨r, ?_⟩
  apply MaximalSpectrum.ext
  ext Q
  exact (hmem Q).symm

end PhilipponMultiplicity.AlgebraicGroupCM

end
end


section
-- Implementation: Solutions/PhilipponGenericSmoothness.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable (K R : Type*) [Field K] [PerfectField K] [CommRing R] [Algebra K R]
  [Algebra.FiniteType K R]

/-- The smooth locus of a reduced algebra over a perfect field contains every
minimal prime. This concerns the actual localization, not a supplied chart. -/
theorem smoothAt_minimalPrime [IsReduced R] (q : Ideal R)
    (hq : q ∈ minimalPrimes R) :
    letI : q.IsPrime := hq.1.1
    Algebra.IsSmoothAt K q := by
  letI : q.IsPrime := hq.1.1
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime q) := .of_isLocalization _ hq _
  letI : Field (Localization.AtPrime q) := Ring.KrullDimLE.isField_of_isReduced.toField
  exact Algebra.FormallySmooth.of_perfectField

/-- In particular, the smooth locus is dense even before choosing a finite
presentation or a point in an embedded group. -/
theorem dense_smoothLocus [IsReduced R] : Dense (Algebra.smoothLocus K R) := by
  intro x
  obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal R) ≤ x.asIdeal from bot_le)
  let y : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have hy : y ∈ Algebra.smoothLocus K R := smoothAt_minimalPrime K R q hq
  exact ((PrimeSpectrum.le_iff_specializes y x).mp hqx).mem_closed
    isClosed_closure (subset_closure hy)

/-- Every nonempty open set contains a closed smooth point. Finite type is
used both for openness of smoothness and the Jacobson property. -/
theorem exists_smooth_maximal_mem_open [IsReduced R]
    (U : Set (PrimeSpectrum R)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ m : PrimeSpectrum R, m ∈ U ∧ m.asIdeal.IsMaximal ∧
      Algebra.IsSmoothAt K m.asIdeal := by
  letI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K) (B := R)
  letI : Algebra.FinitePresentation K R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hne' := (dense_smoothLocus K R).inter_open_nonempty U hU hne
  obtain ⟨m, hm, hclosed⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing
    (U ∩ Algebra.smoothLocus K R) (hU.inter Algebra.isOpen_smoothLocus) hne'
  exact ⟨m, hm.1, (PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mp hclosed, hm.2⟩

end PhilipponMultiplicity.AlgebraicGroupCM

end
end


section
-- Implementation: Solutions/PhilipponEtaleRegularityReuse.lean

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW
namespace S_isRegularLocalRing_localization_atPrime_of_etale_of_comap

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open IsLocalRing Localization

namespace ChildB

private theorem isNoetherianRing_of_essFiniteType (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.EssFiniteType R S] :
    IsNoetherianRing S := by
  haveI hN : IsNoetherianRing (Algebra.EssFiniteType.subalgebra R S) :=
    Algebra.FiniteType.isNoetherianRing R _
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) S hN

end ChildB

theorem etaleRegularAt
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A B)))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := hreg
  haveI hlo : q.LiesOver (q.comap (algebraMap A B)) := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap A B)) q

  haveI : Algebra.FormallyUnramified A B := inferInstance
  haveI hIU : Algebra.IsUnramifiedAt A q := by
    unfold Algebra.IsUnramifiedAt
    infer_instance
  haveI hEFTa : Algebra.EssFiniteType A (Localization.AtPrime q) := inferInstance
  haveI hEFT : Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := Algebra.EssFiniteType.of_comp A _ _
  haveI hNoeth : IsNoetherianRing (Localization.AtPrime q) :=
    ChildB.isNoetherianRing_of_essFiniteType (Localization.AtPrime (q.comap (algebraMap A B))) _

  have hmap : (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).map
      (algebraMap _ (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.map_maximalIdeal

  have h1 : (maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).spanFinrank := by
    rw [← hmap]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)

  haveI : Module.Flat A B := inferInstance
  haveI hflat : Module.Flat (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := inferInstance

  haveI hlom2 : (maximalIdeal (Localization.AtPrime q)).LiesOver
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))) := by
    constructor
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact not_iff_not.mpr
      ⟨fun h => IsLocalHom.map_nonunit x h, fun h => h.map (algebraMap _ _)⟩ |>.symm

  have h2 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := Localization.AtPrime (q.comap (algebraMap A B))) (S := Localization.AtPrime q)
    (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B))))
    (maximalIdeal (Localization.AtPrime q))

  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  calc ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).spanFinrank : WithBot ℕ∞) := by exact_mod_cast h1
    _ = ringKrullDim (Localization.AtPrime (q.comap (algebraMap A B))) :=
        hreg.spanFinrank_maximalIdeal
    _ = ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).height : WithBot ℕ∞) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ ≤ ((maximalIdeal (Localization.AtPrime q)).height : WithBot ℕ∞) := by
        rw [h2]
        exact_mod_cast le_self_add
    _ = ringKrullDim (Localization.AtPrime q) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim

end

end S_isRegularLocalRing_localization_atPrime_of_etale_of_comap
end P2MW
export P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap (etaleRegularAt)

end


section
-- Implementation: Solutions/PhilipponSmoothLocalRegularity.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM

/-- Standard smooth presentations are étale over a polynomial algebra, whose
prime localizations are regular. -/
theorem regularAt_of_standardSmooth (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.IsStandardSmooth K R] (q : Ideal R) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨n, f, hf, he⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap K R) (RingHom.isStandardSmooth_algebraMap.mpr inferInstance)
  algebraize [f]
  haveI : IsRegularRing K := inferInstance
  haveI : IsRegularRing (MvPolynomial (Fin n) K) :=
    MvPolynomial.isRegularRing_of_isRegularRing K
  exact P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap.etaleRegularAt
    (MvPolynomial (Fin n) K) R q
    (IsRegularRing.isRegularLocalRing_localization _)

/-- Smoothness at a prime suffices: choose a standard smooth neighbourhood
and identify its localization with the original local ring. -/
theorem regularAt_of_smoothAt (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.FinitePresentation K R] (p : Ideal R) [hp : p.IsPrime]
    [Algebra.IsSmoothAt K p] : IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  letI := hstd
  have hdis : Disjoint (Submonoid.powers f : Set R) (p : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let q := p.map (algebraMap R (Localization.Away f))
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) (Localization.Away f) p hp hdis
  have heq : q.comap (algebraMap R (Localization.Away f)) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) hp hdis
  letI : IsRegularLocalRing (Localization.AtPrime q) :=
    regularAt_of_standardSmooth K (Localization.Away f) q
  haveI : IsLocalization p.primeCompl (Localization.AtPrime q) := by
    have heq' : (q.comap (algebraMap R (Localization.Away f))).primeCompl = p.primeCompl := by
      ext x
      change x ∉ q.comap (algebraMap R (Localization.Away f)) ↔ x ∉ p
      rw [heq]
    rw [← heq']
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q)).symm.toRingEquiv)

end PhilipponMultiplicity.AlgebraicGroupCM

end
end


section
-- Implementation: Solutions/PhilipponLocalizedQuotient.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM

theorem primeCompl_map_quotient {R : Type*} [CommRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
    p.primeCompl.map (Ideal.Quotient.mk I) = (p.map (Ideal.Quotient.mk I)).primeCompl := by
  letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · rintro ⟨s, hs, heq⟩
    change Ideal.Quotient.mk I r ∉ p.map (Ideal.Quotient.mk I)
    rw [← heq, Ideal.mem_quotient_iff_mem hIp]
    exact hs
  · intro h
    refine ⟨r, ?_, rfl⟩
    exact fun hr => h (Ideal.mem_map_of_mem _ hr)

/-- The two actual rings obtained by quotienting and localizing commute.
This is the identification needed between smooth affine rings and the local
quotients in Philippon's definition. -/
def localizedQuotientEquiv {R : Type*} [CommRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
    ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≃ₐ[R ⧸ I]
      Localization.AtPrime (p.map (Ideal.Quotient.mk I)) := by
  letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  let B := (Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))
  haveI : IsLocalization (p.map (Ideal.Quotient.mk I)).primeCompl B := by
    rw [← primeCompl_map_quotient I p hIp]
    exact inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl) B)
  exact IsLocalization.algEquiv (p.map (Ideal.Quotient.mk I)).primeCompl B _

end PhilipponMultiplicity.AlgebraicGroupCM

end
end


section
-- Implementation: Solutions/PhilipponGroupRegularPoint.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] [IsAlgClosed K]

/-- A genuine homogeneous representative of the embedded group has a regular
localized quotient. The point is constructed from the dense smooth locus of
the reduced affine cone and the open part lying above the actual group. -/
theorem exists_regular_group_representative (G : EmbeddedGroupProduct K) :
    ∃ r : GroupHomogeneousRepresentative G,
      IsRegularLocalRing ((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal))) := by
  classical
  let I := G.vanishingIdeal Set.univ
  let Q := G.CoordinateRing ⧸ I
  let f := Ideal.Quotient.mk I
  have hred : I.IsRadical := G.ambient.vanishingIdeal_isRadical _
  letI : IsReduced Q := (Ideal.isRadical_iff_quotient_reduced I).mp hred
  letI : Algebra.FiniteType K Q := inferInstance
  letI : Algebra.FinitePresentation K Q := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let U := PrimeSpectrum.comap f ⁻¹'
    projectiveConeOpen G.ambient (Set.range G.embedding)
  have hU : IsOpen U := (isOpen_projectiveConeOpen _ _).preimage (PrimeSpectrum.continuous_comap f)
  have hne : U.Nonempty := by
    let m := representativeMaximalIdeal G (representativeOfPoint G 0)
    have hIm : I ≤ m.asIdeal := groupIdeal_le_representative G _
    letI : (m.asIdeal.map f).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa [f] using hIm)
    refine ⟨⟨m.asIdeal.map f,inferInstance⟩,?_⟩
    have heq : (m.asIdeal.map f).comap f = m.asIdeal := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      apply sup_eq_left.mpr
      intro P hP
      exact hIm (Ideal.Quotient.eq_zero_iff_mem.mp hP)
    change (PrimeSpectrum.comap f ⟨m.asIdeal.map f,inferInstance⟩) ∈
      projectiveConeOpen G.ambient (Set.range G.embedding)
    have heq' : PrimeSpectrum.comap f ⟨m.asIdeal.map f,inferInstance⟩ = m.toPrimeSpectrum :=
      PrimeSpectrum.ext heq
    rw [heq']
    exact representative_mem_projectiveConeOpen G _
  obtain ⟨q,hqU,hqmax,hqs⟩ := exists_smooth_maximal_mem_open K Q U hU hne
  letI := hqmax
  let m : MaximalSpectrum G.CoordinateRing :=
    ⟨q.asIdeal.comap f, Ideal.comap_isMaximal_of_surjective f Ideal.Quotient.mk_surjective⟩
  have hIm : I ≤ m.asIdeal := by
    intro P hP
    change f P ∈ q.asIdeal
    rw [show f P = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hP]
    exact q.asIdeal.zero_mem
  obtain ⟨r,hr⟩ := representative_of_mem_projectiveConeOpen G m hIm hqU
  refine ⟨r,?_⟩
  rw [hr]
  letI : (m.asIdeal.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa [f] using hIm)
  have heq : m.asIdeal.map f = q.asIdeal := Ideal.map_comap_of_surjective f
    Ideal.Quotient.mk_surjective q.asIdeal
  letI : Algebra.IsSmoothAt K (m.asIdeal.map f) := by simpa only [heq] using hqs
  letI : IsRegularLocalRing (Localization.AtPrime (m.asIdeal.map f)) :=
    regularAt_of_smoothAt K Q (m.asIdeal.map f)
  exact IsRegularLocalRing.of_ringEquiv
    (R := Localization.AtPrime (m.asIdeal.map f))
    (localizedQuotientEquiv I m.asIdeal hIm).symm.toRingEquiv

end PhilipponMultiplicity.AlgebraicGroupCM

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] [IsAlgClosed K]
    (G : EmbeddedGroupProduct K) :
    ∃ r : GroupHomogeneousRepresentative G,
      IsRegularLocalRing ((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal))) := by
  exact AlgebraicGroupCM.exists_regular_group_representative G
