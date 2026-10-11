-- Prove2me | solution 1 for PhilipponMultiplicity.group_closure_has_proper_scheme_action
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T00:54:30.741872+00:00
-- url     : https://prove2.me/submissions/3f8867a1-ce87-45bd-8314-c86255063f3a

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases
import Mathlib
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveGeometry

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

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

end WeierstrassEllipticZeta
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponPointHilbert

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

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
end PhilipponMultiplicity
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveContact

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
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAdditiveSubgroups

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
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHomogeneousOperations

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
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponRegularMapTopology

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
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProductHilbert

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open SectionThree

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeronesePieces

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

def blockLinearSpace (i : M.FactorIndex) : Submodule K M.CoordinateRing :=
  Submodule.span K (Set.range (fun j : Fin (M.ambientDimension i + 1) => X ⟨i,j⟩))

def blockProductSpace (D : M.FactorIndex → ℕ) : Submodule K M.CoordinateRing :=
  ∏ i, M.blockLinearSpace i ^ D i

theorem blockProductSpace_add (D E : M.FactorIndex → ℕ) :
    M.blockProductSpace (D + E) = M.blockProductSpace D * M.blockProductSpace E := by
  simp [blockProductSpace, pow_add, Finset.prod_mul_distrib]

theorem blockProductSpace_single (i : M.FactorIndex) (n : ℕ) :
    M.blockProductSpace (Pi.single i n) = M.blockLinearSpace i ^ n := by
  classical
  simp [blockProductSpace, Pi.single_apply]

theorem monomial_mem_blockProductSpace (e : M.Variable →₀ ℕ) (c : K) :
    monomial e c ∈ M.blockProductSpace
      (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) e) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp [blockProductSpace]
  | single_add v n e hv hn ih =>
    rw [map_add, Finsupp.weight_single, blockProductSpace_add, monomial_single_add]
    have he : n • Hilbert.blockWeight M.factorCount M.ambientDimension v = Pi.single v.1 n := by
      ext i
      simp [Hilbert.blockWeight, Pi.single_apply]
    rw [he, blockProductSpace_single]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _
      (Submodule.subset_span (Set.mem_range_self v.2)) n) ih

theorem degreePiece_pow_le (D : M.FactorIndex → ℕ) (n : ℕ) :
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D) ^ n ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (n • D) := by
  induction n with
  | zero =>
    simp only [pow_zero, zero_nsmul]
    exact Submodule.one_le.mpr (MvPolynomial.isWeightedHomogeneous_one K _)
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact (mul_le_mul' ih le_rfl).trans
      (MvPolynomial.weightedHomogeneousSubmodule_mul _ _ _)

theorem blockProductSpace_le_degreePiece (D : M.FactorIndex → ℕ) :
    M.blockProductSpace D ≤ Hilbert.degreePiece K M.factorCount M.ambientDimension D := by
  classical
  have hblock (i : M.FactorIndex) : M.blockLinearSpace i ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (Pi.single i 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have he : (Pi.single i 1 : M.FactorIndex → ℕ) = fun k => if k = i then 1 else 0 := by
      ext k
      simp [Pi.single_apply]
    rw [he]
    exact (M.degreePiece_iff _ _).mpr (M.isHomogeneous_X ⟨i,j⟩)
  have hpow (i : M.FactorIndex) : M.blockLinearSpace i ^ D i ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (Pi.single i (D i)) := by
    have h := (pow_le_pow_left' (hblock i) (D i)).trans (M.degreePiece_pow_le _ _)
    have he : D i • (Pi.single i 1 : M.FactorIndex → ℕ) = Pi.single i (D i) := by
      ext j
      simp [Pi.single_apply]
    rw [he] at h
    exact h
  have hprod (s : Finset M.FactorIndex) : (∏ i ∈ s, M.blockLinearSpace i ^ D i) ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (∑ i ∈ s, Pi.single i (D i)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact Submodule.one_le.mpr (MvPolynomial.isWeightedHomogeneous_one K _)
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (mul_le_mul' (hpow i) ih).trans
        (MvPolynomial.weightedHomogeneousSubmodule_mul _ _ _)
  have hsum : (∑ i, Pi.single i (D i)) = D := by
    ext j
    simp [Pi.single_apply]
  simpa only [hsum, blockProductSpace] using hprod Finset.univ

theorem degreePiece_eq_blockProductSpace (D : M.FactorIndex → ℕ) :
    Hilbert.degreePiece K M.factorCount M.ambientDimension D = M.blockProductSpace D := by
  apply le_antisymm _ (M.blockProductSpace_le_degreePiece D)
  intro P hP
  rw [P.as_sum]
  apply Submodule.sum_mem
  intro e he
  have heD := hP (MvPolynomial.mem_support_iff.mp he)
  rw [← heD]
  exact M.monomial_mem_blockProductSpace e _

theorem degreePiece_diagonal_pow (D : M.FactorIndex → ℕ) (n : ℕ) :
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D) ^ n =
      Hilbert.degreePiece K M.factorCount M.ambientDimension (fun i => n * D i) := by
  rw [M.degreePiece_eq_blockProductSpace, M.degreePiece_eq_blockProductSpace]
  change (∏ i, M.blockLinearSpace i ^ D i) ^ n = ∏ i, M.blockLinearSpace i ^ (n * D i)
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, mul_comm]

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponFixedFactorHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

variable {K : Type*} [Field K] (N : ℕ)

theorem projective_homogeneous_iff (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) :
    (projectiveSpace K N).IsHomogeneous P (fun _ => n) ↔ P.IsHomogeneous n := by
  classical
  change (∀ d ∈ P.support, ∀ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ = n) ↔ _
  constructor
  · intro h d hd
    rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
    change (∑ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ • (1 : ℕ)) = n
    simpa [Fin.sum_univ_one] using h d (mem_support_iff.mpr hd) (0 : Fin 1)
  · intro h d hd i
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have hh := h (mem_support_iff.mp hd)
    rw [Finsupp.weight_eq_sum, Fintype.sum_sigma] at hh
    change (∑ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ • (1 : ℕ)) = n at hh
    simpa [Fin.sum_univ_one] using hh

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeroneseHilbert

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K]

theorem ordinary_degreePiece_eq (N n : ℕ) :
    degreePiece K 1 (fun _ => N) (fun _ => n) =
      homogeneousSubmodule (projectiveSpace K N).Variable K n := by
  ext P
  exact ((projectiveSpace K N).degreePiece_iff P _).trans
    (MultiProjectiveSpace.projective_homogeneous_iff N P n)

namespace SegreVeronese
variable (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
  (b : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension D))

def substitution : (projectiveSpace K N).CoordinateRing →ₐ[K] M.CoordinateRing :=
  aeval (fun j => (b j).val)

theorem substitution_degreePiece (n : ℕ) :
    (degreePiece K 1 (fun _ => N) (fun _ => n)).map
      (substitution M D b).toLinearMap =
        degreePiece K M.factorCount M.ambientDimension (fun i => n * D i) := by
  rw [ordinary_degreePiece_eq, ← homogeneousSubmodule_one_pow,
    Submodule.map_pow, homogeneousSubmodule_one_eq_span_X, Submodule.map_span]
  have he : (substitution M D b).toLinearMap '' Set.range X = Set.range (fun j => (b j).val) := by
    rw [← Set.range_comp]
    congr 1
    funext j
    simp [substitution]
  rw [he]
  have hspan : Submodule.span K (Set.range (fun j => (b j).val)) =
      degreePiece K M.factorCount M.ambientDimension D := by
    change Submodule.span K (Set.range
      ((degreePiece K M.factorCount M.ambientDimension D).subtype ∘ b)) = _
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  rw [hspan, M.degreePiece_diagonal_pow]

theorem substitution_homogeneous (n : ℕ)
    (P : (projectiveSpace K N).CoordinateRing) (hP : P.IsHomogeneous n) :
    (substitution M D b P).IsWeightedHomogeneous
      (blockWeight M.factorCount M.ambientDimension) (fun i => n * D i) := by
  have hmem : P ∈ degreePiece K 1 (fun _ => N) (fun _ => n) := by
    rw [ordinary_degreePiece_eq]
    exact hP
  change substitution M D b P ∈ degreePiece K M.factorCount M.ambientDimension _
  rw [← substitution_degreePiece M D b n]
  exact Submodule.mem_map_of_mem hmem

def diagonalIdeal (I : Ideal M.CoordinateRing) :
    Ideal (projectiveSpace K N).CoordinateRing :=
  I.comap (substitution M D b).toRingHom

end SegreVeronese
end PhilipponMultiplicity.Hilbert

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponMonomialPartition

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MonomialCells

variable (p : ℕ) (N : Fin p → ℕ)

abbrev Var := Sigma fun i : Fin p => Fin (N i + 1)

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

end PhilipponMultiplicity.MonomialCells

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeroneseAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K]

theorem ordinary_weight_eq (N : ℕ) (e : ((i : Fin 1) × Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (blockWeight 1 (fun _ => N)) e = fun _ => e.degree := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hd : e.degree = ∑ j : Fin (N + 1), e ⟨(0 : Fin 1), j⟩ := by
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp [Fin.sum_univ_one]
  exact (MonomialCells.weight_apply 1 (fun _ => N) e 0).trans hd.symm

theorem ordinary_component_eq (N : ℕ) (P : CoordinateRing K 1 (fun _ => N))
    (d : Fin 1 → ℕ) :
    weightedHomogeneousComponent (blockWeight 1 (fun _ => N)) d P =
      homogeneousComponent (d 0) P := by
  classical
  apply MvPolynomial.ext
  intro e
  have he : (fun _ : Fin 1 => e.degree) = d ↔ e.degree = d 0 := by
    constructor
    · exact fun h => congrFun h 0
    · intro h
      ext i
      simpa only [Subsingleton.elim i (0 : Fin 1)] using h
  calc
    _ = if Finsupp.weight (blockWeight 1 (fun _ => N)) e = d then coeff e P else 0 :=
      coeff_weightedHomogeneousComponent d P e
    _ = if e.degree = d 0 then coeff e P else 0 := by simp only [ordinary_weight_eq, he]
    _ = _ := (coeff_homogeneousComponent (d 0) P e).symm

namespace SegreVeronese
variable (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
  (b : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension D))

theorem substitution_component (hD : ∀ i, 1 ≤ D i)
    (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) :
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension)
      (fun i => n * D i) (substitution M D b P) =
        substitution M D b (homogeneousComponent n P) := by
  classical
  have hinj : Function.Injective (fun m : ℕ => fun i => m * D i) := by
    intro m n h
    let i : M.FactorIndex := ⟨0, M.positive⟩
    have hi := congrFun h i
    have hpos := hD i
    nlinarith
  rw [P.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hh := isHomogeneous_monomial (coeff e P) (rfl : e.degree = e.degree)
  have hs := substitution_homogeneous M D b e.degree _ hh
  rw [weightedHomogeneousComponent_of_mem hs, homogeneousComponent_of_mem hh]
  by_cases hn : n = e.degree
  · subst n
    simp only [ite_true]
  · rw [if_neg (fun h => hn (hinj h)), if_neg hn, map_zero]

theorem diagonalIdeal_homogeneous (hD : ∀ i, 1 ≤ D i)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    IsMultihomogeneousIdeal (projectiveSpace K N) (diagonalIdeal M D b I) := by
  intro P hP d
  change Fin 1 → ℕ at d
  change substitution M D b
    (weightedHomogeneousComponent (blockWeight 1 (fun _ => N)) d P) ∈ I
  rw [ordinary_component_eq]
  exact (substitution_component M D b hD P (d 0)) ▸
    hI _ hP (fun i => d 0 * D i)

theorem degreePiece_finrank_pos :
    0 < Module.finrank K (degreePiece K M.factorCount M.ambientDimension D) := by
  classical
  let e : M.Variable →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun v => if v.2 = 0 then D v.1 else 0)
  have hhom : M.IsHomogeneous (monomial e (1 : K)) D := by
    intro a ha i
    have he : a = e := Finset.mem_singleton.mp (support_monomial_subset ha)
    subst a
    change (∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩) = D i
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    exact (Finset.sum_ite_eq' Finset.univ (0 : Fin (M.ambientDimension i + 1))
      (fun _ => D i)).trans (if_pos (Finset.mem_univ _))
  have hmem := (M.degreePiece_iff _ _).mpr hhom
  let x : degreePiece K M.factorCount M.ambientDimension D := ⟨monomial e 1, hmem⟩
  have hx : x ≠ 0 := by
    intro h
    have hz := congrArg Subtype.val h
    simpa only [x, ZeroMemClass.coe_zero, monomial_eq_zero, one_ne_zero] using hz
  letI : Nontrivial (degreePiece K M.factorCount M.ambientDimension D) :=
    ⟨⟨x, 0, hx⟩⟩
  exact Module.finrank_pos

theorem exists_coordinate_basis : ∃ N : ℕ,
    Nonempty (Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D)) := by
  classical
  let d := Module.finrank K (degreePiece K M.factorCount M.ambientDimension D)
  have hd : 0 < d := degreePiece_finrank_pos M D
  let N := d - 1
  have hc : Fintype.card (projectiveSpace K N).Variable = d := by
    simp [MultiProjectiveSpace.Variable, projectiveSpace, N, Nat.sub_add_cancel hd]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨N, ⟨(Module.finBasis K (degreePiece K M.factorCount M.ambientDimension D)).reindex e.symm⟩⟩

end SegreVeronese
end PhilipponMultiplicity.Hilbert

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineClosedPoints

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints

open MvPolynomial
open Topology

variable {K : Type*} [Field K] {σ τ : Type*}

@[instance_reducible] def locusTopology (I : Ideal (MvPolynomial σ K)) :
    TopologicalSpace (zeroLocus K I) :=
  TopologicalSpace.induced (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
    inferInstance

theorem nonzero_sets_basis (I : Ideal (MvPolynomial σ K)) :
    letI := locusTopology I
    TopologicalSpace.IsTopologicalBasis
      (Set.range (fun P : MvPolynomial σ K => {x : zeroLocus K I | aeval x.val P ≠ 0})) := by
  let _ := locusTopology I
  have hb := PrimeSpectrum.isTopologicalBasis_basic_opens.induced
    (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
  have hpre (P : MvPolynomial σ K) :
      (fun x : zeroLocus K I => pointToPoint (k := K) x.val) ⁻¹'
        (PrimeSpectrum.basicOpen P : Set (PrimeSpectrum (MvPolynomial σ K))) =
      {x : zeroLocus K I | aeval x.val P ≠ 0} := by
    ext x
    change (P ∉ vanishingIdeal K {x.val}) ↔ aeval x.val P ≠ 0
    rw [mem_vanishingIdeal_singleton_iff]
  simpa only [← Set.range_comp, Function.comp_def, hpre] using hb

def evaluation (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    (MvPolynomial σ K ⧸ I) →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (aeval x.val) x.property

@[simp] theorem evaluation_mk (I : Ideal (MvPolynomial σ K))
    (x : zeroLocus K I) (P : MvPolynomial σ K) :
    evaluation I x (Ideal.Quotient.mk I P) = aeval x.val P := rfl

theorem evaluation_surjective (I : Ideal (MvPolynomial σ K))
    (x : zeroLocus K I) : Function.Surjective (evaluation I x) := by
  intro c
  exact ⟨Ideal.Quotient.mk I (C c), by simp⟩

def point (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    MaximalSpectrum (MvPolynomial σ K ⧸ I) :=
  ⟨RingHom.ker (evaluation I x).toRingHom,
    RingHom.ker_isMaximal_of_surjective _ (evaluation_surjective I x)⟩

theorem comap_point (I : Ideal (MvPolynomial σ K)) (x : zeroLocus K I) :
    Ideal.comap (Ideal.Quotient.mk I) (point I x).asIdeal =
      vanishingIdeal K {x.val} := by
  ext P
  change evaluation I x (Ideal.Quotient.mk I P) = 0 ↔
    P ∈ vanishingIdeal K {x.val}
  rw [evaluation_mk, mem_vanishingIdeal_singleton_iff]

theorem point_injective (I : Ideal (MvPolynomial σ K)) :
    Function.Injective (point I) := by
  intro x y h
  have heq : vanishingIdeal K {x.val} = vanishingIdeal K {y.val} := by
    rw [← comap_point I x, ← comap_point I y, h]
  apply Subtype.ext
  funext i
  have hx : X i - C (x.val i) ∈ vanishingIdeal K {x.val} := by
    simp
  rw [heq, mem_vanishingIdeal_singleton_iff] at hx
  simpa using (sub_eq_zero.mp (by simpa using hx)).symm

theorem point_surjective [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) : Function.Surjective (point I) := by
  intro m
  let q := Ideal.Quotient.mk I
  have hm : (Ideal.comap q m.asIdeal).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective q Ideal.Quotient.mk_surjective
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hm
  have hIx : x ∈ zeroLocus K I := by
    intro P hP
    have hmem : P ∈ Ideal.comap q m.asIdeal := by
      change Ideal.Quotient.mk I P ∈ m.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hP]
      exact m.asIdeal.zero_mem
    rw [hx, mem_vanishingIdeal_singleton_iff] at hmem
    exact hmem
  refine ⟨⟨x, hIx⟩, ?_⟩
  apply MaximalSpectrum.ext
  apply Ideal.comap_injective_of_surjective q Ideal.Quotient.mk_surjective
  exact (comap_point I ⟨x, hIx⟩).trans hx.symm

theorem evaluate_substitution (P : τ → MvPolynomial σ K) (x : σ → K)
    (F : MvPolynomial τ K) :
    aeval x (aeval P F) = aeval (fun i => aeval x (P i)) F := by
  have h : (aeval x).comp (aeval P) = aeval (fun i => aeval x (P i)) := by
    ext i
    simp
  exact DFunLike.congr_fun h F

theorem substitution_mem [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i))
    (F : MvPolynomial τ K) (hF : F ∈ I) : aeval P F ∈ J := by
  have hvan : aeval P F ∈ vanishingIdeal K (zeroLocus K J) := by
    intro x hx
    rw [evaluate_substitution]
    have heq : (fun i => aeval x (P i)) = (g ⟨x, hx⟩).val :=
      funext (fun i => (hg ⟨x, hx⟩ i).symm)
    rw [heq]
    exact (g ⟨x, hx⟩).property F hF
  rwa [vanishingIdeal_zeroLocus_eq_radical, hJ.radical] at hvan

def quotientMap [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i)) :
    (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J) :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ K J).comp (aeval P)) (by
    intro F hF
    change Ideal.Quotient.mk J (aeval P F) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (substitution_mem I J hJ g P hg F hF))

@[simp] theorem quotientMap_mk [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsRadical) (g : zeroLocus K J → zeroLocus K I)
    (P : τ → MvPolynomial σ K)
    (hg : ∀ x i, (g x).val i = aeval x.val (P i)) (F : MvPolynomial τ K) :
    quotientMap I J hJ g P hg (Ideal.Quotient.mk I F) =
      Ideal.Quotient.mk J (aeval P F) := rfl

end PhilipponMultiplicity.AffineClosedPoints

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveNullstellensatz

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponPointConeLinear

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.PointConeLinear
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
  (a : M.Variable → K) (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def equation (j : M.Variable) : M.CoordinateRing :=
  X j - C (a j / a ⟨j.1,b j.1⟩) * X ⟨j.1,b j.1⟩

def ideal : Ideal M.CoordinateRing := Ideal.span (Set.range (equation M a b))

theorem equation_homogeneous (j : M.Variable) :
    M.IsHomogeneous (equation M a b j) (Pi.single j.1 1) := by
  classical
  have hd : (fun i : M.FactorIndex => if i = j.1 then 1 else 0) = Pi.single j.1 1 := by
    funext i
    simp [Pi.single_apply]
  rw [← hd]
  exact
    (M.isHomogeneous_X j).sub M
      ((M.isHomogeneous_X ⟨j.1,b j.1⟩).C_mul M (a j / a ⟨j.1,b j.1⟩))

theorem equation_eval (hb : ∀ i, a ⟨i,b i⟩ ≠ 0) (j : M.Variable) :
    eval a (equation M a b j) = 0 := by
  simp [equation, div_mul_cancel₀ _ (hb j.1)]

theorem zeroLocus_eq_singleton (hb : ∀ i, a ⟨i,b i⟩ ≠ 0)
    (x : M.Point)
    (hrep : ∀ i, ∃ h : (fun j => a ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => a ⟨i,j⟩) h = x i) :
    M.zeroLocus (ideal M a b) = {x} := by
  ext y
  constructor
  · intro hy
    apply Set.mem_singleton_iff.mpr
    funext i
    obtain ⟨ha,hax⟩ := hrep i
    rw [← hax, ← Projectivization.mk_rep (y i)]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(y i).rep (b i) / a ⟨i,b i⟩, ?_⟩
    funext j
    have h := hy (equation M a b ⟨i,j⟩) (Ideal.subset_span ⟨⟨i,j⟩,rfl⟩)
    have h' : (y i).rep j = a ⟨i,j⟩ / a ⟨i,b i⟩ * (y i).rep (b i) := by
      simpa [equation, MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate,
        sub_eq_zero] using h
    simp only [Pi.smul_apply, smul_eq_mul, h']
    ring
  · intro hy
    have hyx := Set.mem_singleton_iff.mp hy
    subst y
    have hle : ideal M a b ≤ RingHom.ker (eval (M.coordinate x)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact (M.eval_eq_zero_iff_of_lift x a hrep _ _ (equation_homogeneous M a b j)).mp
        (equation_eval M a b hb j)
    exact hle

end PhilipponMultiplicity.PointConeLinear
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeronesePoints

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese

open MvPolynomial

variable {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D))

theorem basis_evaluation_ne_zero (p : M.Point) :
    (fun j => M.eval (b j).val p) ≠ 0 := by
  intro hz
  let ev := (aeval (M.coordinate p) : M.CoordinateRing →ₐ[K] K).toLinearMap.domRestrict
    (degreePiece K M.factorCount M.ambientDimension D)
  have hev : ev = 0 := by
    apply b.ext
    intro j
    exact congrFun hz j
  obtain ⟨P, hP, hp⟩ := M.exists_form_nonzero_at p D
  exact hp (LinearMap.congr_fun hev ⟨P, (M.degreePiece_iff P D).mpr hP⟩)

def pointCoordinates (p : M.Point) : Fin (N + 1) → K :=
  fun j => M.eval (b ⟨(0 : Fin 1), j⟩).val p

theorem pointCoordinates_ne_zero (p : M.Point) : pointCoordinates M D b p ≠ 0 := by
  intro h
  apply basis_evaluation_ne_zero M D b p
  funext v
  obtain ⟨i, j⟩ := v
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  exact congrFun h j

def pointMap (p : M.Point) : (projectiveSpace K N).Point :=
  fun _ => Projectivization.mk K (pointCoordinates M D b p) (pointCoordinates_ne_zero M D b p)

theorem pointMap_represents (p : M.Point) (i : (projectiveSpace K N).FactorIndex) :
    ∃ h : (fun j => M.eval (b ⟨i, j⟩).val p) ≠ 0,
      Projectivization.mk K (fun j => M.eval (b ⟨i, j⟩).val p) h = pointMap M D b p i := by
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  exact ⟨pointCoordinates_ne_zero M D b p, rfl⟩

theorem eval_substitution (p : M.Point) (P : (projectiveSpace K N).CoordinateRing) :
    M.eval (substitution M D b P) p = aeval (fun j => M.eval (b j).val p) P := by
  change aeval (M.coordinate p) (aeval (fun j => (b j).val) P) = _
  rw [AffineClosedPoints.evaluate_substitution]
  rfl

theorem pointMap_eval_eq_zero_iff (p : M.Point) (P : (projectiveSpace K N).CoordinateRing)
    (E : (projectiveSpace K N).FactorIndex → ℕ) (hP : (projectiveSpace K N).IsHomogeneous P E) :
    (projectiveSpace K N).eval P (pointMap M D b p) = 0 ↔
      M.eval (substitution M D b P) p = 0 := by
  rw [eval_substitution]
  exact ((projectiveSpace K N).eval_eq_zero_iff_of_lift _ _
    (pointMap_represents M D b p) P E hP).symm

theorem pointMap_regular :
    M.IsRegularAlong (projectiveSpace K N) id (pointMap M D b) := by
  letI := M.zariskiTopology
  intro p i
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, D,
    fun j => (b ⟨i, j⟩).val, ?_, ?_⟩
  · intro j
    exact (M.degreePiece_iff _ D).mp (b ⟨i, j⟩).property
  · intro q _
    exact pointMap_represents M D b q i

theorem pointMap_mem_diagonal_zeroLocus (hD : ∀ i, 1 ≤ D i)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (p : M.Point) (hp : p ∈ M.zeroLocus I) :
    pointMap M D b p ∈ (projectiveSpace K N).zeroLocus (diagonalIdeal M D b I) := by
  apply ((projectiveSpace K N).mem_zeroLocus_iff_homogeneous _
    (diagonalIdeal_homogeneous M D b hD I hI) _).mpr
  intro P hP E hE
  rw [pointMap_eval_eq_zero_iff M D b p P E hE]
  exact hp _ hP

theorem degree_evaluation_iff_of_pointMap_eq (p q : M.Point)
    (heq : pointMap M D b p = pointMap M D b q)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D) :
    M.eval P p = 0 ↔ M.eval P q = 0 := by
  have hmem : P ∈ (degreePiece K 1 (fun _ => N) (fun _ => 1)).map
      (substitution M D b).toLinearMap := by
    rw [substitution_degreePiece]
    simpa only [one_mul] using (M.degreePiece_iff P D).mpr hP
  obtain ⟨F, hF, hFP⟩ := hmem
  change substitution M D b F = P at hFP
  rw [← hFP, ← pointMap_eval_eq_zero_iff M D b p F (fun _ => 1)
    (((projectiveSpace K N).degreePiece_iff F _).mp hF),
    ← pointMap_eval_eq_zero_iff M D b q F (fun _ => 1)
    (((projectiveSpace K N).degreePiece_iff F _).mp hF), heq]

theorem pointMap_injective (hD : ∀ i, 1 ≤ D i) : Function.Injective (pointMap M D b) := by
  classical
  intro p q hpq
  choose a ha using fun i => Function.ne_iff.mp (q i).rep_nonzero
  let v := M.coordinate q
  have hv (i) : v ⟨i, a i⟩ ≠ 0 := ha i
  have hlift (i) : ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = q i :=
    ⟨(q i).rep_nonzero, (q i).mk_rep⟩
  have hp : p ∈ M.zeroLocus (PointConeLinear.ideal M v a) := by
    have hker : PointConeLinear.ideal M v a ≤ RingHom.ker (MvPolynomial.eval (M.coordinate p)) := by
      apply Ideal.span_le.mpr
      rintro L ⟨j, rfl⟩
      let E : M.FactorIndex → ℕ := Pi.single j.1 1
      have hED : E ≤ D := by
        intro i
        by_cases hi : i = j.1
        · subst i
          simpa [E] using hD j.1
        · simp [E, Pi.single_apply, hi]
      obtain ⟨Q, hQ, hQp⟩ := M.exists_form_nonzero_at p (D - E)
      have hhom : M.IsHomogeneous (PointConeLinear.equation M v a j * Q) D := by
        have h := (PointConeLinear.equation_homogeneous M v a j).mul M hQ
        have hd : E + (D - E) = D := add_tsub_cancel_of_le hED
        exact hd ▸ h
      have hzeroq : M.eval (PointConeLinear.equation M v a j * Q) q = 0 := by
        change MvPolynomial.eval v (PointConeLinear.equation M v a j * Q) = 0
        rw [map_mul, PointConeLinear.equation_eval M v a hv, zero_mul]
      have hzerop := (degree_evaluation_iff_of_pointMap_eq M D b p q hpq _ hhom).mpr hzeroq
      change M.eval (PointConeLinear.equation M v a j) p = 0
      have hmul : M.eval (PointConeLinear.equation M v a j) p * M.eval Q p = 0 := by
        simpa only [MultiProjectiveSpace.eval, map_mul] using hzerop
      exact (mul_eq_zero.mp hmul).resolve_right hQp
    exact hker
  rw [PointConeLinear.zeroLocus_eq_singleton M v a hv q hlift] at hp
  exact Set.mem_singleton_iff.mp hp

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponRelevantHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem variable_product_homogeneous (v : ∀ i, Fin (M.ambientDimension i + 1))
    (d : M.FactorIndex → ℕ) :
    M.IsHomogeneous (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) d := by
  classical
  apply (M.degreePiece_iff _ d).mp
  let w := blockWeight M.factorCount M.ambientDimension
  have hx (i : M.FactorIndex) : (X ⟨i, v i⟩ : M.CoordinateRing).IsWeightedHomogeneous w
      (w ⟨i, v i⟩) := isWeightedHomogeneous_X K w ⟨i, v i⟩
  have h := IsWeightedHomogeneous.prod (w := w) Finset.univ
    (fun i => (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i)
    (fun i => d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩)
    (fun i _ => (hx i).pow (d i))
  have heq : (∑ i, d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩) = d := by
    funext i
    simp [blockWeight, Pi.single_apply, Finset.sum_apply, smul_eq_mul]
  rwa [heq] at h

end PhilipponMultiplicity.Hilbert

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreLinearForms

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Pointwise
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial
variable {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D))

def linearForm : degreePiece K M.factorCount M.ambientDimension D →ₗ[K]
    homogeneousSubmodule (projectiveSpace K N).Variable K 1 :=
  b.constr K (fun j => ⟨X j, isHomogeneous_X K j⟩)

@[simp] theorem linearForm_basis (j : (projectiveSpace K N).Variable) :
    (linearForm M D b (b j)).val = X j := by
  simp [linearForm]

theorem substitution_linearForm (P : degreePiece K M.factorCount M.ambientDimension D) :
    substitution M D b (linearForm M D b P).val = P.val := by
  have h : ((substitution M D b).toLinearMap.comp
      (homogeneousSubmodule (projectiveSpace K N).Variable K 1).subtype).comp
      (linearForm M D b) = (degreePiece K M.factorCount M.ambientDimension D).subtype := by
    apply b.ext
    intro j
    simp [substitution]
  exact LinearMap.congr_fun h P

variable (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def pureProduct : M.CoordinateRing := ∏ i, X ⟨i, a i⟩

theorem pureProduct_homogeneous : M.IsHomogeneous (pureProduct M a) (fun _ => 1) := by
  simpa only [pureProduct, pow_one] using variable_product_homogeneous M a (fun _ => 1)

def pureForm : degreePiece K M.factorCount M.ambientDimension (fun _ => 1) :=
  ⟨pureProduct M a, (M.degreePiece_iff _ _).mpr (pureProduct_homogeneous M a)⟩

theorem degree_one_span_pureProducts :
    degreePiece K M.factorCount M.ambientDimension (fun _ => 1) =
      Submodule.span K (Set.range (pureProduct M)) := by
  classical
  rw [M.degreePiece_eq_blockProductSpace]
  simp only [MultiProjectiveSpace.blockProductSpace, pow_one,
    MultiProjectiveSpace.blockLinearSpace, Submodule.prod_span]
  congr 1
  ext P
  rw [Set.mem_fintype_prod]
  constructor
  · rintro ⟨g, hg, hP⟩
    choose a ha using hg
    refine ⟨a, ?_⟩
    simpa only [pureProduct, ha] using hP
  · rintro ⟨a, rfl⟩
    exact ⟨fun i => X ⟨i, a i⟩, fun i => ⟨a i, rfl⟩, rfl⟩

theorem pureForms_span_top :
    Submodule.span K (Set.range (pureForm M)) = ⊤ := by
  apply (Submodule.map_injective_of_injective
    (f := (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)).subtype)
    Subtype.val_injective)
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
  exact (degree_one_span_pureProducts M).symm

variable (b₁ : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))

theorem exists_pureForm_nonzero (p : (projectiveSpace K N).Point) :
    ∃ a, (projectiveSpace K N).eval
      (linearForm M (fun _ => 1) b₁ (pureForm M a)).val p ≠ 0 := by
  classical
  by_contra! h
  let ev := (aeval ((projectiveSpace K N).coordinate p) :
    (projectiveSpace K N).CoordinateRing →ₐ[K] K).toLinearMap.comp
    ((homogeneousSubmodule (projectiveSpace K N).Variable K 1).subtype.comp
      (linearForm M (fun _ => 1) b₁))
  have hker : Submodule.span K (Set.range (pureForm M)) ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact h a
  rw [pureForms_span_top] at hker
  have hz (j : (projectiveSpace K N).Variable) :
      (projectiveSpace K N).coordinate p j = 0 := by
    have hj := hker (Submodule.mem_top : b₁ j ∈ ⊤)
    change aeval ((projectiveSpace K N).coordinate p)
      (linearForm M (fun _ => 1) b₁ (b₁ j)).val = 0 at hj
    simpa only [linearForm_basis, aeval_X] using hj
  exact (p (0 : Fin 1)).rep_nonzero (funext (fun j => hz ⟨(0 : Fin 1), j⟩))

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponNormalizedChartRadicalReuse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section
namespace PhilipponMultiplicity.AffineChartDomain
universe u v
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)
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

end PhilipponMultiplicity.AffineChartDomain
namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end PhilipponMultiplicity.MixedFlag
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreInverseEquations

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))
    (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def omittedProduct (i : M.FactorIndex) : M.CoordinateRing :=
  ∏ k, X ⟨k, a k⟩ ^ (if k = i then 0 else 1)

theorem omittedProduct_homogeneous (i : M.FactorIndex) :
    M.IsHomogeneous (omittedProduct M a i) (fun k => if k = i then 0 else 1) :=
  variable_product_homogeneous M a _

theorem omittedProduct_mul_pivot (i : M.FactorIndex) :
    omittedProduct M a i * X ⟨i, a i⟩ = pureProduct M a := by
  classical
  calc
    _ = (∏ k, (X ⟨k, a k⟩ : M.CoordinateRing) ^ (if k = i then 0 else 1)) *
        (∏ k, (X ⟨k, a k⟩ : M.CoordinateRing) ^ (if k = i then 1 else 0)) := by
      simp [omittedProduct]
    _ = ∏ k, (X ⟨k, a k⟩ : M.CoordinateRing) ^ (if k = i then 0 else 1) *
        X ⟨k, a k⟩ ^ (if k = i then 1 else 0) := by rw [Finset.prod_mul_distrib]
    _ = pureProduct M a := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases h : k = i <;> simp [h]

set_option maxHeartbeats 50000 in
theorem prod_omittedProducts :
    (∏ i, omittedProduct M a i) = pureProduct M a ^ (M.factorCount - 1) := by
  classical
  have hS : pureProduct M a ≠ 0 := by
    change (∏ i, (X ⟨i, a i⟩ : M.CoordinateRing)) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_ne_zero (⟨i, a i⟩ : M.Variable))
  apply mul_right_cancel₀ hS
  calc
    _ = ∏ i, omittedProduct M a i * X ⟨i, a i⟩ := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = ∏ _i : M.FactorIndex, pureProduct M a := by
      apply Finset.prod_congr rfl
      intro i _
      exact omittedProduct_mul_pivot M a i
    _ = pureProduct M a ^ M.factorCount := by simp
    _ = pureProduct M a ^ (M.factorCount - 1) * pureProduct M a := by
      rw [← pow_succ, Nat.sub_add_cancel M.positive]

def replacementForm (v : M.Variable) :
    degreePiece K M.factorCount M.ambientDimension (fun _ => 1) :=
  ⟨omittedProduct M a v.1 * X v, by
    apply (M.degreePiece_iff _ _).mpr
    have h := (omittedProduct_homogeneous M a v.1).mul M (M.isHomogeneous_X v)
    convert h using 1
    ext i
    by_cases hi : i = v.1 <;> simp [hi]⟩

@[simp] theorem replacementForm_pivot (i : M.FactorIndex) :
    replacementForm M a ⟨i, a i⟩ = pureForm M a := by
  apply Subtype.ext
  exact omittedProduct_mul_pivot M a i

def inverseSubstitution : M.CoordinateRing →ₐ[K] (projectiveSpace K N).CoordinateRing :=
  aeval (fun v => (linearForm M (fun _ => 1) b (replacementForm M a v)).val)

theorem substitution_inverseSubstitution (P : M.CoordinateRing)
    (E : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P E) :
    substitution M (fun _ => 1) b (inverseSubstitution M b a P) =
      (∏ i, omittedProduct M a i ^ E i) * P := by
  have hcomp : (substitution M (fun _ => 1) b).comp (inverseSubstitution M b a) =
      aeval (fun v => omittedProduct M a v.1 * X v) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, inverseSubstitution, aeval_X,
      substitution_linearForm, replacementForm]
  change ((substitution M (fun _ => 1) b).comp (inverseSubstitution M b a)) P = _
  rw [hcomp]
  have h := AffineChartDomain.eval₂_block_scale M (C : K →+* M.CoordinateRing)
    P E hP (fun v => X v) (omittedProduct M a)
  change eval₂ C (fun v => omittedProduct M a v.1 * X v) P = _
  simpa only [coe_eval₂Hom, eval₂_eta] using h

theorem inverseSubstitution_mem_diagonal (I : Ideal M.CoordinateRing)
    (P : M.CoordinateRing) (hP : P ∈ I)
    (E : M.FactorIndex → ℕ) (hE : M.IsHomogeneous P E) :
    inverseSubstitution M b a P ∈ diagonalIdeal M (fun _ => 1) b I := by
  change substitution M (fun _ => 1) b (inverseSubstitution M b a P) ∈ I
  rw [substitution_inverseSubstitution M b a P E hE]
  exact I.mul_mem_left _ hP

theorem inverse_basis_relation (I : Ideal M.CoordinateRing)
    (j : (projectiveSpace K N).Variable) :
    inverseSubstitution M b a (b j).val -
      X j * (linearForm M (fun _ => 1) b (pureForm M a)).val ^ (M.factorCount - 1) ∈
        diagonalIdeal M (fun _ => 1) b I := by
  change substitution M (fun _ => 1) b _ ∈ I
  rw [map_sub, substitution_inverseSubstitution M b a _ (fun _ => 1)
    ((M.degreePiece_iff _ _).mp (b j).property)]
  simp only [pow_one, prod_omittedProducts, map_mul, map_pow,
    substitution_linearForm, pureForm]
  have hx : substitution M (fun _ => 1) b (X j) = (b j).val := by
    simp [substitution]
  rw [hx, mul_comm, sub_self]
  exact I.zero_mem

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveNormalizedLift

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
open MvPolynomial
variable {K : Type*} [Field K] (N : ℕ)

theorem exists_lift_normalized_by_linear_form
    (J : Ideal (projectiveSpace K N).CoordinateRing)
    (hJ : IsMultihomogeneousIdeal (projectiveSpace K N) J)
    (p : (projectiveSpace K N).Point) (hp : p ∈ (projectiveSpace K N).zeroLocus J)
    (F : (projectiveSpace K N).CoordinateRing) (hF : F.IsHomogeneous 1)
    (hn : (projectiveSpace K N).eval F p ≠ 0) :
    ∃ z : (projectiveSpace K N).Variable → K,
      (∀ P ∈ J, aeval z P = 0) ∧ aeval z F = 1 ∧
      (∀ i : (projectiveSpace K N).FactorIndex,
        ∃ h : (fun j => z ⟨i, j⟩) ≠ 0,
          Projectivization.mk K (fun j => z ⟨i, j⟩) h = p i) := by
  classical
  let Q := projectiveSpace K N
  let c := (Q.eval F p)⁻¹
  let z : Q.Variable → K := fun v => c * Q.coordinate p v
  have hc : c ≠ 0 := inv_ne_zero hn
  have heval (P : Q.CoordinateRing) (E : Q.FactorIndex → ℕ)
      (hP : Q.IsHomogeneous P E) : aeval z P = c ^ E (0 : Fin 1) * Q.eval P p := by
    have h := Q.eval_block_scale P E hP (Q.coordinate p) (fun _ => c)
    have hprod : (∏ i : Q.FactorIndex, c ^ E i) = c ^ E (0 : Fin 1) :=
      Fin.prod_univ_one _
    rw [hprod] at h
    exact h
  have hker : J ≤ RingHom.ker (aeval z : Q.CoordinateRing →ₐ[K] K).toRingHom := by
    rw [Q.homogeneousIdeal_eq_span J hJ]
    apply Ideal.span_le.mpr
    rintro P ⟨hP, E, hE⟩
    change aeval z P = 0
    rw [heval P E hE, hp P hP, mul_zero]
  refine ⟨z, fun P hP => hker hP, ?_, ?_⟩
  · rw [heval F (fun _ => 1) ((projective_homogeneous_iff N F 1).mpr hF)]
    simpa only [pow_one, c] using inv_mul_cancel₀ hn
  · intro i
    have hz : (fun j => z ⟨i, j⟩) ≠ 0 := by
      intro h
      apply (p i).rep_nonzero
      funext j
      have hj : c * (p i).rep j = 0 := congrFun h j
      exact (mul_eq_zero.mp hj).resolve_left hc
    refine ⟨hz, ?_⟩
    rw [← (p i).mk_rep]
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨c, rfl⟩

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponRegularMapComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem homogeneous_tuple_lift {ι : Type*} (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hn : (fun j => M.eval (P j) p) ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (P j)) h =
        Projectivization.mk K (fun j => M.eval (P j) p) hn := by
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
  let b : K := ∏ i, (a i : K) ^ D i
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (a i).ne_zero)
  have heval : (fun j => MvPolynomial.eval v (P j)) = b • (fun j => M.eval (P j) p) := by
    funext j
    rw [hv', M.eval_block_scale (P j) D (hP j) (M.coordinate p) (fun i => (a i : K))]
    rfl
  have hn' : (fun j => MvPolynomial.eval v (P j)) ≠ 0 := by
    rw [heval]
    exact smul_ne_zero hb hn
  exact ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨b, heval.symm⟩⟩

theorem IsRegularAlong.comp {X : Type u} {M N Q : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} {g : X → Q.Point}
    (hf : M.IsRegularAlong N e f) (hg : N.IsRegularAlong Q f g) :
    M.IsRegularAlong Q e g := by
  classical
  let := M.zariskiTopology
  let := N.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hPlift⟩ := hg x b
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp (hU.preimage hf.continuous)
  choose W hW hxW E R hR hRlift using hf x
  let pull (j : Fin (Q.ambientDimension b + 1)) :=
    eval₂ C (fun t : N.Variable => R t.1 t.2) (P j)
  refine ⟨V ∩ ⋂ a, W a, hV.inter (isOpen_iInter_of_finite hW),
    ⟨?_, mem_iInter.mpr hxW⟩, (fun i => ∑ a, D a * E a i), pull, ?_, ?_⟩
  · have hx : x ∈ f ⁻¹' U := hxU
    rwa [← hVeq] at hx
  · intro j
    exact (hP j).eval₂_blocks M N _ E (fun t => hR t.1 t.2)
  · intro y hy
    have hyU : f y ∈ U := by
      change y ∈ f ⁻¹' U
      rw [← hVeq]
      exact hy.1
    obtain ⟨hn, heq⟩ := hPlift y hyU
    have hlift (a : N.FactorIndex) := hRlift a y (mem_iInter.mp hy.2 a)
    obtain ⟨hn', heq'⟩ := N.homogeneous_tuple_lift (f y)
      (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) hlift P D hP hn
    have heval (j) : M.eval (pull j) (e y) =
        MvPolynomial.eval (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) (P j) := by
      dsimp only [eval, pull]
      rw [← eval_assoc]
      rfl
    simpa only [heval] using ⟨hn', heq'.trans heq⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreLocusSurjectivity

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))

theorem pointMap_represents_of_lift (p : M.Point) (w : M.Variable → K)
    (hw : ∀ i, ∃ h : (fun j => w ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => w ⟨i, j⟩) h = p i)
    (i : (projectiveSpace K N).FactorIndex) :
    ∃ h : (fun j => aeval w (b ⟨i, j⟩).val) ≠ 0,
      Projectivization.mk K (fun j => aeval w (b ⟨i, j⟩).val) h =
        pointMap M (fun _ => 1) b p i := by
  obtain ⟨hn, he⟩ := pointMap_represents M (fun _ => 1) b p i
  obtain ⟨hn', he'⟩ := M.homogeneous_tuple_lift p w hw (fun j => (b ⟨i, j⟩).val)
    (fun _ => 1) (fun j => (M.degreePiece_iff _ _).mp (b ⟨i, j⟩).property) hn
  exact ⟨hn', he'.trans he⟩

theorem exists_inverse_on_pivot
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (p : (projectiveSpace K N).Point)
    (hp : p ∈ (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I))
    (a : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (ha : (projectiveSpace K N).eval
      (linearForm M (fun _ => 1) b (pureForm M a)).val p ≠ 0) :
    ∃ q : M.Point, q ∈ M.zeroLocus I ∧ pointMap M (fun _ => 1) b q = p ∧
      ∀ i : M.FactorIndex,
        ∃ h : (fun j => (projectiveSpace K N).eval
          (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).val p) ≠ 0,
          Projectivization.mk K (fun j => (projectiveSpace K N).eval
            (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).val p) h = q i := by
  classical
  let Q := projectiveSpace K N
  obtain ⟨z, hz, hzS, hzrep⟩ := MultiProjectiveSpace.exists_lift_normalized_by_linear_form N
    (diagonalIdeal M (fun _ => 1) b I)
    (diagonalIdeal_homogeneous M (fun _ => 1) b (fun _ => le_rfl) I hI)
    p hp (linearForm M (fun _ => 1) b (pureForm M a)).val
    (linearForm M (fun _ => 1) b (pureForm M a)).property ha
  let w : M.Variable → K := fun v =>
    aeval z (linearForm M (fun _ => 1) b (replacementForm M a v)).val
  have hw_pivot (i : M.FactorIndex) : w ⟨i, a i⟩ = 1 := by
    simpa only [w, replacementForm_pivot] using hzS
  have hw (i : M.FactorIndex) : (fun j => w ⟨i, j⟩) ≠ 0 := by
    intro h
    have hz0 : w ⟨i, a i⟩ = 0 := congrFun h (a i)
    exact one_ne_zero ((hw_pivot i).symm.trans hz0)
  let q : M.Point := fun i => Projectivization.mk K (fun j => w ⟨i, j⟩) (hw i)
  have hqrep (i : M.FactorIndex) : ∃ h : (fun j => w ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => w ⟨i, j⟩) h = q i := ⟨hw i, rfl⟩
  have heval (P : M.CoordinateRing) :
      aeval w P = aeval z (inverseSubstitution M b a P) :=
    (AffineClosedPoints.evaluate_substitution _ z P).symm
  have hbasis (j : Q.Variable) : aeval w (b j).val = z j := by
    have h := hz _ (inverse_basis_relation M b a I j)
    rw [map_sub, map_mul, map_pow, aeval_X, hzS, one_pow, mul_one] at h
    exact (heval _).trans (sub_eq_zero.mp h)
  refine ⟨q, ?_, ?_, ?_⟩
  · apply (M.mem_zeroLocus_iff_homogeneous I hI q).mpr
    intro P hP E hE
    apply (M.eval_eq_zero_iff_of_lift q w hqrep P E hE).mp
    change aeval w P = 0
    rw [heval]
    exact hz _ (inverseSubstitution_mem_diagonal M b a I P hP E hE)
  · funext i
    obtain ⟨hn, he⟩ := pointMap_represents_of_lift M b q w hqrep i
    obtain ⟨hznon, hzpoint⟩ := hzrep i
    have hcoords : (fun j => aeval w (b ⟨i, j⟩).val) = (fun j => z ⟨i, j⟩) :=
      funext (fun j => hbasis ⟨i, j⟩)
    have hmk : Projectivization.mk K (fun j => aeval w (b ⟨i, j⟩).val) hn = p i := by
      simpa only [hcoords] using hzpoint
    exact he.symm.trans hmk
  · intro i
    let F : Fin (M.ambientDimension i + 1) → Q.CoordinateRing :=
      fun j => (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).val
    have hF (j) : Q.IsHomogeneous (F j) (fun _ => 1) :=
      (MultiProjectiveSpace.projective_homogeneous_iff N (F j) 1).mpr
        (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).property
    have hn : (fun j => Q.eval (F j) p) ≠ 0 := by
      intro h
      have hzero : Q.eval (F (a i)) p = 0 := congrFun h (a i)
      exact ha (by simpa only [F, replacementForm_pivot] using hzero)
    obtain ⟨hn', he⟩ := Q.homogeneous_tuple_lift p z hzrep F (fun _ => 1) hF hn
    exact ⟨hn, he.symm⟩

theorem pointMap_surjective_on_locus
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (p : (projectiveSpace K N).Point)
    (hp : p ∈ (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I)) :
    ∃ q ∈ M.zeroLocus I, pointMap M (fun _ => 1) b q = p := by
  obtain ⟨a, ha⟩ := exists_pureForm_nonzero M b p
  obtain ⟨q, hq, he, _⟩ := exists_inverse_on_pivot M b I hI p hp a ha
  exact ⟨q, hq, he⟩

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreLocusEquivalence

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)

def locusMap : M.zeroLocus I →
    (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I) :=
  fun x => ⟨pointMap M (fun _ => 1) b x.val,
    pointMap_mem_diagonal_zeroLocus M (fun _ => 1) b (fun _ => le_rfl) I hI x.val x.property⟩

theorem locusMap_bijective : Function.Bijective (locusMap M b I hI) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact pointMap_injective M (fun _ => 1) b (fun _ => le_rfl) (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx, he⟩ := pointMap_surjective_on_locus M b I hI y.val y.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩

def locusEquiv : M.zeroLocus I ≃
    (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I) :=
  Equiv.ofBijective (locusMap M b I hI) (locusMap_bijective M b I hI)

theorem locusEquiv_regular : M.IsRegularAlong (projectiveSpace K N)
    Subtype.val (fun x => (locusEquiv M b I hI x).val) :=
  (pointMap_regular M (fun _ => 1) b).comp_domain Subtype.val

theorem locusEquiv_inverse_regular : (projectiveSpace K N).IsRegularAlong M
    Subtype.val (fun x => ((locusEquiv M b I hI).symm x).val) := by
  intro x i
  obtain ⟨a, ha⟩ := exists_pureForm_nonzero M b x.val
  let S := (linearForm M (fun _ => 1) b (pureForm M a)).val
  have hS : (projectiveSpace K N).IsHomogeneous S (fun _ => 1) :=
    (MultiProjectiveSpace.projective_homogeneous_iff N S 1).mpr
      (linearForm M (fun _ => 1) b (pureForm M a)).property
  refine ⟨{p | (projectiveSpace K N).eval S p ≠ 0},
    (projectiveSpace K N).isOpen_basic S (fun _ => 1) hS, ha, fun _ => 1,
    fun j => (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).val,
    ?_, ?_⟩
  · intro j
    exact (MultiProjectiveSpace.projective_homogeneous_iff N _ 1).mpr
      (linearForm M (fun _ => 1) b (replacementForm M a ⟨i, j⟩)).property
  · intro y hy
    obtain ⟨q, hq, he, hlift⟩ := exists_inverse_on_pivot M b I hI y.val y.property a hy
    have heq : locusEquiv M b I hI ⟨q, hq⟩ = y := Subtype.ext he
    have hq' : (⟨q, hq⟩ : M.zeroLocus I) = (locusEquiv M b I hI).symm y := by
      rw [← heq, Equiv.symm_apply_apply]
    have hval : q = ((locusEquiv M b I hI).symm y).val := congrArg Subtype.val hq'
    obtain ⟨hn, hpoint⟩ := hlift i
    exact ⟨hn, hpoint.trans (congrFun hval i)⟩

def locusHomeomorph :
    letI := M.zariskiTopology
    letI := (projectiveSpace K N).zariskiTopology
    M.zeroLocus I ≃ₜ (projectiveSpace K N).zeroLocus (diagonalIdeal M (fun _ => 1) b I) := by
  letI := M.zariskiTopology
  letI := (projectiveSpace K N).zariskiTopology
  exact
    { toEquiv := locusEquiv M b I hI
      continuous_toFun := (locusEquiv_regular M b I hI).continuous.subtype_mk _
      continuous_invFun := (locusEquiv_inverse_regular M b I hI).continuous.subtype_mk _ }

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineMapFractions

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem eval_ratio_of_lift (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P Q : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    MvPolynomial.eval v P / MvPolynomial.eval v Q = M.eval P p / M.eval Q p := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h (p i).rep_nonzero).mp
      (he.trans (p i).mk_rep.symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K)),
    M.eval_block_scale Q D hQ (M.coordinate p) (fun i => (a i : K))]
  exact mul_div_mul_left _ _ hne

theorem IsRegularAlong.local_polynomial_lift
    {X : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point}
    (hf : M.IsRegularAlong N e f) (S : Set X) {σ : Type*}
    (a : S → σ → K) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ w : S, ∀ b, ∃ h : (fun i => aeval (a w) (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval (a w) (L ⟨b, i⟩)) h = e w.val b)
    (z : S) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ U : Set S, IsOpen U ∧ z ∈ U ∧
      ∃ R : N.Variable → MvPolynomial σ K,
        ∀ w ∈ U, ∀ b, ∃ h : (fun i => aeval (a w) (R ⟨b, i⟩)) ≠ 0,
          Projectivization.mk K (fun i => aeval (a w) (R ⟨b, i⟩)) h = f w.val b := by
  classical
  letI := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  choose U hU hzU D P hP hrep using hf z.val
  let V : Set S := ⋂ b, (fun w : S => e w.val) ⁻¹' U b
  let R : N.Variable → MvPolynomial σ K := fun t => eval₂ C L (P t.1 t.2)
  refine ⟨V, isOpen_iInter_of_finite (fun b =>
    (hU b).preimage (continuous_induced_dom.comp continuous_subtype_val)),
    mem_iInter.mpr hzU, R, ?_⟩
  intro w hw b
  obtain ⟨hn, he⟩ := hrep b w.val (mem_iInter.mp hw b)
  obtain ⟨hn', he'⟩ := M.homogeneous_tuple_lift (e w.val)
    (fun v => aeval (a w) (L v)) (hL w) (P b) (D b) (hP b) hn
  have heval (i) : aeval (a w) (R ⟨b, i⟩) =
      MvPolynomial.eval (fun v => aeval (a w) (L v)) (P b i) := by
    change MvPolynomial.eval (a w) (eval₂ C L (P b i)) = _
    rw [← eval_assoc]
    rfl
  simpa only [heval] using ⟨hn', he'.trans he⟩

theorem IsRegularAlong.local_fraction_of_target_ratio
    {X : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point}
    (hf : M.IsRegularAlong N e f) (S : Set X) {σ : Type*}
    (a : S → σ → K) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ w : S, ∀ b, ∃ h : (fun i => aeval (a w) (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval (a w) (L ⟨b, i⟩)) h = e w.val b)
    (P Q : N.CoordinateRing) (D : N.FactorIndex → ℕ)
    (hP : N.IsHomogeneous P D) (hQ : N.IsHomogeneous Q D)
    (hQne : ∀ w : S, N.eval Q (f w.val) ≠ 0) (z : S) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ U : Set S, IsOpen U ∧ z ∈ U ∧ ∃ A B : MvPolynomial σ K,
      ∀ w ∈ U, aeval (a w) B ≠ 0 ∧
        N.eval P (f w.val) / N.eval Q (f w.val) =
          aeval (a w) A / aeval (a w) B := by
  classical
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  obtain ⟨U, hU, hzU, R, hR⟩ := hf.local_polynomial_lift S a L hL z
  refine ⟨U, hU, hzU, eval₂ C R P, eval₂ C R Q, ?_⟩
  intro w hw
  have heval (F : N.CoordinateRing) : aeval (a w) (eval₂ C R F) =
      MvPolynomial.eval (fun v => aeval (a w) (R v)) F := by
    change MvPolynomial.eval (a w) (eval₂ C R F) = _
    rw [← eval_assoc]
    rfl
  simp only [heval]
  exact ⟨(N.eval_eq_zero_iff_of_lift _ _ (hR w hw) Q D hQ).not.mpr (hQne w),
    (N.eval_ratio_of_lift _ _ (hR w hw) P Q D hP hQ).symm⟩

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponMultihomogenization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem exists_multihomogenization_on_chart
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hbound : ∀ m ∈ P.support, ∀ i,
      (∑ k : Fin (M.ambientDimension i + 1), m ⟨i,k⟩) ≤ D i) :
    ∃ H : M.CoordinateRing, M.IsHomogeneous H D ∧
      ∀ v : M.Variable → K, (∀ i, v ⟨i,j i⟩ = 1) →
        MvPolynomial.eval v H = MvPolynomial.eval v P := by
  classical
  let a (m : M.Variable →₀ ℕ) (i : M.FactorIndex) :=
    ∑ k : Fin (M.ambientDimension i + 1), m ⟨i,k⟩
  let T (m : M.Variable →₀ ℕ) : M.CoordinateRing :=
    monomial m (coeff m P) * ∏ i, X (⟨i,j i⟩ : M.Variable) ^ (D i - a m i)
  refine ⟨∑ m ∈ P.support, T m,?_,?_⟩
  · apply M.isHomogeneous_sum
    intro m hm
    have hmon : M.IsHomogeneous (monomial m (coeff m P)) (a m) := by
      intro n hn i
      have hn' : n = m := Finset.mem_singleton.mp (support_monomial_subset hn)
      subst n
      rfl
    have hpowers := M.isHomogeneous_prod Finset.univ
      (fun i => X (⟨i,j i⟩ : M.Variable) ^ (D i - a m i))
      (fun i k => (D i - a m i) * (if k = i then 1 else 0))
      (fun i _ => (M.isHomogeneous_X ⟨i,j i⟩).pow M (D i - a m i))
    have hdeg : a m + (∑ i : M.FactorIndex,
        fun k => (D i - a m i) * (if k = i then 1 else 0)) = D := by
      funext i
      simp only [Pi.add_apply,Finset.sum_apply,mul_ite,mul_one,mul_zero]
      simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
      exact Nat.add_sub_of_le (hbound m hm i)
    rw [← hdeg]
    exact hmon.mul M hpowers
  · intro v hv
    rw [map_sum]
    calc
      ∑ m ∈ P.support, MvPolynomial.eval v (T m) =
          ∑ m ∈ P.support, MvPolynomial.eval v (monomial m (coeff m P)) := by
        apply Finset.sum_congr rfl
        intro m hm
        simp [T,map_prod,hv]
      _ = MvPolynomial.eval v P := by
        rw [← map_sum,support_sum_monomial_coeff]

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
variable {K : Type*} [Field K]

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponStandardAffineChart

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.StandardAffineChart
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def domain : Set M.Point := {x | ∀ i, (x i).rep (b i) ≠ 0}

def equations : Ideal M.CoordinateRing :=
  Ideal.span (Set.range (fun i : M.FactorIndex => X (⟨i, b i⟩ : M.Variable) - 1))

def ideal : Ideal M.CoordinateRing := (equations M b).radical

theorem mem_locus (v : M.Variable → K) :
    v ∈ zeroLocus K (ideal M b) ↔ ∀ i, v ⟨i, b i⟩ = 1 := by
  constructor
  · intro hv i
    have h := hv _ (Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i)))
    simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using h
  · intro hv
    have hI : equations M b ≤ RingHom.ker (aeval v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change aeval v (X (⟨i, b i⟩ : M.Variable) - 1) = 0
      simp [hv i]
    intro P hP
    exact radical_le_vanishingIdeal_zeroLocus (K := K) (equations M b) hP v
      (fun F hF => hI hF)

def normalize (x : domain M b) : zeroLocus K (ideal M b) :=
  ⟨fun v => (x.val v.1).rep v.2 / (x.val v.1).rep (b v.1),
    (mem_locus M b _).mpr (fun i => div_self (x.property i))⟩

theorem block_ne_zero (v : zeroLocus K (ideal M b)) (i : M.FactorIndex) :
    (fun j => v.val ⟨i, j⟩) ≠ 0 := by
  intro h
  have h0 := congrFun h (b i)
  have h1 := (mem_locus M b v.val).mp v.property i
  exact one_ne_zero (h1.symm.trans h0)

def projectivePoint (v : zeroLocus K (ideal M b)) : M.Point :=
  fun i => Projectivization.mk K (fun j => v.val ⟨i, j⟩) (block_ne_zero M b v i)

theorem projectivePoint_mem (v : zeroLocus K (ideal M b)) :
    projectivePoint M b v ∈ domain M b := by
  intro i hz
  have hlift (k : M.FactorIndex) : ∃ h : (fun j => v.val ⟨k, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v.val ⟨k, j⟩) h = projectivePoint M b v k :=
    ⟨block_ne_zero M b v k, rfl⟩
  have hn := (M.eval_eq_zero_iff_of_lift _ v.val hlift (X ⟨i, b i⟩) _
    (M.isHomogeneous_X _)).mpr (by
      simpa only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate] using hz)
  have h1 := (mem_locus M b v.val).mp v.property i
  exact one_ne_zero (h1.symm.trans (by simpa using hn))

def denormalize (v : zeroLocus K (ideal M b)) : domain M b :=
  ⟨projectivePoint M b v, projectivePoint_mem M b v⟩

theorem normalize_denormalize (v : zeroLocus K (ideal M b)) :
    normalize M b (denormalize M b v) = v := by
  apply Subtype.ext
  funext t
  have hlift (i : M.FactorIndex) : ∃ h : (fun j => v.val ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v.val ⟨i, j⟩) h = projectivePoint M b v i :=
    ⟨block_ne_zero M b v i, rfl⟩
  have h := M.eval_ratio_of_lift _ v.val hlift (X t) (X ⟨t.1, b t.1⟩) _
    (M.isHomogeneous_X t) (M.isHomogeneous_X ⟨t.1, b t.1⟩)
  have h1 := (mem_locus M b v.val).mp v.property t.1
  simpa only [normalize, denormalize, MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate,
    eval_X, h1, div_one] using h.symm

theorem denormalize_normalize (x : domain M b) :
    denormalize M b (normalize M b x) = x := by
  apply Subtype.ext
  funext i
  apply Eq.trans ?_ (x.val i).mk_rep
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨((x.val i).rep (b i))⁻¹, ?_⟩
  funext j
  change ((x.val i).rep (b i))⁻¹ * (x.val i).rep j =
    (x.val i).rep j / (x.val i).rep (b i)
  simp only [div_eq_mul_inv, mul_comm]

theorem domain_isOpen : @IsOpen M.Point M.zariskiTopology (domain M b) := by
  letI := M.zariskiTopology
  change IsOpen {x : M.Point | ∀ i, (x i).rep (b i) ≠ 0}
  rw [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  simpa only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate] using
    M.isOpen_basic (X ⟨i, b i⟩) _ (M.isHomogeneous_X _)

theorem normalize_represents (x : domain M b) (i : M.FactorIndex) :
    ∃ h : (fun j => (normalize M b x).val ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => (normalize M b x).val ⟨i, j⟩) h = x.val i := by
  refine ⟨block_ne_zero M b (normalize M b x) i, ?_⟩
  exact congrFun (congrArg Subtype.val (denormalize_normalize M b x)) i

theorem normalize_continuous :
    letI := M.zariskiTopology
    letI := AffineClosedPoints.locusTopology (ideal M b)
    Continuous (normalize M b) := by
  classical
  letI := M.zariskiTopology
  letI := AffineClosedPoints.locusTopology (ideal M b)
  apply (AffineClosedPoints.nonzero_sets_basis (ideal M b)).continuous_iff.mpr
  rintro _ ⟨P, rfl⟩
  let D : M.FactorIndex → ℕ := fun i =>
    ∑ m ∈ P.support, ∑ j : Fin (M.ambientDimension i + 1), m ⟨i, j⟩
  obtain ⟨H, hH, heval⟩ := M.exists_multihomogenization_on_chart P D b (by
    intro m hm i
    dsimp only [D]
    exact Finset.single_le_sum
      (f := fun m : M.Variable →₀ ℕ => ∑ j : Fin (M.ambientDimension i + 1), m ⟨i, j⟩)
      (fun _ _ => Nat.zero_le _) hm)
  have hset : (normalize M b) ⁻¹' {v | aeval v.val P ≠ 0} =
      {x : domain M b | M.eval H x.val ≠ 0} := by
    ext x
    have hn := heval (normalize M b x).val
      ((mem_locus M b _).mp (normalize M b x).property)
    have hiff := M.eval_eq_zero_iff_of_lift x.val (normalize M b x).val
      (normalize_represents M b x) H D hH
    rw [hn] at hiff
    exact hiff.not
  rw [hset]
  exact (M.isOpen_basic H D hH).preimage continuous_subtype_val

theorem denormalize_continuous :
    letI := M.zariskiTopology
    letI := AffineClosedPoints.locusTopology (ideal M b)
    Continuous (denormalize M b) := by
  classical
  letI := M.zariskiTopology
  letI := AffineClosedPoints.locusTopology (ideal M b)
  apply Continuous.subtype_mk
  change Continuous (projectivePoint M b)
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have hset : (projectivePoint M b) ⁻¹' {p | M.eval P p ≠ 0} =
      {v : zeroLocus K (ideal M b) | aeval v.val P ≠ 0} := by
    ext v
    have hlift (i : M.FactorIndex) : ∃ h : (fun j => v.val ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => v.val ⟨i, j⟩) h = projectivePoint M b v i :=
      ⟨block_ne_zero M b v i, rfl⟩
    exact (M.eval_eq_zero_iff_of_lift _ v.val hlift P D hP).not.symm
  rw [hset]
  exact (AffineClosedPoints.nonzero_sets_basis (ideal M b)).isOpen (Set.mem_range_self P)

end PhilipponMultiplicity.StandardAffineChart

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponDehomogenizedProjChart

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.DehomogenizedProjChart

open scoped DirectSum
open HomogeneousLocalization

variable {R S : Type*} [CommRing R] [SetLike S R] [AddSubgroupClass S R]
    (𝒜 : ℕ → S) [GradedRing 𝒜] {f : R} (hf : f ∈ 𝒜 1)

def component (n : ℕ) : 𝒜 n →+ HomogeneousLocalization.Away 𝒜 f where
  toFun x := HomogeneousLocalization.Away.mk 𝒜 hf n x (by simpa using x.property)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero]
    exact Localization.mk_zero _
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_add]
    change Localization.mk ((x : R) + (y : R)) _ =
      Localization.mk (x : R) _ + Localization.mk (y : R) _
    exact (Localization.add_mk_self _ _ _).symm

theorem component_one : component 𝒜 hf 0 (1 : 𝒜 0) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [component, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  simpa using (Localization.mk_one : (Localization.mk (1 : R) 1 : Localization.Away f) = 1)

theorem component_mul {i j : ℕ} (x : 𝒜 i) (y : 𝒜 j) :
    component 𝒜 hf (i + j) (@GradedMonoid.GMul.mul ℕ (fun n => ↥(𝒜 n)) _ _ i j x y) =
      component 𝒜 hf i x * component 𝒜 hf j y := by
  apply HomogeneousLocalization.val_injective
  simp only [component, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_mul,
    Localization.mk_mul]
  congr 1
  apply Subtype.ext
  exact pow_add f i j

def dehomogenize : R →+* HomogeneousLocalization.Away 𝒜 f :=
  (DirectSum.toSemiring (component 𝒜 hf) (component_one 𝒜 hf)
    (component_mul 𝒜 hf)).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

theorem dehomogenize_of_mem {n : ℕ} {a : R} (ha : a ∈ 𝒜 n) :
    dehomogenize 𝒜 hf a = HomogeneousLocalization.Away.mk 𝒜 hf n a (by simpa using ha) := by
  change DirectSum.toSemiring (component 𝒜 hf) (component_one 𝒜 hf)
    (component_mul 𝒜 hf) (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toSemiring_of]
  rfl

theorem dehomogenize_f : dehomogenize 𝒜 hf f = 1 := by
  rw [dehomogenize_of_mem 𝒜 hf hf]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, pow_one]
  exact Localization.mk_self ⟨f, Submonoid.mem_powers f⟩

def ideal (f : R) : Ideal R := Ideal.span {f - 1}

theorem quotient_f : Ideal.Quotient.mk (ideal f) f = 1 := by
  have h : Ideal.Quotient.mk (ideal f) (f - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [map_sub, map_one, sub_eq_zero] using h

def toQuotient : HomogeneousLocalization.Away 𝒜 f →+* (R ⧸ ideal f) :=
  (IsLocalization.Away.lift f (S := Localization.Away f)
    (g := Ideal.Quotient.mk (ideal f)) (by rw [quotient_f]; exact isUnit_one)).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))

theorem toQuotient_mk (n : ℕ) (a : R) (ha : a ∈ 𝒜 (n • (1 : ℕ))) :
    toQuotient 𝒜 (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      Ideal.Quotient.mk (ideal f) a := by
  dsimp only [toQuotient, RingHom.coe_comp, Function.comp_apply]
  rw [HomogeneousLocalization.algebraMap_apply]
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  simp only [map_pow, quotient_f, one_pow, one_mul]

def fromQuotient : (R ⧸ ideal f) →+* HomogeneousLocalization.Away 𝒜 f :=
  Ideal.Quotient.lift (ideal f) (dehomogenize 𝒜 hf) (by
    change Ideal.span {f - 1} ≤ RingHom.ker (dehomogenize 𝒜 hf)
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    change dehomogenize 𝒜 hf (f - 1) = 0
    rw [map_sub, dehomogenize_f, map_one, sub_self])

@[simp] theorem fromQuotient_mk (a : R) :
    fromQuotient 𝒜 hf (Ideal.Quotient.mk (ideal f) a) = dehomogenize 𝒜 hf a := rfl

theorem toQuotient_dehomogenize (a : R) :
    toQuotient 𝒜 (dehomogenize 𝒜 hf a) = Ideal.Quotient.mk (ideal f) a := by
  classical
  have hs := DirectSum.sum_support_decompose 𝒜 a
  calc
    toQuotient 𝒜 (dehomogenize 𝒜 hf a) =
        toQuotient 𝒜 (dehomogenize 𝒜 hf
          (∑ n ∈ (DirectSum.decompose 𝒜 a).support,
            ((DirectSum.decompose 𝒜 a n : 𝒜 n) : R))) := congrArg _ (congrArg _ hs.symm)
    _ = ∑ n ∈ (DirectSum.decompose 𝒜 a).support,
          Ideal.Quotient.mk (ideal f) ((DirectSum.decompose 𝒜 a n : 𝒜 n) : R) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [dehomogenize_of_mem 𝒜 hf (DirectSum.decompose 𝒜 a n).property,
        toQuotient_mk]
    _ = Ideal.Quotient.mk (ideal f) a := by rw [← map_sum, hs]

@[simp] theorem toQuotient_fromQuotient (a : R ⧸ ideal f) :
    toQuotient 𝒜 (fromQuotient 𝒜 hf a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact toQuotient_dehomogenize 𝒜 hf a

@[simp] theorem fromQuotient_toQuotient (a : HomogeneousLocalization.Away 𝒜 f) :
    fromQuotient 𝒜 hf (toQuotient 𝒜 a) = a := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf a
  rw [toQuotient_mk, fromQuotient_mk]
  exact dehomogenize_of_mem 𝒜 hf (by simpa using ha)

def ringEquiv : HomogeneousLocalization.Away 𝒜 f ≃+* (R ⧸ ideal f) :=
  { toQuotient 𝒜 with
    invFun := fromQuotient 𝒜 hf
    left_inv := fromQuotient_toQuotient 𝒜 hf
    right_inv := toQuotient_fromQuotient 𝒜 hf }

@[simp] theorem ringEquiv_mk (n : ℕ) (a : R) (ha : a ∈ 𝒜 (n • (1 : ℕ))) :
    ringEquiv 𝒜 hf (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      Ideal.Quotient.mk (ideal f) a := toQuotient_mk 𝒜 hf n a ha

end PhilipponMultiplicity.DehomogenizedProjChart

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHomogeneousQuotientGrading

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.HomogeneousQuotientGrading

open scoped DirectSum

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜] (I : Ideal R)

def piece (n : ℕ) : Submodule K (R ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ K I).toLinearMap

instance : SetLike.GradedMonoid (piece 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one (Ideal.Quotient.mk I)⟩
  mul_mem := by
    rintro i j x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mk I) a b⟩

def projection (hI : I.IsHomogeneous 𝒜) (n : ℕ) : (R ⧸ I) →ₗ[K] (R ⧸ I) :=
  (I.restrictScalars K).liftQ
    ((Ideal.Quotient.mkₐ K I).toLinearMap.comp (GradedAlgebra.proj 𝒜 n)) (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI n ha))

theorem projection_on_piece (hI : I.IsHomogeneous 𝒜) (n m : ℕ)
    {x : R ⧸ I} (hx : x ∈ piece 𝒜 I m) :
    projection 𝒜 I hI n x = if n = m then x else 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change Ideal.Quotient.mk I (GradedAlgebra.proj 𝒜 n a) = _
  rw [GradedAlgebra.proj_apply]
  by_cases h : n = m
  · subst m
    rw [DirectSum.decompose_of_mem_same 𝒜 ha, if_pos rfl]
    rfl
  · rw [DirectSum.decompose_of_mem_ne 𝒜 ha (Ne.symm h), map_zero, if_neg h]

theorem piece_iSupIndep (hI : I.IsHomogeneous 𝒜) : iSupIndep (piece 𝒜 I) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hz n hn
  have h := congrArg (projection 𝒜 I hI n) hz
  rw [map_sum, map_zero] at h
  have heq : (∑ m ∈ s, projection 𝒜 I hI n (v m)) = v n := by
    rw [Finset.sum_eq_single n]
    · simpa using projection_on_piece 𝒜 I hI n n (hv n hn)
    · intro m hm hmn
      rw [projection_on_piece 𝒜 I hI n m (hv m hm), if_neg hmn.symm]
    · exact fun hnot => False.elim (hnot hn)
  exact heq.symm.trans h

theorem iSup_piece : (⨆ n, piece 𝒜 I n) = ⊤ := by
  change (⨆ n, (𝒜 n).map (Ideal.Quotient.mkₐ K I).toLinearMap) = ⊤
  rw [← Submodule.map_iSup,
    (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mk_surjective)

@[instance_reducible]
def gradedAlgebra (hI : I.IsHomogeneous 𝒜) : GradedAlgebra (piece 𝒜 I) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (piece_iSupIndep 𝒜 I hI) (iSup_piece 𝒜 I)).gradedAlgebra

end PhilipponMultiplicity.HomogeneousQuotientGrading

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponHomogeneousQuotientCharts

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.HomogeneousQuotientGrading

open AlgebraicGeometry CategoryTheory

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜] (I : Ideal R)

theorem quotient_mem_piece {n : ℕ} {a : R} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I a ∈ piece 𝒜 I n := ⟨a, ha, rfl⟩

def normalizedIdeal (f : R) : Ideal R := I ⊔ Ideal.span {f - 1}

theorem normalizedIdeal_map (f : R) :
    DehomogenizedProjChart.ideal (Ideal.Quotient.mk I f) =
      (Ideal.span {f - 1}).map (Ideal.Quotient.mk I) := by
  rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  rfl

variable [GradedAlgebra (piece 𝒜 I)]

def normalizedRingEquiv {f : R} (hf : f ∈ 𝒜 1) :
    HomogeneousLocalization.Away (piece 𝒜 I) (Ideal.Quotient.mk I f) ≃+*
      (R ⧸ normalizedIdeal I f) :=
  (DehomogenizedProjChart.ringEquiv (piece 𝒜 I) (quotient_mem_piece 𝒜 I hf)).trans
    ((Ideal.quotEquivOfEq (normalizedIdeal_map I f)).trans
      (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {f - 1})))

@[simp] theorem normalizedRingEquiv_mk {f : R} (hf : f ∈ 𝒜 1)
    (n : ℕ) (a : R) (ha : a ∈ 𝒜 n) :
    normalizedRingEquiv 𝒜 I hf
      (HomogeneousLocalization.Away.mk (piece 𝒜 I) (quotient_mem_piece 𝒜 I hf) n
        (Ideal.Quotient.mk I a) (by simpa using quotient_mem_piece 𝒜 I ha)) =
      Ideal.Quotient.mk (normalizedIdeal I f) a := by
  rw [normalizedRingEquiv, RingEquiv.trans_apply, DehomogenizedProjChart.ringEquiv_mk,
    RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

def normalizedSchemeIso {f : R} (hf : f ∈ 𝒜 1) :
    (Proj.basicOpen (piece 𝒜 I) (Ideal.Quotient.mk I f)).toScheme ≅
      Spec (.of (R ⧸ normalizedIdeal I f)) :=
  Proj.basicOpenIsoSpec (piece 𝒜 I) (Ideal.Quotient.mk I f)
    (quotient_mem_piece 𝒜 I hf) (by decide) ≪≫
    Scheme.Spec.mapIso (normalizedRingEquiv 𝒜 I hf).symm.toCommRingCatIso.op

theorem normalizedIdeal_isRadical (hred : I.IsRadical) {f : R} (hf : f ∈ 𝒜 1) :
    (normalizedIdeal I f).IsRadical := by
  letI : IsReduced (R ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hred
  letI : IsReduced (HomogeneousLocalization.Away (piece 𝒜 I) (Ideal.Quotient.mk I f)) :=
    isReduced_of_injective
      (algebraMap (HomogeneousLocalization.Away (piece 𝒜 I) (Ideal.Quotient.mk I f))
        (Localization.Away (Ideal.Quotient.mk I f)))
      (HomogeneousLocalization.val_injective _)
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  exact isReduced_of_injective (normalizedRingEquiv 𝒜 I hf).symm
    (normalizedRingEquiv 𝒜 I hf).symm.injective

end PhilipponMultiplicity.HomogeneousQuotientGrading

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineRegularFunctions

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace PhilipponMultiplicity.AffineRegularFunctions
open MvPolynomial

variable {K σ X : Type*} [Field K]

def clearingIdeal (a : X → σ → K) (f : X → K) : Ideal (MvPolynomial σ K) where
  carrier := {P | ∃ Q : MvPolynomial σ K, ∀ x, f x * aeval (a x) P = aeval (a x) Q}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro P Q ⟨P', hP⟩ ⟨Q', hQ⟩
    refine ⟨P' + Q', ?_⟩
    intro x
    simp only [map_add, mul_add, hP x, hQ x]
  smul_mem' := by
    rintro P Q ⟨Q', hQ⟩
    refine ⟨P * Q', ?_⟩
    intro x
    simp only [smul_eq_mul, map_mul]
    calc
      f x * (aeval (a x) P * aeval (a x) Q) =
          aeval (a x) P * (f x * aeval (a x) Q) := by ring
      _ = aeval (a x) P * aeval (a x) Q' := by rw [hQ x]

theorem ideal_le_clearingIdeal (J : Ideal (MvPolynomial σ K))
    (a : X → zeroLocus K J) (f : X → K) :
    J ≤ clearingIdeal (fun x => (a x).val) f := by
  intro P hP
  refine ⟨0, ?_⟩
  intro x
  rw [(a x).property P hP, mul_zero, map_zero]

theorem local_fraction_clears [TopologicalSpace X]
    (J : Ideal (MvPolynomial σ K))
    (a : @Homeomorph X (zeroLocus K J) _ (AffineClosedPoints.locusTopology J))
    (f : X → K) (x : X)
    (hloc : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ P Q : MvPolynomial σ K, ∀ z ∈ U,
        aeval (a z).val Q ≠ 0 ∧ f z = aeval (a z).val P / aeval (a z).val Q) :
    ∃ H ∈ clearingIdeal (fun z => (a z).val) f, aeval (a x).val H ≠ 0 := by
  let _ := AffineClosedPoints.locusTopology J
  obtain ⟨U, hU, hx, P, Q, hPQ⟩ := hloc
  have hopen : IsOpen (a.symm ⁻¹' U) := hU.preimage a.symm.continuous
  have hmem : a x ∈ a.symm ⁻¹' U := by simpa using hx
  obtain ⟨W, ⟨H, rfl⟩, hHx, hHU⟩ :=
    (AffineClosedPoints.nonzero_sets_basis J).isOpen_iff.mp hopen (a x) hmem
  have hin (z : X) (hz : aeval (a z).val H ≠ 0) : z ∈ U := by
    have h := hHU hz
    simpa using h
  refine ⟨H * Q, ⟨H * P, ?_⟩, ?_⟩
  · intro z
    simp only [map_mul]
    by_cases hHz : aeval (a z).val H = 0
    · simp [hHz]
    · obtain ⟨hQ, hf⟩ := hPQ z (hin z hHz)
      have heq := (eq_div_iff hQ).mp hf
      calc
        f z * (aeval (a z).val H * aeval (a z).val Q) =
            aeval (a z).val H * (f z * aeval (a z).val Q) := by ring
        _ = aeval (a z).val H * aeval (a z).val P := by rw [heq]
  · rw [map_mul]
    exact mul_ne_zero hHx (hPQ x hx).1

theorem eq_top_of_no_zero [IsAlgClosed K] [Finite σ]
    (J D : Ideal (MvPolynomial σ K)) (hJD : J ≤ D)
    (hnz : ∀ x : zeroLocus K J, ∃ P ∈ D, aeval x.val P ≠ 0) : D = ⊤ := by
  have hempty : zeroLocus K D = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxJ : x ∈ zeroLocus K J := zeroLocus_anti_mono hJD hx
    obtain ⟨P, hP, hnP⟩ := hnz ⟨x, hxJ⟩
    exact hnP (hx P hP)
  apply Ideal.radical_eq_top.mp
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), hempty, vanishingIdeal_empty]

theorem locally_rational_is_polynomial [IsAlgClosed K] [Finite σ] [TopologicalSpace X]
    (J : Ideal (MvPolynomial σ K))
    (a : @Homeomorph X (zeroLocus K J) _ (AffineClosedPoints.locusTopology J))
    (f : X → K)
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ P Q : MvPolynomial σ K, ∀ z ∈ U,
        aeval (a z).val Q ≠ 0 ∧ f z = aeval (a z).val P / aeval (a z).val Q) :
    ∃ P : MvPolynomial σ K, ∀ x, f x = aeval (a x).val P := by
  let _ := AffineClosedPoints.locusTopology J
  have hD : clearingIdeal (fun z => (a z).val) f = ⊤ := by
    apply eq_top_of_no_zero J _ (ideal_le_clearingIdeal J a f)
    intro y
    obtain ⟨P, hP, hnP⟩ := local_fraction_clears J a f (a.symm y) (hloc _)
    exact ⟨P, hP, by simpa using hnP⟩
  have hone : (1 : MvPolynomial σ K) ∈ clearingIdeal (fun z => (a z).val) f := by
    rw [hD]
    trivial
  obtain ⟨P, hP⟩ := hone
  exact ⟨P, fun x => by simpa using hP x⟩

end PhilipponMultiplicity.AffineRegularFunctions

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineSchemeRealization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] {σ τ υ : Type}

theorem evaluation_ext [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsRadical)
    {a b : MvPolynomial σ K ⧸ I}
    (h : ∀ x : zeroLocus K I, evaluation I x a = evaluation I x b) : a = b := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply sub_eq_zero.mp
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  rw [← hI.radical, ← vanishingIdeal_zeroLocus_eq_radical (K := K)]
  intro x hx
  simpa only [map_sub, evaluation_mk] using sub_eq_zero.mpr (h ⟨x, hx⟩)

theorem algHom_ext [IsAlgClosed K] [Finite σ]
    (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical)
    {A : Type u} [CommRing A] [Algebra K A]
    {φ ψ : A →ₐ[K] (MvPolynomial σ K ⧸ J)}
    (h : ∀ x a, evaluation J x (φ a) = evaluation J x (ψ a)) : φ = ψ := by
  ext a
  exact evaluation_ext J hJ (fun x => h x a)

def pointMap (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J))
    (x : zeroLocus K J) : zeroLocus K I := by
  let v : τ → K := fun j => evaluation J x (φ (Ideal.Quotient.mk I (X j)))
  have hv : aeval v = ((evaluation J x).comp φ).comp (Ideal.Quotient.mkₐ K I) := by
    ext j
    simp [v]
  refine ⟨v, ?_⟩
  intro P hP
  rw [hv]
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hP]

@[simp] theorem pointMap_coordinate
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J))
    (x : zeroLocus K J) (j : τ) :
    (pointMap I J φ x).val j = evaluation J x (φ (Ideal.Quotient.mk I (X j))) := rfl

@[simp] theorem evaluation_pointMap
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J))
    (x : zeroLocus K J) (a : MvPolynomial τ K ⧸ I) :
    evaluation I (pointMap I J φ x) a = evaluation J x (φ a) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h : aeval (pointMap I J φ x).val =
      ((evaluation J x).comp φ).comp (Ideal.Quotient.mkₐ K I) := by
    ext j
    simp
  exact DFunLike.congr_fun h P

theorem pointMap_injective [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical) :
    Function.Injective (pointMap I J) := by
  intro φ ψ h
  apply algHom_ext J hJ
  intro x a
  rw [← evaluation_pointMap I J φ, ← evaluation_pointMap I J ψ, h]

def IsLocallyRationalMap (I : Ideal (MvPolynomial τ K))
    (J : Ideal (MvPolynomial σ K)) (f : zeroLocus K J → zeroLocus K I) : Prop :=
  let _ := locusTopology J
  ∀ x j, ∃ U : Set (zeroLocus K J), IsOpen U ∧ x ∈ U ∧
    ∃ P Q : MvPolynomial σ K, ∀ z ∈ U,
      aeval z.val Q ≠ 0 ∧ (f z).val j = aeval z.val P / aeval z.val Q

theorem isLocallyRationalMap_iff_polynomial [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (f : zeroLocus K J → zeroLocus K I) :
    IsLocallyRationalMap I J f ↔
      ∃ P : τ → MvPolynomial σ K, ∀ x j, (f x).val j = aeval x.val (P j) := by
  classical
  let _ := locusTopology J
  constructor
  · intro h
    have hex (j : τ) : ∃ P : MvPolynomial σ K,
        ∀ x : zeroLocus K J, (f x).val j = aeval x.val P :=
      AffineRegularFunctions.locally_rational_is_polynomial J (Homeomorph.refl _)
        (fun x => (f x).val j) (fun x => h x j)
    choose P hP using hex
    exact ⟨P, fun x j => hP j x⟩
  · rintro ⟨P, hP⟩ x j
    exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, P j, 1, fun z _ => by simp [hP z j]⟩

theorem existsUnique_pullback [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical)
    (f : zeroLocus K J → zeroLocus K I) (hf : IsLocallyRationalMap I J f) :
    ∃! φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J),
      pointMap I J φ = f := by
  obtain ⟨P, hP⟩ := (isLocallyRationalMap_iff_polynomial I J f).mp hf
  refine ⟨quotientMap I J hJ f P hP, ?_, ?_⟩
  · funext x
    apply Subtype.ext
    funext j
    simp [hP x j]
  · intro φ hφ
    apply pointMap_injective I J hJ
    rw [hφ]
    funext x
    apply Subtype.ext
    funext j
    simp [hP x j]

def affineScheme (I : Ideal (MvPolynomial σ K)) : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial σ K ⧸ I))

def structureMap (I : Ideal (MvPolynomial σ K)) : affineScheme I ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ I)))

def schemeMap (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J)) :
    affineScheme J ⟶ affineScheme I :=
  Spec.map (CommRingCat.ofHom φ.toRingHom)

@[simp] theorem schemeMap_over
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J)) :
    schemeMap I J φ ≫ structureMap I = structureMap J := by
  rw [schemeMap, structureMap, ← Spec.map_comp]
  congr 1
  ext a
  exact φ.commutes a

theorem schemeMap_point
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J))
    (x : zeroLocus K J) :
    schemeMap I J φ (point J x).toPrimeSpectrum =
      (point I (pointMap I J φ x)).toPrimeSpectrum := by
  apply PrimeSpectrum.ext
  ext a
  change evaluation J x (φ a) = 0 ↔ evaluation I (pointMap I J φ x) a = 0
  rw [evaluation_pointMap]

end PhilipponMultiplicity.AffineClosedPoints

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffineSchemeMaps

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {K : Type u} [Field K] {σ τ υ : Type}

def coordinateHom (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (f : affineScheme J ⟶ affineScheme I)
    (hf : f ≫ structureMap I = structureMap J) :
    (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J) :=
  { (Spec.preimage f).hom with
    commutes' := fun a => by
      have h : CommRingCat.ofHom (algebraMap K (MvPolynomial τ K ⧸ I)) ≫
          Spec.preimage f = CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ J)) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact hf
      exact ConcreteCategory.congr_hom h a }

@[simp] theorem schemeMap_coordinateHom
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K))
    (f : affineScheme J ⟶ affineScheme I)
    (hf : f ≫ structureMap I = structureMap J) :
    schemeMap I J (coordinateHom I J f hf) = f := Spec.map_preimage f

theorem primePoint_injective (I : Ideal (MvPolynomial σ K)) :
    Function.Injective (fun x : zeroLocus K I => (point I x).toPrimeSpectrum) := by
  intro x y h
  apply point_injective I
  apply MaximalSpectrum.ext
  exact congrArg PrimeSpectrum.asIdeal h

theorem existsUnique_schemeRealization [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical)
    (f : zeroLocus K J → zeroLocus K I) (hf : IsLocallyRationalMap I J f) :
    ∃! F : affineScheme J ⟶ affineScheme I,
      F ≫ structureMap I = structureMap J ∧
      ∀ x : zeroLocus K J,
        F (point J x).toPrimeSpectrum = (point I (f x)).toPrimeSpectrum := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_pullback I J hJ f hf
  refine ⟨schemeMap I J φ, ⟨schemeMap_over I J φ, ?_⟩, ?_⟩
  · intro x
    rw [schemeMap_point, hφ]
  · intro F hF
    let ψ := coordinateHom I J F hF.1
    have hψ : pointMap I J ψ = f := by
      funext x
      apply primePoint_injective I
      change (point I (pointMap I J (coordinateHom I J F hF.1) x)).toPrimeSpectrum =
        (point I (f x)).toPrimeSpectrum
      rw [← schemeMap_point, schemeMap_coordinateHom]
      exact hF.2 x
    have heq := huniq ψ hψ
    rw [← schemeMap_coordinateHom I J F hF.1]
    exact congrArg (schemeMap I J) heq

end PhilipponMultiplicity.AffineClosedPoints

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveCoordinateScheme

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u

theorem proj_isReduced {R S : Type*} [CommRing R] [SetLike S R] [AddSubgroupClass S R]
    (𝒜 : ℕ → S) [GradedRing 𝒜] [_root_.IsReduced R] : IsReduced (Proj 𝒜) := by
  have hcharts (i : (Proj.affineOpenCover 𝒜).I₀) :
      IsReduced ((Proj.affineOpenCover 𝒜).openCover.X i) := by
    letI : _root_.IsReduced (HomogeneousLocalization.Away 𝒜 (i.2 : R)) :=
      isReduced_of_injective
        (algebraMap (HomogeneousLocalization.Away 𝒜 (i.2 : R)) (Localization.Away (i.2 : R)))
        (HomogeneousLocalization.val_injective _)
    change IsReduced (Spec (.of (HomogeneousLocalization.Away 𝒜 (i.2 : R))))
    infer_instance
  letI := hcharts
  exact IsReduced.of_openCover _ (Proj.affineOpenCover 𝒜).openCover

variable {K : Type u} [Field K] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev grading (I : Ideal (MvPolynomial σ K)) : ℕ → Submodule K (MvPolynomial σ K ⧸ I) :=
  HomogeneousQuotientGrading.piece (homogeneousSubmodule σ K) I

local instance zeroAlgebra (I : Ideal (MvPolynomial σ K)) :
    Algebra (grading I 0) (MvPolynomial σ K ⧸ I) :=
  Algebra.ofSubsemiring (SetLike.GradeZero.subsemiring (grading I))

local instance zeroSMul (I : Ideal (MvPolynomial σ K)) :
    SMul (grading I 0) (MvPolynomial σ K ⧸ I) := (zeroAlgebra I).toSMul

def scheme (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : Scheme.{u} := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact Proj (grading I)

theorem zero_algebraMap_surjective (I : Ideal (MvPolynomial σ K)) :
    Function.Surjective (algebraMap K (grading I 0)) := by
  rintro ⟨a, ha⟩
  obtain ⟨P, hP, hPa⟩ := ha
  have hC : P = C (P.coeff 0) := by
    exact (homogeneousComponent_of_mem hP).symm.trans (homogeneousComponent_zero _)
  refine ⟨P.coeff 0, Subtype.ext ?_⟩
  change Ideal.Quotient.mk I (C (P.coeff 0)) = a
  rw [← hC]
  exact hPa

def structureMap (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : scheme I hI ⟶ Spec (.of K) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact Proj.toSpecZero (grading I) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))

theorem finiteType_over_zero [Finite σ] (I : Ideal (MvPolynomial σ K)) :
    Algebra.FiniteType (grading I 0) (MvPolynomial σ K ⧸ I) := by
  letI : IsScalarTower K (grading I 0) (MvPolynomial σ K ⧸ I) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := grading I 0)
      (A := MvPolynomial σ K ⧸ I) (fun _ => rfl)
  letI : Algebra.FiniteType K (MvPolynomial σ K ⧸ I) :=
    Algebra.FiniteType.quotient K I
  exact Algebra.FiniteType.of_restrictScalars_finiteType K (grading I 0) (MvPolynomial σ K ⧸ I)

theorem structureMap_isProper [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : IsProper (structureMap I hI) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  letI : Algebra.FiniteType (grading I 0) (MvPolynomial σ K ⧸ I) :=
    finiteType_over_zero I
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (zero_algebraMap_surjective I)
  change IsProper (Proj.toSpecZero (grading I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0))))
  infer_instance

theorem scheme_isReduced (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hred : I.IsRadical) :
    IsReduced (scheme I hI) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  letI : _root_.IsReduced (MvPolynomial σ K ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp hred
  exact proj_isReduced (grading I)

def chartIdeal (I : Ideal (MvPolynomial σ K)) (j : σ) : Ideal (MvPolynomial σ K) :=
  HomogeneousQuotientGrading.normalizedIdeal I (X j)

theorem chartIdeal_isRadical (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hred : I.IsRadical) (j : σ) :
    (chartIdeal I j).IsRadical := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact HomogeneousQuotientGrading.normalizedIdeal_isRadical
    (homogeneousSubmodule σ K) I hred (isHomogeneous_X K j)

def chartIso (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
    (Proj.basicOpen (grading I) (Ideal.Quotient.mk I (X j))).toScheme ≅
      AffineClosedPoints.affineScheme (chartIdeal I j) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact HomogeneousQuotientGrading.normalizedSchemeIso
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j)

theorem coordinates_generate (I : Ideal (MvPolynomial σ K)) :
    Algebra.adjoin (grading I 0) (Set.range (fun j : σ => Ideal.Quotient.mk I (X j))) = ⊤ := by
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction P using MvPolynomial.induction_on with
  | C a =>
      exact (Algebra.adjoin (grading I 0) _).algebraMap_mem (algebraMap K (grading I 0) a)
  | add P Q hP hQ =>
      simpa only [map_add] using add_mem hP hQ
  | mul_X P j hP =>
      simpa only [map_mul] using mul_mem hP (Algebra.subset_adjoin (Set.mem_range_self j))

def chartOpen (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) : (scheme I hI).Opens := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact Proj.basicOpen (grading I) (Ideal.Quotient.mk I (X j))

theorem iSup_chartOpen (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) : (⨆ j, chartOpen I hI j) = ⊤ := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  apply Proj.iSup_basicOpen_eq_top'
  · intro j
    exact ⟨1, HomogeneousQuotientGrading.quotient_mem_piece
      (homogeneousSubmodule σ K) I (isHomogeneous_X K j)⟩
  · exact coordinates_generate I

def chartImmersion (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    AffineClosedPoints.affineScheme (chartIdeal I j) ⟶ scheme I hI :=
  (chartIso I hI j).inv ≫ (chartOpen I hI j).ι

theorem chartImmersion_isOpenImmersion (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    IsOpenImmersion (chartImmersion I hI j) := by
  unfold chartImmersion
  infer_instance

theorem chartImmersion_opensRange (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    letI := chartImmersion_isOpenImmersion I hI j
    (chartImmersion I hI j).opensRange = chartOpen I hI j := by
  letI := chartImmersion_isOpenImmersion I hI j
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chartOpen I hI j).opensRange_ι

theorem chartImmersion_over (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ) :
    chartImmersion I hI j ≫ structureMap I hI =
      AffineClosedPoints.structureMap (chartIdeal I j) := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  let e := HomogeneousQuotientGrading.normalizedRingEquiv
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j)
  have he : chartImmersion I hI j = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Proj.awayι (grading I) (Ideal.Quotient.mk I (X j))
        (HomogeneousQuotientGrading.quotient_mem_piece
          (homogeneousSubmodule σ K) I (isHomogeneous_X K j)) (by decide) := rfl
  rw [he]
  change (_ ≫ _) ≫ (Proj.toSpecZero (grading I) ≫ _) = _
  rw [Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change e (HomogeneousLocalization.fromZeroRingHom (grading I) _
    (algebraMap K (grading I 0) a)) = Ideal.Quotient.mk (chartIdeal I j) (C a)
  exact HomogeneousQuotientGrading.normalizedRingEquiv_mk
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j) 0 (C a) (isHomogeneous_C σ a)

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveSchemePoints

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped Topology

universe u
variable {K : Type u} [Field K] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

def chartRationalPoint (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) : Spec (.of K) ⟶ scheme I hI :=
  Spec.map (CommRingCat.ofHom (AffineClosedPoints.evaluation (chartIdeal I j) x).toRingHom) ≫
    chartImmersion I hI j

theorem chartRationalPoint_over (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) :
    chartRationalPoint I hI j x ≫ structureMap I hI = 𝟙 (Spec (.of K)) := by
  unfold chartRationalPoint
  rw [Category.assoc, chartImmersion_over]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ chartIdeal I j)) ≫
      CommRingCat.ofHom (AffineClosedPoints.evaluation (chartIdeal I j) x).toRingHom =
        𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    ext a
    exact (AffineClosedPoints.evaluation (chartIdeal I j) x).commutes a
  rw [he, Spec.map_id]

theorem chartRationalPoint_value (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) :
    chartRationalPoint I hI j x (IsLocalRing.closedPoint K) =
      chartImmersion I hI j (AffineClosedPoints.point (chartIdeal I j) x).toPrimeSpectrum := by
  change chartImmersion I hI j
    (Spec.map (CommRingCat.ofHom (AffineClosedPoints.evaluation (chartIdeal I j) x).toRingHom)
      (IsLocalRing.closedPoint K)) = _
  congr 1
  rw [Subsingleton.elim (IsLocalRing.closedPoint K) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)]
  rfl

theorem chartPoint_isClosed (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) :
    IsClosed {chartImmersion I hI j (AffineClosedPoints.point (chartIdeal I j) x).toPrimeSpectrum} := by
  letI : IsClosedImmersion (chartRationalPoint I hI j x) :=
    isClosedImmersion_of_comp_eq_id _ _ (chartRationalPoint_over I hI j x)
  have h := (chartRationalPoint I hI j x).isClosedEmbedding.isClosed_range
  have he : Set.range (chartRationalPoint I hI j x) =
      {chartRationalPoint I hI j x (IsLocalRing.closedPoint K)} := by
    apply Set.range_eq_singleton
    exact fun y => congrArg _ (Subsingleton.elim y _)
  rwa [he, chartRationalPoint_value] at h

theorem closed_points_covered [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (x : scheme I hI) (hx : IsClosed {x}) :
    ∃ (j : σ) (y : zeroLocus K (chartIdeal I j)),
      chartImmersion I hI j (AffineClosedPoints.point (chartIdeal I j) y).toPrimeSpectrum = x := by
  have hxcover : x ∈ ⨆ j, chartOpen I hI j := by rw [iSup_chartOpen]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  letI := chartImmersion_isOpenImmersion I hI j
  have hxr : x ∈ (chartImmersion I hI j).opensRange := by
    rw [chartImmersion_opensRange]
    exact hj
  obtain ⟨a, ha⟩ := hxr
  have hpre : (chartImmersion I hI j) ⁻¹' {x} = {a} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← ha, (chartImmersion I hI j).isOpenEmbedding.injective.eq_iff]
  have hac : IsClosed ({a} : Set (PrimeSpectrum (MvPolynomial σ K ⧸ chartIdeal I j))) := by
    rw [← hpre]
    exact hx.preimage (chartImmersion I hI j).continuous
  have ham := (PrimeSpectrum.isClosed_singleton_iff_isMaximal a).mp hac
  obtain ⟨y, hy⟩ := AffineClosedPoints.point_surjective (chartIdeal I j) ⟨a.asIdeal, ham⟩
  refine ⟨j, y, ?_⟩
  have hy' : (AffineClosedPoints.point (chartIdeal I j) y).toPrimeSpectrum = a :=
    PrimeSpectrum.ext (congrArg MaximalSpectrum.asIdeal hy)
  rw [hy']
  exact ha

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveHilbertExistence

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

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
    rw [MonomialCells.weight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponGroupReduced

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSegreVeroneseScheme

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u
variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ordinaryIdeal_isHomogeneous (N : ℕ) (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I) :
    I.IsHomogeneous (homogeneousSubmodule (projectiveSpace K N).Variable K) := by
  intro n P hP
  have h := hI P hP (fun _ => n)
  change weightedHomogeneousComponent (blockWeight 1 (fun _ => N)) (fun _ => n) P ∈ I at h
  rw [ordinary_component_eq] at h
  change ((MvPolynomial.decompose' K (1 : (projectiveSpace K N).Variable → ℕ) P) n :
    (projectiveSpace K N).CoordinateRing) ∈ I
  rw [MvPolynomial.decompose'_apply]
  exact h

variable (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
  (b : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension D))

def scheme (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hD : ∀ i, 1 ≤ D i) : Scheme.{u} :=
  ProjectiveCoordinateScheme.scheme (diagonalIdeal M D b I)
    (ordinaryIdeal_isHomogeneous N _ (diagonalIdeal_homogeneous M D b hD I hI))

def structureMap (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hD : ∀ i, 1 ≤ D i) : scheme M D b I hI hD ⟶ Spec (.of K) :=
  ProjectiveCoordinateScheme.structureMap (diagonalIdeal M D b I)
    (ordinaryIdeal_isHomogeneous N _ (diagonalIdeal_homogeneous M D b hD I hI))

theorem structureMap_isProper (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hD : ∀ i, 1 ≤ D i) :
    IsProper (structureMap M D b I hI hD) :=
  ProjectiveCoordinateScheme.structureMap_isProper _ _

theorem scheme_isReduced (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hD : ∀ i, 1 ≤ D i) (hred : I.IsRadical) :
    IsReduced (scheme M D b I hI hD) :=
  ProjectiveCoordinateScheme.scheme_isReduced _ _ (hred.comap (substitution M D b).toRingHom)

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponNormalizedProjectiveLocus

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.StandardAffineChart

open MvPolynomial
open scoped Topology

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def normalizedIdeal : Ideal M.CoordinateRing := I ⊔ equations M b

theorem mem_normalized_locus (v : M.Variable → K) :
    v ∈ zeroLocus K (normalizedIdeal M I b) ↔
      v ∈ zeroLocus K I ∧ ∀ i, v ⟨i, b i⟩ = 1 := by
  constructor
  · intro hv
    refine ⟨fun P hP => hv P ((le_sup_left : I ≤ normalizedIdeal M I b) hP), fun i => ?_⟩
    have h := hv _ ((le_sup_right : equations M b ≤ normalizedIdeal M I b)
      (Ideal.subset_span (Set.mem_range_self i)))
    simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using h
  · rintro ⟨hI, hb⟩
    have hker : normalizedIdeal M I b ≤ RingHom.ker (aeval v).toRingHom := by
      refine sup_le hI (Ideal.span_le.mpr ?_)
      rintro _ ⟨i, rfl⟩
      change aeval v (X (⟨i, b i⟩ : M.Variable) - 1) = 0
      simp [hb i]
    exact fun P hP => hker hP

theorem normalize_mem_iff (hI : IsMultihomogeneousIdeal M I)
    (x : domain M b) :
    (normalize M b x).val ∈ zeroLocus K I ↔ x.val ∈ M.zeroLocus I := by
  constructor
  · intro hx
    apply (M.mem_zeroLocus_iff_homogeneous I hI x.val).mpr
    intro P hP D hD
    exact (M.eval_eq_zero_iff_of_lift _ _ (normalize_represents M b x) P D hD).mp
      (hx P hP)
  · intro hx
    have hker : I ≤ RingHom.ker (aeval (normalize M b x).val).toRingHom := by
      rw [M.homogeneousIdeal_eq_span I hI]
      apply Ideal.span_le.mpr
      rintro P ⟨hP, D, hD⟩
      exact (M.eval_eq_zero_iff_of_lift _ _ (normalize_represents M b x) P D hD).mpr
        (hx P hP)
    exact fun P hP => hker hP

def locus : Set (domain M b) := {x | x.val ∈ M.zeroLocus I}

def normalizeLocus (hI : IsMultihomogeneousIdeal M I)
    (x : locus M I b) : zeroLocus K (normalizedIdeal M I b) :=
  ⟨(normalize M b x.val).val, (mem_normalized_locus M I b _).mpr
    ⟨(normalize_mem_iff M I b hI x.val).mpr x.property,
      (mem_locus M b _).mp (normalize M b x.val).property⟩⟩

def normalizedRestriction (x : zeroLocus K (normalizedIdeal M I b)) :
    zeroLocus K (ideal M b) :=
  ⟨x.val, (mem_locus M b _).mpr ((mem_normalized_locus M I b _).mp x.property).2⟩

def denormalizeLocus (hI : IsMultihomogeneousIdeal M I)
    (x : zeroLocus K (normalizedIdeal M I b)) : locus M I b := by
  refine ⟨denormalize M b (normalizedRestriction M I b x), ?_⟩
  apply (normalize_mem_iff M I b hI _).mp
  rw [normalize_denormalize]
  exact ((mem_normalized_locus M I b _).mp x.property).1

theorem denormalizeLocus_normalizeLocus (hI : IsMultihomogeneousIdeal M I)
    (x : locus M I b) :
    denormalizeLocus M I b hI (normalizeLocus M I b hI x) = x := by
  apply Subtype.ext
  exact denormalize_normalize M b x.val

theorem normalizeLocus_denormalizeLocus (hI : IsMultihomogeneousIdeal M I)
    (x : zeroLocus K (normalizedIdeal M I b)) :
    normalizeLocus M I b hI (denormalizeLocus M I b hI x) = x := by
  apply Subtype.ext
  change (normalize M b (denormalize M b (normalizedRestriction M I b x))).val = x.val
  exact congrArg Subtype.val (normalize_denormalize M b (normalizedRestriction M I b x))

def locusEquiv (hI : IsMultihomogeneousIdeal M I) :
    locus M I b ≃ zeroLocus K (normalizedIdeal M I b) where
  toFun := normalizeLocus M I b hI
  invFun := denormalizeLocus M I b hI
  left_inv := denormalizeLocus_normalizeLocus M I b hI
  right_inv := normalizeLocus_denormalizeLocus M I b hI

def locusHomeomorph (hI : IsMultihomogeneousIdeal M I) :
    letI := M.zariskiTopology
    letI := AffineClosedPoints.locusTopology (normalizedIdeal M I b)
    locus M I b ≃ₜ zeroLocus K (normalizedIdeal M I b) := by
  letI := M.zariskiTopology
  letI := AffineClosedPoints.locusTopology (normalizedIdeal M I b)
  refine { locusEquiv M I b hI with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (AffineClosedPoints.nonzero_sets_basis (normalizedIdeal M I b)).continuous_iff.mpr
    rintro _ ⟨P, rfl⟩
    letI := AffineClosedPoints.locusTopology (ideal M b)
    exact ((AffineClosedPoints.nonzero_sets_basis (ideal M b)).isOpen
      (Set.mem_range_self P)).preimage ((normalize_continuous M b).comp continuous_subtype_val)
  · apply Continuous.subtype_mk
    letI := AffineClosedPoints.locusTopology (ideal M b)
    apply (denormalize_continuous M b).comp
    apply (AffineClosedPoints.nonzero_sets_basis (ideal M b)).continuous_iff.mpr
    rintro _ ⟨P, rfl⟩
    exact (AffineClosedPoints.nonzero_sets_basis (normalizedIdeal M I b)).isOpen
      (Set.mem_range_self P)

end PhilipponMultiplicity.StandardAffineChart

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open MvPolynomial

variable {K : Type*} [Field K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing) (j : Fin (N + 1))

theorem normalizedIdeal_single :
    StandardAffineChart.normalizedIdeal (projectiveSpace K N) I (fun _ => j) =
      chartIdeal I ⟨(0 : Fin 1), j⟩ := by
  letI : Nonempty (projectiveSpace K N).FactorIndex := ⟨(0 : Fin 1)⟩
  unfold StandardAffineChart.normalizedIdeal StandardAffineChart.equations
    chartIdeal HomogeneousQuotientGrading.normalizedIdeal
  congr 2
  apply Set.range_eq_singleton
  intro i
  congr 2
  cases Subsingleton.elim (α := Fin 1) i (0 : Fin 1)
  rfl

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveChartEvaluations

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {K : Type u} [Field K] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] zeroAlgebra zeroSMul

def polynomialOpen (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (P : MvPolynomial σ K) :
    (scheme I hI).Opens := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  exact Proj.basicOpen (grading I) (Ideal.Quotient.mk I P)

theorem chartPoint_mem_polynomialOpen (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (j : σ)
    (x : zeroLocus K (chartIdeal I j)) (P : MvPolynomial σ K)
    (n : ℕ) (hP : P.IsHomogeneous n) (hn : 0 < n) :
    chartImmersion I hI j (AffineClosedPoints.point (chartIdeal I j) x).toPrimeSpectrum ∈
      polynomialOpen I hI P ↔ aeval x.val P ≠ 0 := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  let e := HomogeneousQuotientGrading.normalizedRingEquiv
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j)
  let hf := HomogeneousQuotientGrading.quotient_mem_piece
    (homogeneousSubmodule σ K) I (isHomogeneous_X K j)
  let hg := HomogeneousQuotientGrading.quotient_mem_piece
    (homogeneousSubmodule σ K) I hP
  have himm : chartImmersion I hI j =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Proj.awayι (grading I) (Ideal.Quotient.mk I (X j)) hf (by decide) := rfl
  rw [himm]
  change PrimeSpectrum.comap e.toRingHom
      (AffineClosedPoints.point (chartIdeal I j) x).toPrimeSpectrum ∈
    (Proj.awayι (grading I) (Ideal.Quotient.mk I (X j)) hf (by decide)) ⁻¹ᵁ
      Proj.basicOpen (grading I) (Ideal.Quotient.mk I P) ↔ _
  rw [Proj.awayι_preimage_basicOpen (grading I) hf (by decide) hg hn]
  change e (HomogeneousLocalization.Away.isLocalizationElem hf hg) ∉
      (AffineClosedPoints.point (chartIdeal I j) x).asIdeal ↔ _
  have he : e (HomogeneousLocalization.Away.isLocalizationElem hf hg) =
      Ideal.Quotient.mk (chartIdeal I j) P := by
    convert HomogeneousQuotientGrading.normalizedRingEquiv_mk
      (homogeneousSubmodule σ K) I (isHomogeneous_X K j) n P hP using 1 <;> try rfl
    congr 1
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk, pow_one]
  rw [he]
  rfl

theorem point_ext_positive (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {x y : scheme I hI}
    (h : ∀ n : ℕ, 0 < n → ∀ P : MvPolynomial σ K, P.IsHomogeneous n →
      (x ∈ polynomialOpen I hI P ↔ y ∈ polynomialOpen I hI P)) : x = y := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n a ha
  obtain ⟨P, hP, rfl⟩ := ha
  by_cases hn : n = 0
  · subst n
    have hC : P = C (P.coeff 0) :=
      (homogeneousComponent_of_mem hP).symm.trans (homogeneousComponent_zero _)
    rw [hC]
    by_cases hc : P.coeff 0 = 0
    · simp [hc]
    · have hu : IsUnit (Ideal.Quotient.mk I (C (P.coeff 0))) :=
        ((isUnit_iff_ne_zero.mpr hc).map C).map (Ideal.Quotient.mk I)
      exact iff_of_false (Ideal.notMem_of_isUnit _ hu) (Ideal.notMem_of_isUnit _ hu)
  · exact not_iff_not.mp (h n (Nat.pos_of_ne_zero hn) P hP)

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePointSeparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MvPolynomial
namespace PhilipponMultiplicity.MultiProjectiveSpace

theorem point_eq_of_homogeneous_implication {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (x y : M.Point)
    (h : ∀ (P : M.CoordinateRing) (D : M.FactorIndex → ℕ),
      M.IsHomogeneous P D → M.eval P y = 0 → M.eval P x = 0) : x = y := by
  classical
  funext i
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (Projectivization.rep_nonzero (y i))
  change (y i).rep k ≠ 0 at hk
  have heq (j : Fin (M.ambientDimension i + 1)) :
      (y i).rep k * (x i).rep j - (y i).rep j * (x i).rep k = 0 := by
    have hP := (M.isHomogeneous_X ⟨i, j⟩).C_mul M ((y i).rep k)
    have hQ := (M.isHomogeneous_X ⟨i, k⟩).C_mul M ((y i).rep j)
    have hh := h _ _ (hP.sub M hQ) (by simp [eval, coordinate, mul_comm])
    simpa [eval, coordinate] using hh
  rw [← Projectivization.mk_rep (x i), ← Projectivization.mk_rep (y i)]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  exact ⟨(x i).rep k / (y i).rep k, by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    simpa only [mul_comm] using (sub_eq_zero.mp (heq j)).symm⟩

end PhilipponMultiplicity.MultiProjectiveSpace

namespace WeierstrassEllipticZeta.PhilipponApplication.Model
open PhilipponMultiplicity

end WeierstrassEllipticZeta.PhilipponApplication.Model
end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePointComparison

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory
open StandardAffineChart

universe u
variable {K : Type u} [Field K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)

abbrev ordinaryHomogeneous := Hilbert.SegreVeronese.ordinaryIdeal_isHomogeneous N I hI

abbrev scheme := ProjectiveCoordinateScheme.scheme I (ordinaryHomogeneous N I hI)

def coordinates (j : Fin (N + 1)) :
    locus (projectiveSpace K N) I (fun _ => j) ≃
      zeroLocus K (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) :=
  (locusEquiv (projectiveSpace K N) I (fun _ => j) hI).trans
    (Equiv.setCongr (congrArg (zeroLocus K)
      (ProjectiveCoordinateScheme.normalizedIdeal_single N I j)))

theorem coordinates_val (j : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j)) :
    (coordinates N I hI j x).val =
      (normalize (projectiveSpace K N) (fun _ => j) x.val).val := rfl

def pointInChart (j : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j)) : scheme N I hI :=
  ProjectiveCoordinateScheme.chartImmersion I (ordinaryHomogeneous N I hI) ⟨(0 : Fin 1), j⟩
    (AffineClosedPoints.point _ (coordinates N I hI j x)).toPrimeSpectrum

theorem pointInChart_mem_polynomialOpen (j : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j))
    (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) (hP : P.IsHomogeneous n)
    (hn : 0 < n) :
    pointInChart N I hI j x ∈
      ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P ↔
      (projectiveSpace K N).eval P x.val.val ≠ 0 := by
  rw [pointInChart, ProjectiveCoordinateScheme.chartPoint_mem_polynomialOpen
    I (ordinaryHomogeneous N I hI) _ _ P n hP hn, coordinates_val]
  exact ((projectiveSpace K N).eval_eq_zero_iff_of_lift _ _
    (normalize_represents (projectiveSpace K N) (fun _ => j) x.val) P (fun _ => n)
    ((MultiProjectiveSpace.projective_homogeneous_iff N P n).mpr hP)).not

theorem pointInChart_eq (j k : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j))
    (y : locus (projectiveSpace K N) I (fun _ => k)) (hxy : x.val.val = y.val.val) :
    pointInChart N I hI j x = pointInChart N I hI k y := by
  apply ProjectiveCoordinateScheme.point_ext_positive
  intro n hn P hP
  rw [pointInChart_mem_polynomialOpen N I hI j x P n hP hn,
    pointInChart_mem_polynomialOpen N I hI k y P n hP hn, hxy]

def pivot (x : (projectiveSpace K N).zeroLocus I) : Fin (N + 1) :=
  (Function.ne_iff.mp (x.val (0 : Fin 1)).rep_nonzero).choose

def onChart (x : (projectiveSpace K N).zeroLocus I) :
    locus (projectiveSpace K N) I (fun _ => pivot N I x) := by
  refine ⟨⟨x.val, ?_⟩, x.property⟩
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  exact (Function.ne_iff.mp (x.val (0 : Fin 1)).rep_nonzero).choose_spec

def point (x : (projectiveSpace K N).zeroLocus I) : scheme N I hI :=
  pointInChart N I hI (pivot N I x) (onChart N I x)

theorem point_eq_pointInChart (j : Fin (N + 1))
    (x : locus (projectiveSpace K N) I (fun _ => j)) :
    point N I hI ⟨x.val.val, x.property⟩ = pointInChart N I hI j x :=
  pointInChart_eq N I hI _ _ _ _ rfl

theorem point_mem_polynomialOpen (x : (projectiveSpace K N).zeroLocus I)
    (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) (hP : P.IsHomogeneous n)
    (hn : 0 < n) :
    point N I hI x ∈
      ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P ↔
      (projectiveSpace K N).eval P x.val ≠ 0 :=
  pointInChart_mem_polynomialOpen N I hI _ _ P n hP hn

theorem point_isClosed (x : (projectiveSpace K N).zeroLocus I) :
    IsClosed {point N I hI x} :=
  ProjectiveCoordinateScheme.chartPoint_isClosed I (ordinaryHomogeneous N I hI) _ _

theorem point_injective : Function.Injective (point N I hI) := by
  intro x y hxy
  apply Subtype.ext
  apply (projectiveSpace K N).point_eq_of_homogeneous_implication
  intro P D hP hy
  have hD : D = fun _ => D (0 : Fin 1) :=
    funext (fun i => congrArg D (Subsingleton.elim (α := Fin 1) i (0 : Fin 1)))
  rw [hD] at hP
  have hp := (MultiProjectiveSpace.projective_homogeneous_iff N P (D (0 : Fin 1))).mp hP
  by_cases hn : D (0 : Fin 1) = 0
  · rw [hn] at hp
    have hC : P = C (P.coeff 0) :=
      (homogeneousComponent_of_mem hp).symm.trans (homogeneousComponent_zero _)
    rw [hC] at hy ⊢
    simpa only [MultiProjectiveSpace.eval, eval_C] using hy
  · have he := (point_mem_polynomialOpen N I hI x P _ hp (Nat.pos_of_ne_zero hn)).symm.trans
      (hxy ▸ point_mem_polynomialOpen N I hI y P _ hp (Nat.pos_of_ne_zero hn))
    exact not_iff_not.mp he |>.mpr hy

theorem closed_points_surjective [IsAlgClosed K] (z : scheme N I hI) (hz : IsClosed {z}) :
    ∃ x, point N I hI x = z := by
  obtain ⟨⟨i, j⟩, y, hy⟩ := ProjectiveCoordinateScheme.closed_points_covered
    I (ordinaryHomogeneous N I hI) z hz
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  let x := (coordinates N I hI j).symm y
  refine ⟨⟨x.val.val, x.property⟩, ?_⟩
  rw [point_eq_pointInChart]
  change ProjectiveCoordinateScheme.chartImmersion I _ _
      (AffineClosedPoints.point _ (coordinates N I hI j x)).toPrimeSpectrum = z
  rw [show coordinates N I hI j x = y from (coordinates N I hI j).apply_symm_apply y]
  exact hy

def closedPointEquiv [IsAlgClosed K] :
    (projectiveSpace K N).zeroLocus I ≃ {z : scheme N I hI // IsClosed {z}} :=
  Equiv.ofBijective (fun x => ⟨point N I hI x, point_isClosed N I hI x⟩)
    ⟨fun _ _ h => point_injective N I hI (congrArg Subtype.val h), by
      rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := closed_points_surjective N I hI z hz
      exact ⟨x, Subtype.ext hx⟩⟩

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePolynomialBasis

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectiveCoordinateScheme

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra zeroAlgebra zeroSMul

theorem mem_polynomialOpen_C (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (x : scheme I hI) (c : K) :
    x ∈ polynomialOpen I hI (C c) ↔ c ≠ 0 := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  change Ideal.Quotient.mk I (C c) ∉ x.asHomogeneousIdeal ↔ c ≠ 0
  by_cases hc : c = 0
  · simp [hc]
  · have hu : IsUnit (Ideal.Quotient.mk I (C c)) :=
      ((isUnit_iff_ne_zero.mpr hc).map C).map (Ideal.Quotient.mk I)
    exact iff_of_true (Ideal.notMem_of_isUnit _ hu) hc

theorem homogeneous_polynomial_basis (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    TopologicalSpace.IsTopologicalBasis
      {U : Set (scheme I hI) | ∃ n : ℕ, ∃ P : MvPolynomial σ K,
        P.IsHomogeneous n ∧ U = polynomialOpen I hI P} := by
  letI := HomogeneousQuotientGrading.gradedAlgebra (homogeneousSubmodule σ K) I hI
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨n, P, hP, rfl⟩
    exact (polynomialOpen I hI P).isOpen
  · intro x U hx hU
    obtain ⟨_, ⟨a, rfl⟩, hxa, haU⟩ :=
      (ProjectiveSpectrum.isTopologicalBasis_basic_opens (grading I)).exists_subset_of_mem_open hx hU
    have hxproj : x ∈ ⨆ n, Proj.basicOpen (grading I) (GradedRing.proj (grading I) n a) := by
      rw [← Proj.basicOpen_eq_iSup_proj]
      exact hxa
    obtain ⟨n, hn⟩ := TopologicalSpace.Opens.mem_iSup.mp hxproj
    have hpiece : GradedRing.proj (grading I) n a ∈ grading I n :=
      (DirectSum.decompose (grading I) a n).property
    obtain ⟨P, hP, hPa⟩ := hpiece
    change Ideal.Quotient.mk I P = GradedRing.proj (grading I) n a at hPa
    refine ⟨polynomialOpen I hI P, ⟨n, P, hP, rfl⟩, ?_, ?_⟩
    · change x ∈ Proj.basicOpen (grading I) (Ideal.Quotient.mk I P)
      rw [hPa]
      exact hn
    · intro y hy
      apply haU
      change y ∈ Proj.basicOpen (grading I) a
      rw [Proj.basicOpen_eq_iSup_proj]
      apply TopologicalSpace.Opens.mem_iSup.mpr
      refine ⟨n, ?_⟩
      change y ∈ Proj.basicOpen (grading I) (Ideal.Quotient.mk I P) at hy
      rwa [hPa] at hy

end PhilipponMultiplicity.ProjectiveCoordinateScheme

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePointTopology

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory Topology
open scoped Topology

universe u
variable {K : Type u} [Field K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)

theorem point_mem_homogeneousOpen (x : (projectiveSpace K N).zeroLocus I)
    (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) (hP : P.IsHomogeneous n) :
    point N I hI x ∈
      ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P ↔
      (projectiveSpace K N).eval P x.val ≠ 0 := by
  by_cases hn : n = 0
  · subst n
    have hC : P = C (P.coeff 0) :=
      (homogeneousComponent_of_mem hP).symm.trans (homogeneousComponent_zero _)
    rw [hC, ProjectiveCoordinateScheme.mem_polynomialOpen_C]
    simp only [MultiProjectiveSpace.eval, eval_C]
  · exact point_mem_polynomialOpen N I hI x P n hP (Nat.pos_of_ne_zero hn)

theorem point_continuous :
    letI := (projectiveSpace K N).zariskiTopology
    Continuous (point N I hI) := by
  letI := (projectiveSpace K N).zariskiTopology
  apply (ProjectiveCoordinateScheme.homogeneous_polynomial_basis
    I (ordinaryHomogeneous N I hI)).continuous_iff.mpr
  rintro _ ⟨n, P, hP, rfl⟩
  have he : (point N I hI) ⁻¹'
      (ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P) =
      {x | (projectiveSpace K N).eval P x.val ≠ 0} :=
    Set.ext (fun x => point_mem_homogeneousOpen N I hI x P n hP)
  rw [he]
  exact ((projectiveSpace K N).isOpen_basic P (fun _ => n)
    ((MultiProjectiveSpace.projective_homogeneous_iff N P n).mpr hP)).preimage
      continuous_subtype_val

theorem point_isInducing :
    letI := (projectiveSpace K N).zariskiTopology
    IsInducing (point N I hI) := by
  letI := (projectiveSpace K N).zariskiTopology
  refine ⟨le_antisymm (point_continuous N I hI).le_induced ?_⟩
  change TopologicalSpace.induced (point N I hI) inferInstance ≤
    TopologicalSpace.induced Subtype.val (projectiveSpace K N).zariskiTopology
  apply continuous_iff_le_induced.mp
  letI := TopologicalSpace.induced (point N I hI) inferInstance
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have hD : D = fun _ => D (0 : Fin 1) :=
    funext (fun i => congrArg D (Subsingleton.elim (α := Fin 1) i (0 : Fin 1)))
  rw [hD] at hP
  have hp := (MultiProjectiveSpace.projective_homogeneous_iff N P (D (0 : Fin 1))).mp hP
  have he : Subtype.val ⁻¹' {x | (projectiveSpace K N).eval P x ≠ 0} =
      (point N I hI) ⁻¹'
        (ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P) :=
    Set.ext (fun x => (point_mem_homogeneousOpen N I hI x P _ hp).symm)
  rw [he]
  exact (ProjectiveCoordinateScheme.polynomialOpen I (ordinaryHomogeneous N I hI) P).isOpen.preimage
    continuous_induced_dom

def closedPointHomeomorph [IsAlgClosed K] :
    letI := (projectiveSpace K N).zariskiTopology
    (projectiveSpace K N).zeroLocus I ≃ₜ {z : scheme N I hI // IsClosed {z}} := by
  letI := (projectiveSpace K N).zariskiTopology
  apply (closedPointEquiv N I hI).toHomeomorphOfIsInducing
  apply IsInducing.subtypeVal.of_comp_iff.mp
  exact point_isInducing N I hI

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponAffinePrincipalGraph
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set Topology

namespace PhilipponMultiplicity.AffinePrincipalGraph
variable {K : Type*} [Field K] {σ : Type*}

theorem inverse_substitution_fraction (Q : MvPolynomial σ K)
    (P : MvPolynomial (Option σ) K) :
    ∃ A : MvPolynomial σ K, ∃ n : ℕ, ∀ v : σ → K, aeval v Q ≠ 0 →
      aeval (fun t => t.elim ((aeval v Q)⁻¹) v) P = aeval v A / (aeval v Q)^n := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, by simp⟩
  | add P R hP hR =>
    obtain ⟨A, n, hA⟩ := hP
    obtain ⟨B, m, hB⟩ := hR
    refine ⟨A * Q^m + B * Q^n, n + m, ?_⟩
    intro v hv
    simp only [map_add, map_mul, map_pow, hA v hv, hB v hv, pow_add]
    simpa only [mul_comm] using div_add_div (aeval v A) (aeval v B)
      (pow_ne_zero n hv) (pow_ne_zero m hv)
  | mul_X P i hP =>
    obtain ⟨A, n, hA⟩ := hP
    cases i with
    | none =>
      refine ⟨A, n + 1, ?_⟩
      intro v hv
      simp only [map_mul, aeval_X, Option.elim_none, hA v hv, pow_succ]
      rw [div_mul_eq_div_mul_one_div, one_div]
    | some i =>
      refine ⟨A * X i, n, ?_⟩
      intro v hv
      simp only [map_mul, aeval_X, Option.elim_some, hA v hv]
      exact div_mul_eq_mul_div _ _ _

def equations (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    Ideal (MvPolynomial (Option σ) K) :=
  Ideal.span (rename (Option.some : σ → Option σ) '' (I : Set (MvPolynomial σ K)) ∪
    {X none * rename (Option.some : σ → Option σ) Q - 1})

def ideal (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    Ideal (MvPolynomial (Option σ) K) := (equations I Q).radical

theorem ideal_isRadical (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    (ideal I Q).IsRadical := Ideal.radical_isRadical _

theorem mem_locus (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : Option σ → K) :
    v ∈ zeroLocus K (ideal I Q) ↔
      (fun t => v (some t)) ∈ zeroLocus K I ∧
        v none * aeval (fun t => v (some t)) Q = 1 := by
  constructor
  · intro hv
    constructor
    · intro P hP
      have h := hv _ (Ideal.le_radical (Ideal.subset_span
        (Set.mem_union_left _ ⟨P, hP, rfl⟩)))
      simpa only [aeval_rename, Function.comp_def] using h
    · have h := hv _ (Ideal.le_radical (Ideal.subset_span
        (Set.mem_union_right _ (Set.mem_singleton _))))
      simpa only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def,
        map_one, sub_eq_zero] using h
  · rintro ⟨hI, hQ⟩
    have hker : equations I Q ≤ RingHom.ker (aeval v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro P (⟨F, hF, rfl⟩ | rfl)
      · change aeval v (rename some F) = 0
        simpa only [aeval_rename, Function.comp_def] using hI F hF
      · change aeval v (X none * rename some Q - 1) = 0
        simpa only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def,
          map_one, sub_eq_zero] using hQ
    intro P hP
    exact radical_le_vanishingIdeal_zeroLocus (K := K) (equations I Q) hP v
      (fun F hF => hker hF)

def domain (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :
    Set (zeroLocus K I) := {x | aeval x.val Q ≠ 0}

def graph (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (x : domain I Q) : zeroLocus K (ideal I Q) :=
  ⟨fun t => t.elim ((aeval x.val.val Q)⁻¹) x.val.val,
    (mem_locus I Q _).mpr ⟨x.val.property, inv_mul_cancel₀ x.property⟩⟩

theorem denominator_ne_zero (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : zeroLocus K (ideal I Q)) : aeval (fun t => v.val (some t)) Q ≠ 0 := by
  intro h
  have hh := ((mem_locus I Q v.val).mp v.property).2
  rw [h, mul_zero] at hh
  exact zero_ne_one hh

def project (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : zeroLocus K (ideal I Q)) : domain I Q :=
  ⟨⟨fun t => v.val (some t), ((mem_locus I Q v.val).mp v.property).1⟩,
    denominator_ne_zero I Q v⟩

theorem project_graph (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (x : domain I Q) : project I Q (graph I Q x) = x := rfl

theorem graph_project (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (v : zeroLocus K (ideal I Q)) : graph I Q (project I Q v) = v := by
  apply Subtype.ext
  funext t
  cases t with
  | some t => rfl
  | none =>
    change (aeval (fun t => v.val (some t)) Q)⁻¹ = v.val none
    symm
    rw [← one_div]
    exact (eq_div_iff (denominator_ne_zero I Q v)).mpr
      ((mem_locus I Q v.val).mp v.property).2

end PhilipponMultiplicity.AffinePrincipalGraph

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponPrincipalGraphScheme

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.AffinePrincipalGraph

open MvPolynomial AlgebraicGeometry CategoryTheory AffineClosedPoints

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {σ : Type} [Finite σ]
variable (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)

def baseHom : (MvPolynomial σ K ⧸ I) →ₐ[K]
    (MvPolynomial (Option σ) K ⧸ ideal I Q) :=
  quotientMap I (ideal I Q) (ideal_isRadical I Q)
    (fun x => (project I Q x).val) (fun j => X (some j)) (by
      intro x j
      simp [project])

@[simp] theorem evaluation_baseHom (x : zeroLocus K (ideal I Q))
    (a : MvPolynomial σ K ⧸ I) :
    evaluation (ideal I Q) x (baseHom I Q a) = evaluation I (project I Q x).val a := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [baseHom, quotientMap_mk, evaluation_mk, evaluate_substitution, evaluation_mk]
  simp only [aeval_X, project]

theorem baseHom_Q_isUnit : IsUnit (baseHom I Q (Ideal.Quotient.mk I Q)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk (ideal I Q) (X none), ?_⟩
  apply evaluation_ext (ideal I Q) (ideal_isRadical I Q)
  intro x
  simp only [map_mul, evaluation_baseHom, evaluation_mk, aeval_X, map_one]
  exact (mul_comm _ _).trans ((mem_locus I Q x.val).mp x.property).2

theorem exists_fraction (b : MvPolynomial (Option σ) K ⧸ ideal I Q) :
    ∃ n : ℕ, ∃ a : MvPolynomial σ K ⧸ I,
      b * baseHom I Q (Ideal.Quotient.mk I Q) ^ n = baseHom I Q a := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨A, n, hA⟩ := inverse_substitution_fraction Q P
  refine ⟨n, Ideal.Quotient.mk I A, ?_⟩
  apply evaluation_ext (ideal I Q) (ideal_isRadical I Q)
  intro x
  simp only [map_mul, map_pow, evaluation_baseHom, evaluation_mk]
  have h := hA (project I Q x).val.val (project I Q x).property
  have hx : (fun t => t.elim ((aeval (project I Q x).val.val Q)⁻¹)
      (project I Q x).val.val) = x.val :=
    congrArg Subtype.val (graph_project I Q x)
  rw [hx] at h
  exact (eq_div_iff (pow_ne_zero n (project I Q x).property)).mp h

theorem clear_baseHom_equality (hI : I.IsRadical)
    (a b : MvPolynomial σ K ⧸ I) (hab : baseHom I Q a = baseHom I Q b) :
    Ideal.Quotient.mk I Q * a = Ideal.Quotient.mk I Q * b := by
  apply evaluation_ext I hI
  intro x
  simp only [map_mul, evaluation_mk]
  by_cases hx : aeval x.val Q = 0
  · simp [hx]
  · have h := congrArg (evaluation (ideal I Q) (graph I Q ⟨x, hx⟩)) hab
    simp only [evaluation_baseHom, project_graph] at h
    rw [h]

theorem coordinateRing_isLocalization (hI : I.IsRadical) :
    letI : Algebra (MvPolynomial σ K ⧸ I)
        (MvPolynomial (Option σ) K ⧸ ideal I Q) := (baseHom I Q).toRingHom.toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk I Q)
      (MvPolynomial (Option σ) K ⧸ ideal I Q) := by
  letI : Algebra (MvPolynomial σ K ⧸ I)
      (MvPolynomial (Option σ) K ⧸ ideal I Q) := (baseHom I Q).toRingHom.toAlgebra
  apply IsLocalization.Away.mk (Ideal.Quotient.mk I Q) (baseHom_Q_isUnit I Q)
  · exact exists_fraction I Q
  · intro a b hab
    exact ⟨1, by simpa only [pow_one] using clear_baseHom_equality I Q hI a b hab⟩

def schemeProjection : affineScheme (ideal I Q) ⟶ affineScheme I :=
  schemeMap I (ideal I Q) (baseHom I Q)

theorem schemeProjection_isOpenImmersion (hI : I.IsRadical) :
    IsOpenImmersion (schemeProjection I Q) := by
  letI : Algebra (MvPolynomial σ K ⧸ I)
      (MvPolynomial (Option σ) K ⧸ ideal I Q) := (baseHom I Q).toRingHom.toAlgebra
  letI := coordinateRing_isLocalization I Q hI
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk I Q)

theorem schemeProjection_point (x : zeroLocus K (ideal I Q)) :
    schemeProjection I Q (point (ideal I Q) x).toPrimeSpectrum =
      (point I (project I Q x).val).toPrimeSpectrum := by
  rw [schemeProjection, schemeMap_point]
  congr 2
  apply Subtype.ext
  funext j
  simp only [pointMap_coordinate, evaluation_baseHom, evaluation_mk, aeval_X]

end PhilipponMultiplicity.AffinePrincipalGraph

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectivePrincipalCharts

set_option autoImplicit false
set_option maxHeartbeats 180000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints
open MvPolynomial
variable {K : Type*} [Field K] {σ : Type*}

def idealHomeomorph (I J : Ideal (MvPolynomial σ K)) (h : I = J) :
    @Homeomorph (zeroLocus K I) (zeroLocus K J) (locusTopology I) (locusTopology J) := by
  letI := locusTopology I
  letI := locusTopology J
  exact { toEquiv := Equiv.setCongr (congrArg (zeroLocus K) h)
          continuous_toFun := by subst J; exact continuous_id
          continuous_invFun := by subst J; exact continuous_id }

end PhilipponMultiplicity.AffineClosedPoints

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)

def coordinatesHomeomorph (j : Fin (N + 1)) :
    letI := (projectiveSpace K N).zariskiTopology
    letI := AffineClosedPoints.locusTopology (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)
    StandardAffineChart.locus (projectiveSpace K N) I (fun _ => j) ≃ₜ
      zeroLocus K (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := AffineClosedPoints.locusTopology
    (StandardAffineChart.normalizedIdeal (projectiveSpace K N) I (fun _ => j))
  letI := AffineClosedPoints.locusTopology (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)
  exact (StandardAffineChart.locusHomeomorph (projectiveSpace K N) I (fun _ => j) hI).trans
    (AffineClosedPoints.idealHomeomorph _ _ (ProjectiveCoordinateScheme.normalizedIdeal_single N I j))

def chartOriginalPoint (j : Fin (N + 1))
    (y : zeroLocus K (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)) :
    (projectiveSpace K N).zeroLocus I :=
  ⟨((coordinates N I hI j).symm y).val.val, ((coordinates N I hI j).symm y).property⟩

theorem chartOriginalPoint_continuous (j : Fin (N + 1)) :
    letI := (projectiveSpace K N).zariskiTopology
    letI := AffineClosedPoints.locusTopology (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)
    Continuous (chartOriginalPoint N I hI j) := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := AffineClosedPoints.locusTopology (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩)
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    (continuous_subtype_val.comp (coordinatesHomeomorph N I hI j).symm.continuous)

def principalIdeal (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing) :
    Ideal (MvPolynomial (Option (projectiveSpace K N).Variable) K) :=
  AffinePrincipalGraph.ideal (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) Q

def principalPoint (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing)
    (z : zeroLocus K (principalIdeal N I j Q)) : (projectiveSpace K N).zeroLocus I :=
  chartOriginalPoint N I hI j (AffinePrincipalGraph.project _ Q z).val

def principalImmersion (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing) :
    AffineClosedPoints.affineScheme (principalIdeal N I j Q) ⟶ scheme N I hI :=
  AffinePrincipalGraph.schemeProjection _ Q ≫
    ProjectiveCoordinateScheme.chartImmersion I (ordinaryHomogeneous N I hI) ⟨(0 : Fin 1), j⟩

theorem principalImmersion_isOpenImmersion (hred : I.IsRadical)
    (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing) :
    IsOpenImmersion (principalImmersion N I hI j Q) := by
  letI := AffinePrincipalGraph.schemeProjection_isOpenImmersion
    (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) Q
    (ProjectiveCoordinateScheme.chartIdeal_isRadical I (ordinaryHomogeneous N I hI) hred _)
  letI := ProjectiveCoordinateScheme.chartImmersion_isOpenImmersion I (ordinaryHomogeneous N I hI)
    ⟨(0 : Fin 1), j⟩
  change IsOpenImmersion (_ ≫ _)
  infer_instance

theorem principalImmersion_over (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing) :
    principalImmersion N I hI j Q ≫
      ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous N I hI) =
        AffineClosedPoints.structureMap (principalIdeal N I j Q) := by
  rw [principalImmersion, Category.assoc, ProjectiveCoordinateScheme.chartImmersion_over]
  exact AffineClosedPoints.schemeMap_over _ _ _

theorem principalImmersion_point (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing)
    (z : zeroLocus K (principalIdeal N I j Q)) :
    principalImmersion N I hI j Q (AffineClosedPoints.point _ z).toPrimeSpectrum =
      point N I hI (principalPoint N I hI j Q z) := by
  change ProjectiveCoordinateScheme.chartImmersion I _ _
    (AffinePrincipalGraph.schemeProjection _ Q (AffineClosedPoints.point _ z).toPrimeSpectrum) = _
  dsimp only [principalIdeal] at z ⊢
  rw [AffinePrincipalGraph.schemeProjection_point]
  unfold principalPoint chartOriginalPoint
  rw [point_eq_pointInChart, pointInChart, Equiv.apply_symm_apply]

def principalLift : (projectiveSpace K N).Variable →
    MvPolynomial (Option (projectiveSpace K N).Variable) K := fun v => X (some v)

theorem principalPoint_polynomial_lift (j : Fin (N + 1))
    (Q : (projectiveSpace K N).CoordinateRing)
    (z : zeroLocus K (principalIdeal N I j Q)) (i : (projectiveSpace K N).FactorIndex) :
    ∃ h : (fun k => aeval z.val (principalLift N ⟨i, k⟩)) ≠ 0,
      Projectivization.mk K
        (fun k => aeval z.val (principalLift N ⟨i, k⟩)) h =
          (principalPoint N I hI j Q z).val i := by
  let y := (AffinePrincipalGraph.project
    (ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩) Q z).val
  let x := (coordinates N I hI j).symm y
  have hx : (StandardAffineChart.normalize (projectiveSpace K N) (fun _ => j) x.val).val =
      y.val := (coordinates_val N I hI j x).symm.trans
        (congrArg Subtype.val ((coordinates N I hI j).apply_symm_apply y))
  have hrep := StandardAffineChart.normalize_represents (projectiveSpace K N) (fun _ => j) x.val i
  rw [hx] at hrep
  simpa only [principalLift, aeval_X, principalPoint, chartOriginalPoint,
    x, y, AffinePrincipalGraph.project] using hrep

theorem exists_principal_chart_in_open
    (x : (projectiveSpace K N).zeroLocus I) (W : Set ((projectiveSpace K N).zeroLocus I))
    (hW : letI := (projectiveSpace K N).zariskiTopology; IsOpen W) (hxW : x ∈ W) :
    ∃ (j : Fin (N + 1)) (Q : (projectiveSpace K N).CoordinateRing)
      (z : zeroLocus K (principalIdeal N I j Q)),
      principalPoint N I hI j Q z = x ∧ ∀ w, principalPoint N I hI j Q w ∈ W := by
  letI := (projectiveSpace K N).zariskiTopology
  let j := pivot N I x
  let J := ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), j⟩
  letI := AffineClosedPoints.locusTopology J
  let y := coordinates N I hI j (onChart N I x)
  have hy : chartOriginalPoint N I hI j y = x := by
    apply Subtype.ext
    change ((coordinates N I hI j).symm (coordinates N I hI j (onChart N I x))).val.val = x.val
    rw [Equiv.symm_apply_apply]
    rfl
  obtain ⟨_, ⟨Q, rfl⟩, hyQ, hQW⟩ := (AffineClosedPoints.nonzero_sets_basis J).exists_subset_of_mem_open
    (show y ∈ (chartOriginalPoint N I hI j) ⁻¹' W by rwa [Set.mem_preimage, hy])
    (hW.preimage (chartOriginalPoint_continuous N I hI j))
  refine ⟨j, Q, AffinePrincipalGraph.graph J Q ⟨y, hyQ⟩, ?_, ?_⟩
  · exact hy
  · intro w
    exact hQW (AffinePrincipalGraph.project J Q w).property

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponRegularNormalizedSchemeMaps

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] {σ : Type} [Finite σ]

theorem continuous_of_polynomial_projective_lift
    (J : Ideal (MvPolynomial σ K)) (M : MultiProjectiveSpace K)
    (e : zeroLocus K J → M.Point) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ (z : zeroLocus K J) (b : M.FactorIndex),
      ∃ h : (fun i => aeval z.val (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval z.val (L ⟨b, i⟩)) h = e z b) :
    @Continuous _ _ (AffineClosedPoints.locusTopology J) M.zariskiTopology e := by
  letI := AffineClosedPoints.locusTopology J
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have he : e ⁻¹' {x | M.eval P x ≠ 0} =
      {z | aeval z.val ((aeval L) P) ≠ 0} := by
    ext z
    have hv := (M.eval_eq_zero_iff_of_lift (e z) (fun v => aeval z.val (L v)) (hL z) P D hP).not
    change M.eval P (e z) ≠ 0 ↔ aeval z.val (aeval L P) ≠ 0
    rw [AffineClosedPoints.evaluate_substitution, aeval_eq_eval]
    exact hv.symm
  rw [he]
  exact (AffineClosedPoints.nonzero_sets_basis J).isOpen (Set.mem_range_self ((aeval L) P))

namespace StandardAffineChart

variable (N : MultiProjectiveSpace K) (I : Ideal N.CoordinateRing)
    (hI : IsMultihomogeneousIdeal N I)
    (b : ∀ i : N.FactorIndex, Fin (N.ambientDimension i + 1))

def normalizeMap {A : Type*} (f : A → N.zeroLocus I)
    (hb : ∀ z, (f z).val ∈ domain N b) :
    A → zeroLocus K (normalizedIdeal N I b) :=
  fun z => normalizeLocus N I b hI ⟨⟨(f z).val, hb z⟩, (f z).property⟩

@[simp] theorem normalizeMap_coordinate {A : Type*} (f : A → N.zeroLocus I)
    (hb : ∀ z, (f z).val ∈ domain N b) (z : A) (v : N.Variable) :
    (normalizeMap N I hI b f hb z).val v =
      N.eval (X v) (f z).val / N.eval (X ⟨v.1, b v.1⟩) (f z).val := by
  simp only [normalizeMap, normalizeLocus, normalize, MultiProjectiveSpace.eval,
    eval_X, MultiProjectiveSpace.coordinate]

end StandardAffineChart

theorem regular_normalized_map_isLocallyRational
    (J : Ideal (MvPolynomial σ K)) (M N : MultiProjectiveSpace K)
    (I : Ideal N.CoordinateRing) (hI : IsMultihomogeneousIdeal N I)
    (e : zeroLocus K J → M.Point) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ (z : zeroLocus K J) (b : M.FactorIndex),
      ∃ h : (fun i => aeval z.val (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval z.val (L ⟨b, i⟩)) h = e z b)
    (f : zeroLocus K J → N.zeroLocus I)
    (hf : M.IsRegularAlong N e (fun z => (f z).val))
    (b : ∀ i : N.FactorIndex, Fin (N.ambientDimension i + 1))
    (hb : ∀ z, (f z).val ∈ StandardAffineChart.domain N b) :
    AffineClosedPoints.IsLocallyRationalMap (StandardAffineChart.normalizedIdeal N I b) J
      (StandardAffineChart.normalizeMap N I hI b f hb) := by
  letI := AffineClosedPoints.locusTopology J
  have he := continuous_of_polynomial_projective_lift J M e L hL
  intro z v
  let t : zeroLocus K J → (Set.univ : Set (zeroLocus K J)) := fun w => ⟨w, Set.mem_univ _⟩
  letI : TopologicalSpace (Set.univ : Set (zeroLocus K J)) :=
    TopologicalSpace.induced Subtype.val (TopologicalSpace.induced e M.zariskiTopology)
  have ht : Continuous t := by
    apply continuous_induced_rng.mpr
    exact continuous_induced_rng.mpr he
  obtain ⟨U, hU, hzU, A, B, hAB⟩ := hf.local_fraction_of_target_ratio Set.univ
    (fun w => w.val.val) L (fun w => hL w.val)
    (X v) (X ⟨v.1, b v.1⟩) _ (N.isHomogeneous_X v) (N.isHomogeneous_X ⟨v.1, b v.1⟩)
    (fun w => by simpa only [MultiProjectiveSpace.eval, eval_X,
      MultiProjectiveSpace.coordinate] using hb w.val v.1) (t z)
  refine ⟨t ⁻¹' U, hU.preimage ht, hzU, A, B, ?_⟩
  intro w hw
  exact ⟨(hAB (t w) hw).1, (StandardAffineChart.normalizeMap_coordinate N I hI b f hb w v).trans
    (hAB (t w) hw).2⟩

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponClosedPointSchemeGluing

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 1000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Topology

universe u v
variable {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (πX : X ⟶ Spec (.of K)) (πY : Y ⟶ Spec (.of K))
    [IsReduced X] [LocallyOfFiniteType πX] [LocallyOfFiniteType πY] [IsSeparated πY]

theorem scheme_maps_agree_on_overlaps
    (U : X.OpenCover.{v}) (F : ∀ i, U.X i ⟶ Y)
    (hbase : ∀ i, F i ≫ πY = U.f i ≫ πX)
    (hpoints : ∀ i j (x : U.X i) (y : U.X j), IsClosed {U.f i x} →
      U.f i x = U.f j y → F i x = F j y) :
    ∀ i j, pullback.fst (U.f i) (U.f j) ≫ F i =
      pullback.snd (U.f i) (U.f j) ≫ F j := by
  intro i j
  let p := pullback.fst (U.f i) (U.f j) ≫ U.f i
  letI : IsOpenImmersion p := inferInstance
  letI := isReduced_of_isOpenImmersion p
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace πX
  have hb : (pullback.fst (U.f i) (U.f j) ≫ F i) ≫ πY = p ≫ πX := by
    simp only [Category.assoc, hbase, p]
  letI : LocallyOfFiniteType ((pullback.fst (U.f i) (U.f j) ≫ F i) ≫ πY) := by
    rw [hb]
    infer_instance
  apply AlgebraicGeometry.ext_of_apply_eq πY Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro z _ hz
    have hzc : IsClosed {p z} := by
      change z ∈ p ⁻¹' closedPoints X
      rw [p.isOpenEmbedding.preimage_closedPoints]
      exact hz
    exact hpoints i j (pullback.fst (U.f i) (U.f j) z)
      (pullback.snd (U.f i) (U.f j) z) hzc
      (congrArg (fun g : pullback (U.f i) (U.f j) ⟶ X => g z) pullback.condition)
  · simp only [Category.assoc, hbase]
    simpa only [Category.assoc] using
      congrArg (fun g : pullback (U.f i) (U.f j) ⟶ X => g ≫ πX) pullback.condition

theorem existsUnique_schemeMap_of_closedPoint_agreement
    (U : X.OpenCover.{v}) (F : ∀ i, U.X i ⟶ Y)
    (hbase : ∀ i, F i ≫ πY = U.f i ≫ πX)
    (hpoints : ∀ i j (x : U.X i) (y : U.X j), IsClosed {U.f i x} →
      U.f i x = U.f j y → F i x = F j y) :
    ∃! f : X ⟶ Y, f ≫ πY = πX ∧ ∀ i, U.f i ≫ f = F i := by
  let hcompat := scheme_maps_agree_on_overlaps πX πY U F hbase hpoints
  let f := U.glueMorphisms F hcompat
  have hf : ∀ i, U.f i ≫ f = F i := U.ι_glueMorphisms F hcompat
  refine ⟨f, ⟨?_, hf⟩, ?_⟩
  · apply U.hom_ext
    intro i
    rw [← Category.assoc, hf, hbase]
  · intro g hg
    apply U.hom_ext
    intro i
    rw [hg.2, hf]

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponSchemeClosedPointCover

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u v

namespace AffineClosedPoints
variable {K : Type u} [Field K] [IsAlgClosed K] {σ : Type} [Finite σ]

theorem closed_point_surjective (I : Ideal (MvPolynomial σ K))
    (z : affineScheme I) (hz : IsClosed {z}) :
    ∃ x : zeroLocus K I, (point I x).toPrimeSpectrum = z := by
  have hm := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z).mp hz
  obtain ⟨x, hx⟩ := point_surjective I ⟨z.asIdeal, hm⟩
  exact ⟨x, PrimeSpectrum.ext (congrArg MaximalSpectrum.asIdeal hx)⟩

end AffineClosedPoints

theorem covers_of_covers_closed_points (X : Scheme.{u}) [JacobsonSpace X]
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (h : ∀ x : X, IsClosed {x} → ∃ i y, f i y = x) :
    ∀ x : X, ∃ i y, f i y = x := by
  let V : Set X := ⋃ i, Set.range (f i)
  have hV : IsOpen V := isOpen_iUnion (fun i => (f i).isOpenEmbedding.isOpen_range)
  have htop : V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
      (show Vᶜ.Nonempty from ⟨x, hx⟩) hV.isClosed_compl.isLocallyClosed
    obtain ⟨i, y, rfl⟩ := h z hzc
    exact hz (Set.mem_iUnion.mpr ⟨i, Set.mem_range_self y⟩)
  intro x
  have hx : x ∈ V := by rw [htop]; trivial
  exact Set.mem_iUnion.mp hx

def openCoverOfClosedPoints (X : Scheme.{u}) [JacobsonSpace X]
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (h : ∀ x : X, IsClosed {x} → ∃ i y, f i y = x) : X.OpenCover.{v} where
  I₀ := ι
  X := U
  f := f
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨covers_of_covers_closed_points X U f h, fun i => inferInstance⟩

end PhilipponMultiplicity

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveRegularSchemeMap

set_option autoImplicit false
set_option maxHeartbeats 220000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

theorem affine_source_to_projective_chart {σ : Type} [Finite σ]
    (J : Ideal (MvPolynomial σ K)) (hJ : J.IsRadical) (M : MultiProjectiveSpace K)
    (N : ℕ) (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (e : zeroLocus K J → M.Point) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ (z : zeroLocus K J) (b : M.FactorIndex),
      ∃ h : (fun i => aeval z.val (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval z.val (L ⟨b, i⟩)) h = e z b)
    (f : zeroLocus K J → (projectiveSpace K N).zeroLocus I)
    (hf : M.IsRegularAlong (projectiveSpace K N) e (fun z => (f z).val))
    (k : Fin (N + 1))
    (hb : ∀ z, (f z).val ∈ StandardAffineChart.domain (projectiveSpace K N) (fun _ => k)) :
    ∃ F : AffineClosedPoints.affineScheme J ⟶ scheme N I hI,
      F ≫ ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous N I hI) =
        AffineClosedPoints.structureMap J ∧
      ∀ z, F (AffineClosedPoints.point J z).toPrimeSpectrum = point N I hI (f z) := by
  let T := ProjectiveCoordinateScheme.chartIdeal I ⟨(0 : Fin 1), k⟩
  let g : zeroLocus K J → zeroLocus K T := fun z =>
    coordinates N I hI k ⟨⟨(f z).val, hb z⟩, (f z).property⟩
  have hrat : AffineClosedPoints.IsLocallyRationalMap T J g := by
    letI := AffineClosedPoints.locusTopology J
    have h := regular_normalized_map_isLocallyRational J M (projectiveSpace K N) I hI
      e L hL f hf (fun _ => k) hb
    intro z v
    obtain ⟨U, hU, hzU, A, B, hAB⟩ := h z v
    exact ⟨U, hU, hzU, A, B, hAB⟩
  obtain ⟨F, hF, _⟩ := AffineClosedPoints.existsUnique_schemeRealization T J hJ g hrat
  refine ⟨F ≫ ProjectiveCoordinateScheme.chartImmersion I (ordinaryHomogeneous N I hI)
    ⟨(0 : Fin 1), k⟩, ?_, ?_⟩
  · rw [Category.assoc, ProjectiveCoordinateScheme.chartImmersion_over]
    exact hF.1
  · intro z
    change ProjectiveCoordinateScheme.chartImmersion I _ _
      (F (AffineClosedPoints.point J z).toPrimeSpectrum) = _
    rw [hF.2]
    exact (point_eq_pointInChart N I hI k ⟨⟨(f z).val, hb z⟩, (f z).property⟩).symm

theorem regular_map_local_schemeMap
    (M N : ℕ) (I : Ideal (projectiveSpace K M).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K M) I)
    (J : Ideal (projectiveSpace K N).CoordinateRing)
    (hJ : IsMultihomogeneousIdeal (projectiveSpace K N) J)
    (f : (projectiveSpace K M).zeroLocus I → (projectiveSpace K N).zeroLocus J)
    (hf : (projectiveSpace K M).IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun z => (f z).val)) (x : (projectiveSpace K M).zeroLocus I) :
    ∃ (j : Fin (M + 1)) (Q : (projectiveSpace K M).CoordinateRing)
      (z : zeroLocus K (principalIdeal M I j Q))
      (F : AffineClosedPoints.affineScheme (principalIdeal M I j Q) ⟶ scheme N J hJ),
      principalPoint M I hI j Q z = x ∧
      F ≫ ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ) =
        AffineClosedPoints.structureMap (principalIdeal M I j Q) ∧
      ∀ w, F (AffineClosedPoints.point _ w).toPrimeSpectrum =
        point N J hJ (f (principalPoint M I hI j Q w)) := by
  letI := (projectiveSpace K M).zariskiTopology
  letI := (projectiveSpace K N).zariskiTopology
  have hfc : Continuous f := continuous_induced_rng.mpr hf.continuous
  let k := pivot N J (f x)
  let W := {y : (projectiveSpace K M).zeroLocus I |
    (f y).val ∈ StandardAffineChart.domain (projectiveSpace K N) (fun _ => k)}
  have hW : IsOpen W := (StandardAffineChart.domain_isOpen (projectiveSpace K N) (fun _ => k)).preimage
    (continuous_subtype_val.comp hfc)
  have hxW : x ∈ W := (onChart N J (f x)).val.property
  obtain ⟨j, Q, z, hz, hall⟩ := exists_principal_chart_in_open M I hI x W hW hxW
  obtain ⟨F, hF, hFp⟩ := affine_source_to_projective_chart (principalIdeal M I j Q)
    (AffinePrincipalGraph.ideal_isRadical _ Q) (projectiveSpace K M) N J hJ
    (fun w => (principalPoint M I hI j Q w).val) (principalLift M)
    (principalPoint_polynomial_lift M I hI j Q)
    (fun w => f (principalPoint M I hI j Q w))
    (hf.comp_domain (principalPoint M I hI j Q)) k hall
  exact ⟨j, Q, z, F, hz, hF, hFp⟩

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveRegularGluing

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Topology

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

theorem existsUnique_regular_schemeMap
    (M N : ℕ) (I : Ideal (projectiveSpace K M).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K M) I) (hred : I.IsRadical)
    (J : Ideal (projectiveSpace K N).CoordinateRing)
    (hJ : IsMultihomogeneousIdeal (projectiveSpace K N) J)
    (f : (projectiveSpace K M).zeroLocus I → (projectiveSpace K N).zeroLocus J)
    (hf : (projectiveSpace K M).IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun z => (f z).val)) :
    ∃! F : scheme M I hI ⟶ scheme N J hJ,
      F ≫ ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ) =
        ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous M I hI) ∧
      ∀ x, F (point M I hI x) = point N J hJ (f x) := by
  classical
  let πX := ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous M I hI)
  let πY := ProjectiveCoordinateScheme.structureMap J (ordinaryHomogeneous N J hJ)
  letI : IsProper πX := ProjectiveCoordinateScheme.structureMap_isProper I _
  letI : IsProper πY := ProjectiveCoordinateScheme.structureMap_isProper J _
  letI : IsReduced (scheme M I hI) :=
    ProjectiveCoordinateScheme.scheme_isReduced I (ordinaryHomogeneous M I hI) hred
  letI : JacobsonSpace (scheme M I hI) := LocallyOfFiniteType.jacobsonSpace πX
  choose j Q z F hz hF hFp using regular_map_local_schemeMap M N I hI J hJ f hf
  let A (x : (projectiveSpace K M).zeroLocus I) :=
    AffineClosedPoints.affineScheme (principalIdeal M I (j x) (Q x))
  let inc (x : (projectiveSpace K M).zeroLocus I) : A x ⟶ scheme M I hI :=
    principalImmersion M I hI (j x) (Q x)
  letI (x : (projectiveSpace K M).zeroLocus I) : IsOpenImmersion (inc x) :=
    principalImmersion_isOpenImmersion M I hI hred (j x) (Q x)
  have hcover : ∀ a : scheme M I hI, IsClosed {a} → ∃ i y, inc i y = a := by
    intro a ha
    obtain ⟨x, rfl⟩ := closed_points_surjective M I hI a ha
    refine ⟨x, (AffineClosedPoints.point _ (z x)).toPrimeSpectrum, ?_⟩
    change principalImmersion M I hI (j x) (Q x) _ = _
    rw [principalImmersion_point, hz]
  let U := openCoverOfClosedPoints (scheme M I hI) A inc hcover
  have hbase : ∀ i, F i ≫ πY = U.f i ≫ πX := by
    intro i
    exact (hF i).trans (principalImmersion_over M I hI (j i) (Q i)).symm
  have hagree : ∀ i k (a : U.X i) (b : U.X k), IsClosed {U.f i a} →
      U.f i a = U.f k b → F i a = F k b := by
    intro i k a b ha hab
    have hac : IsClosed {a} :=
      (preimage_closedPoints_subset (U.f i).isOpenEmbedding.injective (U.f i).continuous) ha
    have hb : IsClosed {U.f k b} := hab ▸ ha
    have hbc : IsClosed {b} :=
      (preimage_closedPoints_subset (U.f k).isOpenEmbedding.injective (U.f k).continuous) hb
    obtain ⟨a', rfl⟩ := AffineClosedPoints.closed_point_surjective _ a hac
    obtain ⟨b', rfl⟩ := AffineClosedPoints.closed_point_surjective _ b hbc
    rw [hFp i a', hFp k b']
    apply congrArg (fun x => point N J hJ (f x))
    apply point_injective M I hI
    change principalImmersion M I hI (j i) (Q i) _ =
      principalImmersion M I hI (j k) (Q k) _ at hab
    rwa [principalImmersion_point, principalImmersion_point] at hab
  obtain ⟨φ, ⟨hφbase, hφrestr⟩, _⟩ :=
    existsUnique_schemeMap_of_closedPoint_agreement πX πY U F hbase hagree
  have hφpoints : ∀ x, φ (point M I hI x) = point N J hJ (f x) := by
    intro x
    have he := congrArg (fun g : A x ⟶ scheme N J hJ =>
      g (AffineClosedPoints.point _ (z x)).toPrimeSpectrum) (hφrestr x)
    change φ (principalImmersion M I hI (j x) (Q x)
      (AffineClosedPoints.point _ (z x)).toPrimeSpectrum) = _ at he
    rwa [principalImmersion_point, hFp, hz] at he
  refine ⟨φ, ⟨hφbase, hφpoints⟩, ?_⟩
  intro ψ hψ
  letI : LocallyOfFiniteType (ψ ≫ πY) := by
    rw [hψ.1]
    exact inferInstanceAs (LocallyOfFiniteType πX)
  apply AlgebraicGeometry.ext_of_apply_eq πY Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro a _ ha
    obtain ⟨x, rfl⟩ := closed_points_surjective M I hI a ha
    exact (hψ.2 x).trans (hφpoints x).symm
  · exact hψ.1.trans hφbase.symm

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponProjectiveSchemeAction

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ProjectivePointComparison

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

theorem exists_scheme_action
    (N : ℕ) (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I) (hred : I.IsRadical)
    (B : Type u) [AddGroup B]
    (τ : B → ((projectiveSpace K N).zeroLocus I ≃ (projectiveSpace K N).zeroLocus I))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g + h) = (τ h).trans (τ g))
    (hregular : ∀ g, (projectiveSpace K N).IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun x => (τ g x).val)) :
    ∃ T : B → (scheme N I hI ≅ scheme N I hI),
      (∀ g, (T g).hom ≫ ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous N I hI) =
        ProjectiveCoordinateScheme.structureMap I (ordinaryHomogeneous N I hI)) ∧
      (∀ g x, (T g).hom (point N I hI x) = point N I hI (τ g x)) ∧
      T 0 = Iso.refl _ ∧ ∀ g h, T (g + h) = T h ≪≫ T g := by
  classical
  choose A hA huniq using fun g =>
    existsUnique_regular_schemeMap N N I hI hred I hI (τ g) (hregular g)
  have hA0 : A 0 = 𝟙 (scheme N I hI) := by
    symm
    apply huniq 0
    refine ⟨Category.id_comp _, fun x => ?_⟩
    rw [hzero]
    rfl
  have hcomp : ∀ g h, A h ≫ A g = A (g + h) := by
    intro g h
    apply huniq (g + h)
    refine ⟨?_, fun x => ?_⟩
    · rw [Category.assoc, (hA g).1, (hA h).1]
    · change A g (A h (point N I hI x)) = _
      rw [(hA h).2, (hA g).2]
      exact congrArg (point N I hI) (congrArg (fun e => e x) (hadd g h)).symm
  let T (g : B) : scheme N I hI ≅ scheme N I hI :=
    { hom := A g
      inv := A (-g)
      hom_inv_id := by rw [hcomp, neg_add_cancel, hA0]
      inv_hom_id := by rw [hcomp, add_neg_cancel, hA0] }
  refine ⟨T, fun g => (hA g).1, fun g => (hA g).2, ?_, ?_⟩
  · apply Iso.ext
    exact hA0
  · intro g h
    apply Iso.ext
    exact (hcomp g h).symm

end PhilipponMultiplicity.ProjectivePointComparison

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponMultiprojectiveSchemeAction

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 1500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert.SegreVeronese
open MvPolynomial AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    (M : MultiProjectiveSpace K) {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension (fun _ => 1)))
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)

def schemePoint (x : M.zeroLocus I) : scheme M (fun _ => 1) b I hI (fun _ => le_rfl) :=
  ProjectivePointComparison.point N (diagonalIdeal M (fun _ => 1) b I)
    (diagonalIdeal_homogeneous M (fun _ => 1) b (fun _ => le_rfl) I hI)
    (locusEquiv M b I hI x)

def closedPointHomeomorph :
    letI := M.zariskiTopology
    M.zeroLocus I ≃ₜ {x : scheme M (fun _ => 1) b I hI (fun _ => le_rfl) | IsClosed {x}} := by
  letI := M.zariskiTopology
  letI := (projectiveSpace K N).zariskiTopology
  exact (locusHomeomorph M b I hI).trans
    (ProjectivePointComparison.closedPointHomeomorph N _
      (diagonalIdeal_homogeneous M (fun _ => 1) b (fun _ => le_rfl) I hI))

theorem exists_multiprojective_scheme_action (hred : I.IsRadical)
    (B : Type u) [AddGroup B] (τ : B → (M.zeroLocus I ≃ M.zeroLocus I))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g + h) = (τ h).trans (τ g))
    (hregular : ∀ g, M.IsRegularAlong M Subtype.val (fun x => (τ g x).val)) :
    ∃ T : B → (scheme M (fun _ => 1) b I hI (fun _ => le_rfl) ≅
        scheme M (fun _ => 1) b I hI (fun _ => le_rfl)),
      (∀ g, (T g).hom ≫ structureMap M (fun _ => 1) b I hI (fun _ => le_rfl) =
        structureMap M (fun _ => 1) b I hI (fun _ => le_rfl)) ∧
      (∀ g x, (T g).hom (schemePoint M b I hI x) = schemePoint M b I hI (τ g x)) ∧
      T 0 = Iso.refl _ ∧ ∀ g h, T (g + h) = T h ≪≫ T g := by
  classical
  let e := locusEquiv M b I hI
  let τ' (g : B) := (e.symm.trans (τ g)).trans e
  have hzero' : τ' 0 = Equiv.refl _ := by
    ext x
    simp [τ', hzero]
  have hadd' (g h : B) : τ' (g + h) = (τ' h).trans (τ' g) := by
    ext x
    simp [τ', hadd]
  have hregular' (g : B) : (projectiveSpace K N).IsRegularAlong (projectiveSpace K N)
      Subtype.val (fun x => (τ' g x).val) := by
    have h₁ := locusEquiv_inverse_regular M b I hI
    have h₂ := (hregular g).comp_domain e.symm
    have h₃ := (locusEquiv_regular M b I hI).comp_domain (fun x => τ g (e.symm x))
    exact h₁.comp (h₂.comp h₃)
  obtain ⟨T, hT, hpoint, hTzero, hTadd⟩ :=
    ProjectivePointComparison.exists_scheme_action N (diagonalIdeal M (fun _ => 1) b I)
      (diagonalIdeal_homogeneous M (fun _ => 1) b (fun _ => le_rfl) I hI)
      (hred.comap (substitution M (fun _ => 1) b).toRingHom)
      B τ' hzero' hadd' hregular'
  refine ⟨T, hT, ?_, hTzero, hTadd⟩
  intro g x
  have h := hpoint g (e x)
  simp only [τ', Equiv.trans_apply, Equiv.symm_apply_apply] at h
  exact h

end PhilipponMultiplicity.Hilbert.SegreVeronese

end
end

section
set_option maxErrors 2
-- Reused implementation: Solutions.PhilipponGroupClosureScheme

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosureScheme
open MvPolynomial AlgebraicGeometry CategoryTheory
open Hilbert.SegreVeronese
universe u
variable {K : Type u} [Field K] (G : EmbeddedGroupProduct K)

def ideal : Ideal G.ambient.CoordinateRing := G.ambient.vanishingIdeal (Set.range G.embedding)

theorem ideal_homogeneous : IsMultihomogeneousIdeal G.ambient (ideal G) :=
  vanishingIdeal_multihomogeneous K G.ambient (Set.range G.embedding)

theorem ideal_radical : (ideal G).IsRadical :=
  G.ambient.vanishingIdeal_isRadical (Set.range G.embedding)

theorem zeroLocus_eq : G.ambient.zeroLocus (ideal G) = groupProjectiveClosure G :=
  G.ambient.zeroLocus_vanishingIdeal_eq_closure (Set.range G.embedding)

def locusEquiv : groupProjectiveClosure G ≃ G.ambient.zeroLocus (ideal G) :=
  Equiv.setCongr (zeroLocus_eq G).symm

def locusHomeomorph : letI := G.ambient.zariskiTopology
    groupProjectiveClosure G ≃ₜ G.ambient.zeroLocus (ideal G) := by
  letI := G.ambient.zariskiTopology
  exact Homeomorph.setCongr (zeroLocus_eq G).symm

variable {N : ℕ}
    (b : Module.Basis (projectiveSpace K N).Variable K
      (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension (fun _ => 1)))

def scheme : Scheme.{u} :=
  Hilbert.SegreVeronese.scheme G.ambient (fun _ => 1) b (ideal G)
    (ideal_homogeneous G) (fun _ => le_rfl)

def structureMap : scheme G b ⟶ Spec (.of K) :=
  Hilbert.SegreVeronese.structureMap G.ambient (fun _ => 1) b (ideal G)
    (ideal_homogeneous G) (fun _ => le_rfl)

theorem isProper : IsProper (structureMap G b) :=
  structureMap_isProper G.ambient (fun _ => 1) b _ _ _

theorem isReduced : IsReduced (scheme G b) :=
  scheme_isReduced G.ambient (fun _ => 1) b _ _ _ (ideal_radical G)

def point (x : groupProjectiveClosure G) : scheme G b :=
  schemePoint G.ambient b (ideal G) (ideal_homogeneous G) (locusEquiv G x)

variable [IsAlgClosed K]

def closedPointHomeomorph : letI := G.ambient.zariskiTopology
    groupProjectiveClosure G ≃ₜ {x : scheme G b | IsClosed {x}} := by
  letI := G.ambient.zariskiTopology
  exact (locusHomeomorph G).trans
    (Hilbert.SegreVeronese.closedPointHomeomorph G.ambient b (ideal G) (ideal_homogeneous G))

theorem exists_action
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g + h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      Subtype.val (fun x => (τ g x).val)) :
    ∃ T : G.Point → (scheme G b ≅ scheme G b),
      (∀ g, (T g).hom ≫ structureMap G b = structureMap G b) ∧
      (∀ g x, (T g).hom (point G b x) = point G b (τ g x)) ∧
      T 0 = Iso.refl _ ∧ ∀ g h, T (g + h) = T h ≪≫ T g := by
  classical
  let e := locusEquiv G
  let τ' (g : G.Point) := (e.symm.trans (τ g)).trans e
  have hzero' : τ' 0 = Equiv.refl _ := by
    ext x
    simp [τ', hzero]
  have hadd' (g h : G.Point) : τ' (g + h) = (τ' h).trans (τ' g) := by
    ext x
    simp [τ', hadd]
  have hregular' (g : G.Point) : G.ambient.IsRegularAlong G.ambient
      Subtype.val (fun x => (τ' g x).val) :=
    (hregular g).comp_domain e.symm
  obtain ⟨T, hT, hpoint, hTzero, hTadd⟩ := exists_multiprojective_scheme_action
    G.ambient b (ideal G) (ideal_homogeneous G) (ideal_radical G)
    G.Point τ' hzero' hadd' hregular'
  refine ⟨T, hT, ?_, hTzero, hTadd⟩
  intro g x
  have h := hpoint g (e x)
  simp only [τ', Equiv.trans_apply, Equiv.symm_apply_apply] at h
  exact h

end PhilipponMultiplicity.ClosureScheme

namespace PhilipponMultiplicity
open AlgebraicGeometry CategoryTheory
universe u

theorem group_closure_has_proper_scheme_action_proof
    (K : Type u) [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g + h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      Subtype.val (fun x => (τ g x).val)) :
    letI := G.ambient.zariskiTopology
    ∃ (X : Scheme.{u}) (π : X ⟶ Spec (.of K))
      (e : groupProjectiveClosure G ≃ₜ {x : X | IsClosed {x}}),
      IsProper π ∧ IsReduced X ∧
      ∃ T : G.Point → (X ≅ X),
        (∀ g, (T g).hom ≫ π = π) ∧
        (∀ g x, (T g).hom (e x).val = (e (τ g x)).val) ∧
        T 0 = Iso.refl _ ∧ ∀ g h, T (g + h) = T h ≪≫ T g := by
  classical
  letI := G.ambient.zariskiTopology
  obtain ⟨N, ⟨b⟩⟩ := Hilbert.SegreVeronese.exists_coordinate_basis G.ambient (fun _ => 1)
  refine ⟨ClosureScheme.scheme G b, ClosureScheme.structureMap G b,
    ClosureScheme.closedPointHomeomorph G b, ClosureScheme.isProper G b,
    ClosureScheme.isReduced G b, ?_⟩
  exact ClosureScheme.exists_action G b τ hzero hadd hregular

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity AlgebraicGeometry CategoryTheory
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g + h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      Subtype.val (fun x => (τ g x).val)) :
    letI := G.ambient.zariskiTopology
    ∃ (X : Scheme.{u}) (π : X ⟶ Spec (.of K))
      (e : groupProjectiveClosure G ≃ₜ {x : X | IsClosed {x}}),
      IsProper π ∧ IsReduced X ∧
      ∃ T : G.Point → (X ≅ X),
        (∀ g, (T g).hom ≫ π = π) ∧
        (∀ g x, (T g).hom (e x).val = (e (τ g x)).val) ∧
        T 0 = Iso.refl _ ∧ ∀ g h, T (g + h) = T h ≪≫ T g := by
  exact group_closure_has_proper_scheme_action_proof K G τ hzero hadd hregular
