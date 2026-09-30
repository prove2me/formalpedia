-- Prove2me | solution 1 for PhilipponMultiplicity.first_prolongation_preserves_subgroup_vanishingIdeal
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T07:07:21.0806+00:00
-- url     : https://prove2.me/submissions/f3e3cf18-f0fb-4587-a7b0-5eee2bc55477

import Theorems.Thm_PhilipponMultiplicity_retainedPolynomialOperatorIdeal_eq_differentialIdeal
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic

-- Reused implementation: Solutions.PhilipponProjectiveContact
section

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

private theorem completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact completeSpace_of_isometric_ringEquiv e he

end PhilipponMultiplicity
end
end

-- Reused implementation: Solutions.PhilipponProjectiveGeometry
section

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

end MultiProjectiveSpace
end PhilipponMultiplicity
end
end

-- Reused implementation: Solutions.PhilipponHomogeneousOperations
section

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

-- Reused implementation: Solutions.PhilipponAnalyticContainment
section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_lift_eq_zero_of_mem_vanishingIdeal
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    {V : Set M.Point} {p : M.Point} (hp : p ∈ V)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal V) :
    MvPolynomial.eval v P = 0 := by
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
  have hideal : M.vanishingIdeal V ≤ RingHom.ker (MvPolynomial.eval v) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hz⟩
    change MvPolynomial.eval v Q = 0
    rw [hv', M.eval_block_scale Q D hD (M.coordinate p) (fun i => (a i : K)),
      show MvPolynomial.eval (M.coordinate p) Q = 0
      from hz p hp, mul_zero]
  exact hideal hP

end PhilipponMultiplicity
end
end

-- Reused implementation: Solutions.PhilipponAdditiveSubgroups
section

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

-- Reused implementation: Solutions.PhilipponPointHilbert
section

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

-- Reused implementation: Solutions.PhilipponPolynomialIdealHomogeneous
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [Field K]

theorem homogeneous_span (M : MultiProjectiveSpace K) (S : Set M.CoordinateRing)
    (hS : ∀ P ∈ S, ∃ D, M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (Ideal.span S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hh : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D,hD⟩ := hS P hP
    exact ⟨D,(M.degreePiece_iff P D).mpr hD⟩
  intro P hP D
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP D

end PhilipponMultiplicity.OperatorSupport
end
end

-- Reused implementation: Solutions.PhilipponRegularMapTopology
section

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

-- Reused implementation: Solutions.PhilipponRegularMapComposition
section

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

/-- Composition of regular maps, including maps given along arbitrary embedded domains. -/
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

-- Reused implementation: Solutions.PhilipponProjectiveTranslations
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K] {n : ℕ}

def projectiveLeftSlice (a : Projectivization K (Fin (n + 1) → K))
    (p : (projectiveSpace K n).Point) : (projectiveSquare K n).Point :=
  fun b => if b.val = 0 then p (0 : Fin 1) else a

def projectiveLeftSlicePolynomial (a : Projectivization K (Fin (n + 1) → K))
    (v : (projectiveSquare K n).Variable) : (projectiveSpace K n).CoordinateRing :=
  if v.1.val = 0 then X ⟨(0 : Fin 1), v.2⟩ else C (a.rep v.2)

theorem projectiveLeftSlicePolynomial_homogeneous
    (a : Projectivization K (Fin (n + 1) → K)) (v : (projectiveSquare K n).Variable) :
    (projectiveSpace K n).IsHomogeneous (projectiveLeftSlicePolynomial a v)
      (fun _ => if v.1.val = 0 then 1 else 0) := by
  classical
  by_cases hv : v.1.val = 0
  · simp only [projectiveLeftSlicePolynomial, if_pos hv]
    convert (projectiveSpace K n).isHomogeneous_X ⟨(0 : Fin 1), v.2⟩ using 1
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    simp [hi]
  · simpa only [projectiveLeftSlicePolynomial, if_neg hv] using!
      (projectiveSpace K n).isHomogeneous_C (a.rep v.2)

theorem projectiveLeftSlice_eval (a : Projectivization K (Fin (n + 1) → K))
    (P : (projectiveSquare K n).CoordinateRing) (p : (projectiveSpace K n).Point) :
    (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p =
      (projectiveSquare K n).eval P (projectiveLeftSlice a p) := by
  dsimp only [MultiProjectiveSpace.eval]
  rw [← eval_assoc]
  apply congrArg (fun v => MvPolynomial.eval v P)
  funext v
  by_cases hv : v.1.val = 0 <;>
    simp [projectiveLeftSlicePolynomial, projectiveLeftSlice,
      MultiProjectiveSpace.coordinate, hv]

theorem projectiveLeftSlice_continuous (a : Projectivization K (Fin (n + 1) → K)) :
    @Continuous _ _ (projectiveSpace K n).zariskiTopology
      (projectiveSquare K n).zariskiTopology (projectiveLeftSlice a) := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have heq : projectiveLeftSlice a ⁻¹' {p | (projectiveSquare K n).eval P p ≠ 0} =
      {p | (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0} := by
    ext p
    change (projectiveSquare K n).eval P (projectiveLeftSlice a p) ≠ 0 ↔
      (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0
    rw [projectiveLeftSlice_eval]
  rw [heq]
  apply (projectiveSpace K n).isOpen_basic
  exact hP.eval₂_blocks _ _ _ (fun b _ => if b.val = 0 then 1 else 0)
    (projectiveLeftSlicePolynomial_homogeneous a)

/-- Fixing one projective argument of a regular map gives a regular map. -/
theorem MultiProjectiveSpace.IsRegularAlong.of_left_slice
    {X : Type u} (N : MultiProjectiveSpace K)
    (a : Projectivization K (Fin (n + 1) → K))
    {e : X → (projectiveSpace K n).Point} {f : X → N.Point}
    (hf : (projectiveSquare K n).IsRegularAlong N (projectiveLeftSlice a ∘ e) f) :
    (projectiveSpace K n).IsRegularAlong N e f := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  let := (projectiveSquare K n).zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hlift⟩ := hf x b
  refine ⟨projectiveLeftSlice a ⁻¹' U, hU.preimage (projectiveLeftSlice_continuous a),
    hxU, (fun i => ∑ c, D c * (if c.val = 0 then 1 else 0)),
    (fun j => eval₂ C (projectiveLeftSlicePolynomial a) (P j)), ?_, ?_⟩
  · intro j
    exact (hP j).eval₂_blocks _ _ _ (fun c _ => if c.val = 0 then 1 else 0)
      (projectiveLeftSlicePolynomial_homogeneous a)
  · intro y hy
    obtain ⟨hn, heq⟩ := hlift y hy
    simpa only [projectiveLeftSlice_eval, Function.comp_apply] using ⟨hn, heq⟩

/-- The regular group law supplies regular translations. -/
theorem EmbeddedCommutativeGroup.translation_regular
    (G : EmbeddedCommutativeGroup K) (a : G.Point) :
    (projectiveSpace K G.ambientDimension).IsRegularAlong
      (projectiveSpace K G.ambientDimension)
      (fun x : G.Point => fun _ => x.val)
      (fun x => fun _ => (x + a).val) := by
  apply MultiProjectiveSpace.IsRegularAlong.of_left_slice _ a.val
  exact G.addition_regular.comp_domain (fun x : G.Point => (x, a))

end PhilipponMultiplicity
end
end

-- Reused implementation: Solutions.PhilipponProductRegularity
section

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

theorem EmbeddedGroupProduct.translation_regular (G : EmbeddedGroupProduct K) (a : G.Point) :
    G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (x + a)) := by
  intro x b
  have hp := (G.ambient.projection_regular b).comp_domain G.embedding
  have ht := ((G.factor b).translation_regular (a b)).comp_domain (fun y : G.Point => y b)
  obtain ⟨U, hU, hx, D, P, hP, hl⟩ := (hp.comp ht) x (0 : Fin 1)
  exact ⟨U, hU, hx, D, P, hP, hl⟩

theorem EmbeddedGroupProduct.negation_regular (G : EmbeddedGroupProduct K) :
    G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (-x)) := by
  intro x b
  have hp := (G.ambient.projection_regular b).comp_domain G.embedding
  have hn := (G.factor b).negation_regular.comp_domain (fun y : G.Point => y b)
  obtain ⟨U, hU, hx, D, P, hP, hl⟩ := (hp.comp hn) x (0 : Fin 1)
  exact ⟨U, hU, hx, D, P, hP, hl⟩

end PhilipponMultiplicity
end
end

-- Reused implementation: Solutions.PhilipponPolynomialMapCharts
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K] {X : Type u}
  {M N : MultiProjectiveSpace K} {e : X → M.Point} {f : X → N.Point}

/-- Polynomial formulas for one target block, with a homogeneous basic domain.
The entire tuple vanishes off that domain, giving global compatibility. -/
structure PolynomialMapChart (M N : MultiProjectiveSpace K)
    {X : Type u} (e : X → M.Point) (f : X → N.Point) (b : N.FactorIndex) where
  cut : M.CoordinateRing
  cutDegree : M.FactorIndex → ℕ
  cut_homogeneous : M.IsHomogeneous cut cutDegree
  degree : M.FactorIndex → ℕ
  coordinates : Fin (N.ambientDimension b + 1) → M.CoordinateRing
  homogeneous : ∀ j, M.IsHomogeneous (coordinates j) degree
  zero_off : ∀ x, M.eval cut (e x) = 0 → ∀ j, M.eval (coordinates j) (e x) = 0
  represents : ∀ x, M.eval cut (e x) ≠ 0 →
    ∃ h : (fun j => M.eval (coordinates j) (e x)) ≠ 0,
      Projectivization.mk K (fun j => M.eval (coordinates j) (e x)) h = f x b

theorem PolynomialMapChart.compatible {b : N.FactorIndex}
    (chart : PolynomialMapChart M N e f b) (x : X)
    (j k : Fin (N.ambientDimension b + 1)) :
    M.eval (chart.coordinates j) (e x) * (f x b).rep k =
      M.eval (chart.coordinates k) (e x) * (f x b).rep j := by
  by_cases hx : M.eval chart.cut (e x) = 0
  · rw [chart.zero_off x hx j,chart.zero_off x hx k,zero_mul,zero_mul]
  · obtain ⟨hn,heq⟩ := chart.represents x hx
    exact (projectivization_mk_eq_iff_cross _ _ hn (f x b).rep_nonzero).mp
      (heq.trans (f x b).mk_rep.symm) j k

theorem IsRegularAlong.exists_polynomialMapChart (hf : M.IsRegularAlong N e f)
    (x : X) (b : N.FactorIndex) :
    ∃ chart : PolynomialMapChart M N e f b, M.eval chart.cut (e x) ≠ 0 := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  obtain ⟨U,hU,hx,D,P,hP,hrep⟩ := hf x b
  obtain ⟨V,⟨q,E,hq,rfl⟩,hxq,hqU⟩ :=
    M.isTopologicalBasis_basic.exists_subset_of_mem_open hx hU
  let chart : PolynomialMapChart M N e f b :=
    { cut := q
      cutDegree := E
      cut_homogeneous := hq
      degree := E+D
      coordinates := fun j => q * P j
      homogeneous := fun j => hq.mul M (hP j)
      zero_off := by
        intro y hy j
        simp only [eval,map_mul] at hy ⊢
        rw [hy,zero_mul]
      represents := by
        intro y hy
        obtain ⟨hn,heq⟩ := hrep y (hqU hy)
        have hval : (fun j => M.eval (q * P j) (e y)) =
            M.eval q (e y) • (fun j => M.eval (P j) (e y)) := by
          funext j
          simp only [eval,map_mul,Pi.smul_apply,smul_eq_mul]
        have hn' : (fun j => M.eval (q * P j) (e y)) ≠ 0 := by
          rw [hval]
          exact smul_ne_zero hy hn
        exact ⟨hn',((Projectivization.mk_eq_mk_iff' K _ _ hn' hn).mpr
          ⟨M.eval q (e y),hval.symm⟩).trans heq⟩ }
  exact ⟨chart,hxq⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

-- Reused implementation: Solutions.PhilipponPolynomialChartLifts
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K] {X : Type u}
  {M N : MultiProjectiveSpace K} {e : X → M.Point} {f : X → N.Point}
  {b : N.FactorIndex}

theorem PolynomialMapChart.represents_lift (chart : PolynomialMapChart M N e f b)
    (x : X) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = e x i)
    (hcut : MvPolynomial.eval v chart.cut ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (chart.coordinates j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (chart.coordinates j)) h = f x b := by
  have hc : M.eval chart.cut (e x) ≠ 0 :=
    (M.eval_eq_zero_iff_of_lift (e x) v hv chart.cut chart.cutDegree chart.cut_homogeneous).not.mp hcut
  obtain ⟨hn,heq⟩ := chart.represents x hc
  obtain ⟨hn',heq'⟩ := M.homogeneous_tuple_lift (e x) v hv chart.coordinates chart.degree chart.homogeneous hn
  exact ⟨hn',heq'.trans heq⟩

/-- The chart cross-product identity survives arbitrary genuine homogeneous
lifts of both source and target, including outside the chart domain. -/
theorem PolynomialMapChart.compatible_lifts (chart : PolynomialMapChart M N e f b)
    (x : X) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = e x i)
    (w : Fin (N.ambientDimension b + 1) → K) (hw : w ≠ 0)
    (hwrep : Projectivization.mk K w hw = f x b) :
    ∀ j k, MvPolynomial.eval v (chart.coordinates j) * w k =
      MvPolynomial.eval v (chart.coordinates k) * w j := by
  by_cases hcut : MvPolynomial.eval v chart.cut = 0
  · have hc := (M.eval_eq_zero_iff_of_lift (e x) v hv chart.cut chart.cutDegree
      chart.cut_homogeneous).mp hcut
    have hz (j) : MvPolynomial.eval v (chart.coordinates j) = 0 :=
      (M.eval_eq_zero_iff_of_lift (e x) v hv (chart.coordinates j) chart.degree
        (chart.homogeneous j)).mpr (chart.zero_off x hc j)
    intro j k
    rw [hz j,hz k,zero_mul,zero_mul]
  · obtain ⟨hn,heq⟩ := chart.represents_lift x v hv hcut
    exact (projectivization_mk_eq_iff_cross _ _ hn hw).mp (heq.trans hwrep.symm)

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

-- Reused implementation: Solutions.PhilipponDifferentialVanishing
section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem chartDomain_isOpen (b : CoordinateChart G) :
    @IsOpen _ G.zariskiTopology (chartDomain G b) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have h (i : G.FactorIndex) : @IsOpen _ G.zariskiTopology
      {x | (G.embedding x i).rep (b i) ≠ 0} := by
    let v : G.ambient.Variable := ⟨i, b i⟩
    have hh : G.ambient.IsHomogeneous (X v) (Pi.single i 1) := by
      apply (G.ambient.degreePiece_iff _ _).mp
      exact isWeightedHomogeneous_X K _ v
    have ho := G.ambient.isOpen_basic (X v) (Pi.single i 1) hh
    have hp := ho.preimage (continuous_induced_dom :
      @Continuous _ _ G.zariskiTopology G.ambient.zariskiTopology G.embedding)
    simpa [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate, v] using hp
  have heq : chartDomain G b = ⋂ i, {x | (G.embedding x i).rep (b i) ≠ 0} := by
    ext x
    simp [chartDomain]
  rw [heq]
  exact isOpen_iInter_of_finite h

theorem exists_chartDomain (x : G.Point) : ∃ b : CoordinateChart G, x ∈ chartDomain G b := by
  have h (i : G.FactorIndex) : ∃ j, (G.embedding x i).rep j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using (G.embedding x i).rep_nonzero
  choose b hb using h
  exact ⟨b, hb⟩

theorem chartValue_homogeneous (b : CoordinateChart G) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) (x : G.Point) :
    chartValue G b P x =
      (∏ i, ((G.embedding x i).rep (b i))⁻¹ ^ D i) * G.ambient.eval P (G.embedding x) := by
  unfold chartValue
  calc
    _ = MvPolynomial.eval
        (fun v : G.ambient.Variable =>
          ((G.embedding x v.1).rep (b v.1))⁻¹ * (G.embedding x v.1).rep v.2) P := by
      apply congrArg (fun v : G.ambient.Variable → K => MvPolynomial.eval v P)
      funext v
      exact div_eq_inv_mul _ _
    _ = _ := G.ambient.eval_block_scale P D hP (G.ambient.coordinate (G.embedding x))
      (fun i : G.FactorIndex => ((G.embedding x i).rep (b i))⁻¹)

end PhilipponMultiplicity.OperatorSupport
end
end

-- Reused implementation: Solutions.PhilipponNormalizedChartGerms
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem projective_pivot_ne_zero {ι : Type*} (v : ι → K) (hv : v ≠ 0)
    (p : Projectivization K (ι → K)) (hp : Projectivization.mk K v hv = p)
    (j : ι) (hj : p.rep j ≠ 0) : v j ≠ 0 := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v p.rep hv p.rep_nonzero).mp
    (hp.trans p.mk_rep.symm)
  have hj' : v j = (a : K) * p.rep j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  rw [hj']
  exact mul_ne_zero a.ne_zero hj

theorem projective_pivot_ne_zero_iff {ι : Type*} (v : ι → K) (hv : v ≠ 0)
    (p : Projectivization K (ι → K)) (hp : Projectivization.mk K v hv = p)
    (j : ι) : v j ≠ 0 ↔ p.rep j ≠ 0 := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v p.rep hv p.rep_nonzero).mp
    (hp.trans p.mk_rep.symm)
  have hj : v j = (a : K) * p.rep j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  simp [hj,a.ne_zero]

theorem lift_pivot_ne_zero (A : AnalyticSubgroup G) (g : G.Point)
    (b : CoordinateChart G) (hg : g ∈ chartDomain G b) (i : G.FactorIndex) :
    A.lift g 0 ⟨i,b i⟩ ≠ 0 := by
  obtain ⟨hz,hi⟩ := (A.lift_represents g).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  rw [hz',A.map_zero,add_zero] at hi
  obtain ⟨hne,heq⟩ := hi i
  exact projective_pivot_ne_zero _ hne _ heq _ (hg i)

end PhilipponMultiplicity.OperatorSupport
end
end

-- Reused implementation: Solutions.PhilipponOrbitLocality
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem polynomialPullback_analytic (A : AnalyticSubgroup G)
    (g : G.Point) (P : G.CoordinateRing) :
    AnalyticAt K (A.pullback P g) 0 :=
  AnalyticAt.aeval_mvPolynomial (fun v => A.lift_analytic g v) P

theorem lift_zero_represents (A : AnalyticSubgroup G) (g : G.Point) :
    ∀ i : G.FactorIndex, ∃ h : (fun j => A.lift g 0 ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => A.lift g 0 ⟨i,j⟩) h = G.embedding g i := by
  obtain ⟨hz,hrep⟩ := (A.lift_represents g).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  simpa only [hz',A.map_zero,add_zero] using hrep

end PhilipponMultiplicity.OperatorSupport
end
end

-- Reused implementation: Solutions.PhilipponTangentTransport
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- At a zero of the polynomial, changing an analytic projective lift
multiplies every directional derivative by one nonzero scalar. -/
theorem MultiProjectiveSpace.fderiv_eval_zero_iff_of_projective_lifts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (f g : E → M.Variable → K) (x v : E)
    (hf : ∀ j, AnalyticAt K (fun z => f z j) x)
    (hg : ∀ j, AnalyticAt K (fun z => g z j) x)
    (hrep : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i,j⟩) ≠ 0,
      ∃ hgi : (fun j => g z ⟨i,j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i,j⟩) hfi =
          Projectivization.mk K (fun j => g z ⟨i,j⟩) hgi)
    (hzero : MvPolynomial.eval (g x) P = 0) :
    fderiv K (fun z => MvPolynomial.eval (f z) P) x v = 0 ↔
      fderiv K (fun z => MvPolynomial.eval (g z) P) x v = 0 := by
  classical
  have hpivot (i : M.FactorIndex) : ∃ j, g x ⟨i,j⟩ ≠ 0 := by
    obtain ⟨_,hgi,_⟩ := hrep.self_of_nhds i
    simpa only [ne_eq,funext_iff,Pi.zero_apply,not_forall] using hgi
  choose j hj using hpivot
  let a (z : E) (i : M.FactorIndex) := f z ⟨i,j i⟩ / g z ⟨i,j i⟩
  let u (z : E) := ∏ i, a z i ^ D i
  have ha (i : M.FactorIndex) : AnalyticAt K (fun z => a z i) x :=
    (hf _).div (hg _) (hj i)
  have hu : AnalyticAt K u x :=
    Finset.analyticAt_fun_prod _ (fun i _ => (ha i).pow _)
  have hscale (z : E) (hz : ∀ i : M.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i,j⟩) ≠ 0,
      ∃ hgi : (fun j => g z ⟨i,j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i,j⟩) hfi =
          Projectivization.mk K (fun j => g z ⟨i,j⟩) hgi)
      (hjz : ∀ i, g z ⟨i,j i⟩ ≠ 0) :
      (∀ i, a z i ≠ 0) ∧ f z = fun q => a z q.1 * g z q := by
    have hh (i : M.FactorIndex) :
        a z i ≠ 0 ∧ ∀ k, f z ⟨i,k⟩ = a z i * g z ⟨i,k⟩ := by
      obtain ⟨hfi,hgi,heq⟩ := hz i
      obtain ⟨b,hb⟩ := (Projectivization.mk_eq_mk_iff K _ _ hfi hgi).mp heq
      have he (k) : f z ⟨i,k⟩ = (b : K) * g z ⟨i,k⟩ := by
        simpa only [Pi.smul_apply,Units.smul_def,smul_eq_mul] using (congrFun hb k).symm
      have hab : a z i = (b : K) := by
        dsimp [a]
        rw [he, mul_div_cancel_right₀ _ (hjz i)]
      exact ⟨hab ▸ b.ne_zero, fun k => by rw [hab]; exact he k⟩
    exact ⟨fun i => (hh i).1, funext fun q => (hh q.1).2 q.2⟩
  have hux : u x ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ ((hscale x hrep.self_of_nhds hj).1 i))
  have hnear : ∀ᶠ z in 𝓝 x, ∀ i, g z ⟨i,j i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    exact fun i => (hg _).continuousAt.eventually_ne (hj i)
  have heq : (fun z => MvPolynomial.eval (f z) P) =ᶠ[𝓝 x]
      (fun z => u z * MvPolynomial.eval (g z) P) := by
    filter_upwards [hrep,hnear] with z hz hjz
    rw [(hscale z hz hjz).2, M.eval_block_scale P D hP]
  have hgP : AnalyticAt K (fun z => MvPolynomial.eval (g z) P) x :=
    AnalyticAt.aeval_mvPolynomial hg P
  rw [heq.fderiv_eq, fderiv_fun_mul hu.differentiableAt hgP.differentiableAt]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    hzero,smul_eq_mul,zero_mul,add_zero]
  exact mul_eq_zero_iff_left hux

variable {G : EmbeddedGroupProduct K}

/-- Homogeneous equations suffice to test the actual ideal-defined tangent
kernel. The product rule handles their arbitrary polynomial multiples. -/
theorem AnalyticSubgroup.fderiv_zero_of_homogeneous_equations
    (A : AnalyticSubgroup G) (V : Set G.Point) (x : G.Point) (hx : x ∈ V)
    (v : A.ParameterSpace)
    (h : ∀ P : G.CoordinateRing, (∃ D, G.ambient.IsHomogeneous P D) →
      (∀ y ∈ V, G.ambient.eval P (G.embedding y) = 0) →
      fderiv K (A.pullback P x) 0 v = 0)
    (P : G.CoordinateRing) (hP : P ∈ G.vanishingIdeal V) :
    fderiv K (A.pullback P x) 0 v = 0 := by
  have hzero (Q : G.CoordinateRing) (hQ : Q ∈ G.vanishingIdeal V) :
      A.pullback Q x 0 = 0 := G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding hx) _ (lift_zero_represents A x) hQ
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    exact h Q hQ.1 (fun y hy => hQ.2 _ ⟨y,hy,rfl⟩)
  | zero =>
    change fderiv K (fun z : A.ParameterSpace => MvPolynomial.eval (A.lift x z) 0) 0 v = 0
    simp only [_root_.map_zero, fderiv_const_apply, ContinuousLinearMap.zero_apply]
  | add Q R hQ hR ihQ ihR =>
    have heq : A.pullback (Q+R) x = fun z => A.pullback Q x z + A.pullback R x z := by
      funext z; exact _root_.map_add _ _ _
    rw [heq, fderiv_fun_add (polynomialPullback_analytic A x Q).differentiableAt
      (polynomialPullback_analytic A x R).differentiableAt]
    simp only [ContinuousLinearMap.add_apply,ihQ,ihR,add_zero]
  | smul a Q hQ ih =>
    have heq : A.pullback (a • Q) x = fun z => A.pullback a x z * A.pullback Q x z := by
      funext z; exact map_mul _ _ _
    rw [heq, fderiv_fun_mul (polynomialPullback_analytic A x a).differentiableAt
      (polynomialPullback_analytic A x Q).differentiableAt]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ih,hzero Q hQ,smul_zero,zero_smul,add_zero]

end PhilipponMultiplicity
end
end

-- Reused implementation: Solutions.PhilipponFirstProlongation
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport

namespace FirstProlongationProof

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)

/-- Translate a homogeneous equation by a subgroup point, clear the chart
cuts, and transport its first derivative back to the identity. -/
theorem fderiv_zero_at_subgroup
    (htangent : A.tangentKernel H.carrier = ⊤)
    (x : G.Point) (hx : x ∈ H.carrier) (v : A.ParameterSpace)
    (Q : G.CoordinateRing) (hQ : Q ∈ G.vanishingIdeal H.carrier) :
    fderiv K (A.pullback Q x) 0 v = 0 := by
  classical
  apply A.fderiv_zero_of_homogeneous_equations H.carrier x hx v _ Q hQ
  rintro P ⟨D, hP⟩ hPH
  have hPI : P ∈ G.vanishingIdeal H.carrier :=
    Ideal.subset_span ⟨⟨D, hP⟩, by rintro _ ⟨y, hy, rfl⟩; exact hPH y hy⟩
  have hPx : A.pullback P x 0 = 0 :=
    G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
      (Set.mem_image_of_mem G.embedding hx) _ (lift_zero_represents A x) hPI
  choose chart hchart using
    (fun i => (G.translation_regular x).exists_polynomialMapChart 0 i)
  let coords (q : G.ambient.Variable) := (chart q.1).coordinates q.2
  let s : G.CoordinateRing := ∏ i, (chart i).cut
  let E : G.FactorIndex → ℕ := ∑ i, (chart i).cutDegree
  let R : G.CoordinateRing := eval₂ C coords P
  let F : G.FactorIndex → ℕ := fun i => ∑ b, D b * (chart b).degree i
  have hs : G.ambient.IsHomogeneous s E :=
    G.ambient.isHomogeneous_prod _ _ _ (fun i _ => (chart i).cut_homogeneous)
  have hR : G.ambient.IsHomogeneous R F :=
    hP.eval₂_blocks G.ambient G.ambient coords (fun i => (chart i).degree)
      (fun q => (chart q.1).homogeneous q.2)
  have hseval (y : G.Point) :
      G.ambient.eval s (G.embedding y) = ∏ i, G.ambient.eval (chart i).cut (G.embedding y) :=
    map_prod _ _ _
  have hReval (y : G.Point) : G.ambient.eval R (G.embedding y) =
      MvPolynomial.eval (fun q => G.ambient.eval (coords q) (G.embedding y)) P := by
    dsimp only [R, MultiProjectiveSpace.eval]
    rw [← eval_assoc]
    rfl
  have hsR : s * R ∈ G.vanishingIdeal H.carrier := by
    apply Ideal.subset_span
    refine ⟨⟨E + F, hs.mul G.ambient hR⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    change G.ambient.eval (s * R) (G.embedding y) = 0
    rw [show G.ambient.eval (s * R) (G.embedding y) =
      G.ambient.eval s (G.embedding y) * G.ambient.eval R (G.embedding y) from map_mul _ _ _]
    by_cases hsy : G.ambient.eval s (G.embedding y) = 0
    · rw [hsy, zero_mul]
    · have hcuts : ∀ i, G.ambient.eval (chart i).cut (G.embedding y) ≠ 0 := by
        have hp : (∏ i, G.ambient.eval (chart i).cut (G.embedding y)) ≠ 0 :=
          (hseval y) ▸ hsy
        exact fun i => (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
      have hyH : y + x ∈ H.carrier := H.toAddSubgroup.add_mem hy hx
      have hz : G.ambient.eval R (G.embedding y) = 0 := by
        rw [hReval]
        apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
          (Set.mem_image_of_mem G.embedding hyH) _ _ hPI
        exact fun i => (chart i).represents y (hcuts i)
      rw [hz, mul_zero]
  let f (z : A.ParameterSpace) (q : G.ambient.Variable) :=
    MvPolynomial.eval (A.lift 0 z) (coords q)
  have hf (q) : AnalyticAt K (fun z => f z q) 0 :=
    polynomialPullback_analytic A 0 (coords q)
  have hcut0 (i : G.FactorIndex) : A.pullback (chart i).cut 0 0 ≠ 0 :=
    (G.ambient.eval_eq_zero_iff_of_lift (G.embedding 0) (A.lift 0 0)
      (lift_zero_represents A 0) _ _ (chart i).cut_homogeneous).not.mpr (hchart i)
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ i,
      A.pullback (chart i).cut 0 z ≠ 0 := by
    rw [Filter.eventually_all]
    exact fun i => (polynomialPullback_analytic A 0 _).continuousAt.eventually_ne (hcut0 i)
  have hrep : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ i : G.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i, j⟩) ≠ 0,
      ∃ hgi : (fun j => A.lift x z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) hfi =
          Projectivization.mk K (fun j => A.lift x z ⟨i, j⟩) hgi := by
    filter_upwards [hnear, A.lift_represents 0, A.lift_represents x] with z hz hz0 hzx
    obtain ⟨hz0, h0lift⟩ := hz0
    obtain ⟨hzx, hxlift⟩ := hzx
    have hsame : (⟨z, hz0⟩ : A.domain) = ⟨z, hzx⟩ := Subtype.ext rfl
    intro i
    obtain ⟨hn, heq⟩ := (chart i).represents_lift (0 + A.map ⟨z, hz0⟩)
      (A.lift 0 z) h0lift (hz i)
    obtain ⟨hnx, heqx⟩ := hxlift i
    refine ⟨hn, hnx, heq.trans ?_⟩
    rw [heqx, hsame]
    exact congrArg (fun y => G.embedding y i) (by abel)
  have hRpull : A.pullback R 0 = fun z => MvPolynomial.eval (f z) P := by
    funext z
    dsimp only [AnalyticSubgroup.pullback, R, f]
    rw [← eval_assoc]
    rfl
  have hR0 : A.pullback R 0 0 = 0 := by
    rw [hRpull]
    apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
      (Set.mem_image_of_mem G.embedding hx) _ _ hPI
    intro i
    obtain ⟨hn, hnx, heq⟩ := hrep.self_of_nhds i
    obtain ⟨hn', heq'⟩ := lift_zero_represents A x i
    exact ⟨hn, heq.trans heq'⟩
  have hs0 : A.pullback s 0 0 ≠ 0 := by
    change MvPolynomial.eval (A.lift 0 0) (∏ i, (chart i).cut) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hcut0 i)
  have hv : v ∈ A.tangentKernel H.carrier := by rw [htangent]; trivial
  have hsd : fderiv K (A.pullback (s * R) 0) 0 v = 0 :=
    (Submodule.mem_iInf _).mp hv ⟨s * R, hsR⟩
  have hmul : A.pullback (s * R) 0 = fun z => A.pullback s 0 z * A.pullback R 0 z := by
    funext z; exact map_mul _ _ _
  rw [hmul, fderiv_fun_mul (polynomialPullback_analytic A 0 s).differentiableAt
    (polynomialPullback_analytic A 0 R).differentiableAt] at hsd
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    hR0, smul_eq_mul, zero_mul, add_zero] at hsd
  have hRd : fderiv K (A.pullback R 0) 0 v = 0 := (mul_eq_zero.mp hsd).resolve_left hs0
  rw [hRpull] at hRd
  exact (G.ambient.fderiv_eval_zero_iff_of_projective_lifts P D hP f (A.lift x)
    0 v hf (A.lift_analytic x) hrep hPx).mp hRd

omit H in
/-- Normalization at the origin agrees with the ordinary projective chart. -/
theorem normalizedPullback_zero (x : G.Point) (b : CoordinateChart G)
    (P : G.CoordinateRing) :
    normalizedPullback A 0 b P x 0 = chartValue G b P x := by
  unfold normalizedPullback chartValue
  simp only [zero_add]
  apply congrArg (fun f : G.ambient.Variable → K => MvPolynomial.eval f P)
  funext v
  obtain ⟨hv, he⟩ := lift_zero_represents A x v.1
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ hv
    (G.embedding x v.1).rep_nonzero).mp
    (he.trans (G.embedding x v.1).mk_rep.symm)
  have hh (j) : A.lift x 0 ⟨v.1, j⟩ = (a : K) * (G.embedding x v.1).rep j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  rw [hh, hh, mul_div_mul_left _ _ a.ne_zero]

/-- Both the value and the first derivative vanish after normalizing a lift. -/
theorem normalizedJet_zero_on_subgroup
    (htangent : A.tangentKernel H.carrier = ⊤)
    (P : G.CoordinateRing) (hPI : P ∈ G.vanishingIdeal H.carrier)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) (hx : x ∈ H.carrier) (b : CoordinateChart G)
    (hb : x ∈ chartDomain G b) (j : JetIndex A.parameterDimension 1) :
    normalizedJet A 0 b P j x = 0 := by
  classical
  let u (z : A.ParameterSpace) := ∏ i, (A.lift x z ⟨i, b i⟩)⁻¹ ^ D i
  have hu : AnalyticAt K u 0 :=
    Finset.analyticAt_fun_prod _ fun i _ =>
      ((A.lift_analytic x _).inv (lift_pivot_ne_zero A x b hb i)).pow _
  have hnorm : normalizedPullback A 0 b P x =
      fun z => u z * A.pullback P x z := by
    funext z
    unfold normalizedPullback
    simp only [zero_add]
    have heq : (fun v : G.ambient.Variable => A.lift x z v / A.lift x z ⟨v.1, b v.1⟩) =
        fun v : G.ambient.Variable => (A.lift x z ⟨v.1, b v.1⟩)⁻¹ * A.lift x z v := by
      funext v
      exact div_eq_inv_mul _ _
    rw [heq]
    exact G.ambient.eval_block_scale P D hP (A.lift x z)
      (fun i => (A.lift x z ⟨i, b i⟩)⁻¹)
  have hzero : A.pullback P x 0 = 0 :=
    G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
      (Set.mem_image_of_mem G.embedding hx) _ (lift_zero_represents A x) hPI
  rcases j with ⟨n, hn, dirs⟩
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · simp only [normalizedJet, iteratedFDeriv_zero_apply, hnorm, hzero, mul_zero]
  · rw [normalizedJet, iteratedFDeriv_one_apply, hnorm,
      fderiv_fun_mul hu.differentiableAt (polynomialPullback_analytic A x P).differentiableAt]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      fderiv_zero_at_subgroup A H htangent x hx _ P hPI, hzero,
      smul_zero, zero_smul, add_zero]

/-- Local rational combinations of these zero jets vanish on the subgroup. -/
theorem differentialIdeal_le_vanishingIdeal
    (htangent : A.tangentKernel H.carrier = ⊤) :
    differentialIdeal A 0 1 (G.vanishingIdeal H.carrier) ≤ G.vanishingIdeal H.carrier := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D, hD⟩, hP⟩
  apply Ideal.subset_span
  refine ⟨⟨D, hD⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨b, U, hU, hxU, hsub, n, f, r, hfr, heq⟩ := hP x
  have hz : chartValue G b P x = 0 := by
    rw [heq x hxU]
    apply Finset.sum_eq_zero
    intro i _
    have hfi : (f i).val.value x = 0 := by
      obtain ⟨Q, hQ, ⟨E, hE⟩, c, j, hf⟩ := (f i).property
      have hc : x ∈ chartDomain G c := by
        simpa only [hf, zero_add, Set.mem_setOf_eq] using (hfr i x hxU).1
      rw [hf]
      exact normalizedJet_zero_on_subgroup A H htangent Q hQ E hE x hx c hc j
    rw [hfi, mul_zero]
  rw [chartValue_homogeneous b P D hD x] at hz
  exact (mul_eq_zero.mp hz).resolve_left
    (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (inv_ne_zero (hsub hxU i)))

/-- The order-zero sections include every homogeneous subgroup equation. -/
theorem vanishingIdeal_le_differentialIdeal :
    G.vanishingIdeal H.carrier ≤ differentialIdeal A 0 1 (G.vanishingIdeal H.carrier) := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D, hD⟩, hP⟩
  have hPI : P ∈ G.vanishingIdeal H.carrier := Ideal.subset_span ⟨⟨D, hD⟩, hP⟩
  apply Ideal.subset_span
  refine ⟨⟨D, hD⟩, ?_⟩
  intro x
  obtain ⟨b, hb⟩ := exists_chartDomain x
  let j : JetIndex A.parameterDimension 1 := ⟨0, Nat.zero_le _, Fin.elim0⟩
  let f : differentialSections A 0 1 (G.vanishingIdeal H.carrier) :=
    ⟨⟨{y | 0 + y ∈ chartDomain G b}, normalizedJet A 0 b P j⟩,
      P, hPI, ⟨D, hD⟩, b, j, rfl⟩
  let r : RationalCoefficient G :=
    ⟨1, 1, 0, G.ambient.isHomogeneous_one, G.ambient.isHomogeneous_one⟩
  refine ⟨b, chartDomain G b, chartDomain_isOpen b, hb, Set.Subset.rfl,
    1, (fun _ => f), (fun _ => r), ?_, ?_⟩
  · intro i y hy
    exact ⟨by simpa [f] using hy, by simp [r, MultiProjectiveSpace.eval]⟩
  · intro y hy
    simp only [Fintype.sum_unique, f, r, RationalCoefficient.value,
      MultiProjectiveSpace.eval, map_one, div_self one_ne_zero, one_mul,
      normalizedJet, j, iteratedFDeriv_zero_apply]
    exact (normalizedPullback_zero A y b P).symm

end FirstProlongationProof
end PhilipponMultiplicity


open PhilipponMultiplicity

/-- Tangent inclusion fixes the full retained first differential ideal. -/
theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (htangent : A.tangentKernel H.carrier = ⊤)
    (atlas : TranslationAtlas A (0 : G.Point)) :
    retainedPolynomialOperatorIdeal atlas 1 (G.vanishingIdeal H.carrier) =
      G.vanishingIdeal H.carrier := by
  letI : CompleteSpace K := hK.completeSpace
  have hI : IsMultihomogeneousIdeal G.ambient (G.vanishingIdeal H.carrier) := by
    apply OperatorSupport.homogeneous_span
    exact fun _ h => h.1
  rw [retainedPolynomialOperatorIdeal_eq_differentialIdeal K hK G A 0 atlas 1
    (G.vanishingIdeal H.carrier) hI]
  exact le_antisymm (FirstProlongationProof.differentialIdeal_le_vanishingIdeal A H htangent)
    (FirstProlongationProof.vanishingIdeal_le_differentialIdeal A H)

end
end

