-- Prove2me | solution 1 for PhilipponMultiplicity.quadratic_contact_hilbert_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-10T18:31:27.293702+00:00
-- url     : https://prove2.me/submissions/b5488c64-5727-43a5-848c-f3d4efd6a237

import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_ErratumCorrections
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.RingTheory.Polynomial.Basic
import Theorems.Thm_PhilipponMultiplicity_analytic_subgroup_local_containment_of_tangent

section
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

end MultiProjectiveSpace

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

end WeierstrassEllipticZeta
end
end

section
-- Reused implementation: Solutions.PhilipponFiniteBasicCover

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity

theorem finite_polynomial_nonzero_cover {K σ X ι : Type*} [Field K] [Finite σ]
    (P : ι → MvPolynomial σ K) (v : X → σ → K)
    (hcover : ∀ x, ∃ i, MvPolynomial.eval (v x) (P i) ≠ 0) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, MvPolynomial.eval (v x) (P i) ≠ 0 := by
  classical
  obtain ⟨s,hs,hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := MvPolynomial σ K) (Set.range P)).mp
      (IsNoetherian.noetherian (Ideal.span (Set.range P)))
  choose ind hind using (fun q : s => hs q.property)
  let t : Finset ι := Finset.univ.image ind
  refine ⟨t,?_⟩
  intro x
  by_contra hx
  push Not at hx
  have hle : Ideal.span (Set.range P) ≤ RingHom.ker (MvPolynomial.eval (v x)) := by
    change Ideal.span (Set.range P) = Ideal.span (s : Set (MvPolynomial σ K)) at hspan
    rw [hspan]
    apply Ideal.span_le.mpr
    intro q hq
    change MvPolynomial.eval (v x) q = 0
    have hi : P (ind ⟨q,hq⟩) = q := hind ⟨q,hq⟩
    rw [← hi]
    exact hx (ind ⟨q,hq⟩) (Finset.mem_image.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,rfl⟩)
  obtain ⟨i,hi⟩ := hcover x
  exact hi (hle (Ideal.subset_span (Set.mem_range_self i)))

namespace MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem finite_open_subcover {X ι : Type*} (e : X → M.Point)
    (U : ι → Set M.Point) (hU : ∀ i, @IsOpen _ M.zariskiTopology (U i))
    (hcover : ∀ x, ∃ i, e x ∈ U i) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, e x ∈ U i := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  choose ind hind using hcover
  have hbasic (x : X) : ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
      M.eval P (e x) ≠ 0 ∧ {p : M.Point | M.eval P p ≠ 0} ⊆ U (ind x) := by
    obtain ⟨V,⟨P,D,hP,rfl⟩,hx,hV⟩ :=
      M.isTopologicalBasis_basic.exists_subset_of_mem_open (hind x) (hU (ind x))
    exact ⟨P,D,hP,hx,hV⟩
  choose P D hP hx hPU using hbasic
  obtain ⟨s,hs⟩ := finite_polynomial_nonzero_cover P (fun x => M.coordinate (e x))
    (fun x => ⟨x,hx x⟩)
  refine ⟨s.image ind,?_⟩
  intro x
  obtain ⟨y,hy,hyx⟩ := hs x
  exact ⟨ind y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,hPU y hyx⟩

end MultiProjectiveSpace
end PhilipponMultiplicity

end
end

section
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
-- Reused implementation: Solutions.PhilipponAnalyticUnitOrder

set_option autoImplicit false
open scoped Topology BigOperators ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity
variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

theorem iteratedFDeriv_mul_eq_zero_of_vanishing_jet
    {f u : E → K} {x : E} {n : ℕ}
    (hf : ContDiffAt K n f x) (hu : ContDiffAt K n u x)
    (hz : ∀ i ≤ n, iteratedFDeriv K i f x = 0) :
    iteratedFDeriv K n (fun y => u y * f y) x = 0 := by
  obtain ⟨s, hs, hopen, hxs⟩ := eventually_nhds_iff.mp
    ((hf.eventually (by simp)).and (hu.eventually (by simp)))
  have hfs : ContDiffOn K n f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have hus : ContDiffOn K n u s := fun y hy => (hs y hy).2.contDiffWithinAt
  have hbound := norm_iteratedFDerivWithin_mul_le hus hfs hopen.uniqueDiffOn hxs
    (le_refl (n : ℕ∞ω))
  simp only [iteratedFDerivWithin_of_isOpen _ hopen hxs] at hbound
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv K i u x‖ * ‖iteratedFDeriv K (n - i) f x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hz (n - i) (Nat.sub_le _ _)]
  rw [hsum] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

def jetOrder (f : E → K) (x : E) : WithTop ℕ :=
  sInf ((fun n : ℕ => (n : WithTop ℕ)) '' {n | iteratedFDeriv K n f x ≠ 0})

theorem natCast_le_jetOrder_iff {f : E → K} {x : E} {n : ℕ} :
    (n : WithTop ℕ) ≤ jetOrder f x ↔
      ∀ i < n, iteratedFDeriv K i f x = 0 := by
  constructor
  · intro h i hi
    by_contra hne
    have hle : jetOrder f x ≤ (i : WithTop ℕ) := sInf_le ⟨i, hne, rfl⟩
    have : n ≤ i := by exact_mod_cast h.trans hle
    omega
  · intro h
    apply le_sInf
    rintro _ ⟨i, hi, rfl⟩
    by_contra! hlt
    have hin : i < n := by exact_mod_cast hlt
    exact hi (h i hin)

theorem jetOrder_mul_unit [CompleteSpace K] {f u : E → K} {x : E}
    (hf : AnalyticAt K f x) (hu : AnalyticAt K u x) (hu0 : u x ≠ 0) :
    jetOrder (fun y => u y * f y) x = jetOrder f x := by
  apply WithTop.eq_of_forall_coe_le_iff
  intro n
  change ((n : WithTop ℕ) ≤ jetOrder (fun y => u y * f y) x) ↔
    (n : WithTop ℕ) ≤ jetOrder f x
  rw [natCast_le_jetOrder_iff, natCast_le_jetOrder_iff]
  have hunit : ∀ᶠ y in 𝓝 x, u y ≠ 0 := hu.continuousAt.eventually_ne hu0
  have hinv : (fun y => (u y)⁻¹ * (u y * f y)) =ᶠ[𝓝 x] f := by
    filter_upwards [hunit] with y hy
    simp [hy]
  constructor
  · intro h i hi
    have hz := iteratedFDeriv_mul_eq_zero_of_vanishing_jet
      (hu.mul hf).contDiffAt (hu.inv hu0).contDiffAt
      (fun j hj => h j (hj.trans_lt hi))
    change iteratedFDeriv K i (fun y => (u y)⁻¹ * (u y * f y)) x = 0 at hz
    rw [(hinv.iteratedFDeriv K i).eq_of_nhds] at hz
    exact hz
  · intro h i hi
    exact iteratedFDeriv_mul_eq_zero_of_vanishing_jet hf.contDiffAt hu.contDiffAt
      (fun j hj => h j (hj.trans_lt hi))

end PhilipponMultiplicity
end
end

section
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

section
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
-- Reused implementation: Solutions.PhilipponProjectiveTranslations

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

section
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

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
-- Reused implementation: Solutions.PhilipponProductRegularity

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

end PhilipponMultiplicity
end
end

section
-- Reused implementation: Solutions.PhilipponOperatorEvaluation

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem coordinate_coeff_analytic (chart : TranslationChart A g)
    (v : G.ambient.Variable) (e : G.ambient.Variable →₀ ℕ) :
    AnalyticAt K ((chart.coordinates v).coeff e) 0 := by
  by_cases he : e ∈ (chart.coordinates v).support
  · exact chart.coefficient_analytic v e he
  · have he0 : (chart.coordinates v).coeff e = 0 := by
      simpa only [mem_support_iff, not_not] using he
    rw [he0]
    exact analyticAt_const

theorem substituted_coeff_analytic (chart : TranslationChart A g)
    (P : G.CoordinateRing) (e : G.ambient.Variable →₀ ℕ) :
    AnalyticAt K ((substitutedPolynomial chart P).coeff e) 0 := by
  classical
  induction P using MvPolynomial.induction_on generalizing e with
  | C a =>
    simp only [substitutedPolynomial, eval₂Hom_C, RingHom.comp_apply, coeff_C]
    split_ifs <;> exact analyticAt_const
  | add P Q hP hQ =>
    simp only [substitutedPolynomial, map_add, coeff_add]
    exact (hP e).add (hQ e)
  | mul_X P v hP =>
    simp only [substitutedPolynomial, map_mul, eval₂Hom_X']
    change AnalyticAt K ((substitutedPolynomial chart P * chart.coordinates v).coeff e) 0
    rw [coeff_mul]
    exact Finset.analyticAt_sum _ fun p _ => (hP p.1).mul (coordinate_coeff_analytic chart v p.2)

theorem evaluated_coefficients_analytic
    (F : MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A))
    (hF : ∀ e, AnalyticAt K (F.coeff e) 0) (x : G.Point) :
    AnalyticAt K (evaluateCoefficientPolynomial A F x) 0 := by
  classical
  change AnalyticAt K (fun z => eval₂ (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z)
    (G.ambient.coordinate (G.embedding x)) F) 0
  simp only [eval₂_eq, Pi.evalRingHom_apply]
  exact Finset.analyticAt_fun_sum _ fun e _ => (hF e).mul analyticAt_const

theorem evaluate_substituted (chart : TranslationChart A g) (P : G.CoordinateRing)
    (x : G.Point) (z : A.ParameterSpace) :
    evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x z =
      MvPolynomial.eval (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) P := by
  unfold evaluateCoefficientPolynomial substitutedPolynomial
  rw [MvPolynomial.map_eval₂Hom]
  change eval₂Hom _ _ P = eval₂Hom (RingHom.id K) _ P
  congr 2
  ext a
  simp

theorem polynomialOperator_eval (chart : TranslationChart A g) (P : G.CoordinateRing)
    (x : G.Point) (n : ℕ) (directions : Fin n → Fin A.parameterDimension) :
    G.ambient.eval (polynomialOperator chart n directions P) (G.embedding x) =
      iteratedFDeriv K n
        (fun z => MvPolynomial.eval
          (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) P) 0
        (fun i => Pi.single (directions i) 1) := by
  classical
  let F := substitutedPolynomial chart P
  let v := G.ambient.coordinate (G.embedding x)
  have heval : (fun z => MvPolynomial.eval
      (fun w => evaluateCoefficientPolynomial A (chart.coordinates w) x z) P) =
      fun z => ∑ e ∈ F.support, (∏ i ∈ e.support, v i ^ e i) * F.coeff e z := by
    funext z
    rw [← evaluate_substituted]
    change eval₂ _ v F = _
    simp only [eval₂_eq, Pi.evalRingHom_apply, mul_comm]
  rw [heval, iteratedFDeriv_fun_sum_apply
    (f := fun e z => (∏ i ∈ e.support, v i ^ e i) * F.coeff e z)
    (fun e _ => (analyticAt_const.mul (substituted_coeff_analytic chart P e)).contDiffAt)]
  simp only [ContinuousMultilinearMap.sum_apply]
  unfold polynomialOperator MultiProjectiveSpace.eval
  change MvPolynomial.eval v ((AddMonoidAlgebra.coeff F).sum _) = _
  rw [Finsupp.sum]
  simp only [map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro e _
  rw [show (fun z => (∏ i ∈ e.support, v i ^ e i) * F.coeff e z) =
    (fun z => (∏ i ∈ e.support, v i ^ e i) • F.coeff e z) from rfl,
    iteratedFDeriv_const_smul_apply' (substituted_coeff_analytic chart P e).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, Finsupp.prod]
  exact mul_comm _ _

end PhilipponMultiplicity.OperatorSupport
end
end

section
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

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
end PhilipponMultiplicity
end
end

section
-- Reused implementation: Solutions.PhilipponOperatorAlgebra

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperator_coeff (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P : G.CoordinateRing)
    (e : G.ambient.Variable →₀ ℕ) :
    (polynomialOperator chart n directions P).coeff e =
      iteratedFDeriv K n ((substitutedPolynomial chart P).coeff e) 0
        (fun i => Pi.single (directions i) 1) := by
  classical
  unfold polynomialOperator
  rw [Finsupp.sum]
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with he
  · rfl
  · have hz : (substitutedPolynomial chart P).coeff e = 0 := by
      exact Finsupp.notMem_support_iff.mp he
    simp [hz]

theorem polynomialOperator_add (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P Q : G.CoordinateRing) :
    polynomialOperator chart n directions (P + Q) =
      polynomialOperator chart n directions P + polynomialOperator chart n directions Q := by
  ext e
  simp only [coeff_add, polynomialOperator_coeff]
  have heq : (substitutedPolynomial chart (P + Q)).coeff e =
      fun z => (substitutedPolynomial chart P).coeff e z +
        (substitutedPolynomial chart Q).coeff e z := by
    simp [substitutedPolynomial]
    rfl
  rw [heq, fun_iteratedFDeriv_add_apply (substituted_coeff_analytic chart P e).contDiffAt
    (substituted_coeff_analytic chart Q e).contDiffAt]
  rfl

theorem polynomialOperator_C_mul (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (a : K) (P : G.CoordinateRing) :
    polynomialOperator chart n directions (C a * P) =
      C a * polynomialOperator chart n directions P := by
  ext e
  simp only [coeff_C_mul, polynomialOperator_coeff]
  have heq : (substitutedPolynomial chart (C a * P)).coeff e =
      fun z => a • (substitutedPolynomial chart P).coeff e z := by
    simp [substitutedPolynomial, coeff_C_mul, smul_eq_mul]
    rfl
  rw [heq, iteratedFDeriv_const_smul_apply' (substituted_coeff_analytic chart P e).contDiffAt]
  rfl

theorem substitutedPolynomial_homogeneous (chart : TranslationChart A g)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    (substitutedPolynomial chart P).IsWeightedHomogeneous
      (Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension)
      (fun i => chart.degree i * D i) := by
  classical
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  let c : G.ambient.Variable → G.FactorIndex → ℕ := fun v i =>
    chart.degree i * w v i
  have hc (v : G.ambient.Variable) : (chart.coordinates v).IsWeightedHomogeneous w (c v) := by
    intro e he
    funext i
    rw [G.ambient.blockWeight_apply]
    obtain ⟨h₁, h₂⟩ := chart.coordinate_homogeneous v e (mem_support_iff.mpr he)
    by_cases hi : i = v.1
    · subst i
      simpa [c, w, Hilbert.blockWeight] using h₁
    · simpa [c, w, Hilbert.blockWeight, Ne.symm hi] using h₂ i hi
  have hwP : P.IsWeightedHomogeneous w D := (G.ambient.degreePiece_iff P D).mpr hP
  apply IsWeightedHomogeneous.induction_on (motive := fun Q _ =>
    (substitutedPolynomial chart Q).IsWeightedHomogeneous w
      (fun i => chart.degree i * D i)) ?_ ?_ ?_ hwP
  · simpa [substitutedPolynomial] using
      isWeightedHomogeneous_zero (AnalyticCoefficientRing A) w (fun i => chart.degree i * D i)
  · intro P Q hP hQ ihP ihQ
    simpa only [substitutedPolynomial, map_add] using ihP.add ihQ
  · intro e a he
    have hweight : (∑ v ∈ e.support, e v • c v) = fun i => chart.degree i * D i := by
      funext i
      have hwi := congrFun he i
      rw [Finsupp.weight_eq_sum] at hwi
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hwi ⊢
      calc
        ∑ v ∈ e.support, e v * c v i =
            chart.degree i * ∑ v ∈ e.support, e v * w v i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          dsimp [c]
          ring
        _ = chart.degree i * D i := by
          congr 1
          rw [← hwi]
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          rw [Finsupp.notMem_support_iff.mp hv, zero_mul]
    unfold substitutedPolynomial
    rw [eval₂Hom_monomial, Finsupp.prod]
    change IsWeightedHomogeneous w (C _ * _) _
    have hprod := (IsWeightedHomogeneous.prod e.support
      (fun v => chart.coordinates v ^ e v) (fun v => e v • c v)
        (fun v _ => (hc v).pow (e v))).C_mul ((Pi.constRingHom A.ParameterSpace K) a)
    exact hweight ▸ hprod

theorem polynomialOperator_homogeneous (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (polynomialOperator chart n directions P)
      (fun i => chart.degree i * D i) := by
  intro e he i
  have hc : (substitutedPolynomial chart P).coeff e ≠ 0 := by
    intro hz
    have := mem_support_iff.mp he
    rw [polynomialOperator_coeff, hz] at this
    simpa using this
  have hw := substitutedPolynomial_homogeneous chart P D hP hc
  exact (G.ambient.blockWeight_apply e i).symm.trans (congrFun hw i)

end PhilipponMultiplicity.OperatorSupport
end
end

section
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
-- Reused implementation: Solutions.PhilipponDifferentialVanishing

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem exists_chartDomain (x : G.Point) : ∃ b : CoordinateChart G, x ∈ chartDomain G b := by
  have h (i : G.FactorIndex) : ∃ j, (G.embedding x i).rep j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using (G.embedding x i).rep_nonzero
  choose b hb using h
  exact ⟨b, hb⟩

end PhilipponMultiplicity.OperatorSupport
end
end

section
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
-- Reused implementation: Solutions.PhilipponLocalPolynomialSections

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

def pivotPolynomial (b : CoordinateChart G) (D : G.FactorIndex → ℕ) : G.CoordinateRing :=
  ∏ i, X ⟨i, b i⟩ ^ D i

theorem pivotPolynomial_homogeneous (b : CoordinateChart G) (D : G.FactorIndex → ℕ) :
    G.ambient.IsHomogeneous (pivotPolynomial b D) D :=
  Hilbert.variable_product_homogeneous G.ambient b D

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponLocalRational

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem exists_basic_subset (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U)
    (x : G.Point) (hx : x ∈ U) :
    ∃ s : G.CoordinateRing, ∃ E : G.FactorIndex → ℕ, G.ambient.IsHomogeneous s E ∧
      G.ambient.eval s (G.embedding x) ≠ 0 ∧
      {y : G.Point | G.ambient.eval s (G.embedding y) ≠ 0} ⊆ U := by
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨W, ⟨s,E,hs,rfl⟩, hxW, hWV⟩ :=
    G.ambient.isTopologicalBasis_basic.exists_subset_of_mem_open hx hV
  exact ⟨s,E,hs,hxW,fun y hy => hWV hy⟩

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponTranslationSeparation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set MvPolynomial TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem noetherian_induced {X : Type*} (e : X → M.Point) :
    @NoetherianSpace X (TopologicalSpace.induced e M.zariskiTopology) := by
  letI : TopologicalSpace M.Point := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  apply noetherianSpace_iff_isCompact.mpr
  intro S
  apply isCompact_iff_finite_subcover.mpr
  intro ι U hU hcover
  choose W hW heq using fun i => isOpen_induced_iff.mp (hU i)
  obtain ⟨t,ht⟩ := M.finite_open_subcover (fun x : S => e x.val) W hW (by
    intro x
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover x.property)
    exact ⟨i,by change x.val ∈ e ⁻¹' W i; rwa [heq i]⟩)
  refine ⟨t,?_⟩
  intro x hx
  obtain ⟨i,hi,hxi⟩ := ht ⟨x,hx⟩
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,by rw [← heq i]; exact hxi⟩⟩

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.TranslationSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

end PhilipponMultiplicity.TranslationSupport
end
end

section
-- Reused implementation: Solutions.PhilipponConnectedGroupIrreducible

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity

theorem irreducible_of_transitive_homeomorphisms {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [ConnectedSpace X]
    (htrans : ∀ x y : X, ∃ e : X ≃ₜ X, e x = y) : IrreducibleSpace X := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨U,hU,⟨p,hp⟩,hUC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hCopen : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨e,he⟩ := htrans p y
    have hopen : IsOpen (e '' U) := e.isOpenMap _ hU
    have hclosed : IsClosed (e '' C) := e.isClosedMap _
      (isClosed_of_mem_irreducibleComponents C hC)
    have hydense : C ⊆ closure (C ∩ e '' U) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hopen
        ⟨y,hy,p,hp,he⟩
    have hCeC : C ⊆ e '' C := hydense.trans (closure_minimal
      (fun z hz => Set.image_mono hUC hz.2) hclosed)
    have heCC : e '' C ⊆ C := hC.2 (hC.1.image e e.continuous.continuousOn) hCeC
    exact Filter.mem_of_superset (hopen.mem_nhds ⟨p,hp,he⟩)
      ((Set.image_mono hUC).trans heCC)
  have hfull : C = univ := (show IsClopen C from
    ⟨isClosed_of_mem_irreducibleComponents C hC,hCopen⟩).eq_univ hC.1.nonempty
  exact { isPreirreducible_univ := by simpa only [hfull] using hC.1.2
          toNonempty := inferInstance }

variable {K : Type*} [Field K] {G : EmbeddedGroupProduct K}

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponGroupPairIrreducible

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 60000
open Set TopologicalSpace
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

theorem preirreducible_of_continuous_slices
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PreirreducibleSpace X] [PreirreducibleSpace Y]
    (t : TopologicalSpace (X × Y))
    (hl : ∀ y, @Continuous X (X × Y) _ t (fun x => (x,y)))
    (hr : ∀ x, @Continuous Y (X × Y) _ t (fun y => (x,y))) :
    @IsPreirreducible (X × Y) t univ := by
  let : TopologicalSpace (X × Y) := t
  intro U V hU hV hUne hVne
  let A : Set X := {x | ∃ y, (x,y) ∈ U}
  let B : Set X := {x | ∃ y, (x,y) ∈ V}
  have hA : IsOpen A := by
    have he : A = ⋃ y, (fun x : X => (x,y)) ⁻¹' U := by ext x; simp [A]
    rw [he]
    exact isOpen_iUnion (fun y => hU.preimage (hl y))
  have hB : IsOpen B := by
    have he : B = ⋃ y, (fun x : X => (x,y)) ⁻¹' V := by ext x; simp [B]
    rw [he]
    exact isOpen_iUnion (fun y => hV.preimage (hl y))
  obtain ⟨a, -, ha⟩ := hUne
  obtain ⟨b, -, hb⟩ := hVne
  obtain ⟨x, -, ⟨y, hy⟩, ⟨z, hz⟩⟩ :=
    PreirreducibleSpace.isPreirreducible_univ A B hA hB
      ⟨a.1, mem_univ _, a.2, ha⟩ ⟨b.1, mem_univ _, b.2, hb⟩
  obtain ⟨w, -, hwU, hwV⟩ :=
    PreirreducibleSpace.isPreirreducible_univ _ _
      (hU.preimage (hr x)) (hV.preimage (hr x))
      ⟨y, mem_univ _, hy⟩ ⟨z, mem_univ _, hz⟩
  exact ⟨(x,w), mem_univ _, hwU, hwV⟩

universe u
variable {K : Type u} [Field K]

abbrev EmbeddedCommutativeGroup.pointZariskiTopology (E : EmbeddedCommutativeGroup K) :
    TopologicalSpace E.Point :=
  TopologicalSpace.induced (fun x : E.Point => fun _ => x.val)
    (projectiveSpace K E.ambientDimension).zariskiTopology

theorem EmbeddedCommutativeGroup.irreducible_of_connected
    (E : EmbeddedCommutativeGroup K)
    (hE : @ConnectedSpace E.Point E.pointZariskiTopology) :
    @IrreducibleSpace E.Point E.pointZariskiTopology := by
  let := E.pointZariskiTopology
  let := (projectiveSpace K E.ambientDimension).zariskiTopology
  let : ConnectedSpace E.Point := hE
  let : NoetherianSpace E.Point :=
    (projectiveSpace K E.ambientDimension).noetherian_induced (fun x : E.Point => fun _ => x.val)
  apply irreducible_of_transitive_homeomorphisms
  intro x y
  have hc (a : E.Point) : Continuous (fun z : E.Point => z+a) :=
    continuous_induced_rng.mpr (E.translation_regular a).continuous
  let e : E.Point ≃ₜ E.Point := {
    toEquiv := {
      toFun := fun z => z+(y-x)
      invFun := fun z => z-(y-x)
      left_inv := fun z => add_sub_cancel_right z (y-x)
      right_inv := fun z => sub_add_cancel z (y-x) }
    continuous_toFun := hc (y-x)
    continuous_invFun := by simpa only [sub_eq_add_neg] using hc (-(y-x)) }
  refine ⟨e, ?_⟩
  change x+(y-x)=y
  abel

theorem projectiveSquare_swap_continuous (n : ℕ) :
    @Continuous _ _ (projectiveSquare K n).zariskiTopology
      (projectiveSquare K n).zariskiTopology
      (fun p : (projectiveSquare K n).Point => fun b : Fin 2 => p b.rev) := by
  let := (projectiveSquare K n).zariskiTopology
  have hr : (projectiveSquare K n).IsRegularAlong (projectiveSquare K n) id
      (fun p => fun b : Fin 2 => p b.rev) := by
    intro p b
    refine ⟨univ, isOpen_univ, mem_univ _,
      (fun i => if i=b.rev then 1 else 0),
      (fun j => MvPolynomial.X ⟨b.rev,j⟩),
      (fun j => (projectiveSquare K n).isHomogeneous_X ⟨b.rev,j⟩), ?_⟩
    intro q _
    simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_X,
      MultiProjectiveSpace.coordinate, id_eq]
    exact ⟨Projectivization.rep_nonzero (q b.rev), Projectivization.mk_rep (q b.rev)⟩
  have hc := hr.continuous
  rw [induced_id] at hc
  exact hc

theorem EmbeddedCommutativeGroup.preirreducible_pairs
    (F : EmbeddedCommutativeGroup K)
    (hF : @ConnectedSpace F.Point F.pointZariskiTopology) :
    @IsPreirreducible (F.Point × F.Point)
      (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
        (projectiveSquare K F.ambientDimension).zariskiTopology) univ := by
  let := F.pointZariskiTopology
  let := (projectiveSpace K F.ambientDimension).zariskiTopology
  let := (projectiveSquare K F.ambientDimension).zariskiTopology
  let : IrreducibleSpace F.Point := F.irreducible_of_connected hF
  have hl (y : F.Point) : Continuous (fun x : F.Point => F.additionPair x y) :=
    (projectiveLeftSlice_continuous y.val).comp
      (show Continuous (show F.Point → (projectiveSpace K F.ambientDimension).Point
        from fun x => fun _ => x.val) from continuous_induced_dom)
  have hr (x : F.Point) : Continuous (fun y : F.Point => F.additionPair x y) := by
    have he : (fun y : F.Point => F.additionPair x y) =
        (fun p : (projectiveSquare K F.ambientDimension).Point => fun b : Fin 2 => p b.rev) ∘
          (fun y : F.Point => F.additionPair y x) := by
      funext y b
      fin_cases b <;> rfl
    rw [he]
    exact (projectiveSquare_swap_continuous F.ambientDimension).comp (hl x)
  apply preirreducible_of_continuous_slices
  · intro y
    exact continuous_induced_rng.mpr (hl y)
  · intro x
    exact continuous_induced_rng.mpr (hr x)

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponLocalAdditionLaws

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000
noncomputable section
open Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

namespace MultiProjectiveSpace

theorem isOpen_tuple_nonzero {X : Type u} (M : MultiProjectiveSpace K)
    (e : X → M.Point) {n : ℕ} (D : M.FactorIndex → ℕ)
    (P : Fin (n+1) → M.CoordinateRing) (hP : ∀ j, M.IsHomogeneous (P j) D) :
    @IsOpen X (TopologicalSpace.induced e M.zariskiTopology)
      {x | (fun j => M.eval (P j) (e x)) ≠ 0} := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  have ho : IsOpen {y : X | M.eval (P j) (e y) ≠ 0} :=
    (M.isOpen_basic _ _ (hP j)).preimage continuous_induced_dom
  refine Filter.mem_of_superset (ho.mem_nhds hj) ?_
  intro y hy hz
  exact hy (congrFun hz j)

theorem IsRegularAlong.tuple_eq_of_nonempty_open
    {X : Type u} (M : MultiProjectiveSpace K) {n : ℕ}
    (e : X → M.Point) (f : X → (projectiveSpace K n).Point)
    (hf : M.IsRegularAlong (projectiveSpace K n) e f)
    (hirr : @IsPreirreducible X (TopologicalSpace.induced e M.zariskiTopology) univ)
    (U : Set X) (hU : @IsOpen X (TopologicalSpace.induced e M.zariskiTopology) U)
    (hne : U.Nonempty) (D : M.FactorIndex → ℕ)
    (P : Fin (n+1) → M.CoordinateRing) (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hlocal : ∀ x ∈ U, ∃ h : (fun j => M.eval (P j) (e x)) ≠ 0,
      Projectivization.mk K (fun j => M.eval (P j) (e x)) h = f x (0 : Fin 1)) :
    ∀ x (h : (fun j => M.eval (P j) (e x)) ≠ 0),
      Projectivization.mk K (fun j => M.eval (P j) (e x)) h = f x (0 : Fin 1) := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  let S : Set X := {x | (fun j => M.eval (P j) (e x)) ≠ 0}
  have hS : IsOpen S := M.isOpen_tuple_nonzero e D P hP
  let : PreirreducibleSpace S := Subtype.preirreducibleSpace
    (hirr.open_subset hS (subset_univ _))
  let q : S → (projectiveSpace K n).Point := fun x _ =>
    Projectivization.mk K (fun j => M.eval (P j) (e x.val)) x.property
  have hq : M.IsRegularAlong (projectiveSpace K n) (e ∘ Subtype.val) q := by
    intro x b
    exact ⟨univ, isOpen_univ, mem_univ _, D, P, hP,
      fun y _ => ⟨y.property, rfl⟩⟩
  have hopen : IsOpen (Subtype.val ⁻¹' U : Set S) := hU.preimage continuous_subtype_val
  have hnonempty : (Subtype.val ⁻¹' U : Set S).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, (hlocal x hx).choose⟩, hx⟩
  have hdense : @Dense S
      (TopologicalSpace.induced (e ∘ Subtype.val) M.zariskiTopology)
      (Subtype.val ⁻¹' U) := by
    rw [← induced_compose]
    exact hopen.dense hnonempty
  have heq := hq.eq_of_dense M (projectiveSpace K n) (hf.comp_domain Subtype.val)
    (Subtype.val ⁻¹' U) hdense (by
      intro x hx
      funext b
      have hb : b = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) b 0
      subst b
      exact (hlocal x.val hx).choose_spec)
  intro x hx
  exact congrFun (congrFun heq ⟨x, hx⟩) (0 : Fin 1)

end MultiProjectiveSpace

def EmbeddedCommutativeGroup.additionLawOfLocal
    (F : EmbeddedCommutativeGroup K)
    (hirr : @IsPreirreducible (F.Point × F.Point)
      (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
        (projectiveSquare K F.ambientDimension).zariskiTopology) univ)
    (U : Set (F.Point × F.Point))
    (hU : @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
      (projectiveSquare K F.ambientDimension).zariskiTopology) U)
    (hne : U.Nonempty) (D : (projectiveSquare K F.ambientDimension).FactorIndex → ℕ)
    (P : Fin (F.ambientDimension+1) → (projectiveSquare K F.ambientDimension).CoordinateRing)
    (hP : ∀ j, (projectiveSquare K F.ambientDimension).IsHomogeneous (P j) D)
    (hlocal : ∀ xy ∈ U, ∃ h :
      (fun j => (projectiveSquare K F.ambientDimension).eval (P j)
        (F.additionPair xy.1 xy.2)) ≠ 0,
      Projectivization.mk K (fun j => (projectiveSquare K F.ambientDimension).eval
        (P j) (F.additionPair xy.1 xy.2)) h = (xy.1+xy.2).val) : F.AdditionLaw where
  degree := D
  coordinates := P
  homogeneous := hP
  represents := by
    intro x y h
    exact MultiProjectiveSpace.IsRegularAlong.tuple_eq_of_nonempty_open
      (X := F.Point × F.Point) (n := F.ambientDimension)
      (projectiveSquare K F.ambientDimension)
      (fun xy => F.additionPair xy.1 xy.2) (fun xy _ => (xy.1+xy.2).val)
      F.addition_regular hirr U hU hne D P hP hlocal (x,y) h

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponAnalyticPolynomialSubstitution

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AtlasSupport

theorem substitution_coeff_analytic
    {K Z σ τ : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup Z] [NormedSpace K Z]
    (Q : σ → MvPolynomial τ (Z → K)) (z : Z)
    (hQ : ∀ v e, AnalyticAt K ((Q v).coeff e) z)
    (P : MvPolynomial σ K) (e : τ →₀ ℕ) :
    AnalyticAt K ((eval₂Hom (C.comp (Pi.constRingHom Z K)) Q P).coeff e) z := by
  classical
  induction P using MvPolynomial.induction_on generalizing e with
  | C a =>
    simp only [eval₂Hom_C,RingHom.comp_apply,coeff_C]
    split_ifs <;> exact analyticAt_const
  | add P R hP hR =>
    simp only [map_add,coeff_add]
    exact (hP e).add (hR e)
  | mul_X P v hP =>
    simp only [map_mul,eval₂Hom_X']
    rw [coeff_mul]
    exact Finset.analyticAt_sum _ fun p _ => (hP p.1).mul (hQ v p.2)

theorem homogeneous_substitution
    {K R τ L : Type*} [Field K] [CommSemiring R] [AddCommMonoid L]
    (M : MultiProjectiveSpace K) (φ : K →+* R) (w : τ → L)
    (Q : M.Variable → MvPolynomial τ R) (E : M.FactorIndex → L)
    (hQ : ∀ v, (Q v).IsWeightedHomogeneous w (E v.1))
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    (eval₂Hom (C.comp φ) Q P).IsWeightedHomogeneous w (∑ i, D i • E i) := by
  classical
  change (eval₂ (C.comp φ) Q P).IsWeightedHomogeneous w _
  rw [eval₂_eq']
  apply IsWeightedHomogeneous.sum
  intro d hd
  have hh := (IsWeightedHomogeneous.prod Finset.univ (fun v => Q v ^ d v)
    (fun v => d v • E v.1) (fun v _ => (hQ v).pow (d v))).C_mul (φ (coeff d P))
  have he : (∑ v : M.Variable, d v • E v.1) = ∑ i, D i • E i := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ j, d ⟨i,j⟩ • E i) = D i • E i
    rw [Finset.sum_nsmul_assoc,hP d hd i]
  simpa only [he,RingHom.comp_apply] using hh

end PhilipponMultiplicity.AtlasSupport
end
end

section
-- Reused implementation: Solutions.PhilipponBoundedAdditionCharts

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

namespace EmbeddedCommutativeGroup

def additionSource (E : EmbeddedCommutativeGroup K) (xy : E.Point × E.Point) :
    (projectiveSquare K E.ambientDimension).Point :=
  fun i => if i.val = 0 then xy.1.val else xy.2.val

end EmbeddedCommutativeGroup
end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponAdditionSubstitution

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AtlasSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (g : G.Point)

abbrev factorSquare (i : G.FactorIndex) := projectiveSquare K (G.factor i).ambientDimension

def firstBlock (i : G.FactorIndex) : (factorSquare i).FactorIndex :=
  ⟨0,by change 0 < 2; decide⟩

def pairSubstitutionCoordinate (i : G.FactorIndex) (v : (factorSquare i).Variable) :
    MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A) :=
  if v.1.val = 0 then X ⟨i,v.2⟩ else C (fun z => A.lift g z ⟨i,v.2⟩)

def pairSubstitution (i : G.FactorIndex) : (factorSquare i).CoordinateRing →+*
    MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A) :=
  eval₂Hom (C.comp (Pi.constRingHom A.ParameterSpace K)) (pairSubstitutionCoordinate A g i)

def pairLift (i : G.FactorIndex) (x : G.Point) (z : A.ParameterSpace)
    (v : (factorSquare i).Variable) : K :=
  if v.1.val = 0 then (G.embedding x i).rep v.2 else A.lift g z ⟨i,v.2⟩

theorem evaluate_pairSubstitution (i : G.FactorIndex) (P : (factorSquare i).CoordinateRing)
    (x : G.Point) (z : A.ParameterSpace) :
    evaluateCoefficientPolynomial A (pairSubstitution A g i P) x z =
      MvPolynomial.eval (pairLift A g i x z) P := by
  change eval₂Hom _ _ (eval₂Hom _ _ P) = eval₂Hom (RingHom.id K) _ P
  rw [map_eval₂Hom]
  congr 2
  · ext a
    simp
  · funext v
    by_cases hv : v.1.val = 0
    · simp [pairSubstitutionCoordinate,pairLift,hv,MultiProjectiveSpace.coordinate]
    · simp [pairSubstitutionCoordinate,pairLift,hv]

theorem pairSubstitution_coeff_analytic (i : G.FactorIndex)
    (P : (factorSquare i).CoordinateRing) (e : G.ambient.Variable →₀ ℕ) :
    AnalyticAt K ((pairSubstitution A g i P).coeff e) 0 := by
  apply substitution_coeff_analytic
  intro v d
  by_cases hv : v.1.val = 0
  · simp only [pairSubstitutionCoordinate,if_pos hv,coeff_X]
    split_ifs <;> exact analyticAt_const
  · simp only [pairSubstitutionCoordinate,if_neg hv,coeff_C]
    split_ifs
    · exact A.lift_analytic g _
    · exact analyticAt_const

theorem pairSubstitution_homogeneous (i : G.FactorIndex)
    (P : (factorSquare i).CoordinateRing) (D : (factorSquare i).FactorIndex → ℕ)
    (hP : (factorSquare i).IsHomogeneous P D) :
    (pairSubstitution A g i P).IsWeightedHomogeneous
      (Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension)
      (Pi.single i (D (firstBlock i))) := by
  classical
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  let E : (factorSquare i).FactorIndex → G.FactorIndex → ℕ :=
    fun b => if b.val = 0 then Pi.single i 1 else 0
  have hQ (v : (factorSquare i).Variable) :
      (pairSubstitutionCoordinate A g i v).IsWeightedHomogeneous w (E v.1) := by
    by_cases hv : v.1.val = 0
    · simp only [pairSubstitutionCoordinate,E,if_pos hv]
      exact isWeightedHomogeneous_X (AnalyticCoefficientRing A) w ⟨i,v.2⟩
    · simp only [pairSubstitutionCoordinate,E,if_neg hv]
      exact isWeightedHomogeneous_C w _
  have hh := homogeneous_substitution (factorSquare i) (Pi.constRingHom A.ParameterSpace K)
    w (pairSubstitutionCoordinate A g i) E hQ P D hP
  have he : (∑ b, D b • E b) = Pi.single i (D (firstBlock i)) := by
    funext k
    change (∑ b : Fin 2, D b * E b k) = _
    rw [Fin.sum_univ_two]
    simp [E,firstBlock,factorSquare,projectiveSquare,Pi.single_apply]
  simpa only [he,w,pairSubstitution] using hh

def specializationAtZero (i : G.FactorIndex) (P : (factorSquare i).CoordinateRing) :
    G.CoordinateRing :=
  MvPolynomial.map (Pi.evalRingHom (fun _ : A.ParameterSpace => K) 0) (pairSubstitution A g i P)

theorem specializationAtZero_eval (i : G.FactorIndex) (P : (factorSquare i).CoordinateRing)
    (x : G.Point) :
    G.ambient.eval (specializationAtZero A g i P) (G.embedding x) =
      MvPolynomial.eval (pairLift A g i x 0) P := by
  rw [← evaluate_pairSubstitution A g i P x 0]
  exact (eval₂_eq_eval_map _ _ _).symm

theorem specializationAtZero_homogeneous (i : G.FactorIndex)
    (P : (factorSquare i).CoordinateRing) (D : (factorSquare i).FactorIndex → ℕ)
    (hP : (factorSquare i).IsHomogeneous P D) :
    G.ambient.IsHomogeneous (specializationAtZero A g i P) (Pi.single i (D (firstBlock i))) := by
  classical
  intro e he k
  have he' : (pairSubstitution A g i P).coeff e ≠ 0 := by
    intro hz
    have hn := mem_support_iff.mp he
    simp only [specializationAtZero,coeff_map,hz,map_zero,ne_eq,not_true_eq_false] at hn
  exact (G.ambient.blockWeight_apply e k).symm.trans
    (congrFun (pairSubstitution_homogeneous A g i P D hP he') k)

end PhilipponMultiplicity.AtlasSupport
end
end

section
-- Reused implementation: Solutions.PhilipponAdditionChartGerms

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AtlasSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (g : G.Point)

theorem pairLift_evaluation_analytic (i : G.FactorIndex)
    (P : (factorSquare i).CoordinateRing) (x : G.Point) :
    AnalyticAt K (fun z => MvPolynomial.eval (pairLift A g i x z) P) 0 := by
  apply AnalyticAt.aeval_mvPolynomial
  intro v
  by_cases hv : v.1.val = 0
  · simp only [pairLift,if_pos hv]
    exact analyticAt_const
  · simpa only [pairLift,if_neg hv] using A.lift_analytic g ⟨i,v.2⟩

theorem liftAtZero_represents (i : G.FactorIndex) :
    ∃ h : (fun j => A.lift g 0 ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => A.lift g 0 ⟨i,j⟩) h = G.embedding g i := by
  obtain ⟨hz,hi⟩ := (A.lift_represents g).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  rw [hz',A.map_zero,add_zero] at hi
  exact hi i

theorem pairLift_represents (i : G.FactorIndex) (x : G.Point) (z : A.ParameterSpace)
    (y : G.Point)
    (hy : ∃ h : (fun j => A.lift g z ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => A.lift g z ⟨i,j⟩) h = G.embedding y i) :
    ∀ b : (factorSquare i).FactorIndex,
      ∃ h : (fun j => pairLift A g i x z ⟨b,j⟩) ≠ 0,
        Projectivization.mk K (fun j => pairLift A g i x z ⟨b,j⟩) h =
          (G.factor i).additionSource (x i,y i) b := by
  intro b
  by_cases hb : b.val = 0
  · simp only [pairLift,EmbeddedCommutativeGroup.additionSource,if_pos hb]
    exact ⟨(G.embedding x i).rep_nonzero,(G.embedding x i).mk_rep⟩
  · simp only [pairLift,EmbeddedCommutativeGroup.additionSource,if_neg hb]
    exact hy

end PhilipponMultiplicity.AtlasSupport
end
end

section
-- Reused implementation: Solutions.PhilipponAdditionLawAtlases

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.EmbeddedCommutativeGroup
universe u
variable {K : Type u} [Field K] {E : EmbeddedCommutativeGroup K}

theorem AdditionLaw.represents_lift (law : E.AdditionLaw) (x y : E.Point)
    (v : (projectiveSquare K E.ambientDimension).Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = E.additionPair x y i)
    (hn : (fun j => MvPolynomial.eval v (law.coordinates j)) ≠ 0) :
    Projectivization.mk K (fun j => MvPolynomial.eval v (law.coordinates j)) hn =
      (x+y).val := by
  let M := projectiveSquare K E.ambientDimension
  have hn' : (fun j => M.eval (law.coordinates j) (E.additionPair x y)) ≠ 0 := by
    intro hz
    apply hn
    funext j
    exact (M.eval_eq_zero_iff_of_lift _ v hv _ law.degree (law.homogeneous j)).mpr
      (congrFun hz j)
  obtain ⟨h,heq⟩ := M.homogeneous_tuple_lift _ v hv law.coordinates law.degree law.homogeneous hn'
  exact heq.trans (law.represents x y hn')

theorem AdditionLaw.compatible_lifts (law : E.AdditionLaw) (x y : E.Point)
    (v : (projectiveSquare K E.ambientDimension).Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = E.additionPair x y i)
    (w : Fin (E.ambientDimension + 1) → K) (hw : w ≠ 0)
    (hwrep : Projectivization.mk K w hw = (x+y).val) (j k : Fin (E.ambientDimension + 1)) :
    MvPolynomial.eval v (law.coordinates j) * w k =
      MvPolynomial.eval v (law.coordinates k) * w j := by
  by_cases hn : (fun j => MvPolynomial.eval v (law.coordinates j)) = 0
  · rw [congrFun hn j,congrFun hn k,Pi.zero_apply,Pi.zero_apply,zero_mul,zero_mul]
  · exact (MultiProjectiveSpace.projectivization_mk_eq_iff_cross _ _ hn hw).mp
      ((law.represents_lift x y v hv hn).trans hwrep.symm) j k

end PhilipponMultiplicity.EmbeddedCommutativeGroup

namespace PhilipponMultiplicity.AtlasSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (g : G.Point)

def lawDomain (i : G.FactorIndex) (law : (G.factor i).AdditionLaw) : Set G.Point :=
  ⋃ j, {x | G.ambient.eval (specializationAtZero A g i (law.coordinates j))
    (G.embedding x) ≠ 0}

theorem lawDomain_isOpen (i : G.FactorIndex) (law : (G.factor i).AdditionLaw) :
    @IsOpen _ G.zariskiTopology (lawDomain A g i law) := by
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  letI : TopologicalSpace G.Point := G.zariskiTopology
  apply isOpen_iUnion
  intro j
  exact (G.ambient.isOpen_basic _ _
    (specializationAtZero_homogeneous A g i (law.coordinates j) law.degree
      (law.homogeneous j))).preimage
    (continuous_induced_dom : @Continuous _ _ G.zariskiTopology G.ambient.zariskiTopology G.embedding)

theorem mem_lawDomain (i : G.FactorIndex) (law : (G.factor i).AdditionLaw) (x : G.Point)
    (hn : (fun j => (factorSquare i).eval (law.coordinates j)
      ((G.factor i).additionPair (x i) (g i))) ≠ 0) :
    x ∈ lawDomain A g i law := by
  obtain ⟨j,hj⟩ : ∃ j, (factorSquare i).eval (law.coordinates j)
      ((G.factor i).additionPair (x i) (g i)) ≠ 0 := by
    simpa only [ne_eq,funext_iff,Pi.zero_apply,not_forall] using hn
  apply Set.mem_iUnion.mpr
  refine ⟨j,?_⟩
  change G.ambient.eval (specializationAtZero A g i (law.coordinates j)) (G.embedding x) ≠ 0
  rw [specializationAtZero_eval]
  exact ((factorSquare i).eval_eq_zero_iff_of_lift _ (pairLift A g i x 0)
    (pairLift_represents A g i x 0 g (liftAtZero_represents A g i))
    _ law.degree (law.homogeneous j)).not.mpr hj

theorem law_represents (i : G.FactorIndex) (law : (G.factor i).AdditionLaw)
    (x : G.Point) (hx : x ∈ lawDomain A g i law) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      ∃ h : (fun j => MvPolynomial.eval (pairLift A g i x z) (law.coordinates j)) ≠ 0,
        Projectivization.mk K
          (fun j => MvPolynomial.eval (pairLift A g i x z) (law.coordinates j)) h =
          G.embedding (x+g+A.map ⟨z,hz⟩) i := by
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
  have hx' : MvPolynomial.eval (pairLift A g i x 0) (law.coordinates j) ≠ 0 := by
    rw [← specializationAtZero_eval]
    exact hj
  have hnear := (pairLift_evaluation_analytic A g i (law.coordinates j) x).continuousAt.eventually_ne hx'
  filter_upwards [hnear,A.lift_represents g] with z hz hrep
  obtain ⟨hzA,hL⟩ := hrep
  have hn : (fun j => MvPolynomial.eval (pairLift A g i x z) (law.coordinates j)) ≠ 0 :=
    fun h => hz (congrFun h j)
  have heq := law.represents_lift (x i) ((g+A.map ⟨z,hzA⟩) i) (pairLift A g i x z)
    (pairLift_represents A g i x z _ (hL i)) hn
  refine ⟨hzA,hn,?_⟩
  simpa only [EmbeddedGroupProduct.embedding,Pi.add_apply,add_assoc] using heq

theorem law_compatible (i : G.FactorIndex) (law : (G.factor i).AdditionLaw)
    (x : G.Point) (j k : Fin (G.ambient.ambientDimension i + 1)) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      MvPolynomial.eval (pairLift A g i x z) (law.coordinates j) * A.lift (g+x) z ⟨i,k⟩ =
        MvPolynomial.eval (pairLift A g i x z) (law.coordinates k) * A.lift (g+x) z ⟨i,j⟩ := by
  filter_upwards [A.lift_represents g,A.lift_represents (g+x)] with z hg hgx
  obtain ⟨hz,hL⟩ := hg
  obtain ⟨hz',hL'⟩ := hgx
  have hzeq : (⟨z,hz'⟩ : A.domain) = ⟨z,hz⟩ := Subtype.ext rfl
  rw [hzeq] at hL'
  obtain ⟨hn,heq⟩ := hL' i
  apply law.compatible_lifts (x i) ((g+A.map ⟨z,hz⟩) i) (pairLift A g i x z)
    (pairLift_represents A g i x z _ (hL i)) (fun l => A.lift (g+x) z ⟨i,l⟩) hn ?_ j k
  change Projectivization.mk K (fun l : Fin (G.ambient.ambientDimension i + 1) =>
    A.lift (g+x) z ⟨i,l⟩) hn = (x i + (g i + A.map ⟨z,hz⟩ i)).val
  simpa only [EmbeddedGroupProduct.embedding,Pi.add_apply,add_assoc,add_left_comm] using heq

def assembledLawChart (laws : ∀ i, (G.factor i).AdditionLaw) : TranslationChart A g where
  domain := ⋂ i, lawDomain A g i (laws i)
  domain_isOpen := by
    letI : TopologicalSpace G.Point := G.zariskiTopology
    exact isOpen_iInter_of_finite (fun i => lawDomain_isOpen A g i (laws i))
  degree i := (laws i).degree (firstBlock i)
  coordinates v := pairSubstitution A g v.1 ((laws v.1).coordinates v.2)
  coefficient_analytic v e _ := pairSubstitution_coeff_analytic A g v.1 _ e
  coordinate_homogeneous := by
    intro v e he
    have hh := pairSubstitution_homogeneous A g v.1 ((laws v.1).coordinates v.2)
      (laws v.1).degree ((laws v.1).homogeneous v.2) (mem_support_iff.mp he)
    have hd (i : G.FactorIndex) := (G.ambient.blockWeight_apply e i).symm.trans (congrFun hh i)
    refine ⟨?_,?_⟩
    · simpa only [Pi.single_eq_same] using hd v.1
    · intro i hi
      simpa only [Pi.single_apply,if_neg hi] using hd i
  coordinate_compatible := by
    intro x i j k
    simpa only [evaluate_pairSubstitution] using law_compatible A g i (laws i) x j k
  represents := by
    intro x hx
    have hh : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ i,
        ∃ hz : z ∈ A.domain,
        ∃ h : (fun j => MvPolynomial.eval (pairLift A g i x z) ((laws i).coordinates j)) ≠ 0,
          Projectivization.mk K
            (fun j => MvPolynomial.eval (pairLift A g i x z) ((laws i).coordinates j)) h =
              G.embedding (x+g+A.map ⟨z,hz⟩) i :=
      Filter.eventually_all.mpr (fun i => law_represents A g i (laws i) x (Set.mem_iInter.mp hx i))
    filter_upwards [hh,A.domain_open.mem_nhds A.zero_mem] with z hrep hz
    refine ⟨hz,?_⟩
    intro i
    obtain ⟨hzi,hn,heq⟩ := hrep i
    have hzeq : (⟨z,hzi⟩ : A.domain) = ⟨z,hz⟩ := Subtype.ext rfl
    rw [hzeq] at heq
    simp only [evaluate_pairSubstitution]
    exact ⟨hn,heq⟩

end PhilipponMultiplicity.AtlasSupport

end
end

section
-- Reused implementation: Solutions.PhilipponAdditionDegreeAtlas

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
universe u
section Algebraic
variable {K : Type u} [Field K]

theorem EmbeddedCommutativeGroup.addition_laws_of_degree_condition
    (E : EmbeddedCommutativeGroup K)
    (hE : @ConnectedSpace E.Point E.pointZariskiTopology)
    (c : ℕ) (hadd : E.HasAdditionDegreeAtMost c) :
    ∀ x y : E.Point, ∃ law : E.AdditionLaw,
      law.degree (0 : Fin 2) ≤ c ∧
      (fun j => (projectiveSquare K E.ambientDimension).eval (law.coordinates j)
        (E.additionPair x y)) ≠ 0 := by
  intro x y
  letI := (projectiveSquare K E.ambientDimension).zariskiTopology
  letI := TopologicalSpace.induced (fun xy : E.Point × E.Point => E.additionPair xy.1 xy.2)
    (projectiveSquare K E.ambientDimension).zariskiTopology
  obtain ⟨U, hU, hxy, D, hD, P, hP, hrep⟩ := hadd (x, y) (0 : Fin 1)
  let V : Set (E.Point × E.Point) :=
    (fun xy : E.Point × E.Point => E.additionPair xy.1 xy.2) ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_induced_dom
  have hxyV : (x, y) ∈ V := hxy
  let law := E.additionLawOfLocal (E.preirreducible_pairs hE) V hV ⟨(x, y), hxyV⟩
    D P hP (fun xy hxy => hrep xy hxy)
  exact ⟨law, hD, (hrep (x, y) hxy).choose⟩

theorem EmbeddedGroupProduct.factor_connectedSpace
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected) (i : G.FactorIndex) :
    @ConnectedSpace (G.factor i).Point (G.factor i).pointZariskiTopology := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace (G.factor i).Point := (G.factor i).pointZariskiTopology
  letI : ConnectedSpace G.Point := connectedSpace_iff_univ.mpr hG
  let f : G.Point → (G.factor i).Point := fun x => x i
  have hc : Continuous f := by
    apply continuous_induced_rng.mpr
    exact ((G.ambient.projection_regular i).comp_domain G.embedding).continuous
  have hs : Function.Surjective f := by
    intro y
    refine ⟨Function.update (0 : G.Point) i y, ?_⟩
    simp [f]
  exact hs.connectedSpace hc

end Algebraic

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponGenericChoice

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.GenericChoice
variable {K σ : Type*} [Field K] [Infinite K]

theorem exists_eval_ne_zero (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x F ≠ 0 := by
  by_contra! h
  apply hF
  apply MvPolynomial.funext
  intro x
  simpa using h x

theorem exists_eval_ne_zero_avoiding_subspaces [Fintype σ]
    (S : Finset (Submodule K (σ → K))) (hS : ∀ U ∈ S, U ≠ ⊤)
    (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x F ≠ 0 ∧ ∀ U ∈ S, x ∉ U := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
    obtain ⟨x,hx⟩ := exists_eval_ne_zero F hF
    exact ⟨x,hx,by simp⟩
  | @insert U S hUS ih =>
    have hU : U ≠ ⊤ := hS U (Finset.mem_insert_self _ _)
    obtain ⟨v,hv⟩ : ∃ v : σ → K, v ∉ U := by
      by_contra! h
      exact hU (top_unique (fun x _ => h x))
    obtain ⟨f,hfv,hUf⟩ := Submodule.exists_le_ker_of_notMem hv
    let g : MvPolynomial σ K := ∑ i, MvPolynomial.C (f (Pi.single i 1)) * MvPolynomial.X i
    have heval (x : σ → K) : MvPolynomial.eval x g = f x := by
      calc
        MvPolynomial.eval x g = ∑ i, f (Pi.single i 1) * x i := by simp [g]
        _ = f (∑ i, x i • Pi.single i (1 : K)) := by
          simp [map_sum, map_smul, smul_eq_mul, mul_comm]
        _ = f x := by
          congr 1
          ext j
          simp [Pi.single_apply]
    have hg : g ≠ 0 := by
      intro hz
      have := heval v
      rw [hz, map_zero] at this
      exact hfv this.symm
    obtain ⟨x,hx,havoid⟩ := ih (fun V hV => hS V (Finset.mem_insert_of_mem hV))
      (F * g) (mul_ne_zero hF hg)
    rw [map_mul, mul_ne_zero_iff] at hx
    refine ⟨x,hx.1,?_⟩
    intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV
    · intro hxU
      apply hx.2
      rw [heval]
      exact hUf hxU
    · exact havoid V hV

end PhilipponMultiplicity.GenericChoice

end
end

section
-- Reused implementation: Solutions.PhilipponFiniteEvaluation

set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
variable {K X : Type*} [Field K]

namespace GenericChoice

theorem exists_dotProduct_ne_zero [Infinite K] {ι σ : Type*}
    [Fintype ι] [Fintype σ] (v : ι → σ → K) (hv : ∀ i, v i ≠ 0) :
    ∃ a : σ → K, ∀ i, (∑ j, a j * v i j) ≠ 0 := by
  classical
  let f (i : ι) : (σ → K) →ₗ[K] K :=
    { toFun := fun a => ∑ j, a j * v i j
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; simp [smul_eq_mul, mul_assoc, Finset.mul_sum] }
  let S : Finset (Submodule K (σ → K)) := Finset.univ.image (fun i => LinearMap.ker (f i))
  have hS : ∀ U ∈ S, U ≠ ⊤ := by
    intro U hU
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hU
    intro htop
    obtain ⟨j, hj⟩ : ∃ j, v i j ≠ 0 := Function.ne_iff.mp (hv i)
    have hmem : Pi.single j 1 ∈ LinearMap.ker (f i) := by rw [htop]; trivial
    have hz : f i (Pi.single j 1) = 0 := hmem
    apply hj
    simpa [f, Pi.single_apply] using hz
  obtain ⟨a, _, ha⟩ := exists_eval_ne_zero_avoiding_subspaces S hS
    (1 : MvPolynomial σ K) one_ne_zero
  refine ⟨a, fun i hi => ha (LinearMap.ker (f i)) ?_ hi⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

end GenericChoice
end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponPointLocusHilbertMonotone

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K)

theorem exists_homogeneous_nonzero_at_finite_points {ι : Type*} [Fintype ι]
    (p : ι → M.Point) (D : M.FactorIndex → ℕ) :
    ∃ P : M.CoordinateRing, M.IsHomogeneous P D ∧ ∀ x, M.eval P (p x) ≠ 0 := by
  classical
  have hchoice (i : M.FactorIndex) : ∃ a : Fin (M.ambientDimension i + 1) → K,
      ∀ x, (∑ j, a j * (p x i).rep j) ≠ 0 :=
    GenericChoice.exists_dotProduct_ne_zero (fun x => (p x i).rep)
      (fun x => (p x i).rep_nonzero)
  choose a ha using hchoice
  let L (i : M.FactorIndex) : M.CoordinateRing :=
    ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X ⟨i, j⟩
  have hL (i : M.FactorIndex) : M.IsHomogeneous (L i)
      (fun k => if k = i then 1 else 0) := by
    apply M.isHomogeneous_sum
    intro j _
    exact (M.isHomogeneous_X ⟨i, j⟩).C_mul M (a i j)
  refine ⟨∏ i, L i ^ D i, ?_, ?_⟩
  · have h := M.isHomogeneous_prod Finset.univ (fun i => L i ^ D i)
      (fun i j => D i * if j = i then 1 else 0) (fun i _ => (hL i).pow M (D i))
    convert h using 1
    ext j
    simp
  · intro x
    simp only [eval, map_prod, map_pow]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply pow_ne_zero
    simpa [L, coordinate] using ha i x

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
-- Reused implementation: Solutions.PhilipponFiniteAdditionChart

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.EmbeddedCommutativeGroup
variable {K : Type*} [Field K] {E : EmbeddedCommutativeGroup K}

theorem AdditionLaw.coordinate_compatible (law : E.AdditionLaw) (x y : E.Point)
    (j k : Fin (E.ambientDimension + 1)) :
    (projectiveSquare K E.ambientDimension).eval (law.coordinates j) (E.additionPair x y) *
        (x + y).val.rep k =
      (projectiveSquare K E.ambientDimension).eval (law.coordinates k) (E.additionPair x y) *
        (x + y).val.rep j := by
  by_cases h : (fun j => (projectiveSquare K E.ambientDimension).eval
      (law.coordinates j) (E.additionPair x y)) = 0
  · rw [congrFun h j, congrFun h k, Pi.zero_apply, Pi.zero_apply, zero_mul, zero_mul]
  · exact (MultiProjectiveSpace.projectivization_mk_eq_iff_cross _ _ h
      (x + y).val.rep_nonzero).mp ((law.represents x y h).trans (x + y).val.mk_rep.symm) j k

theorem exists_additionLaw_nonzero_on_finite_pairs [Infinite K]
    {ι : Type*} [Fintype ι] (x y : ι → E.Point) (c : ℕ)
    (hcover : ∀ a, ∃ law : E.AdditionLaw, law.degree (0 : Fin 2) ≤ c ∧
      (fun j => (projectiveSquare K E.ambientDimension).eval (law.coordinates j)
        (E.additionPair (x a) (y a))) ≠ 0) :
    ∃ law : E.AdditionLaw, law.degree (0 : Fin 2) = c ∧ ∀ a,
      (fun j => (projectiveSquare K E.ambientDimension).eval (law.coordinates j)
        (E.additionPair (x a) (y a))) ≠ 0 := by
  classical
  let M := projectiveSquare K E.ambientDimension
  choose law hlaw hnonzero using hcover
  let D : M.FactorIndex → ℕ :=
    fun i => if i = (0 : Fin 2) then c else Finset.univ.sup (fun a => (law a).degree (1 : Fin 2))
  have hdegree (a : ι) : (law a).degree ≤ D := by
    intro i
    fin_cases i
    · simpa [D] using hlaw a
    · simpa [D] using (Finset.le_sup (f := fun a => (law a).degree (1 : Fin 2))
        (Finset.mem_univ a))
  have hpad (a : ι) : ∃ R : M.CoordinateRing,
      M.IsHomogeneous R (D - (law a).degree) ∧
      ∀ b, M.eval R (E.additionPair (x b) (y b)) ≠ 0 :=
    M.exists_homogeneous_nonzero_at_finite_points
      (fun b => E.additionPair (x b) (y b)) (D - (law a).degree)
  choose R hR hRne using hpad
  let P (a : ι) (j : Fin (E.ambientDimension + 1)) : M.CoordinateRing :=
    R a * (law a).coordinates j
  have hP (a : ι) (j) : M.IsHomogeneous (P a j) D := by
    simpa only [tsub_add_cancel_of_le (hdegree a)] using
      (hR a).mul M ((law a).homogeneous j)
  have hex (a : ι) : ∃ j, M.eval ((law a).coordinates j) (E.additionPair (x a) (y a)) ≠ 0 :=
    Function.ne_iff.mp (hnonzero a)
  choose pivot hpivot using hex
  let v (b a : ι) : K := M.eval (P a (pivot b)) (E.additionPair (x b) (y b))
  have hv (b : ι) : v b ≠ 0 := by
    intro hzero
    have hz : v b b = 0 := congrFun hzero b
    have hne : v b b ≠ 0 := by
      change M.eval (R b * (law b).coordinates (pivot b)) (E.additionPair (x b) (y b)) ≠ 0
      simpa only [MultiProjectiveSpace.eval, map_mul] using
        mul_ne_zero (hRne b b) (hpivot b)
    exact hne hz
  obtain ⟨a, ha⟩ := GenericChoice.exists_dotProduct_ne_zero v hv
  let Q (j : Fin (E.ambientDimension + 1)) : M.CoordinateRing :=
    ∑ b, MvPolynomial.C (a b) * P b j
  have hQ (j) : M.IsHomogeneous (Q j) D :=
    M.isHomogeneous_sum Finset.univ _ D (fun b _ => (hP b j).C_mul M (a b))
  have hcompat (x y : E.Point) (j k : Fin (E.ambientDimension + 1)) :
      M.eval (Q j) (E.additionPair x y) * (x + y).val.rep k =
        M.eval (Q k) (E.additionPair x y) * (x + y).val.rep j := by
    simp only [Q, P, MultiProjectiveSpace.eval, map_sum, map_mul, MvPolynomial.eval_C,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    have hh := (law b).coordinate_compatible x y j k
    change M.eval ((law b).coordinates j) (E.additionPair x y) * (x + y).val.rep k =
      M.eval ((law b).coordinates k) (E.additionPair x y) * (x + y).val.rep j at hh
    simpa only [MultiProjectiveSpace.eval, mul_assoc] using congrArg
      (fun t => a b * (M.eval (R b) (E.additionPair x y) * t)) hh
  let combined : E.AdditionLaw :=
    { degree := D
      coordinates := Q
      homogeneous := hQ
      represents := by
        intro x y h
        exact ((MultiProjectiveSpace.projectivization_mk_eq_iff_cross _ _ h
          (x + y).val.rep_nonzero).mpr (hcompat x y)).trans (x + y).val.mk_rep }
  refine ⟨combined, by simp [combined, D], ?_⟩
  intro b hzero
  apply ha b
  have hz := congrFun hzero (pivot b)
  simpa only [combined, Q, MultiProjectiveSpace.eval, map_sum, map_mul,
    MvPolynomial.eval_C, Pi.zero_apply, v, M] using hz

end PhilipponMultiplicity.EmbeddedCommutativeGroup

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

theorem exists_bounded_translation_chart_covering_finset
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected)
    (c : G.FactorIndex → ℕ)
    (hadd : ∀ i, (G.factor i).HasAdditionDegreeAtMost (c i))
    (A : AnalyticSubgroup G) (g : G.Point) (S : Finset G.Point) :
    ∃ chart : TranslationChart A g,
      (∀ i, chart.degree i = c i) ∧ (S : Set G.Point) ⊆ chart.domain := by
  classical
  have h (i : G.FactorIndex) : ∃ law : (G.factor i).AdditionLaw,
      law.degree (0 : Fin 2) = c i ∧ ∀ x : S,
      (fun j => (projectiveSquare K (G.factor i).ambientDimension).eval (law.coordinates j)
        ((G.factor i).additionPair (x.val i) (g i))) ≠ 0 := by
    apply EmbeddedCommutativeGroup.exists_additionLaw_nonzero_on_finite_pairs
      (fun x : S => x.val i) (fun _ => g i) (c i)
    intro x
    exact (G.factor i).addition_laws_of_degree_condition (G.factor_connectedSpace hG i)
      (c i) (hadd i) (x.val i) (g i)
  choose law hdegree hnonzero using h
  refine ⟨AtlasSupport.assembledLawChart A g law, hdegree, ?_⟩
  intro x hx
  apply Set.mem_iInter.mpr
  intro i
  exact AtlasSupport.mem_lawDomain A g i (law i) x (hnonzero i ⟨x, hx⟩)

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponMixedLeibniz

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

def mixedDeriv : List E → (E → K) → E → K
  | [], f => f
  | v :: w, f => fun x => fderiv K (mixedDeriv w f) x v

theorem mixedDeriv_analytic {f : E → K} {x : E} (hf : AnalyticAt K f x)
    (w : List E) : AnalyticAt K (mixedDeriv w f) x := by
  induction w with
  | nil => exact hf
  | cons v w ih =>
    exact ((ContinuousLinearMap.apply K K v).analyticAt _).comp ih.fderiv

theorem mixedDeriv_congr {f g : E → K} {x : E} (h : f =ᶠ[𝓝 x] g)
    (w : List E) : mixedDeriv w f =ᶠ[𝓝 x] mixedDeriv w g := by
  induction w with
  | nil => exact h
  | cons v w ih =>
    filter_upwards [ih.fderiv (𝕜 := K)] with y hy
    exact congrArg (fun L : E →L[K] K => L v) hy

theorem mixedDeriv_eq_iteratedFDeriv {f : E → K} {x : E}
    (hf : AnalyticAt K f x) (w : List E) :
    mixedDeriv w f x = iteratedFDeriv K w.length f x w.get := by
  induction w generalizing x with
  | nil => simp [mixedDeriv]
  | cons v w ih =>
    have hn : (mixedDeriv w f) =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv K w.length f y w.get) := by
      have he : ∀ᶠ y in 𝓝 x, AnalyticAt K f y := hf.eventually_analyticAt
      filter_upwards [he] with y hy
      exact ih hy
    change fderiv K (mixedDeriv w f) x v = _
    rw [hn.fderiv_eq]
    have hd := (hf.contDiffAt : ContDiffAt K (⊤ : ℕ∞ω) f x).differentiableAt_iteratedFDeriv
      (m := w.length) (by simp)
    have htail : Fin.tail (v::w).get = w.get := by funext i; rfl
    simpa only [List.length_cons,htail,List.get_cons_zero] using
      (hd.iteratedFDeriv_succ_apply_left' (m := (v::w).get)).symm

def properSplits : List E → List (List E × List E)
  | [] => []
  | v :: w => ([v],w) ::
      ((properSplits w).map (fun p => (v :: p.1,p.2)) ++
       (properSplits w).map (fun p => (p.1,v :: p.2)))

omit [NormedAddCommGroup E] in
theorem properSplits_lengths (w : List E) (p : List E × List E)
    (hp : p ∈ properSplits w) :
    0 < p.1.length ∧ p.1.length + p.2.length = w.length ∧ p.2.length < w.length := by
  induction w generalizing p with
  | nil => simp [properSplits] at hp
  | cons v w ih =>
    simp only [properSplits,List.mem_cons,List.mem_append,List.mem_map] at hp
    rcases hp with rfl | ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · simp [Nat.add_comm]
    · obtain ⟨h₁,h₂,h₃⟩ := ih q hq
      simp only [List.length_cons,Prod.fst,Prod.snd]
      omega
    · obtain ⟨h₁,h₂,h₃⟩ := ih q hq
      simp only [List.length_cons,Prod.fst,Prod.snd]
      omega

theorem differentiableAt_list_sum {ι : Type*} (s : List ι) (f : ι → E → K) (x : E)
    (hf : ∀ i ∈ s, DifferentiableAt K (f i) x) :
    DifferentiableAt K (fun y => (s.map fun i => f i y).sum) x := by
  induction s with
  | nil => simpa using (differentiableAt_const (c := (0 : K)))
  | cons i s ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hf i (by simp)).fun_add (ih (fun j hj => hf j (by simp [hj])))

theorem fderiv_list_sum_apply {ι : Type*} (s : List ι) (f : ι → E → K) (x v : E)
    (hf : ∀ i ∈ s, DifferentiableAt K (f i) x) :
    fderiv K (fun y => (s.map fun i => f i y).sum) x v =
      (s.map fun i => fderiv K (f i) x v).sum := by
  induction s with
  | nil => simp
  | cons i s ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [fderiv_fun_add (hf i (by simp))
      (differentiableAt_list_sum s f x (fun j hj => hf j (by simp [hj]))),
      ContinuousLinearMap.add_apply,ih (fun j hj => hf j (by simp [hj]))]

theorem mixedDeriv_mul {f g : E → K} {x : E}
    (hf : AnalyticAt K f x) (hg : AnalyticAt K g x) (w : List E) :
    mixedDeriv w (fun y => f y * g y) x =
      f x * mixedDeriv w g x +
        ((properSplits w).map fun p => mixedDeriv p.1 f x * mixedDeriv p.2 g x).sum := by
  induction w generalizing x with
  | nil => simp [mixedDeriv,properSplits]
  | cons v w ih =>
    have heq : mixedDeriv w (fun y => f y * g y) =ᶠ[𝓝 x]
        (fun y => f y * mixedDeriv w g y +
          ((properSplits w).map fun p => mixedDeriv p.1 f y * mixedDeriv p.2 g y).sum) := by
      filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with y hfy hgy
      exact ih hfy hgy
    have hd (p : List E × List E) :
        DifferentiableAt K (fun y => mixedDeriv p.1 f y * mixedDeriv p.2 g y) x :=
      ((mixedDeriv_analytic hf p.1).mul (mixedDeriv_analytic hg p.2)).differentiableAt
    have hmain : DifferentiableAt K (fun y => f y * mixedDeriv w g y) x :=
      (hf.mul (mixedDeriv_analytic hg w)).differentiableAt
    change fderiv K (mixedDeriv w (fun y => f y * g y)) x v = _
    rw [heq.fderiv_eq,fderiv_fun_add hmain
      (differentiableAt_list_sum _ _ x (fun p _ => hd p)),ContinuousLinearMap.add_apply,
      fderiv_fun_mul hf.differentiableAt (mixedDeriv_analytic hg w).differentiableAt,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,
      fderiv_list_sum_apply _ _ x v (fun p _ => hd p)]
    have hterm (p : List E × List E) :
        fderiv K (fun y => mixedDeriv p.1 f y * mixedDeriv p.2 g y) x v =
          mixedDeriv (v::p.1) f x * mixedDeriv p.2 g x +
            mixedDeriv p.1 f x * mixedDeriv (v::p.2) g x := by
      rw [fderiv_fun_mul (mixedDeriv_analytic hf p.1).differentiableAt
        (mixedDeriv_analytic hg p.2).differentiableAt]
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,mixedDeriv]
      ring
    simp only [hterm,properSplits,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,List.sum_map_add,smul_eq_mul]
    simp only [mixedDeriv]
    ring

end PhilipponMultiplicity.JetSupport

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

omit [NormedAddCommGroup E] in
theorem properSplits_map {ι : Type*} (v : ι → E) (w : List ι) :
    properSplits (w.map v) = (properSplits w).map (fun p => (p.1.map v,p.2.map v)) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [properSplits,ih,List.map_map,Function.comp_def]

theorem iteratedFDeriv_apply_congr {n m : ℕ} (h : n = m) (f : E → K) (x : E)
    (v : Fin n → E) (w : Fin m → E) (hv : ∀ i, v i = w (Fin.cast h i)) :
    iteratedFDeriv K n f x v = iteratedFDeriv K m f x w := by
  subst m
  congr 1
  funext i
  exact hv i

theorem mixedDeriv_map_eq_iteratedFDeriv {ι : Type*} (v : ι → E)
    {f : E → K} {x : E} (hf : AnalyticAt K f x) (w : List ι) :
    mixedDeriv (w.map v) f x = iteratedFDeriv K w.length f x (fun i => v (w.get i)) := by
  rw [mixedDeriv_eq_iteratedFDeriv hf]
  apply iteratedFDeriv_apply_congr (List.length_map ..)
  intro i
  simp

theorem mixedDeriv_map_mul {ι : Type*} (v : ι → E)
    {f g : E → K} {x : E} (hf : AnalyticAt K f x) (hg : AnalyticAt K g x) (w : List ι) :
    mixedDeriv (w.map v) (fun y => f y * g y) x =
      f x * mixedDeriv (w.map v) g x +
        ((properSplits w).map fun p =>
          mixedDeriv (p.1.map v) f x * mixedDeriv (p.2.map v) g x).sum := by
  simpa only [properSplits_map,List.map_map,Function.comp_def] using mixedDeriv_mul hf hg (w.map v)

end PhilipponMultiplicity.JetSupport
end
end

section
-- Reused implementation: Solutions.AnalyticMonomialJets

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.JetSupport
variable {K E F : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]

theorem mixedDeriv_ofFn {f : E → K} {x : E} (hf : AnalyticAt K f x)
    {n : ℕ} (v : Fin n → E) :
    mixedDeriv (List.ofFn v) f x = iteratedFDeriv K n f x v := by
  rw [mixedDeriv_eq_iteratedFDeriv hf]
  apply iteratedFDeriv_apply_congr (List.length_ofFn ..)
  intro i
  exact List.get_ofFn v i

end PhilipponMultiplicity.JetSupport

end
end

section
-- Reused implementation: Solutions.PhilipponSymmetricJets

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

abbrev SymmetricJetIndex (b T : ℕ) := Σ n : Fin (T + 1), Sym (Fin b) n.val

theorem symmetricJetIndex_card (b T : ℕ) :
    Fintype.card (SymmetricJetIndex b T) = Nat.choose (T + b) b := by
  rw [Fintype.card_sigma]
  simp only [Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_multichoose]

def unorderedDirections {b n : ℕ} (w : Fin n → Fin b) : Sym (Fin b) n :=
  ⟨(List.ofFn w : Multiset (Fin b)), by simp⟩

theorem unorderedDirections_cons {b n : ℕ} (a : Fin b) (w : Fin n → Fin b) :
    unorderedDirections (Fin.cons a w) = Sym.cons a (unorderedDirections w) := by
  apply Sym.ext
  simp [unorderedDirections, List.ofFn_succ, Sym.coe_cons]

theorem unorderedDirections_comp {b d n : ℕ} (a : Fin b → Fin d) (w : Fin n → Fin b) :
    unorderedDirections (a ∘ w) = (unorderedDirections w).map a := by
  apply Sym.ext
  simp [unorderedDirections, List.map_ofFn, Function.comp_def]

theorem unorderedDirections_surjective (b n : ℕ) :
    Function.Surjective (@unorderedDirections b n) := by
  induction n with
  | zero =>
    intro s
    exact ⟨Fin.elim0, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro s
    obtain ⟨a, t, rfl⟩ := Sym.exists_eq_cons_of_succ s
    obtain ⟨w, rfl⟩ := ih t
    exact ⟨Fin.cons a w, unorderedDirections_cons a w⟩

def symmetricDirections {b n : ℕ} (s : Sym (Fin b) n) : Fin n → Fin b :=
  Classical.choose (unorderedDirections_surjective b n s)

theorem unordered_symmetricDirections {b n : ℕ} (s : Sym (Fin b) n) :
    unorderedDirections (symmetricDirections s) = s :=
  Classical.choose_spec (unorderedDirections_surjective b n s)

namespace OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

end OperatorSupport

namespace JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

theorem mixedDeriv_perm {f : E → K} {x : E} (hf : AnalyticAt K f x)
    {l m : List E} (h : l.Perm m) : mixedDeriv l f x = mixedDeriv m f x := by
  induction h generalizing x with
  | nil => rfl
  | @cons a l m h ih =>
    change fderiv K (mixedDeriv l f) x a = fderiv K (mixedDeriv m f) x a
    have heq : mixedDeriv l f =ᶠ[nhds x] mixedDeriv m f := by
      filter_upwards [hf.eventually_analyticAt] with y hy
      exact ih hy
    rw [heq.fderiv_eq]
  | swap a b l =>
    have ht := mixedDeriv_analytic hf l
    have ha := mixedDeriv_ofFn ht (![a, b] : Fin 2 → E)
    have hb := mixedDeriv_ofFn ht (![b, a] : Fin 2 → E)
    have hs := ht.contDiffAt.iteratedFDeriv_comp_perm
      (![a, b] : Fin 2 → E) (Equiv.swap 0 1)
    have hv : (![a, b] : Fin 2 → E) ∘ Equiv.swap 0 1 = ![b, a] := by
      ext i
      fin_cases i <;> simp
    rw [hv] at hs
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at ha hb
    exact hb.trans (hs.trans ha.symm)
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ hf).trans (ih₂ hf)

end JetSupport

namespace OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperator_eq_of_unordered_eq (chart : TranslationChart A g) (n : ℕ)
    (v w : Fin n → Fin A.parameterDimension) (h : unorderedDirections v = unorderedDirections w)
    (P : G.CoordinateRing) : polynomialOperator chart n v P = polynomialOperator chart n w P := by
  have hm : (List.ofFn v : Multiset (Fin A.parameterDimension)) = List.ofFn w :=
    congrArg Sym.toMultiset h
  have hp : (List.ofFn v).Perm (List.ofFn w) := Quotient.exact hm
  ext e
  simp only [polynomialOperator_coeff]
  have ha := substituted_coeff_analytic chart P e
  have hd := JetSupport.mixedDeriv_perm ha
    (hp.map (fun i : Fin A.parameterDimension => Pi.single i (1 : K)))
  simpa only [List.map_ofFn, JetSupport.mixedDeriv_ofFn ha, Function.comp_def] using hd

def polynomialOperatorLinearMap (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) : G.CoordinateRing →ₗ[K] G.CoordinateRing where
  toFun := polynomialOperator chart n directions
  map_add' := polynomialOperator_add chart n directions
  map_smul' a P := by
    simpa only [MvPolynomial.smul_eq_C_mul, RingHom.id_apply] using
      polynomialOperator_C_mul chart n directions a P

def symmetricPolynomialOperator (chart : TranslationChart A g) {b T : ℕ}
    (axes : Fin b → Fin A.parameterDimension) (j : SymmetricJetIndex b T)
    (P : G.CoordinateRing) : G.CoordinateRing :=
  polynomialOperator chart j.1.val (axes ∘ symmetricDirections j.2) P

theorem polynomialOperator_eq_symmetric (chart : TranslationChart A g) {b T : ℕ}
    (axes : Fin b → Fin A.parameterDimension) (n : ℕ) (hn : n ≤ T)
    (w : Fin n → Fin b) (P : G.CoordinateRing) :
    polynomialOperator chart n (axes ∘ w) P =
      symmetricPolynomialOperator (T := T) chart axes ⟨⟨n, by omega⟩, unorderedDirections w⟩ P := by
  apply polynomialOperator_eq_of_unordered_eq
  rw [unorderedDirections_comp, unorderedDirections_comp, unordered_symmetricDirections]

end OperatorSupport
end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponSymmetricOperatorRank

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem hilbertFunction_le_of_transverse_operator_detection
    (chart : TranslationChart A g) {b : ℕ}
    (axes : Fin b → Fin A.parameterDimension) (T : ℕ) (D : G.FactorIndex → ℕ)
    (I J : Ideal G.CoordinateRing)
    (hdetect : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (∀ n ≤ T, ∀ w : Fin n → Fin b,
        polynomialOperator chart n (axes ∘ w) P ∈ I) → P ∈ J) :
    Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension J D ≤
      Nat.choose (T + b) b *
        Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension I
          (fun i => chart.degree i * D i) := by
  classical
  let W := Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension D
  let B : G.FactorIndex → ℕ := fun i => chart.degree i * D i
  let Q := Hilbert.quotientPiece K G.ambient.factorCount G.ambient.ambientDimension I B
  let : Module.Finite K W := G.ambient.degreePiece_finite D
  let : Module.Finite K (Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension B) :=
    G.ambient.degreePiece_finite B
  let : Module.Finite K Q := by
    dsimp only [Q, Hilbert.quotientPiece]
    infer_instance
  let : Module.Free K Q := Module.Free.of_divisionRing K Q
  let f (j : SymmetricJetIndex b T) : W →ₗ[K] (G.CoordinateRing ⧸ I) :=
    (((Ideal.Quotient.mkₐ K I).toLinearMap).comp
      (polynomialOperatorLinearMap chart j.1.val (axes ∘ symmetricDirections j.2))).domRestrict W
  have hf (j : SymmetricJetIndex b T) (P : W) : f j P ∈ Q := by
    refine ⟨symmetricPolynomialOperator chart axes j P.val, ?_, rfl⟩
    apply (G.ambient.degreePiece_iff _ _).mpr
    exact polynomialOperator_homogeneous chart j.1.val (axes ∘ symmetricDirections j.2)
      P.val D ((G.ambient.degreePiece_iff _ _).mp P.property)
  let F : W →ₗ[K] (SymmetricJetIndex b T → Q) :=
    LinearMap.pi (fun j => (f j).codRestrict Q (hf j))
  let q : W →ₗ[K] (G.CoordinateRing ⧸ J) :=
    (Ideal.Quotient.mkₐ K J).toLinearMap.domRestrict W
  have hker : LinearMap.ker F ≤ LinearMap.ker q := by
    intro P hP
    change Ideal.Quotient.mk J P.val = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hdetect P.val ((G.ambient.degreePiece_iff _ _).mp P.property)
    intro n hn w
    rw [polynomialOperator_eq_symmetric chart axes n hn w P.val]
    let j : SymmetricJetIndex b T := ⟨⟨n, by omega⟩, unorderedDirections w⟩
    have hz : F P = 0 := hP
    have hj := congrArg Subtype.val (congrFun hz j)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hj
  have hdim := Submodule.finrank_mono hker
  have hF := F.finrank_range_add_finrank_ker
  have hq := q.finrank_range_add_finrank_ker
  have hrange : Module.finrank K (LinearMap.range q) ≤
      Module.finrank K (LinearMap.range F) := by omega
  have hqrank : Module.finrank K (LinearMap.range q) =
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension J D := by
    rw [LinearMap.range_domRestrict]
    rfl
  rw [← hqrank]
  apply hrange.trans
  apply (Submodule.finrank_le (LinearMap.range F)).trans_eq
  have hpi : Module.finrank K (SymmetricJetIndex b T → Q) =
      Fintype.card (SymmetricJetIndex b T) * Module.finrank K Q := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  rw [hpi, symmetricJetIndex_card]
  rfl

end PhilipponMultiplicity.OperatorSupport

end
end

section
-- Reused implementation: Solutions.PhilipponJetIdeal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem natCast_lt_jetOrder_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    (f : E → K) (x : E) (k : ℕ) :
    (k : WithTop ℕ) < jetOrder f x ↔ ∀ n ≤ k, iteratedFDeriv K n f x = 0 := by
  have h (r : WithTop ℕ) : (k : WithTop ℕ) < r ↔ ((k + 1 : ℕ) : WithTop ℕ) ≤ r := by
    exact (ENat.natCast_add_one_le_iff (m := k) (n := r)).symm
  rw [h, natCast_le_jetOrder_iff]
  simp only [Nat.lt_succ_iff]

theorem pullback_analytic (A : AnalyticSubgroup G) (P : G.CoordinateRing) (g : G.Point) :
    AnalyticAt K (A.pullback P g) 0 := by
  exact AnalyticAt.aeval_mvPolynomial (A.lift_analytic g) P

def jetIdeal (A : AnalyticSubgroup G) (g : G.Point) (k : ℕ) : Ideal G.CoordinateRing where
  carrier := {P | ∀ n ≤ k, iteratedFDeriv K n (A.pullback P g) 0 = 0}
  zero_mem' := by
    intro n hn
    change iteratedFDeriv K n (fun z => MvPolynomial.eval (A.lift g z) (0 : G.CoordinateRing)) 0 = 0
    simp
  add_mem' := by
    intro P Q hP hQ n hn
    change iteratedFDeriv K n (fun z => MvPolynomial.eval (A.lift g z) (P + Q)) 0 = 0
    simp only [map_add]
    calc
      _ = iteratedFDeriv K n (A.pullback P g) 0 + iteratedFDeriv K n (A.pullback Q g) 0 :=
        fun_iteratedFDeriv_add_apply (pullback_analytic A P g).contDiffAt
          (pullback_analytic A Q g).contDiffAt
      _ = 0 := by rw [hP n hn, hQ n hn, add_zero]
  smul_mem' := by
    intro Q P hP n hn
    change iteratedFDeriv K n (fun z => MvPolynomial.eval (A.lift g z) (Q * P)) 0 = 0
    simp only [map_mul]
    exact iteratedFDeriv_mul_eq_zero_of_vanishing_jet
      (pullback_analytic A P g).contDiffAt (pullback_analytic A Q g).contDiffAt
      (fun i hi => hP i (hi.trans hn))

theorem mem_jetIdeal_iff (A : AnalyticSubgroup G) (g : G.Point) (k : ℕ)
    (P : G.CoordinateRing) : P ∈ jetIdeal A g k ↔ (k : WithTop ℕ) < vanishingOrder A P g :=
  (natCast_lt_jetOrder_iff (A.pullback P g) 0 k).symm

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponFilterRegularSections

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_eq_of_homogeneous_mem_iff
    (I J : Ideal M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hmem : ∀ P, M.IsHomogeneous P D → (P ∈ I ↔ P ∈ J)) :
    hilbertFunction K M.factorCount M.ambientDimension I D =
      hilbertFunction K M.factorCount M.ambientDimension J D := by
  let V := degreePiece K M.factorCount M.ambientDimension D
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := (Ideal.Quotient.mkₐ K J).toLinearMap.domRestrict V
  have hker : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ Ideal.Quotient.mk J P.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem P.val ((M.degreePiece_iff _ _).mp P.property)
  have hrange (A : Ideal M.CoordinateRing) :
      LinearMap.range ((Ideal.Quotient.mkₐ K A).toLinearMap.domRestrict V) =
        V.map (Ideal.Quotient.mkₐ K A).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P,rfl⟩
      exact ⟨P.val,P.property,rfl⟩
    · rintro ⟨P,hP,rfl⟩
      exact ⟨⟨P,hP⟩,rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange)).finrank_eq
  rw [hrange I,hrange J] at he
  exact he

end PhilipponMultiplicity.Hilbert
end
end

section
-- Reused implementation: Solutions.PhilipponContactHilbertSubadditivity

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
namespace Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end Hilbert

open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

def contactIdealOn (A : AnalyticSubgroup G) (S : Set G.Point) (T : ℕ) :
    Ideal G.CoordinateRing := ⨅ x : S, jetIdeal A x.val T

theorem mem_contactIdealOn_iff (A : AnalyticSubgroup G) (S : Set G.Point) (T : ℕ)
    (P : G.CoordinateRing) :
    P ∈ contactIdealOn A S T ↔
      ∀ x ∈ S, ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P x := by
  simp only [contactIdealOn, Ideal.mem_iInf, mem_jetIdeal_iff]
  constructor
  · intro h x hx
    exact ENat.natCast_add_one_le_iff.mpr (h ⟨x,hx⟩)
  · intro h x
    exact ENat.natCast_add_one_le_iff.mp (h x.val x.property)

theorem mem_contactIdealOn_translate_iff (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup G) (g : G.Point) (T : ℕ) (P : G.CoordinateRing) :
    P ∈ contactIdealOn A (translate g H.carrier) T ↔
      ∀ h ∈ H.carrier, ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h) := by
  rw [mem_contactIdealOn_iff]
  exact Set.forall_mem_image

end PhilipponMultiplicity
end
end

section
-- Reused implementation: Solutions.PhilipponFiniteContactRank

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

theorem exists_finset_iInf_submodule {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (U : ι → Submodule K V) :
    ∃ S : Finset ι, (⨅ i ∈ S, U i) = ⨅ i, U i := by
  classical
  let Z (S : Finset ι) : Submodule K V := ⨅ i ∈ S, U i
  have hex : ∃ n : ℕ, ∃ S : Finset ι, Module.finrank K (Z S) = n := ⟨_, ∅, rfl⟩
  obtain ⟨S, hS⟩ := Nat.find_spec hex
  refine ⟨S, le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro i
    have hle : Z (insert i S) ≤ Z S := by
      simp only [Z, Finset.iInf_insert]
      exact inf_le_right
    have heq : Z (insert i S) = Z S :=
      Submodule.eq_of_le_of_finrank_le hle (by
        rw [hS]
        exact Nat.find_min' hex ⟨insert i S, rfl⟩)
    change Z S ≤ U i
    rw [← heq]
    simp only [Z, Finset.iInf_insert]
    exact inf_le_left
  · exact le_iInf (fun i => le_iInf (fun _ => iInf_le U i))

open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem exists_finite_contact_detection (A : AnalyticSubgroup G)
    (V : Set G.Point) (g : G.Point) (T : ℕ) (D : G.FactorIndex → ℕ) :
    ∃ S : Finset V, ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (∀ x ∈ S, P ∈ jetIdeal A (g + x.val) T) →
      P ∈ contactIdealOn A (translate g V) T := by
  classical
  let W := Hilbert.degreePiece K G.ambient.factorCount G.ambient.ambientDimension D
  let : Module.Finite K W := G.ambient.degreePiece_finite D
  let U (x : V) : Submodule K W :=
    ((jetIdeal A (g + x.val) T).restrictScalars K).comap W.subtype
  obtain ⟨S, hS⟩ := exists_finset_iInf_submodule U
  refine ⟨S, ?_⟩
  intro P hP hfinite
  let p : W := ⟨P, (G.ambient.degreePiece_iff _ _).mpr hP⟩
  have hp : p ∈ ⨅ x ∈ S, U x := by
    simp only [Submodule.mem_iInf]
    exact hfinite
  rw [hS] at hp
  apply Ideal.mem_iInf.mpr
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := hy
  exact (Submodule.mem_iInf _).mp hp ⟨x, hx⟩

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponTangentCoordinates

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [NontriviallyNormedField K]
variable {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)

theorem analyticCodimension_eq_finrank_quotient (V : Set G.Point) :
    analyticCodimension A V = Module.finrank K
      (A.ParameterSpace ⧸ A.tangentKernel V) := by
  have h := (A.tangentKernel V).finrank_quotient_add_finrank
  have hp : Module.finrank K A.ParameterSpace = A.parameterDimension := by
    simp [AnalyticSubgroup.ParameterSpace]
  rw [hp] at h
  unfold analyticCodimension
  omega

theorem exists_transverseCoordinateFamily (H : AlgebraicSubgroup G) :
    ∃ directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension,
      IsTransverseCoordinateFamily A H directions := by
  classical
  let S := A.tangentKernel H.carrier
  let v : Fin A.parameterDimension → A.ParameterSpace ⧸ S :=
    fun i => S.mkQ (Pi.single i 1)
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    have hb := (Pi.basisFun K (Fin A.parameterDimension)).span_eq
    have hr : Set.range v = S.mkQ ''
        Set.range (Pi.basisFun K (Fin A.parameterDimension)) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp only [v, Function.comp_apply, Pi.basisFun_apply]
    rw [hr, ← Submodule.map_span, hb, Submodule.map_top,
      LinearMap.range_eq_top.mpr S.mkQ_surjective]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  rw [hv] at hspan
  letI : Fintype κ := Fintype.ofInjective a ha
  let b : Module.Basis κ K (A.ParameterSpace ⧸ S) := Module.Basis.mk hli hspan.ge
  have hc : Fintype.card κ = analyticCodimension A H.carrier :=
    (Module.finrank_eq_card_basis b).symm.trans
      (analyticCodimension_eq_finrank_quotient A H.carrier).symm
  let e : κ ≃ Fin (analyticCodimension A H.carrier) :=
    (Fintype.equivFin κ).trans (finCongr hc)
  refine ⟨a ∘ e.symm, ?_, ?_⟩
  · exact hli.comp e.symm e.symm.injective
  · change Submodule.span K (Set.range ((v ∘ a) ∘ e.symm)) = ⊤
    rw [e.symm.surjective.range_comp]
    exact hspan

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponAnalyticLinearRestriction

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.AnalyticSubgroup
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)

def precompLinear {d : ℕ} (hd : 0 < d)
    (L : (Fin d → K) →L[K] A.ParameterSpace) : AnalyticSubgroup G := by
  let ρ := A.radius / (‖L‖ + 1)
  have hn : 0 < ‖L‖ + 1 := by positivity
  have hρ : 0 < ρ := div_pos A.radius_pos hn
  have heq : ρ * (‖L‖ + 1) = A.radius := div_mul_cancel₀ _ hn.ne'
  have hmap {z : Fin d → K} (hz : z ∈ Metric.ball 0 ρ) : L z ∈ A.domain := by
    rw [A.domain_eq_ball, Metric.mem_ball, dist_zero_right]
    have hz' : ‖z‖ < ρ := by simpa using hz
    calc
      ‖L z‖ ≤ ‖L‖ * ‖z‖ := L.le_opNorm z
      _ ≤ (‖L‖ + 1) * ‖z‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)
      _ < (‖L‖ + 1) * ρ := mul_lt_mul_of_pos_left hz' hn
      _ = A.radius := by simpa [mul_comm] using heq
  refine
    { parameterDimension := d
      parameterDimension_pos := hd
      radius := ρ
      radius_pos := hρ
      domain := Metric.ball 0 ρ
      domain_eq_ball := rfl
      domain_open := Metric.isOpen_ball
      zero_mem := Metric.mem_ball_self hρ
      map := fun z => A.map ⟨L z.val, hmap z.property⟩
      map_zero := by simpa only [_root_.map_zero] using A.map_zero
      map_add := ?_
      lift := fun g z v => A.lift g (L z) v
      lift_analytic := ?_
      base_series := ?_
      base_represents := fun z i => A.base_represents ⟨L z.val, hmap z.property⟩ i
      lift_represents := ?_ }
  · intro x y h
    simpa only [_root_.map_add] using A.map_add
      ⟨L x.val, hmap x.property⟩ ⟨L y.val, hmap y.property⟩ (by
        simpa only [_root_.map_add] using hmap h)
  · intro g v
    have h : AnalyticAt K (fun z => A.lift g z v) (L 0) := by
      simpa only [_root_.map_zero] using A.lift_analytic g v
    exact h.compContinuousLinearMap
  · intro v
    obtain ⟨p, hp⟩ := A.base_series v
    have hp' : HasFPowerSeriesOnBall (fun z => A.lift 0 z v) p (L 0)
        (ENNReal.ofReal A.radius) := by simpa only [_root_.map_zero] using hp
    refine ⟨p.compContinuousLinearMap L, hp'.compContinuousLinearMap.mono
      (ENNReal.ofReal_pos.mpr hρ) ?_⟩
    apply (ENNReal.le_div_iff_mul_le
      (Or.inr (ENNReal.ofReal_pos.mpr A.radius_pos).ne') (Or.inl enorm_ne_top)).mpr
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hρ.le]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  · intro g
    have hnear := (L.continuous.tendsto 0).eventually (by
      simpa only [_root_.map_zero] using A.lift_represents g)
    filter_upwards [hnear, Metric.ball_mem_nhds (0 : Fin d → K) hρ] with z hz hzd
    obtain ⟨hzA, hrep⟩ := hz
    exact ⟨hzd, hrep⟩

@[simp] theorem precompLinear_pullback {d : ℕ} (hd : 0 < d)
    (L : (Fin d → K) →L[K] A.ParameterSpace) (P : G.CoordinateRing) (g : G.Point) :
    (A.precompLinear hd L).pullback P g = A.pullback P g ∘ L := rfl

theorem precompLinear_tangentKernel {d : ℕ} (hd : 0 < d)
    (L : (Fin d → K) →L[K] A.ParameterSpace) (V : Set G.Point) :
    (A.precompLinear hd L).tangentKernel V =
      (A.tangentKernel V).comap L.toLinearMap := by
  ext z
  simp only [tangentKernel, Submodule.mem_iInf, LinearMap.mem_ker,
    Submodule.mem_comap, ContinuousLinearMap.coe_coe, precompLinear_pullback]
  apply forall_congr'
  intro P
  have hp : DifferentiableAt K (A.pullback P.val 0) (L 0) := by
    simpa only [_root_.map_zero] using (OperatorSupport.pullback_analytic A P.val 0).differentiableAt
  rw [fderiv_comp 0 hp L.differentiableAt]
  simp only [_root_.map_zero, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]

end PhilipponMultiplicity.AnalyticSubgroup

end
end

section
-- Reused implementation: Solutions.PhilipponOrbitLocality

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

theorem orbit_eventually_mem_open (A : AnalyticSubgroup G) (g : G.Point)
    (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U) (hg : g ∈ U) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      g + A.map ⟨z,hz⟩ ∈ U := by
  obtain ⟨P,D,hP,hgP,hPU⟩ := exists_basic_subset U hU g hg
  have h0 : A.pullback P g 0 ≠ 0 := by
    exact (not_congr (G.ambient.eval_eq_zero_iff_of_lift (G.embedding g)
      (A.lift g 0) (lift_zero_represents A g) P D hP)).mpr hgP
  filter_upwards [(polynomialPullback_analytic A g P).continuousAt.eventually_ne h0,
      A.lift_represents g] with z hz hrep
  obtain ⟨hzdom,hrep⟩ := hrep
  refine ⟨hzdom,hPU ?_⟩
  exact (not_congr (G.ambient.eval_eq_zero_iff_of_lift
    (G.embedding (g+A.map ⟨z,hzdom⟩)) (A.lift g z) hrep P D hP)).mp hz

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponTangentLocalDerivatives

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem tangent_derivative_zero_of_local_vanishing
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hcontain : ∀ B : AnalyticSubgroup G, B.tangentKernel H.carrier = ⊤ →
      ∀ᶠ z in 𝓝 (0 : B.ParameterSpace), ∀ hz : z ∈ B.domain,
        B.map ⟨z, hz⟩ ∈ H.carrier)
    (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U)
    (x : G.Point) (hxH : x ∈ H.carrier) (hxU : x ∈ U)
    (f : G.Point → K) (hzero : ∀ y ∈ H.carrier, y ∈ U → f y = 0)
    (F : A.ParameterSpace → K) (hdiff : DifferentiableAt K F 0)
    (hF : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      F z = f (x + A.map ⟨z, hz⟩))
    (v : A.ParameterSpace) (hv : v ∈ A.tangentKernel H.carrier) :
    fderiv K F 0 v = 0 := by
  classical
  let L : (Fin 1 → K) →L[K] A.ParameterSpace :=
    (ContinuousLinearMap.proj (0 : Fin 1)).smulRight v
  let B := A.precompLinear (by decide : 0 < 1) L
  have htop : B.tangentKernel H.carrier = ⊤ := by
    change (A.precompLinear (by decide : 0 < 1) L).tangentKernel H.carrier = ⊤
    rw [AnalyticSubgroup.precompLinear_tangentKernel]
    apply top_unique
    intro z _
    change z (0 : Fin 1) • v ∈ A.tangentKernel H.carrier
    exact (A.tangentKernel H.carrier).smul_mem (z (0 : Fin 1)) hv
  have hcont := hcontain B htop
  have hopen := orbit_eventually_mem_open B x U hU hxU
  have hF' : ∀ᶠ z in 𝓝 (0 : Fin 1 → K), ∃ hz : L z ∈ A.domain,
      F (L z) = f (x + A.map ⟨L z, hz⟩) := by
    have hL : Tendsto L (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using L.continuous.tendsto 0
    exact hL.eventually hF
  have hgerm : F ∘ L =ᶠ[𝓝 (0 : Fin 1 → K)] 0 := by
    filter_upwards [hcont, hopen, hF'] with z hzH hzU hzF
    obtain ⟨hzB, hxzU⟩ := hzU
    obtain ⟨hzA, hval⟩ := hzF
    have heq : B.map ⟨z, hzB⟩ = A.map ⟨L z, hzA⟩ := rfl
    change F (L z) = 0
    rw [hval, ← heq]
    exact hzero _ (H.toAddSubgroup.add_mem hxH (hzH hzB)) hxzU
  have hderiv : (fderiv K F 0).comp L = 0 := by
    have hdiff' : DifferentiableAt K F (L 0) := by simpa only [map_zero] using hdiff
    have hcomp := fderiv_comp 0 hdiff' L.differentiableAt
    rw [map_zero, ContinuousLinearMap.fderiv] at hcomp
    rw [← hcomp, hgerm.fderiv_eq]
    simp
  have hvalue := congrArg (fun d : (Fin 1 → K) →L[K] K => d (Pi.single 0 1)) hderiv
  simpa [L] using hvalue

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponNormalizedChartGerms

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

theorem normalizedPullback_analytic (A : AnalyticSubgroup G) (g : G.Point)
    (b : CoordinateChart G) (P : G.CoordinateRing) (x : G.Point)
    (hx : g + x ∈ chartDomain G b) :
    AnalyticAt K (normalizedPullback A g b P x) 0 := by
  apply AnalyticAt.aeval_mvPolynomial
  intro v
  exact (A.lift_analytic (g+x) v).div (A.lift_analytic (g+x) ⟨v.1,b v.1⟩)
    (lift_pivot_ne_zero A (g+x) b hx v.1)

theorem chart_normalized_factorization (chart : TranslationChart A g)
    (b : CoordinateChart G) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (x : G.Point)
    (hx : g+x ∈ chartDomain G b) :
    evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x =ᶠ[𝓝 0]
      (fun z => (∏ i, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z ^ D i) *
        normalizedPullback A g b P x z) := by
  classical
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ i : G.FactorIndex, A.lift (g+x) z ⟨i,b i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (A.lift_analytic (g+x) _).continuousAt.eventually_ne
      (lift_pivot_ne_zero A (g+x) b hx i)
  have hcompat : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ v : G.ambient.Variable,
      evaluateCoefficientPolynomial A (chart.coordinates v) x z * A.lift (g+x) z ⟨v.1,b v.1⟩ =
        evaluateCoefficientPolynomial A (chart.coordinates ⟨v.1,b v.1⟩) x z * A.lift (g+x) z v := by
    rw [Filter.eventually_all]
    intro v
    exact chart.coordinate_compatible x v.1 v.2 (b v.1)
  filter_upwards [hnear,hcompat] with z hz hc
  rw [evaluate_substituted]
  have heq : (fun v : G.ambient.Variable => evaluateCoefficientPolynomial A (chart.coordinates v) x z) =
      fun v : G.ambient.Variable => evaluateCoefficientPolynomial A (chart.coordinates ⟨v.1,b v.1⟩) x z *
        (A.lift (g+x) z v / A.lift (g+x) z ⟨v.1,b v.1⟩) := by
    funext v
    apply (mul_right_cancel₀ (hz v.1))
    rw [mul_assoc,div_mul_cancel₀ _ (hz v.1)]
    exact hc v
  rw [heq]
  exact G.ambient.eval_block_scale P D hP
    (fun v : G.ambient.Variable => A.lift (g+x) z v / A.lift (g+x) z ⟨v.1,b v.1⟩)
    (fun i : G.FactorIndex => evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z)

theorem chart_pivot_ne_zero (chart : TranslationChart A g) (x : G.Point)
    (hchart : x ∈ chart.domain) (b : CoordinateChart G)
    (hx : g+x ∈ chartDomain G b) (i : G.FactorIndex) :
    evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x 0 ≠ 0 := by
  obtain ⟨hz,hi⟩ := (chart.represents x hchart).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  rw [hz',A.map_zero,add_zero] at hi
  obtain ⟨hne,heq⟩ := hi i
  apply projective_pivot_ne_zero _ hne _ heq
  simpa only [add_comm x g] using hx i

theorem evaluate_pivot_substitution (chart : TranslationChart A g)
    (b : CoordinateChart G) (D : G.FactorIndex → ℕ) (x : G.Point) (z : A.ParameterSpace) :
    evaluateCoefficientPolynomial A (substitutedPolynomial chart (pivotPolynomial b D)) x z =
      ∏ i, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z ^ D i := by
  rw [evaluate_substituted]
  simp only [pivotPolynomial,map_prod,map_pow,eval_X]
  rfl

theorem exists_translation_pivot_neighborhood (chart : TranslationChart A g)
    (b : CoordinateChart G) (x : G.Point) (hchart : x ∈ chart.domain)
    (hx : g+x ∈ chartDomain G b) :
    ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧ U ⊆ chart.domain ∧
      ∀ y ∈ U, g+y ∈ chartDomain G b ∧
        ∀ i : G.FactorIndex, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) y 0 ≠ 0 := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  let B := pivotPolynomial b (fun _ => 1)
  let Q := polynomialOperator chart 0 Fin.elim0 B
  have hQ : G.ambient.IsHomogeneous Q chart.degree := by
    simpa only [mul_one] using polynomialOperator_homogeneous chart 0 Fin.elim0 B (fun _ => 1)
      (pivotPolynomial_homogeneous b (fun _ => 1))
  have hQeval (y : G.Point) : G.ambient.eval Q (G.embedding y) =
      ∏ i, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) y 0 := by
    rw [polynomialOperator_eval]
    simp only [iteratedFDeriv_zero_apply]
    rw [← evaluate_substituted]
    simpa only [pow_one] using evaluate_pivot_substitution chart b (fun _ => 1) y 0
  let U := chart.domain ∩ {y : G.Point | G.ambient.eval Q (G.embedding y) ≠ 0}
  have ho : @IsOpen _ G.zariskiTopology {y : G.Point | G.ambient.eval Q (G.embedding y) ≠ 0} :=
    (G.ambient.isOpen_basic Q chart.degree hQ).preimage continuous_induced_dom
  refine ⟨U,chart.domain_isOpen.inter ho,⟨hchart,?_⟩,Set.inter_subset_left,?_⟩
  · change G.ambient.eval Q (G.embedding x) ≠ 0
    rw [hQeval]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => chart_pivot_ne_zero chart x hchart b hx i)
  · intro y hy
    have hn : ∀ i : G.FactorIndex,
        evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) y 0 ≠ 0 := by
      have hh : G.ambient.eval Q (G.embedding y) ≠ 0 := hy.2
      rw [hQeval] at hh
      exact fun i => Finset.prod_ne_zero_iff.mp hh i (Finset.mem_univ i)
    refine ⟨?_,hn⟩
    intro i
    obtain ⟨hz,hi⟩ := (chart.represents y hy.1).self_of_nhds
    have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
    rw [hz',A.map_zero,add_zero] at hi
    obtain ⟨hne,heq⟩ := hi i
    have hh := (projective_pivot_ne_zero_iff _ hne _ heq (b i)).mp (hn i)
    simpa only [add_comm y g] using hh

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponTranslatedJetGerms

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

end PhilipponMultiplicity.JetSupport

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem projective_ratios_eq {ι : Type*} (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk K v hv = Projectivization.mk K w hw) (i j : ι) :
    v i / v j = w i / w j := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp h
  have he (k : ι) : v k = (a : K) * w k := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm
  rw [he i,he j,mul_div_mul_left _ _ a.ne_zero]

theorem normalizedPullback_shift_germ (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      normalizedPullback A g' b P (g + x + A.map ⟨z,hz⟩) =ᶠ[𝓝 0]
        (fun w => normalizedPullback A (g + g') b P x (z + w)) := by
  let q := g + g' + x
  have hrep := A.lift_represents q
  have hrepnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ᶠ t in 𝓝 z, ∃ ht : t ∈ A.domain, ∀ i : G.FactorIndex,
        ∃ h : (fun j => A.lift q t ⟨i,j⟩) ≠ 0,
          Projectivization.mk K (fun j => A.lift q t ⟨i,j⟩) h =
            G.embedding (q + A.map ⟨t,ht⟩) i := hrep.eventually_nhds
  filter_upwards [A.domain_open.mem_nhds A.zero_mem,hrepnear] with z hz hrepsz
  refine ⟨hz,?_⟩
  have hadd : Tendsto (fun w : A.ParameterSpace => z + w) (𝓝 0) (𝓝 z) := by
    have hc : ContinuousAt (fun w : A.ParameterSpace => z + w) 0 :=
      continuousAt_const.add continuousAt_id
    simpa only [add_zero] using hc.tendsto
  filter_upwards [A.lift_represents (g' + (g + x + A.map ⟨z,hz⟩)),
      hadd.eventually hrepsz] with w hleft hright
  obtain ⟨hw,hl⟩ := hleft
  obtain ⟨hzw,hr⟩ := hright
  have heq : g' + (g + x + A.map ⟨z,hz⟩) + A.map ⟨w,hw⟩ =
      q + A.map ⟨z+w,hzw⟩ := by
    rw [A.map_add ⟨z,hz⟩ ⟨w,hw⟩ hzw]
    dsimp only [q]
    abel
  unfold normalizedPullback
  apply congrArg (fun f : G.ambient.Variable → K => MvPolynomial.eval f P)
  funext v
  obtain ⟨hvl,hpl⟩ := hl v.1
  obtain ⟨hvr,hpr⟩ := hr v.1
  exact projective_ratios_eq _ _ hvl hvr
    (hpl.trans ((congrArg (fun y => G.embedding y v.1) heq).trans hpr.symm)) v.2 (b v.1)

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponTransverseJetDetection

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem transverse_and_tangent_span (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (axes : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (haxes : IsTransverseCoordinateFamily A H axes) :
    Submodule.span K (Set.range (Sum.elim
      (Subtype.val : A.tangentKernel H.carrier → A.ParameterSpace)
      (fun j => Pi.single (axes j) (1 : K)))) = ⊤ := by
  have hmap : (Submodule.span K (Set.range (fun j => Pi.single (axes j) (1 : K)))).map
      (A.tangentKernel H.carrier).mkQ = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact haxes.2
  rw [Set.Sum.elim_range, Submodule.span_union, Subtype.range_coe_subtype]
  change Submodule.span K (A.tangentKernel H.carrier : Set A.ParameterSpace) ⊔ _ = ⊤
  rw [Submodule.span_eq]
  exact (Submodule.map_mkQ_eq_top _ _).mp hmap

theorem normalized_directional_jet_translate (A : AnalyticSubgroup G)
    (g x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    (n : ℕ) (w : Fin n → A.ParameterSpace) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      iteratedFDeriv K n (normalizedPullback A g b P x) z w =
        iteratedFDeriv K n (normalizedPullback A g b P (x + A.map ⟨z, hz⟩)) 0 w := by
  filter_upwards [normalizedPullback_shift_germ A 0 g x b P] with z hz
  obtain ⟨hz, heq⟩ := hz
  refine ⟨hz, ?_⟩
  have hh := congrArg (fun d => d w) ((heq.iteratedFDeriv (𝕜 := K) n).self_of_nhds)
  rw [iteratedFDeriv_comp_add_left] at hh
  simpa only [zero_add, add_zero] using hh.symm

theorem full_jets_of_transverse_jets_on_subgroup_open
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hcontain : ∀ B : AnalyticSubgroup G, B.tangentKernel H.carrier = ⊤ →
      ∀ᶠ z in 𝓝 (0 : B.ParameterSpace), ∀ hz : z ∈ B.domain,
        B.map ⟨z, hz⟩ ∈ H.carrier)
    (axes : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (haxes : IsTransverseCoordinateFamily A H axes)
    (g : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U)
    (hUb : ∀ x ∈ U, g + x ∈ chartDomain G b) (T : ℕ)
    (hpure : ∀ x ∈ H.carrier, x ∈ U → ∀ n ≤ T,
      ∀ w : Fin n → Fin (analyticCodimension A H.carrier),
        iteratedFDeriv K n (normalizedPullback A g b P x) 0
          (fun i => Pi.single (axes (w i)) 1) = 0) :
    ∀ x ∈ H.carrier, x ∈ U → ∀ n ≤ T,
      iteratedFDeriv K n (normalizedPullback A g b P x) 0 = 0 := by
  classical
  let gen := Sum.elim (Subtype.val : A.tangentKernel H.carrier → A.ParameterSpace)
    (fun j => Pi.single (axes j) (1 : K))
  have hspan : Submodule.span K (Set.range gen) = ⊤ := transverse_and_tangent_span A H axes haxes
  suffices hall : ∀ n ≤ T, ∀ x ∈ H.carrier, x ∈ U →
      iteratedFDeriv K n (normalizedPullback A g b P x) 0 = 0 by
    exact fun x hxH hxU n hn => hall n hn x hxH hxU
  intro n
  induction n with
  | zero =>
    intro hn x hxH hxU
    ext w
    have h := hpure x hxH hxU 0 hn Fin.elim0
    simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.zero_apply] using h
  | succ n ih =>
    intro hn x hxH hxU
    have hf := normalizedPullback_analytic A g b P x (hUb x hxU)
    have hndiff : DifferentiableAt K
        (iteratedFDeriv K n (normalizedPullback A g b P x)) 0 :=
      (hf.contDiffAt : ContDiffAt K (⊤ : ℕ∞ω) _ _).differentiableAt_iteratedFDeriv (by simp)
    have heq : (iteratedFDeriv K (n + 1) (normalizedPullback A g b P x) 0).toMultilinearMap = 0 := by
      apply MultilinearMap.ext_of_span_eq_top (fun _ => hspan)
      intro w
      change iteratedFDeriv K (n + 1) (normalizedPullback A g b P x) 0 (fun i => gen (w i)) = 0
      by_cases ht : ∃ i, ∃ v : A.tangentKernel H.carrier, w i = Sum.inl v
      · obtain ⟨i, v, hi⟩ := ht
        let m : Fin (n + 1) → A.ParameterSpace := fun j => gen (w j)
        let m' := m ∘ Equiv.swap 0 i
        have hfirst : m' 0 = v.val := by simp [m', m, hi, gen]
        have hsym := hf.contDiffAt.iteratedFDeriv_comp_perm m (Equiv.swap 0 i)
        change iteratedFDeriv K (n + 1) (normalizedPullback A g b P x) 0 m = 0
        rw [← hsym, hndiff.iteratedFDeriv_succ_apply_left']
        change fderiv K (fun y => iteratedFDeriv K n
          (normalizedPullback A g b P x) y (Fin.tail m')) 0 (m' 0) = 0
        rw [hfirst]
        apply tangent_derivative_zero_of_local_vanishing A H hcontain U hU x hxH hxU
          (fun y => iteratedFDeriv K n (normalizedPullback A g b P y) 0 (Fin.tail m'))
          (fun y hyH hyU => by rw [ih (by omega) y hyH hyU]; rfl)
          _ (hndiff.continuousMultilinear_apply_const _) ?_ v.val v.property
        exact normalized_directional_jet_translate A g x b P n (Fin.tail m')
      · have hall : ∀ i, ∃ a, w i = Sum.inr a := by
          intro i
          cases hw : w i with
          | inl v => exact False.elim (ht ⟨i, v, hw⟩)
          | inr a => exact ⟨a, rfl⟩
        choose a ha using hall
        have htuple : (fun i => gen (w i)) = (fun i => Pi.single (axes (a i)) (1 : K)) := by
          ext i
          rw [ha i]
          rfl
        rw [htuple]
        exact hpure x hxH hxU (n + 1) hn a
    ext w
    exact congrArg (fun d : MultilinearMap K (fun _ : Fin (n + 1) => A.ParameterSpace) K => d w) heq

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponTransverseOperatorNormalization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology BigOperators
open Filter
noncomputable section

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

theorem mixedDeriv_map_zero_of_unit_factor {ι : Type*} (v : ι → E)
    {f u h : E → K} {x : E} (hu : AnalyticAt K u x) (hh : AnalyticAt K h x)
    (heq : f =ᶠ[𝓝 x] (fun y => u y * h y)) (hunit : u x ≠ 0) (T : ℕ)
    (hzero : ∀ w : List ι, w.length ≤ T → mixedDeriv (w.map v) f x = 0) :
    ∀ w : List ι, w.length ≤ T → mixedDeriv (w.map v) h x = 0 := by
  suffices hall : ∀ n, ∀ w : List ι, w.length = n → w.length ≤ T →
      mixedDeriv (w.map v) h x = 0 from fun w hw => hall w.length w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn hw
    have he := (mixedDeriv_congr heq (w.map v)).self_of_nhds
    rw [hzero w hw, mixedDeriv_map_mul v hu hh w] at he
    have hsum : ((properSplits w).map (fun p =>
        mixedDeriv (p.1.map v) u x * mixedDeriv (p.2.map v) h x)).sum = 0 := by
      apply List.sum_eq_zero
      intro t ht
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
      have hlen := (properSplits_lengths w p hp).2.2
      rw [ih p.2.length (by omega) p.2 rfl (by omega), mul_zero]
    rw [hsum, add_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hunit

end PhilipponMultiplicity.JetSupport

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem normalized_transverse_jets_zero_of_polynomial_operators
    (chart : TranslationChart A g) {r : ℕ} (axes : Fin r → Fin A.parameterDimension)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) (hx : x ∈ chart.domain) (b : CoordinateChart G)
    (hb : g + x ∈ chartDomain G b) (T : ℕ)
    (hops : ∀ n ≤ T, ∀ w : Fin n → Fin r,
      G.ambient.eval (polynomialOperator chart n (axes ∘ w) P) (G.embedding x) = 0) :
    ∀ n ≤ T, ∀ w : Fin n → Fin r,
      iteratedFDeriv K n (normalizedPullback A g b P x) 0
        (fun i => Pi.single (axes (w i)) 1) = 0 := by
  classical
  let f := evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x
  let u := evaluateCoefficientPolynomial A (substitutedPolynomial chart (pivotPolynomial b D)) x
  have hu : AnalyticAt K u 0 :=
    evaluated_coefficients_analytic _ (substituted_coeff_analytic chart _) x
  have hh := normalizedPullback_analytic A g b P x hb
  have heq : f =ᶠ[𝓝 0] (fun z => u z * normalizedPullback A g b P x z) := by
    simpa only [f, u, evaluate_pivot_substitution] using
      chart_normalized_factorization chart b P D hP x hb
  have hunit : u 0 ≠ 0 := by
    dsimp only [u]
    rw [evaluate_pivot_substitution]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
      pow_ne_zero _ (chart_pivot_ne_zero chart x hx b hb i))
  have hzero (w : List (Fin r)) (hw : w.length ≤ T) :
      mixedDeriv (w.map (fun j => Pi.single (axes j) (1 : K))) f 0 = 0 := by
    have hf : AnalyticAt K f 0 :=
      evaluated_coefficients_analytic _ (substituted_coeff_analytic chart P) x
    rw [mixedDeriv_map_eq_iteratedFDeriv _ hf]
    have h := hops w.length hw w.get
    rw [polynomialOperator_eval] at h
    have hfun : f = fun z => MvPolynomial.eval
        (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) P :=
      funext (evaluate_substituted chart P x)
    rw [hfun]
    exact h
  have hnorm := mixedDeriv_map_zero_of_unit_factor
    (fun j => Pi.single (axes j) (1 : K)) hu hh heq hunit T hzero
  intro n hn w
  have h := hnorm (List.ofFn w) (by simpa using hn)
  rw [mixedDeriv_map_eq_iteratedFDeriv _ hh] at h
  have he : iteratedFDeriv K (List.ofFn w).length (normalizedPullback A g b P x) 0
      (fun i => Pi.single (axes ((List.ofFn w).get i)) 1) =
      iteratedFDeriv K n (normalizedPullback A g b P x) 0
        (fun i => Pi.single (axes (w i)) 1) := by
    apply iteratedFDeriv_apply_congr (List.length_ofFn ..)
    intro i
    simp only [List.get_ofFn]
  exact he.symm.trans h

end PhilipponMultiplicity.OperatorSupport

end
end

section
-- Reused implementation: Solutions.PhilipponTransverseContactRank

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology BigOperators
open Filter
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem normalizedPullback_jetOrder (A : AnalyticSubgroup G)
    (g x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (hb : g + x ∈ chartDomain G b) :
    jetOrder (normalizedPullback A g b P x) 0 = vanishingOrder A P (g + x) := by
  classical
  let u (z : A.ParameterSpace) := ∏ i, (A.lift (g + x) z ⟨i, b i⟩)⁻¹ ^ D i
  have hu : AnalyticAt K u 0 :=
    Finset.analyticAt_fun_prod _ fun i _ =>
      ((A.lift_analytic (g + x) _).inv (lift_pivot_ne_zero A (g + x) b hb i)).pow _
  have hunit : u 0 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
    pow_ne_zero _ (inv_ne_zero (lift_pivot_ne_zero A (g + x) b hb i))
  have hnorm : normalizedPullback A g b P x =
      fun z => u z * A.pullback P (g + x) z := by
    funext z
    unfold normalizedPullback
    have heq : (fun v : G.ambient.Variable =>
        A.lift (g + x) z v / A.lift (g + x) z ⟨v.1, b v.1⟩) =
        fun v : G.ambient.Variable =>
          (A.lift (g + x) z ⟨v.1, b v.1⟩)⁻¹ * A.lift (g + x) z v := by
      funext v
      exact div_eq_inv_mul _ _
    rw [heq]
    exact G.ambient.eval_block_scale P D hP (A.lift (g + x) z)
      (fun i => (A.lift (g + x) z ⟨i, b i⟩)⁻¹)
  rw [hnorm, jetOrder_mul_unit (pullback_analytic A P (g + x)) hu hunit]
  rfl

theorem contact_at_chart_point_of_transverse_operators
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hcontain : ∀ B : AnalyticSubgroup G, B.tangentKernel H.carrier = ⊤ →
      ∀ᶠ z in 𝓝 (0 : B.ParameterSpace), ∀ hz : z ∈ B.domain,
        B.map ⟨z, hz⟩ ∈ H.carrier)
    (axes : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (haxes : IsTransverseCoordinateFamily A H axes)
    (g : G.Point) (chart : TranslationChart A g)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (T : ℕ)
    (hops : ∀ n ≤ T, ∀ w : Fin n → Fin (analyticCodimension A H.carrier),
      polynomialOperator chart n (axes ∘ w) P ∈ G.vanishingIdeal H.carrier)
    (x : G.Point) (hxH : x ∈ H.carrier) (hx : x ∈ chart.domain) :
    P ∈ jetIdeal A (g + x) T := by
  obtain ⟨b, hb⟩ := exists_chartDomain (g + x)
  obtain ⟨U, hU, hxU, hUc, hUb⟩ := exists_translation_pivot_neighborhood chart b x hx hb
  have hfull := full_jets_of_transverse_jets_on_subgroup_open A H hcontain axes haxes
    g b P U hU (fun y hy => (hUb y hy).1) T (by
      intro y hyH hyU
      apply normalized_transverse_jets_zero_of_polynomial_operators chart axes P D hP
        y (hUc hyU) b (hUb y hyU).1 T
      intro n hn w
      exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal (hops n hn w)
        (Set.mem_image_of_mem G.embedding hyH))
  apply (mem_jetIdeal_iff A (g + x) T P).mpr
  rw [← normalizedPullback_jetOrder A g x b P D hP hb]
  exact (natCast_lt_jetOrder_iff _ 0 T).mpr (hfull x hxH hxU)

theorem contact_hilbert_le_transverse_jets
    (hG : G.IsConnected) (c : G.FactorIndex → ℕ)
    (hadd : ∀ i, (G.factor i).HasAdditionDegreeAtMost (c i))
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hcontain : ∀ B : AnalyticSubgroup G, B.tangentKernel H.carrier = ⊤ →
      ∀ᶠ z in 𝓝 (0 : B.ParameterSpace), ∀ hz : z ∈ B.domain,
        B.map ⟨z, hz⟩ ∈ H.carrier)
    (g : G.Point) (T : ℕ) (D : G.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (contactIdealOn A (translate g H.carrier) T) D ≤
      Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) *
        Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
          (G.vanishingIdeal H.carrier) (fun i => c i * D i) := by
  classical
  obtain ⟨axes, haxes⟩ := exists_transverseCoordinateFamily A H
  obtain ⟨S, hS⟩ := exists_finite_contact_detection A H.carrier g T D
  obtain ⟨chart, hdegree, hchart⟩ := exists_bounded_translation_chart_covering_finset
    G hG c hadd A g (S.image Subtype.val)
  have hbound := hilbertFunction_le_of_transverse_operator_detection chart axes T D
    (G.vanishingIdeal H.carrier) (contactIdealOn A (translate g H.carrier) T) (by
      intro P hP hops
      apply hS P hP
      intro x hx
      exact contact_at_chart_point_of_transverse_operators A H hcontain axes haxes g chart P D hP T
        hops x.val x.property (hchart (Finset.mem_image.mpr ⟨x, hx, rfl⟩)))
  simpa only [hdegree, EmbeddedGroupProduct.ambient] using hbound

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponQuadraticContactRankLocal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology BigOperators
noncomputable section

namespace PhilipponMultiplicity

theorem quadratic_contact_hilbert_bound_proved
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected)
    (hadd : ∀ i, (G.factor i).HasAdditionDegreeAtMost 2)
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g : G.Point)
    (T : ℕ) (D : G.FactorIndex → ℕ) (J : Ideal G.CoordinateRing)
    (hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h))) :
    Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D ≤
      Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) *
        Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
          (G.vanishingIdeal H.carrier) (fun i => 2 * D i) := by
  let : CompleteSpace K := hK.completeSpace
  have heq := Hilbert.hilbertFunction_eq_of_homogeneous_mem_iff G.ambient J
    (contactIdealOn A (translate g H.carrier) T) D (fun P hP =>
      (hJ P hP).trans (mem_contactIdealOn_translate_iff A H g T P).symm)
  have hbound := contact_hilbert_le_transverse_jets hG (fun _ => 2) hadd A H
    (fun B => analytic_subgroup_local_containment_of_tangent K hK G B H) g T D
  calc
    _ = Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (contactIdealOn A (translate g H.carrier) T) D := by
      simpa only [EmbeddedGroupProduct.ambient] using heq
    _ ≤ _ := hbound

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected)
    (hadd : ∀ i, (G.factor i).HasAdditionDegreeAtMost 2)
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g : G.Point)
    (T : ℕ) (D : G.FactorIndex → ℕ) (J : Ideal G.CoordinateRing)
    (hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h))) :
    Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D ≤
      Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) *
        Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
          (G.vanishingIdeal H.carrier) (fun i => 2 * D i) := by
  exact quadratic_contact_hilbert_bound_proved K hK G hG hadd A H g T D J hJ
