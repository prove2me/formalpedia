-- Prove2me | solution 1 for PhilipponMultiplicity.group_representative_local_rings_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-29T12:02:32.206793+00:00
-- url     : https://prove2.me/submissions/82a627fe-697e-4828-9665-411f86beff97

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic

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
-- Implementation: Solutions/PhilipponProjectiveTranslations.lean

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


section
-- Implementation: Solutions/PhilipponRegularMapComposition.lean

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
-- Implementation: Solutions/PhilipponGroupLocalVanishing.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped Topology
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] [IsAlgClosed K]

/-- A basic affine neighborhood of a homogeneous representative on which every
closed point of the group closure is again an actual group representative. -/
theorem exists_representative_cone_denominator (G : EmbeddedGroupProduct K)
    (r : GroupHomogeneousRepresentative G) :
    ∃ H : G.CoordinateRing, representativeEvaluation G r H ≠ 0 ∧
      ∀ v : G.ambient.Variable → K,
        (∀ P ∈ G.vanishingIdeal Set.univ, MvPolynomial.eval v P = 0) →
        MvPolynomial.eval v H ≠ 0 →
        ∃ s : GroupHomogeneousRepresentative G, s.coordinates = v := by
  classical
  let p : PrimeSpectrum G.CoordinateRing :=
    ⟨(representativeMaximalIdeal G r).asIdeal, inferInstance⟩
  obtain ⟨U, ⟨H, rfl⟩, hrH, hHU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (representative_mem_projectiveConeOpen G r) (isOpen_projectiveConeOpen _ _)
  refine ⟨H, hrH, ?_⟩
  intro v hv hH
  let m : MaximalSpectrum G.CoordinateRing :=
    ⟨MvPolynomial.vanishingIdeal K {v}, inferInstance⟩
  have hm (P : G.CoordinateRing) : P ∈ m.asIdeal ↔ MvPolynomial.eval v P = 0 := by
    simp [m, MvPolynomial.vanishingIdeal]
  obtain ⟨s, hs⟩ := representative_of_mem_projectiveConeOpen G m
    (fun P hP => (hm P).mpr (hv P hP)) (hHU (by
      change H ∉ m.asIdeal
      rwa [hm]))
  refine ⟨s, ?_⟩
  funext j
  have hmem : X j - C (v j) ∈ (representativeMaximalIdeal G s).asIdeal := by
    rw [hs, hm]
    simp
  change representativeEvaluation G s (X j - C (v j)) = 0 at hmem
  simpa [representativeEvaluation, sub_eq_zero] using hmem

/-- Vanishing on an actual affine neighborhood of the representative implies
zero in the localized coordinate ring. This holds for arbitrary polynomials,
not just multihomogeneous equations. -/
theorem local_mem_of_vanishing_near_representative (G : EmbeddedGroupProduct K)
    (r : GroupHomogeneousRepresentative G) (P F : G.CoordinateRing)
    (hF : representativeEvaluation G r F ≠ 0)
    (hP : ∀ s : GroupHomogeneousRepresentative G,
      representativeEvaluation G s F ≠ 0 → representativeEvaluation G s P = 0) :
    algebraMap G.CoordinateRing
      (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) P ∈
      (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
        (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal)) := by
  obtain ⟨H, hrH, hH⟩ := exists_representative_cone_denominator G r
  have hprod : (H * F) * P ∈ G.vanishingIdeal Set.univ := by
    have hrad : (G.vanishingIdeal Set.univ).radical = G.vanishingIdeal Set.univ :=
      (G.ambient.vanishingIdeal_isRadical (G.embedding '' Set.univ)).radical
    rw [← hrad,
      ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro v hv
    change MvPolynomial.eval v ((H * F) * P) = 0
    by_cases hvH : MvPolynomial.eval v H = 0
    · simp [hvH]
    by_cases hvF : MvPolynomial.eval v F = 0
    · simp [hvF]
    obtain ⟨s, hs⟩ := hH v hv hvH
    have hz := hP s (by simpa [representativeEvaluation, hs] using hvF)
    simpa [representativeEvaluation, hs, map_mul, hz] using
      congrArg (fun z => MvPolynomial.eval v (H * F) * z) hz
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (representativeMaximalIdeal G r).asIdeal.primeCompl _ _ P).mpr
  refine ⟨H * F, ?_, hprod⟩
  change representativeEvaluation G r (H * F) ≠ 0
  simpa only [map_mul] using mul_ne_zero hrH hF

end PhilipponMultiplicity.AlgebraicGroupCM
end
end


section
-- Implementation: Solutions/PhilipponGroupLocalGerms.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

/-- Affine Zariski neighborhoods on the nonzero homogeneous cone. -/
def representativeFilter (r : GroupHomogeneousRepresentative G) :
    Filter (GroupHomogeneousRepresentative G) where
  sets := {U | ∃ P : G.CoordinateRing, representativeEvaluation G r P ≠ 0 ∧
    ∀ s, representativeEvaluation G s P ≠ 0 → s ∈ U}
  univ_sets := ⟨1, by simp, fun _ _ => Set.mem_univ _⟩
  sets_of_superset := by
    rintro U V ⟨P, hP, hPU⟩ hUV
    exact ⟨P, hP, fun s hs => hUV (hPU s hs)⟩
  inter_sets := by
    rintro U V ⟨P, hP, hPU⟩ ⟨Q, hQ, hQV⟩
    refine ⟨P * Q, by simpa using mul_ne_zero hP hQ, ?_⟩
    intro s hs
    rw [map_mul, mul_ne_zero_iff] at hs
    exact ⟨hPU s hs.1, hQV s hs.2⟩

theorem representative_eventually_iff (r : GroupHomogeneousRepresentative G)
    (p : GroupHomogeneousRepresentative G → Prop) :
    (∀ᶠ s in representativeFilter G r, p s) ↔
      ∃ P : G.CoordinateRing, representativeEvaluation G r P ≠ 0 ∧
        ∀ s, representativeEvaluation G s P ≠ 0 → p s := Iff.rfl

theorem representative_eventually_self (r : GroupHomogeneousRepresentative G)
    {p : GroupHomogeneousRepresentative G → Prop}
    (h : ∀ᶠ s in representativeFilter G r, p s) : p r := by
  obtain ⟨P, hP, hp⟩ := h
  exact hp r hP

instance representativeFilter_neBot (r : GroupHomogeneousRepresentative G) :
    (representativeFilter G r).NeBot := by
  exact ⟨fun h => by
    have hf : ∀ᶠ _ in representativeFilter G r, False := by rw [h]; simp
    exact representative_eventually_self G r hf⟩

abbrev RepresentativeGerm (r : GroupHomogeneousRepresentative G) :=
  Filter.Germ (representativeFilter G r) K

def polynomialGerm (r : GroupHomogeneousRepresentative G) :
    G.CoordinateRing →+* RepresentativeGerm G r :=
  (Filter.Germ.coeRingHom _).comp
    { toFun := fun P s => representativeEvaluation G s P
      map_zero' := by ext s; exact map_zero _
      map_one' := by ext s; exact map_one _
      map_add' := fun _ _ => by ext s; exact map_add _ _ _
      map_mul' := fun _ _ => by ext s; exact map_mul _ _ _ }

theorem polynomialGerm_isUnit (r : GroupHomogeneousRepresentative G)
    (P : G.CoordinateRing) (hP : representativeEvaluation G r P ≠ 0) :
    IsUnit (polynomialGerm G r P) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨((fun s => (representativeEvaluation G s P)⁻¹) : RepresentativeGerm G r), ?_⟩
  apply Filter.Germ.coe_eq.mpr
  exact ⟨P, hP, fun s hs => mul_inv_cancel₀ hs⟩

abbrev RepresentativeLocalization (r : GroupHomogeneousRepresentative G) :=
  Localization.AtPrime (representativeMaximalIdeal G r).asIdeal

abbrev RepresentativeLocalRing (r : GroupHomogeneousRepresentative G) :=
  (RepresentativeLocalization G r) ⧸ (G.vanishingIdeal Set.univ).map
    (algebraMap G.CoordinateRing (RepresentativeLocalization G r))

def localPolynomial (r : GroupHomogeneousRepresentative G) :
    G.CoordinateRing →+* RepresentativeLocalRing G r :=
  (Ideal.Quotient.mk _).comp (algebraMap _ _)

def localizationGerm (r : GroupHomogeneousRepresentative G) :
    RepresentativeLocalization G r →+* RepresentativeGerm G r :=
  IsLocalization.lift (fun P : (representativeMaximalIdeal G r).asIdeal.primeCompl =>
    polynomialGerm_isUnit G r P P.property)

@[simp] theorem localizationGerm_algebraMap (r : GroupHomogeneousRepresentative G)
    (P : G.CoordinateRing) :
    localizationGerm G r (algebraMap _ _ P) = polynomialGerm G r P :=
  IsLocalization.lift_eq _ _

theorem groupIdeal_le_ker_polynomialGerm (r : GroupHomogeneousRepresentative G) :
    G.vanishingIdeal Set.univ ≤ RingHom.ker (polynomialGerm G r) := by
  intro P hP
  apply Filter.Germ.coe_eq.mpr
  exact Eventually.of_forall (fun s => groupIdeal_le_representative G s hP)

def localRingGerm (r : GroupHomogeneousRepresentative G) :
    RepresentativeLocalRing G r →+* RepresentativeGerm G r :=
  Ideal.Quotient.lift _ (localizationGerm G r) (by
    change (G.vanishingIdeal Set.univ).map (algebraMap _ _) ≤
      RingHom.ker (localizationGerm G r)
    rw [Ideal.map_le_iff_le_comap]
    intro P hP
    change localizationGerm G r (algebraMap _ _ P) = 0
    rw [localizationGerm_algebraMap]
    exact groupIdeal_le_ker_polynomialGerm G r hP)

@[simp] theorem localRingGerm_localPolynomial (r : GroupHomogeneousRepresentative G)
    (P : G.CoordinateRing) :
    localRingGerm G r (localPolynomial G r P) = polynomialGerm G r P :=
  localizationGerm_algebraMap G r P

theorem localPolynomial_isUnit (r : GroupHomogeneousRepresentative G)
    (P : G.CoordinateRing) (hP : representativeEvaluation G r P ≠ 0) :
    IsUnit (localPolynomial G r P) :=
  (IsLocalization.map_units (RepresentativeLocalization G r)
    (⟨P,hP⟩ : (representativeMaximalIdeal G r).asIdeal.primeCompl)).map (Ideal.Quotient.mk _)

theorem localPolynomial_eq_zero_of_germ_eq_zero [IsAlgClosed K]
    (r : GroupHomogeneousRepresentative G) (P : G.CoordinateRing)
    (hP : polynomialGerm G r P = 0) : localPolynomial G r P = 0 := by
  obtain ⟨F, hF, hPF⟩ := Filter.Germ.coe_eq.mp hP
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (local_mem_of_vanishing_near_representative G r P F hF hPF)

/-- The reduced local coordinate ring embeds faithfully in germs of actual
K-valued functions on the nonzero homogeneous group cone. -/
theorem localRingGerm_injective [IsAlgClosed K] (r : GroupHomogeneousRepresentative G) :
    Function.Injective (localRingGerm G r) := by
  apply (injective_iff_map_eq_zero (localRingGerm G r)).mpr
  intro x hx
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a,b⟩, ht⟩ := IsLocalization.surj
    (representativeMaximalIdeal G r).asIdeal.primeCompl t
  have he : Ideal.Quotient.mk _ t * localPolynomial G r b = localPolynomial G r a :=
    congrArg (Ideal.Quotient.mk _) ht
  have ha : polynomialGerm G r a = 0 := by
    rw [← localRingGerm_localPolynomial, ← he, map_mul, hx, zero_mul]
  have hz := localPolynomial_eq_zero_of_germ_eq_zero G r a ha
  exact (localPolynomial_isUnit G r b b.property).mul_left_eq_zero.mp (he.trans hz)

end PhilipponMultiplicity.AlgebraicGroupCM
end
end


section
-- Implementation: Solutions/PhilipponGroupConeCharts.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem representative_ext (r s : GroupHomogeneousRepresentative G)
    (hp : r.point = s.point) (hc : r.coordinates = s.coordinates) : r = s := by
  cases r
  cases s
  cases hp
  cases hc
  rfl

theorem representative_block_scale (r : GroupHomogeneousRepresentative G) (i : G.FactorIndex) :
    ∃ a : Kˣ, ∀ j, r.coordinates ⟨i,j⟩ =
      (a : K) * (G.embedding r.point i).rep j := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ (r.nonzero i)
    (G.embedding r.point i).rep_nonzero).mp
    ((r.represents i).trans (G.embedding r.point i).mk_rep.symm)
  exact ⟨a,fun j => by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm⟩

theorem representative_coordinate_ne_zero_iff (r : GroupHomogeneousRepresentative G)
    (i : G.FactorIndex) (j : Fin ((G.factor i).ambientDimension + 1)) :
    r.coordinates ⟨i,j⟩ ≠ 0 ↔ (G.embedding r.point i).rep j ≠ 0 := by
  obtain ⟨a,ha⟩ := representative_block_scale G r i
  rw [ha]
  exact mul_ne_zero_iff.trans (and_iff_right a.ne_zero)

theorem representative_normalize (r : GroupHomogeneousRepresentative G)
    (i : G.FactorIndex) (j k : Fin ((G.factor i).ambientDimension + 1))
    (hk : (G.embedding r.point i).rep k ≠ 0) :
    r.coordinates ⟨i,k⟩ / (G.embedding r.point i).rep k *
      (G.embedding r.point i).rep j = r.coordinates ⟨i,j⟩ := by
  obtain ⟨a,ha⟩ := representative_block_scale G r i
  rw [ha k, ha j, mul_div_cancel_right₀ _ hk]

abbrev ConePivot := ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1)

/-- Use the fixed coordinate on its chart, choosing another nonzero coordinate
only at points outside that chart. -/
def conePivotAt (b : ConePivot G) (x : G.Point) (i : G.FactorIndex) :
    Fin ((G.factor i).ambientDimension + 1) := by
  classical
  exact if h : (G.embedding x i).rep (b i) ≠ 0 then b i else
    Classical.choose (Function.ne_iff.mp (G.embedding x i).rep_nonzero)

theorem conePivotAt_ne_zero (b : ConePivot G) (x : G.Point) (i : G.FactorIndex) :
    (G.embedding x i).rep (conePivotAt G b x i) ≠ 0 := by
  classical
  unfold conePivotAt
  split
  · assumption
  · exact Classical.choose_spec (Function.ne_iff.mp (G.embedding x i).rep_nonzero)

theorem conePivotAt_eq (b : ConePivot G) (x : G.Point) (i : G.FactorIndex)
    (h : (G.embedding x i).rep (b i) ≠ 0) : conePivotAt G b x i = b i := by
  classical
  simp [conePivotAt, h]

def representativeFromScales (b : ConePivot G) (x : G.Point)
    (a : G.FactorIndex → Kˣ) : GroupHomogeneousRepresentative G where
  point := x
  coordinates := fun v => (a v.1 : K) / (G.embedding x v.1).rep (conePivotAt G b x v.1) *
    (G.embedding x v.1).rep v.2
  nonzero := by
    intro i hz
    have h := congrFun hz (conePivotAt G b x i)
    change (a i : K) / _ * _ = 0 at h
    rw [div_mul_cancel₀ _ (conePivotAt_ne_zero G b x i)] at h
    exact (a i).ne_zero h
  represents := by
    intro i
    apply Eq.trans ?_ (G.embedding x i).mk_rep
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
    refine ⟨a i / Units.mk0 _ (conePivotAt_ne_zero G b x i), ?_⟩
    funext j
    simp [Pi.smul_apply, Units.smul_def, smul_eq_mul]

@[simp] theorem representativeFromScales_pivot (b : ConePivot G) (x : G.Point)
    (a : G.FactorIndex → Kˣ) (i : G.FactorIndex) :
    (representativeFromScales G b x a).coordinates ⟨i,conePivotAt G b x i⟩ = a i := by
  exact div_mul_cancel₀ _ (conePivotAt_ne_zero G b x i)

/-- A representative is a projective group point together with one nonzero
affine scale in each block. Fixed pivots make this identification rational
on the corresponding chart. -/
def coneChartEquiv (b : ConePivot G) :
    GroupHomogeneousRepresentative G ≃ G.Point × (G.FactorIndex → Kˣ) where
  toFun := fun r => ⟨r.point,fun i => Units.mk0
    (r.coordinates ⟨i,conePivotAt G b r.point i⟩)
    ((representative_coordinate_ne_zero_iff G r i _).mpr (conePivotAt_ne_zero G b r.point i))⟩
  invFun := fun z => representativeFromScales G b z.1 z.2
  left_inv := by
    intro r
    apply representative_ext G
    · rfl
    · funext v
      exact representative_normalize G r v.1 v.2 _ (conePivotAt_ne_zero G b r.point v.1)
  right_inv := by
    rintro ⟨x,a⟩
    apply Prod.ext
    · rfl
    · funext i
      apply Units.ext
      exact representativeFromScales_pivot G b x a i

/-- Lift a bijection of group points to an actual bijection of their nonzero
homogeneous cones, retaining the affine scales in the chosen charts. -/
def coneEquiv (b c : ConePivot G) (e : G.Point ≃ G.Point) :
    GroupHomogeneousRepresentative G ≃ GroupHomogeneousRepresentative G :=
  (coneChartEquiv G b).trans ((e.prodCongr (Equiv.refl _)).trans (coneChartEquiv G c).symm)

@[simp] theorem coneEquiv_point (b c : ConePivot G) (e : G.Point ≃ G.Point)
    (r : GroupHomogeneousRepresentative G) : (coneEquiv G b c e r).point = e r.point := rfl

theorem coneEquiv_coordinate (b c : ConePivot G) (e : G.Point ≃ G.Point)
    (r : GroupHomogeneousRepresentative G) (v : G.ambient.Variable)
    (hb : (G.embedding r.point v.1).rep (b v.1) ≠ 0)
    (hc : (G.embedding (e r.point) v.1).rep (c v.1) ≠ 0) :
    (coneEquiv G b c e r).coordinates v =
      r.coordinates ⟨v.1,b v.1⟩ / (G.embedding (e r.point) v.1).rep (c v.1) *
        (G.embedding (e r.point) v.1).rep v.2 := by
  change r.coordinates ⟨v.1,conePivotAt G b r.point v.1⟩ /
    (G.embedding (e r.point) v.1).rep (conePivotAt G c (e r.point) v.1) * _ = _
  rw [conePivotAt_eq G b _ _ hb, conePivotAt_eq G c _ _ hc]
  rfl

end PhilipponMultiplicity.AlgebraicGroupCM
end
end


section
-- Implementation: Solutions/PhilipponGroupLocalFractions.lean

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

def representativeGermValue (r : GroupHomogeneousRepresentative G) :
    RepresentativeGerm G r →+* K where
  toFun := fun f => f.liftOn (fun f => f r)
    (fun _ _ h => representative_eventually_self G r h)
  map_zero' := rfl
  map_one' := rfl
  map_add' := fun f g => Filter.Germ.inductionOn₂ f g (fun _ _ => rfl)
  map_mul' := fun f g => Filter.Germ.inductionOn₂ f g (fun _ _ => rfl)

@[simp] theorem representativeGermValue_coe (r : GroupHomogeneousRepresentative G)
    (f : GroupHomogeneousRepresentative G → K) :
    representativeGermValue G r (f : RepresentativeGerm G r) = f r := rfl

@[simp] theorem representativeGermValue_polynomialGerm (r : GroupHomogeneousRepresentative G)
    (P : G.CoordinateRing) :
    representativeGermValue G r (polynomialGerm G r P) = representativeEvaluation G r P := rfl

def localValue (r : GroupHomogeneousRepresentative G) :
    RepresentativeLocalRing G r →+* K :=
  (representativeGermValue G r).comp (localRingGerm G r)

@[simp] theorem localValue_localPolynomial (r : GroupHomogeneousRepresentative G)
    (P : G.CoordinateRing) :
    localValue G r (localPolynomial G r P) = representativeEvaluation G r P := by
  simp [localValue]

theorem local_exists_fraction (r : GroupHomogeneousRepresentative G)
    (x : RepresentativeLocalRing G r) :
    ∃ P Q : G.CoordinateRing, representativeEvaluation G r Q ≠ 0 ∧
      x * localPolynomial G r Q = localPolynomial G r P := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨P,Q⟩, h⟩ := IsLocalization.surj
    (representativeMaximalIdeal G r).asIdeal.primeCompl t
  exact ⟨P, Q, Q.property, congrArg (Ideal.Quotient.mk _) h⟩

theorem local_isUnit_iff (r : GroupHomogeneousRepresentative G)
    (x : RepresentativeLocalRing G r) : IsUnit x ↔ localValue G r x ≠ 0 := by
  constructor
  · intro h
    have hv : IsUnit (localValue G r x) := h.map (localValue G r)
    exact hv.ne_zero
  intro hx
  obtain ⟨P,Q,hQ,h⟩ := local_exists_fraction G r x
  have hP : representativeEvaluation G r P ≠ 0 := by
    have he := congrArg (localValue G r) h
    simp only [map_mul, localValue_localPolynomial] at he
    rw [← he]
    exact mul_ne_zero hx hQ
  have hxQ : IsUnit (x * localPolynomial G r Q) := by
    rw [h]
    exact localPolynomial_isUnit G r P hP
  letI : IsDedekindFiniteMonoid (RepresentativeLocalRing G r) :=
    ⟨fun {a b} h => (mul_comm b a).trans h⟩
  exact isUnit_of_mul_isUnit_left (x := x) (y := localPolynomial G r Q) hxQ

def localFraction (r : GroupHomogeneousRepresentative G) (P Q : G.CoordinateRing)
    (hQ : representativeEvaluation G r Q ≠ 0) : RepresentativeLocalRing G r :=
  Ideal.Quotient.mk _ (IsLocalization.mk' (RepresentativeLocalization G r) P
    (⟨Q,hQ⟩ : (representativeMaximalIdeal G r).asIdeal.primeCompl))

theorem localFraction_mul_den (r : GroupHomogeneousRepresentative G)
    (P Q : G.CoordinateRing) (hQ : representativeEvaluation G r Q ≠ 0) :
    localFraction G r P Q hQ * localPolynomial G r Q = localPolynomial G r P := by
  exact congrArg (Ideal.Quotient.mk _)
    (IsLocalization.mk'_spec (RepresentativeLocalization G r) P
      (⟨Q,hQ⟩ : (representativeMaximalIdeal G r).asIdeal.primeCompl))

theorem localRingGerm_localFraction (r : GroupHomogeneousRepresentative G)
    (P Q : G.CoordinateRing) (hQ : representativeEvaluation G r Q ≠ 0) :
    localRingGerm G r (localFraction G r P Q hQ) =
      ((fun s => representativeEvaluation G s P / representativeEvaluation G s Q) :
        RepresentativeGerm G r) := by
  apply (polynomialGerm_isUnit G r Q hQ).mul_right_cancel
  have h := congrArg (localRingGerm G r) (localFraction_mul_den G r P Q hQ)
  simp only [map_mul, localRingGerm_localPolynomial] at h
  rw [h]
  apply Filter.Germ.coe_eq.mpr
  exact ⟨Q,hQ,fun s hs => (div_mul_cancel₀ _ hs).symm⟩

theorem germ_isUnit_iff_eventually_ne_zero (r : GroupHomogeneousRepresentative G)
    (f : GroupHomogeneousRepresentative G → K) :
    IsUnit (f : RepresentativeGerm G r) ↔ ∀ᶠ s in representativeFilter G r, f s ≠ 0 := by
  constructor
  · intro h
    obtain ⟨g,hg⟩ := isUnit_iff_exists_inv.mp h
    induction g using Filter.Germ.inductionOn with
    | h g =>
      exact (Filter.Germ.coe_eq.mp hg).mono (fun s hs => by
        change f s * g s = 1 at hs
        exact fun hz => by simp [hz] at hs)
  · intro h
    apply isUnit_iff_exists_inv.mpr
    refine ⟨((fun s => (f s)⁻¹) : RepresentativeGerm G r), ?_⟩
    exact Filter.Germ.coe_eq.mpr (h.mono (fun s hs => mul_inv_cancel₀ hs))

def germPullback (r s : GroupHomogeneousRepresentative G)
    (f : GroupHomogeneousRepresentative G → GroupHomogeneousRepresentative G)
    (hf : Tendsto f (representativeFilter G r) (representativeFilter G s)) :
    RepresentativeGerm G s →+* RepresentativeGerm G r where
  toFun := fun g => g.compTendsto f hf
  map_zero' := rfl
  map_one' := rfl
  map_add' := fun a b => Filter.Germ.inductionOn₂ a b (fun _ _ => rfl)
  map_mul' := fun a b => Filter.Germ.inductionOn₂ a b (fun _ _ => rfl)

end PhilipponMultiplicity.AlgebraicGroupCM
end
end


section
-- Implementation: Solutions/PhilipponGroupRationalPullback.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

/-- Every coordinate of the map has a polynomial fraction on a neighborhood
of the specified homogeneous representative, with denominator nonzero there. -/
def IsRationalAtRepresentative (r : GroupHomogeneousRepresentative G)
    (f : GroupHomogeneousRepresentative G → GroupHomogeneousRepresentative G) : Prop :=
  ∀ j : G.ambient.Variable, ∃ P Q : G.CoordinateRing,
    representativeEvaluation G r Q ≠ 0 ∧
      (fun s => (f s).coordinates j) =ᶠ[representativeFilter G r]
        (fun s => representativeEvaluation G s P / representativeEvaluation G s Q)

def pulledPolynomialGerm (r : GroupHomogeneousRepresentative G)
    (f : GroupHomogeneousRepresentative G → GroupHomogeneousRepresentative G) :
    G.CoordinateRing →+* RepresentativeGerm G r :=
  (Filter.Germ.coeRingHom _).comp
    { toFun := fun P s => representativeEvaluation G (f s) P
      map_zero' := by ext s; exact map_zero _
      map_one' := by ext s; exact map_one _
      map_add' := fun _ _ => by ext s; exact map_add _ _ _
      map_mul' := fun _ _ => by ext s; exact map_mul _ _ _ }

theorem exists_polynomial_pullback (r : GroupHomogeneousRepresentative G)
    (f : GroupHomogeneousRepresentative G → GroupHomogeneousRepresentative G)
    (hf : IsRationalAtRepresentative G r f) :
    ∃ φ : G.CoordinateRing →+* RepresentativeLocalRing G r,
      (localRingGerm G r).comp φ = pulledPolynomialGerm G r f := by
  classical
  choose P Q hQ hPQ using hf
  let φ : G.CoordinateRing →+* RepresentativeLocalRing G r :=
    MvPolynomial.eval₂Hom ((localPolynomial G r).comp C)
      (fun j => localFraction G r (P j) (Q j) (hQ j))
  refine ⟨φ, ?_⟩
  ext c
  · change localRingGerm G r (φ (C c)) = pulledPolynomialGerm G r f (C c)
    simp only [φ, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, localRingGerm_localPolynomial]
    apply Filter.Germ.coe_eq.mpr
    exact Eventually.of_forall (fun _ => by simp [representativeEvaluation])
  · change localRingGerm G r (φ (X c)) = pulledPolynomialGerm G r f (X c)
    rw [show φ (X c) = localFraction G r (P c) (Q c) (hQ c) from eval₂Hom_X' _ _ _,
      localRingGerm_localFraction]
    apply Filter.Germ.coe_eq.mpr
    simpa only [representativeEvaluation, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, MvPolynomial.eval_X] using (hPQ c).symm

/-- A rational cone map induces a genuine homomorphism of local quotient
rings. The compatibility with function germs makes composition checkable. -/
theorem exists_local_pullback [IsAlgClosed K]
    (r s : GroupHomogeneousRepresentative G)
    (f : GroupHomogeneousRepresentative G → GroupHomogeneousRepresentative G)
    (hfr : f r = s) (hf : IsRationalAtRepresentative G r f) :
    ∃ (φ : RepresentativeLocalRing G s →+* RepresentativeLocalRing G r)
      (ht : Tendsto f (representativeFilter G r) (representativeFilter G s)),
      (localRingGerm G r).comp φ =
        (germPullback G r s f ht).comp (localRingGerm G s) := by
  obtain ⟨F, hF⟩ := exists_polynomial_pullback G r f hf
  have hvalue (P : G.CoordinateRing) :
      localValue G r (F P) = representativeEvaluation G s P := by
    change representativeGermValue G r (localRingGerm G r (F P)) = _
    rw [show localRingGerm G r (F P) = pulledPolynomialGerm G r f P from
      DFunLike.congr_fun hF P]
    change representativeEvaluation G (f r) P = _
    rw [hfr]
  have hunit (P : (representativeMaximalIdeal G s).asIdeal.primeCompl) : IsUnit (F P) := by
    rw [local_isUnit_iff, hvalue]
    exact P.property
  have hzero : G.vanishingIdeal Set.univ ≤ RingHom.ker F := by
    intro P hP
    apply localRingGerm_injective G r
    rw [map_zero, show localRingGerm G r (F P) = pulledPolynomialGerm G r f P from
      DFunLike.congr_fun hF P]
    apply Filter.Germ.coe_eq.mpr
    exact Eventually.of_forall (fun x => groupIdeal_le_representative G (f x) hP)
  let L : RepresentativeLocalization G s →+* RepresentativeLocalRing G r :=
    IsLocalization.lift (S := RepresentativeLocalization G s)
      (P := RepresentativeLocalRing G r) (g := F) hunit
  let φ : RepresentativeLocalRing G s →+* RepresentativeLocalRing G r :=
    Ideal.Quotient.lift _ L (by
      change (G.vanishingIdeal Set.univ).map (algebraMap _ _) ≤ RingHom.ker L
      rw [Ideal.map_le_iff_le_comap]
      intro P hP
      change L (algebraMap _ _ P) = 0
      rw [show L (algebraMap _ _ P) = F P from IsLocalization.lift_eq hunit P]
      exact hzero hP)
  have ht : Tendsto f (representativeFilter G r) (representativeFilter G s) := by
    intro U hU
    obtain ⟨P,hP,hPU⟩ := hU
    have hu : IsUnit (pulledPolynomialGerm G r f P) := by
      rw [← DFunLike.congr_fun hF P]
      exact (hunit ⟨P,hP⟩).map (localRingGerm G r)
    exact ((germ_isUnit_iff_eventually_ne_zero G r _).mp hu).mono (fun x hx => hPU (f x) hx)
  refine ⟨φ, ht, ?_⟩
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (representativeMaximalIdeal G s).asIdeal.primeCompl
  apply RingHom.ext
  intro P
  change localRingGerm G r (L (algebraMap _ _ P)) =
    germPullback G r s f ht (localRingGerm G s (localPolynomial G s P))
  rw [show L (algebraMap _ _ P) = F P from IsLocalization.lift_eq hunit P]
  rw [localRingGerm_localPolynomial]
  exact DFunLike.congr_fun hF P

end PhilipponMultiplicity.AlgebraicGroupCM
end
end


section
-- Implementation: Solutions/PhilipponGroupConeRationality.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Filter
open scoped Topology
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem representative_eventually_projective_open (r : GroupHomogeneousRepresentative G)
    (U : Set G.ambient.Point) (hU : @IsOpen _ G.ambient.zariskiTopology U)
    (hr : G.embedding r.point ∈ U) :
    ∀ᶠ s in representativeFilter G r, G.embedding s.point ∈ U := by
  letI := G.ambient.zariskiTopology
  obtain ⟨V, ⟨P,D,hP,rfl⟩, hrP, hPU⟩ :=
    G.ambient.isTopologicalBasis_basic.exists_subset_of_mem_open hr hU
  have hzero (s : GroupHomogeneousRepresentative G) :
      representativeEvaluation G s P = 0 ↔ G.ambient.eval P (G.embedding s.point) = 0 :=
    G.ambient.eval_eq_zero_iff_of_lift _ s.coordinates
      (fun i => ⟨s.nonzero i,s.represents i⟩) P D hP
  exact ⟨P, (hzero r).not.mpr hrP, fun s hs => hPU ((hzero s).not.mp hs)⟩

/-- A projectively regular map gives rational coordinate functions on the
homogeneous cone when the source and target affine scales are retained. -/
theorem coneEquiv_isRationalAt (r : GroupHomogeneousRepresentative G)
    (b c : ConePivot G) (e : G.Point ≃ G.Point)
    (he : G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (e x)))
    (hb : ∀ i, (G.embedding r.point i).rep (b i) ≠ 0)
    (hc : ∀ i, (G.embedding (e r.point) i).rep (c i) ≠ 0) :
    IsRationalAtRepresentative G r (coneEquiv G b c e) := by
  classical
  intro v
  obtain ⟨U,hU,hrU,D,P,hP,hlift⟩ := he r.point v.1
  have hscale (s : GroupHomogeneousRepresentative G) (hs : G.embedding s.point ∈ U) :
      ∃ a : Kˣ, ∀ j, representativeEvaluation G s (P j) =
        (a : K) * (G.embedding (e s.point) v.1).rep j := by
    obtain ⟨hn,hmk⟩ := hlift s.point hs
    obtain ⟨hn',hmk'⟩ := G.ambient.homogeneous_tuple_lift (G.embedding s.point) s.coordinates
      (fun i => ⟨s.nonzero i,s.represents i⟩) P D hP hn
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ hn'
      (G.embedding (e s.point) v.1).rep_nonzero).mp
      (hmk'.trans (hmk.trans (G.embedding (e s.point) v.1).mk_rep.symm))
    exact ⟨a, fun j => by
      simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul, representativeEvaluation]
        using (congrFun ha j).symm⟩
  have hden : representativeEvaluation G r (P (c v.1)) ≠ 0 := by
    obtain ⟨a,ha⟩ := hscale r hrU
    rw [ha]
    exact mul_ne_zero a.ne_zero (hc v.1)
  refine ⟨X ⟨v.1,b v.1⟩ * P v.2, P (c v.1), hden, ?_⟩
  have hsource : ∀ᶠ s in representativeFilter G r, s.coordinates ⟨v.1,b v.1⟩ ≠ 0 :=
    ⟨X ⟨v.1,b v.1⟩,
      by simpa [representativeEvaluation] using
        (representative_coordinate_ne_zero_iff G r _ _).mpr (hb v.1),
      fun s hs => by simpa [representativeEvaluation] using hs⟩
  have htarget : ∀ᶠ s in representativeFilter G r,
      representativeEvaluation G s (P (c v.1)) ≠ 0 :=
    ⟨P (c v.1),hden,fun _ h => h⟩
  filter_upwards [representative_eventually_projective_open G r U hU hrU,
    hsource, htarget] with s hsU hsb hsc
  obtain ⟨a,ha⟩ := hscale s hsU
  have hsct : (G.embedding (e s.point) v.1).rep (c v.1) ≠ 0 := by
    rw [ha] at hsc
    exact (mul_ne_zero_iff.mp hsc).2
  rw [coneEquiv_coordinate G b c e s v
    ((representative_coordinate_ne_zero_iff G s _ _).mp hsb) hsct]
  simp only [map_mul, representativeEvaluation, MvPolynomial.eval_X]
  change _ = s.coordinates ⟨v.1,b v.1⟩ * representativeEvaluation G s (P v.2) /
    representativeEvaluation G s (P (c v.1))
  rw [ha,ha]
  field_simp

theorem coneEquiv_symm (b c : ConePivot G) (e : G.Point ≃ G.Point) :
    (coneEquiv G b c e).symm = coneEquiv G c b e.symm := by
  ext r
  rfl

end PhilipponMultiplicity.AlgebraicGroupCM
end
end


section
-- Implementation: Solutions/PhilipponGroupRationalLocalEquiv.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] [IsAlgClosed K]

/-- Inverse rational maps near homogeneous representatives induce an
isomorphism of the actual localized coordinate quotients. -/
theorem local_rings_equiv_of_rational_inverse (G : EmbeddedGroupProduct K)
    (r s : GroupHomogeneousRepresentative G)
    (f g : GroupHomogeneousRepresentative G → GroupHomogeneousRepresentative G)
    (hfr : f r = s) (hgs : g s = r)
    (hf : IsRationalAtRepresentative G r f) (hg : IsRationalAtRepresentative G s g)
    (hgf : (g ∘ f) =ᶠ[representativeFilter G r] id)
    (hfg : (f ∘ g) =ᶠ[representativeFilter G s] id) :
    Nonempty (RepresentativeLocalRing G r ≃+* RepresentativeLocalRing G s) := by
  obtain ⟨F,ht,hF⟩ := exists_local_pullback G r s f hfr hf
  obtain ⟨H,hu,hH⟩ := exists_local_pullback G s r g hgs hg
  have hF' (x : RepresentativeLocalRing G s) :
      localRingGerm G r (F x) = germPullback G r s f ht (localRingGerm G s x) :=
    DFunLike.congr_fun hF x
  have hH' (x : RepresentativeLocalRing G r) :
      localRingGerm G s (H x) = germPullback G s r g hu (localRingGerm G r x) :=
    DFunLike.congr_fun hH x
  have hid {a b : GroupHomogeneousRepresentative G}
      {v w : GroupHomogeneousRepresentative G → GroupHomogeneousRepresentative G}
      (hv : Tendsto v (representativeFilter G a) (representativeFilter G b))
      (hw : Tendsto w (representativeFilter G b) (representativeFilter G a))
      (h : (w ∘ v) =ᶠ[representativeFilter G a] id) (z : RepresentativeGerm G a) :
      germPullback G a b v hv (germPullback G b a w hw z) = z := by
    induction z using Filter.Germ.inductionOn with
    | h z =>
      apply Filter.Germ.coe_eq.mpr
      exact h.mono (fun x hx => congrArg z hx)
  have hFH : F.comp H = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply localRingGerm_injective G r
    change localRingGerm G r (F (H x)) = localRingGerm G r x
    rw [hF', hH']
    exact hid ht hu hgf _
  have hHF : H.comp F = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply localRingGerm_injective G s
    change localRingGerm G s (H (F x)) = localRingGerm G s x
    rw [hH', hF']
    exact hid hu ht hfg _
  exact ⟨RingEquiv.ofRingHom H F hHF hFH⟩

end PhilipponMultiplicity.AlgebraicGroupCM
end
end


section
-- Implementation: Solutions/PhilipponGroupLiftScaling.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

def blockScaleHom (a : M.FactorIndex → K) : M.CoordinateRing →ₐ[K] M.CoordinateRing :=
  MvPolynomial.aeval (fun v => C (a v.1) * X v)

def blockScaleEquiv (a : M.FactorIndex → Kˣ) : M.CoordinateRing ≃ₐ[K] M.CoordinateRing :=
  AlgEquiv.ofAlgHom (blockScaleHom M (fun i => a i))
    (blockScaleHom M (fun i => ↑((a i)⁻¹)))
    (by
      ext v : 1
      simp only [AlgHom.comp_apply, AlgHom.id_apply, blockScaleHom, aeval_X, map_mul, aeval_C]
      change C (↑((a v.1)⁻¹) : K) * (C (a v.1 : K) * X v) = X v
      rw [← mul_assoc, ← map_mul]
      simp)
    (by
      ext v : 1
      simp only [AlgHom.comp_apply, AlgHom.id_apply, blockScaleHom, aeval_X, map_mul, aeval_C]
      change C (a v.1 : K) * (C (↑((a v.1)⁻¹) : K) * X v) = X v
      rw [← mul_assoc, ← map_mul]
      simp)

theorem blockScaleHom_homogeneous (a : M.FactorIndex → K)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    blockScaleHom M a P = C (∏ i, a i ^ D i) * P := by
  classical
  have hscale (e : M.Variable →₀ ℕ) (he : e ∈ P.support) :
      (∏ v : M.Variable, (C (a v.1) : M.CoordinateRing) ^ e v) = C (∏ i, a i ^ D i) := by
    simp only [← map_pow, ← map_prod]
    congr 1
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ e ⟨i,j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP e he i]
  have hself : MvPolynomial.eval₂ C X P = P := by
    exact MvPolynomial.aeval_X_left_apply P
  change MvPolynomial.eval₂ C (fun v => C (a v.1) * X v) P = _
  conv_rhs => rw [← hself]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [mul_pow, Finset.prod_mul_distrib, hscale e he]
  ring

/-- Changing the nonzero block scales preserves the original homogeneous
vanishing ideal as an actual ideal, before passing to zero loci. -/
theorem blockScaleHom_maps_vanishingIdeal (a : M.FactorIndex → K) (S : Set M.Point) :
    (M.vanishingIdeal S).map (blockScaleHom M a).toRingHom ≤ M.vanishingIdeal S := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  change blockScaleHom M a P ∈ M.vanishingIdeal S
  rw [blockScaleHom_homogeneous M a P D hD]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨D,hD⟩,hP⟩)

theorem blockScaleEquiv_map_vanishingIdeal (a : M.FactorIndex → Kˣ) (S : Set M.Point) :
    (M.vanishingIdeal S).map (blockScaleEquiv M a).toRingEquiv.toRingHom =
      M.vanishingIdeal S := by
  have he : (blockScaleEquiv M a).toRingEquiv.toRingHom =
      (blockScaleHom M (fun i => a i)).toRingHom := rfl
  apply le_antisymm (blockScaleHom_maps_vanishingIdeal M (fun i => a i) S)
  have h := Ideal.map_mono (f := (blockScaleEquiv M a).toRingEquiv.toRingHom)
    (blockScaleHom_maps_vanishingIdeal M (fun i => ↑((a i)⁻¹)) S)
  rw [Ideal.map_map, show (blockScaleEquiv M a).toRingEquiv.toRingHom.comp
    (blockScaleHom M (fun i => ↑((a i)⁻¹))).toRingHom = RingHom.id _ from
      RingHom.ext (fun P => (blockScaleEquiv M a).apply_symm_apply P), Ideal.map_id] at h
  rwa [he] at h

end PhilipponMultiplicity.AlgebraicGroupCM

end
end


section
-- Implementation: Solutions/PhilipponLocalRingEquivTransport.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM

/-- An automorphism preserving the actual ideal and carrying the chosen prime
induces an equivalence of the actual localized quotient rings. -/
def localQuotientEquiv_of_ringEquiv {R : Type*} [CommRing R]
    (I p q : Ideal R) [p.IsPrime] [q.IsPrime] (e : R ≃+* R)
    (hI : I.map e = I) (hp : q.comap e = p) :
    ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≃+*
      ((Localization.AtPrime q) ⧸ I.map (algebraMap R (Localization.AtPrime q))) := by
  have hcompl : (q.comap e).primeCompl = p.primeCompl := by
    ext x
    change x ∉ q.comap e ↔ x ∉ p
    rw [hp]
  have H : p.primeCompl.map e.toMonoidHom = q.primeCompl := by
    rw [← hcompl]
    exact Ideal.map_primeCompl_comap_of_surjective e e.surjective q
  let E := IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime p) (Localization.AtPrime q) e H
  have he : (E : Localization.AtPrime p →+* Localization.AtPrime q).comp
      (algebraMap R (Localization.AtPrime p)) =
      (algebraMap R (Localization.AtPrime q)).comp e := by
    ext x
    exact IsLocalization.ringEquivOfRingEquiv_eq H x
  apply Ideal.quotientEquiv _ _ E
  rw [Ideal.map_map, he, ← Ideal.map_map]
  exact congrArg (Ideal.map (algebraMap R (Localization.AtPrime q))) hI.symm

end PhilipponMultiplicity.AlgebraicGroupCM

end
end


section
-- Implementation: Solutions/PhilipponGroupSamePointLocalRing.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K]

/-- Local coordinate rings are independent of the homogeneous representative
of a fixed group point. This part needs no algebraic closure hypothesis. -/
theorem local_rings_equiv_of_same_point (G : EmbeddedGroupProduct K)
    (r s : GroupHomogeneousRepresentative G) (hrs : r.point = s.point) :
    Nonempty (((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
      (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
        (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal))) ≃+*
      ((Localization.AtPrime (representativeMaximalIdeal G s).asIdeal) ⧸
      (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
        (Localization.AtPrime (representativeMaximalIdeal G s).asIdeal)))) := by
  classical
  have ha (i : G.FactorIndex) : ∃ a : Kˣ,
      ∀ j, (a : K) * r.coordinates ⟨i,j⟩ = s.coordinates ⟨i,j⟩ := by
    have he : Projectivization.mk K (fun j => s.coordinates ⟨i,j⟩) (s.nonzero i) =
        Projectivization.mk K (fun j => r.coordinates ⟨i,j⟩) (r.nonzero i) := by
      rw [s.represents, r.represents, hrs]
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ (s.nonzero i) (r.nonzero i)).mp he
    exact ⟨a,fun j => by simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using congrFun ha j⟩
  choose a ha using ha
  let e := (blockScaleEquiv G.ambient a).toRingEquiv
  have heval : (MvPolynomial.eval r.coordinates).comp e.toRingHom =
      MvPolynomial.eval s.coordinates := by
    ext c
    · simp [e,blockScaleEquiv,blockScaleHom]
    · simpa [e,blockScaleEquiv,blockScaleHom] using ha c.1 c.2
  have hp : (representativeMaximalIdeal G r).asIdeal.comap e.toRingHom =
      (representativeMaximalIdeal G s).asIdeal := by
    ext P
    change MvPolynomial.eval r.coordinates (e P) = 0 ↔ MvPolynomial.eval s.coordinates P = 0
    rw [show MvPolynomial.eval r.coordinates (e P) = MvPolynomial.eval s.coordinates P from
      DFunLike.congr_fun heval P]
  exact ⟨(localQuotientEquiv_of_ringEquiv (G.vanishingIdeal Set.univ)
    (representativeMaximalIdeal G s).asIdeal (representativeMaximalIdeal G r).asIdeal e
    (blockScaleEquiv_map_vanishingIdeal G.ambient a _) hp).symm⟩

end PhilipponMultiplicity.AlgebraicGroupCM

end
end


section
-- Implementation: Solutions/PhilipponGroupTranslationLocalRing.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] [IsAlgClosed K]

/-- Translation and its inverse, lifted through polynomial projective charts,
identify the actual local coordinate rings at any two group representatives. -/
theorem group_local_rings_equiv (G : EmbeddedGroupProduct K)
    (r s : GroupHomogeneousRepresentative G) :
    Nonempty (RepresentativeLocalRing G r ≃+* RepresentativeLocalRing G s) := by
  classical
  let a : G.Point := s.point - r.point
  let e : G.Point ≃ G.Point :=
    { toFun := fun x => x + a
      invFun := fun x => x - a
      left_inv := fun x => add_sub_cancel_right x a
      right_inv := fun x => sub_add_cancel x a }
  have her : e r.point = s.point := by dsimp [e,a]; abel
  have he : G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (e x)) :=
    G.translation_regular a
  have hei : G.ambient.IsRegularAlong G.ambient G.embedding
      (fun x => G.embedding (e.symm x)) := by
    change G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (x - a))
    simpa only [sub_eq_add_neg] using G.translation_regular (-a)
  have hbr (i : G.FactorIndex) : ∃ j, (G.embedding r.point i).rep j ≠ 0 :=
    Function.ne_iff.mp (G.embedding r.point i).rep_nonzero
  have hcs (i : G.FactorIndex) : ∃ j, (G.embedding s.point i).rep j ≠ 0 :=
    Function.ne_iff.mp (G.embedding s.point i).rep_nonzero
  choose b hb using hbr
  choose c hc using hcs
  let E := coneEquiv G b c e
  let t : GroupHomogeneousRepresentative G := E r
  have ht : t.point = s.point := her
  have hE : IsRationalAtRepresentative G r E :=
    coneEquiv_isRationalAt G r b c e he hb (fun i => by rw [her]; exact hc i)
  have hEi : IsRationalAtRepresentative G t E.symm := by
    change IsRationalAtRepresentative G t (coneEquiv G b c e).symm
    rw [coneEquiv_symm]
    apply coneEquiv_isRationalAt G t c b e.symm hei
    · intro i
      rw [ht]
      exact hc i
    · intro i
      change (G.embedding (e.symm (e r.point)) i).rep (b i) ≠ 0
      rw [e.symm_apply_apply]
      exact hb i
  obtain ⟨F⟩ := local_rings_equiv_of_rational_inverse G r t E E.symm rfl
    (E.symm_apply_apply r) hE hEi
    (Eventually.of_forall E.symm_apply_apply) (Eventually.of_forall E.apply_symm_apply)
  obtain ⟨H⟩ := local_rings_equiv_of_same_point G t s ht
  exact ⟨F.trans H⟩

end PhilipponMultiplicity.AlgebraicGroupCM

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] [IsAlgClosed K]
    (G : EmbeddedGroupProduct K)
    (r s : GroupHomogeneousRepresentative G) :
    Nonempty (((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal))) ≃+*
        ((Localization.AtPrime (representativeMaximalIdeal G s).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G s).asIdeal)))) := by
  exact AlgebraicGroupCM.group_local_rings_equiv G r s
