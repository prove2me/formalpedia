-- Prove2me | solution 1 for PhilipponMultiplicity.regular_group_representatives_give_cm_locus
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-29T11:14:59.676765+00:00
-- url     : https://prove2.me/submissions/0be22c17-0162-4031-8e96-f4443a243845

import Definitions.Def_Patching_SystemTypes
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Theorems.Thm_IsRegularLocalRing_depth_self_eq_ringKrullDim

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
-- Implementation: Solutions/PhilipponCohenMacaulayCut.lean


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Pointwise
noncomputable section

namespace PhilipponMultiplicity.RegularCutSupport
open IsLocalRing RingTheory

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem depth_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    Module.depth R M = Module.depth R N := by
  rw [Module.depth, Module.depth]
  congr 1
  ext k
  constructor
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, (e.isWeaklyRegular_congr s).mp hs, hs', rfl⟩
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, (e.isWeaklyRegular_congr s).mpr hs, hs', rfl⟩

/-- Finite lower bounds on depth are attained by actual regular sequences. -/
theorem exists_weaklyRegular_of_le_depth (n : ℕ) (hn : (n : ℕ∞) ≤ Module.depth R R) :
    ∃ s : List R, Sequence.IsWeaklyRegular R s ∧
      (∀ r ∈ s, r ∈ maximalIdeal R) ∧ s.length = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨[], Sequence.IsWeaklyRegular.nil R R, by simp, rfl⟩
  have hlt : ((n - 1 : ℕ) : ℕ∞) < Module.depth R R :=
    lt_of_lt_of_le (Nat.cast_lt.mpr (by omega)) hn
  rw [Module.depth, lt_sSup_iff] at hlt
  obtain ⟨b, ⟨s, hs, hs', rfl⟩, hb⟩ := hlt
  have hlen : n ≤ s.length := by
    have := Nat.cast_lt.mp hb
    omega
  refine ⟨s.take n, ?_, ?_, ?_⟩
  · exact ((Sequence.isWeaklyRegular_append_iff R (s.take n) (s.drop n)).mp
      (by rwa [List.take_append_drop])).1
  · exact fun r hr => hs' r (List.take_subset n s hr)
  · rw [List.length_take]; omega

end PhilipponMultiplicity.RegularCutSupport
end
end


section
-- Implementation: Solutions/PhilipponRegularLocalCM.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.RegularCutSupport
open IsLocalRing RingTheory

/-- The standard regular-local-ring theorem gives an actual full regular
sequence, as required by Philippon's local definition. -/
theorem fullRegularSequence_of_isRegularLocalRing
    (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    ∃ s : List R, (∀ r ∈ s, ¬ IsUnit r) ∧ Sequence.IsRegular R s ∧
      (s.length : WithBot ℕ∞) = ringKrullDim R := by
  have hd := IsRegularLocalRing.depth_self_eq_ringKrullDim R
  have hlen : Module.depth R R = ((maximalIdeal R).spanFinrank : ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at hd
    exact WithBot.coe_injective hd
  obtain ⟨s, hs, hsm, hsn⟩ := exists_weaklyRegular_of_le_depth
    (R := R) (maximalIdeal R).spanFinrank (le_of_eq hlen.symm)
  refine ⟨s, fun r hr => (mem_maximalIdeal r).mp (hsm r hr), ?_, ?_⟩
  · exact (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hsm).mpr hs
  · rw [hsn, IsRegularLocalRing.spanFinrank_maximalIdeal]

end PhilipponMultiplicity.RegularCutSupport

namespace PhilipponMultiplicity.Hilbert

/-- Regularity of the actual localized quotient implies exactly the
Cohen--Macaulay predicate used in Proposition 3.3. -/
theorem cohenMacaulayAt_of_isRegularLocalRing
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (m : MaximalSpectrum M.CoordinateRing)
    (hreg : IsRegularLocalRing ((Localization.AtPrime m.asIdeal) ⧸
      I.map (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal)))) :
    IsCohenMacaulayAt K M.factorCount M.ambientDimension I m := by
  letI := hreg
  exact Or.inr (RegularCutSupport.fullRegularSequence_of_isRegularLocalRing
    ((Localization.AtPrime m.asIdeal) ⧸
      I.map (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal))))

end PhilipponMultiplicity.Hilbert

end
end


section
-- Implementation: Solutions/PhilipponGroupCMLocus.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM
variable {K : Type*} [NontriviallyNormedField K] [IsAlgClosed K]

/-- The canonical maximal-spectrum open set above the actual embedded group. -/
def groupMaximalOpen (G : EmbeddedGroupProduct K) :
    TopologicalSpace.Opens (MaximalSpectrum G.CoordinateRing) :=
  ⟨MaximalSpectrum.toPrimeSpectrum ⁻¹'
    projectiveConeOpen G.ambient (Set.range G.embedding),
    (isOpen_projectiveConeOpen _ _).preimage MaximalSpectrum.toPrimeSpectrum_continuous⟩

theorem representative_mem_groupMaximalOpen (G : EmbeddedGroupProduct K)
    (r : GroupHomogeneousRepresentative G) :
    representativeMaximalIdeal G r ∈ groupMaximalOpen G :=
  representative_mem_projectiveConeOpen G r

/-- Once regularity is established at group representatives, the genuine
open-locus hypothesis of Proposition 3.3 follows. Points of the open locus
outside the group ideal have zero localized quotient. -/
theorem locallyCohenMacaulayOn_of_representative_regular (G : EmbeddedGroupProduct K)
    (hreg : ∀ r : GroupHomogeneousRepresentative G,
      IsRegularLocalRing ((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal)))) :
    Hilbert.IsLocallyCohenMacaulayOn K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal Set.univ) (groupMaximalOpen G) := by
  intro m hm
  by_cases hG : G.vanishingIdeal Set.univ ≤ m.asIdeal
  · obtain ⟨r,hr⟩ := representative_of_mem_projectiveConeOpen G m hG hm
    have h := hreg r
    rw [hr] at h
    exact Hilbert.cohenMacaulayAt_of_isRegularLocalRing G.ambient _ m h
  · apply Or.inl
    exact Ideal.Quotient.subsingleton_iff.mpr
      (IsLocalization.AtPrime.map_eq_top_of_not_le (S := Localization.AtPrime m.asIdeal) hG)

theorem exists_group_cm_locus_of_regular_representatives (G : EmbeddedGroupProduct K)
    (hreg : ∀ r : GroupHomogeneousRepresentative G,
      IsRegularLocalRing ((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal)))) :
    ∃ U : TopologicalSpace.Opens (MaximalSpectrum G.CoordinateRing),
      (∀ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r ∈ U) ∧
      (∀ m ∈ U, G.vanishingIdeal Set.univ ≤ m.asIdeal →
        ∃ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r = m) ∧
      Hilbert.IsLocallyCohenMacaulayOn K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) U := by
  refine ⟨groupMaximalOpen G, representative_mem_groupMaximalOpen G, ?_,
    locallyCohenMacaulayOn_of_representative_regular G hreg⟩
  exact fun m hm hG => representative_of_mem_projectiveConeOpen G m hG hm

end PhilipponMultiplicity.AlgebraicGroupCM

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] [IsAlgClosed K]
    (G : EmbeddedGroupProduct K)
    (hreg : ∀ r : GroupHomogeneousRepresentative G,
      IsRegularLocalRing ((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal)))) :
    ∃ U : TopologicalSpace.Opens (MaximalSpectrum G.CoordinateRing),
      (∀ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r ∈ U) ∧
      (∀ m ∈ U, G.vanishingIdeal Set.univ ≤ m.asIdeal →
        ∃ r : GroupHomogeneousRepresentative G, representativeMaximalIdeal G r = m) ∧
      Hilbert.IsLocallyCohenMacaulayOn K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) U := by
  exact AlgebraicGroupCM.exists_group_cm_locus_of_regular_representatives G hreg
