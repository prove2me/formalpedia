-- Prove2me | solution 1 for PhilipponMultiplicity.masser_wustholz_geometric_coset_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T18:07:33.407722+00:00
-- url     : https://prove2.me/submissions/4cb64f79-05f1-407a-a600-0d9e0be3d7a0

import Theorems.Thm_PhilipponMultiplicity_masser_wustholz_local_prime_estimate
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Lasker
import Mathlib.Topology.Algebra.Group.Quotient

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

theorem singleBlock_isHomogeneous {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    (projectiveSpace K N).IsHomogeneous
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => d) := by
  classical
  intro a ha i
  have h := hP.rename_isHomogeneous (f := fun j => (⟨(0 : Fin 1), j⟩ :
    (projectiveSpace K N).Variable)) (MvPolynomial.mem_support_iff.mp ha)
  change Finsupp.weight (1 : (projectiveSpace K N).Variable → ℕ) a = d at h
  rw [Finsupp.weight_eq_sum] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma] at h
  change (∑ x : Fin 1, ∑ y : Fin (N + 1), a ⟨x, y⟩) = d at h
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (∑ j : Fin (N + 1), a ⟨(0 : Fin 1), j⟩) = d
  exact (Fin.sum_univ_one _).symm.trans h

theorem projective_isClosed_zero {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    @IsClosed _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | MvPolynomial.eval p.rep P = 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isClosed_zero _ _
    (singleBlock_isHomogeneous hP)).preimage hcont
  convert h using 1
  ext p
  change MvPolynomial.eval p.rep P = 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => p) = 0
  simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_rename]
  rfl

theorem projective_isOpen_coordinate {K : Type*} [Field K] {N : ℕ}
    (j : Fin (N + 1)) :
    @IsOpen _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | p.rep j ≠ 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isOpen_basic _ _
    (singleBlock_isHomogeneous (MvPolynomial.isHomogeneous_X K j))).preimage
      hcont
  convert h using 1
  ext p
  change p.rep j ≠ 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) (MvPolynomial.X j)) (fun _ => p) ≠ 0
  simp [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate]

theorem projective_regular_of_homogeneous
    {K X : Type u} [Field K] {N N' d : ℕ}
    (e : X → Projectivization K (Fin (N + 1) → K))
    (f : X → Projectivization K (Fin (N' + 1) → K))
    (P : Fin (N' + 1) → MvPolynomial (Fin (N + 1)) K)
    (hP : ∀ j, (P j).IsHomogeneous d)
    (hf : ∀ x, ∃ h : (fun j => MvPolynomial.eval (e x).rep (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval (e x).rep (P j)) h = f x) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K N) (projectiveSpace K N')
      (fun x => fun _ => e x) (fun x => fun _ => f x) := by
  letI := (projectiveSpace K N).zariskiTopology
  intro x b
  let Q : Fin (N' + 1) → (projectiveSpace K N).CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(0 : Fin 1), k⟩) (P j)
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => d,
    Q,
    (fun j => singleBlock_isHomogeneous (hP j)), ?_⟩
  intro y _
  have heq : (fun j => (projectiveSpace K N).eval (Q j) (fun _ => e y)) =
      (fun j => MvPolynomial.eval (e y).rep (P j)) := by
    ext j
    change MvPolynomial.eval _ (MvPolynomial.rename _ (P j)) = _
    rw [MvPolynomial.eval_rename]
    rfl
  obtain ⟨hne, hmk⟩ := hf y
  change ∃ h : (fun j : Fin (N' + 1) =>
      (projectiveSpace K N).eval (Q j) (fun _ => e y)) ≠ 0,
    Projectivization.mk K
      (fun j : Fin (N' + 1) => (projectiveSpace K N).eval (Q j) (fun _ => e y)) h = f y
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hne
  · simpa only [heq] using hmk

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

theorem projective_extension_locallyClosed (g₂ g₃ : ℂ) :
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p _ => p) (projectiveSpace ℂ 4).zariskiTopology)
      {p : Projectivization ℂ (Fin 5 → ℂ) |
        MvPolynomial.eval p.rep extensionQuadric = 0 ∧
        MvPolynomial.eval p.rep (extensionCubic g₂ g₃) = 0 ∧
        (p.rep 0 ≠ 0 ∨ p.rep 2 ≠ 0)} := by
  letI := TopologicalSpace.induced (fun (p : Projectivization ℂ (Fin 5 → ℂ)) =>
    (fun _ => p : (projectiveSpace ℂ 4).Point)) (projectiveSpace ℂ 4).zariskiTopology
  have hq : extensionQuadric.IsHomogeneous 2 := by
    exact ((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X ℂ 4)).sub
      ((MvPolynomial.isHomogeneous_X ℂ 2).mul (MvPolynomial.isHomogeneous_X ℂ 3)) |>.sub
        (MvPolynomial.isHomogeneous_C_mul_X_pow 2 1 2)
  have hc : (extensionCubic g₂ g₃).IsHomogeneous 3 := by
    exact (((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X_pow 2 2)).sub
      (MvPolynomial.isHomogeneous_C_mul_X_pow 4 1 3)).add
        ((MvPolynomial.isHomogeneous_C_mul_X_pow g₂ 0 2).mul
          (MvPolynomial.isHomogeneous_X ℂ 1)) |>.add
        (MvPolynomial.isHomogeneous_C_mul_X_pow g₃ 0 3)
  convert
    ((projective_isClosed_zero hq).inter (projective_isClosed_zero hc)).isLocallyClosed.inter
      ((projective_isOpen_coordinate (K := ℂ) (0 : Fin 5)).union
        (projective_isOpen_coordinate (K := ℂ) (2 : Fin 5))).isLocallyClosed using 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, and_assoc]

theorem projective_extension_fiber_action_regular (g₂ g₃ u : ℂ)
    (F : ProjectiveExtensionFiberModel g₂ g₃) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun p : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => extensionProjectivePoint p)
      (fun p => fun _ => extensionProjectivePoint (F.action u p)) := by
  let P : Fin 5 → MvPolynomial (Fin 5) ℂ :=
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
      MvPolynomial.X 3 + MvPolynomial.C u * MvPolynomial.X 0,
      MvPolynomial.X 4 + MvPolynomial.C u * MvPolynomial.X 2]
  apply projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact MvPolynomial.isHomogeneous_X ℂ 2
    · exact (MvPolynomial.isHomogeneous_X ℂ 3).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 0))
    · exact (MvPolynomial.isHomogeneous_X ℂ 4).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 2))
  · intro p
    have heq : (fun j => MvPolynomial.eval (extensionProjectivePoint p).rep (P j)) =
        extensionFiberShear u (extensionProjectivePoint p).rep := by
      ext j
      fin_cases j <;> simp [P, extensionFiberShear]
    obtain ⟨h, hh⟩ := F.action_coords u p
    exact ⟨by simpa only [heq] using h, by simpa only [heq] using hh.symm⟩

end WeierstrassEllipticZeta
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
-- Reused implementation: Solutions.PhilipponAnalyticUnitOrder

set_option autoImplicit false
open scoped Topology BigOperators ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity
variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- Multiplication preserves a vanishing finite jet. -/
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

theorem jetOrder_congr {f g : E → K} {x : E} (h : f =ᶠ[𝓝 x] g) :
    jetOrder f x = jetOrder g x := by
  unfold jetOrder
  congr 3
  ext n
  rw [(h.iteratedFDeriv K n).eq_of_nhds]

/-- An analytic unit does not change the order defined by iterated Fréchet derivatives. -/
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

private theorem PhilipponProjectiveContact_coordinate_ratio {K : Type*} [Field K] {ι : Type*}
    {f g : ι → K} {hf : f ≠ 0} {hg : g ≠ 0}
    (h : Projectivization.mk K f hf = Projectivization.mk K g hg)
    (j : ι) (hj : g j ≠ 0) :
    f j / g j ≠ 0 ∧ ∀ k, f k = (f j / g j) * g k := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K f g hf hg).mp h
  have hj' : f j = (a : K) * g j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  have hratio : f j / g j = (a : K) := by rw [hj']; exact mul_div_cancel_right₀ _ hj
  rw [hratio]
  refine ⟨a.ne_zero, ?_⟩
  intro k
  simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm

/-- Locally equal projective lifts change a multihomogeneous pullback by an analytic unit. -/
theorem MultiProjectiveSpace.jetOrder_eq_of_projective_lifts
    {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (f g : E → M.Variable → K) (x : E)
    (hf : ∀ v, AnalyticAt K (fun z => f z v) x)
    (hg : ∀ v, AnalyticAt K (fun z => g z v) x)
    (hrep : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i, j⟩) ≠ 0,
      ∃ hgi : (fun j => g z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) hfi =
          Projectivization.mk K (fun j => g z ⟨i, j⟩) hgi) :
    jetOrder (fun z => MvPolynomial.eval (f z) P) x = jetOrder (fun z => MvPolynomial.eval (g z) P) x := by
  classical
  have hpivot (i : M.FactorIndex) : ∃ j, g x ⟨i, j⟩ ≠ 0 := by
    obtain ⟨_, hgi, _⟩ := hrep.self_of_nhds i
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hgi
  choose j hj using hpivot
  let a (z : E) (i : M.FactorIndex) := f z ⟨i, j i⟩ / g z ⟨i, j i⟩
  let u (z : E) := ∏ i, a z i ^ D i
  have ha (i : M.FactorIndex) : AnalyticAt K (fun z => a z i) x :=
    (hf _).div (hg _) (hj i)
  have hu : AnalyticAt K u x := by
    exact Finset.analyticAt_fun_prod _ (fun i _ => (ha i).pow (D i))
  have hax (i : M.FactorIndex) : a x i ≠ 0 := by
    obtain ⟨hfi, hgi, heq⟩ := hrep.self_of_nhds i
    exact (PhilipponProjectiveContact_coordinate_ratio heq (j i) (hj i)).1
  have hux : u x ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hax i))
  have hjnear : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex, g z ⟨i, j i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (hg _).continuousAt.eventually_ne (hj i)
  have hfg : (fun z => MvPolynomial.eval (f z) P) =ᶠ[𝓝 x]
      (fun z => u z * MvPolynomial.eval (g z) P) := by
    filter_upwards [hrep, hjnear] with z hz hjz
    have hcoords : f z = fun v => a z v.1 * g z v := by
      funext v
      obtain ⟨hfi, hgi, heq⟩ := hz v.1
      exact (PhilipponProjectiveContact_coordinate_ratio heq (j v.1) (hjz v.1)).2 v.2
    rw [hcoords, M.eval_block_scale P D hP]
  have hgP : AnalyticAt K (fun z => MvPolynomial.eval (g z) P) x := by
    change AnalyticAt K (fun z => aeval (g z) P) x
    exact AnalyticAt.aeval_mvPolynomial hg P
  exact (jetOrder_congr hfg).trans (jetOrder_mul_unit hgP hu hux)

private theorem PhilipponProjectiveContact_completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact PhilipponProjectiveContact_completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact PhilipponProjectiveContact_completeSpace_of_isometric_ringEquiv e he

/-- The independence assertion in Philippon's definition of contact order, p. 358. -/
theorem projective_lift_contact_invariance
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g : G.Point) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : IsMultihomogeneousOfDegree G P D)
    (f : A.ParameterSpace → G.ambient.Variable → K)
    (hf : ∀ v, AnalyticAt K (fun z => f z v) 0)
    (hrep : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      ∀ i : G.FactorIndex, ∃ h : (fun j => f z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) h =
          G.embedding (g + A.map ⟨z, hz⟩) i) :
    vanishingOrder A P g = sInf ((fun n : ℕ => (n : WithTop ℕ)) ''
      {n | iteratedFDeriv K n (fun z => MvPolynomial.eval (f z) P) 0 ≠ 0}) := by
  letI : CompleteSpace K := hK.completeSpace
  apply G.ambient.jetOrder_eq_of_projective_lifts P D hP
    (A.lift g) f 0 (A.lift_analytic g) hf
  filter_upwards [A.lift_represents g, hrep] with z hz hfz
  obtain ⟨hz, hAz⟩ := hz
  obtain ⟨hfz, hFz⟩ := hfz
  intro i
  obtain ⟨hA, heqA⟩ := hAz i
  obtain ⟨hF, heqF⟩ := hFz i
  exact ⟨hA, hF, heqA.trans heqF.symm⟩

end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponAnalyticContainment

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

/-- Containment forces every defining equation to have zero first derivative along A. -/
theorem analyticCodimension_eq_zero_of_carrier_subset
    {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hsub : A.carrier ⊆ H.carrier) : analyticCodimension A H.carrier = 0 := by
  have hker : A.tangentKernel H.carrier = ⊤ := by
    apply top_unique
    intro t _
    apply (Submodule.mem_iInf _).mpr
    intro P
    have hpull : A.pullback P.val 0 =ᶠ[𝓝 0] (fun _ => (0 : K)) := by
      filter_upwards [A.lift_represents 0] with z hz
      obtain ⟨hz, hlift⟩ := hz
      have hmem : A.map ⟨z, hz⟩ ∈ H.carrier :=
        hsub (AddSubgroup.subset_closure ⟨⟨z, hz⟩, rfl⟩)
      apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding hmem) (A.lift 0 z) _ P.property
      intro i
      obtain ⟨h, he⟩ := hlift i
      exact ⟨h, by simpa only [zero_add] using he⟩
    change fderiv K (A.pullback P.val 0) 0 t = 0
    rw [hpull.fderiv_eq]
    simp
  unfold analyticCodimension
  rw [hker, finrank_top]
  simp [AnalyticSubgroup.ParameterSpace]

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

theorem AlgebraicSubgroup.mem_of_homogeneous_equations
    {K : Type*} [Field K] {G : EmbeddedGroupProduct K}
    (H : AlgebraicSubgroup G) (x : G.Point)
    (hx : ∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
      G.ambient.IsHomogeneous P D →
      (∀ y ∈ H.carrier, G.ambient.eval P (G.embedding y) = 0) →
      G.ambient.eval P (G.embedding x) = 0) : x ∈ H.carrier := by
  letI := G.ambient.zariskiTopology
  letI := G.zariskiTopology
  have hcl : @closure _ G.zariskiTopology H.carrier =
      G.embedding ⁻¹' G.ambient.zeroLocus (G.vanishingIdeal H.carrier) := by
    ext y
    rw [EmbeddedGroupProduct.zariskiTopology, closure_induced,
      ← G.ambient.zeroLocus_vanishingIdeal_eq_closure]
    rfl
  have hclosed : closure H.carrier = H.carrier := H.isClosed.closure_eq
  rw [← hclosed, hcl]
  intro P hP
  have hideal : G.vanishingIdeal H.carrier ≤
      RingHom.ker (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hQ⟩
    exact hx Q D hD (fun y hy => hQ _ ⟨y, hy, rfl⟩)
  exact hideal hP

/-- Closed algebraic subgroups pull back to linear subspaces under additive
parametrizations with affine-linear projective coordinates, in characteristic zero. -/
theorem AlgebraicSubgroup.smul_mem_of_affine_linear_lift
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {G : EmbeddedGroupProduct K} (H : AlgebraicSubgroup G)
    (q : V →+ G.Point) (b : G.ambient.Variable → K)
    (ell : G.ambient.Variable → V →ₗ[K] K)
    (hrep : ∀ v : V, ∀ i : G.FactorIndex,
      ∃ h : (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) ≠ 0,
        Projectivization.mk K (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) h =
          G.embedding (q v) i)
    (v : V) (hv : q v ∈ H.carrier) (c : K) : q (c • v) ∈ H.carrier := by
  classical
  apply H.mem_of_homogeneous_equations
  intro P D hP hzero
  let F : MvPolynomial (Fin 1) K := eval₂ C
    (fun j => C (b j) + C (ell j v) * X 0) P
  have hEval (a : K) : MvPolynomial.eval (fun _ : Fin 1 => a) F =
      MvPolynomial.eval (fun j => b j + ell j (a • v)) P := by
    dsimp only [F]
    rw [← eval_assoc]
    apply congrArg (fun w => MvPolynomial.eval w P)
    funext j
    simp [map_smul, mul_comm]
  have hF : F = 0 := by
    apply MvPolynomial.funext_set (fun _ : Fin 1 => Set.range (fun n : ℕ => (n : K)))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro w hw
    obtain ⟨n, hn⟩ := hw 0 (Set.mem_univ _)
    have hw' : w = fun _ => (n : K) := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hn.symm
    rw [hw', hEval, map_zero]
    apply (G.ambient.eval_eq_zero_iff_of_lift (G.embedding (q ((n : K) • v)))
      (fun j => b j + ell j ((n : K) • v)) (hrep _) P D hP).mpr
    apply hzero
    change q ((n : K) • v) ∈ H.toAddSubgroup
    simpa only [Nat.cast_smul_eq_nsmul K, map_nsmul] using H.toAddSubgroup.nsmul_mem hv n
  have hfinal := hEval c
  rw [hF, map_zero] at hfinal
  exact (G.ambient.eval_eq_zero_iff_of_lift (G.embedding (q (c • v)))
    (fun j => b j + ell j (c • v)) (hrep _) P D hP).mp hfinal.symm

/-- In the additive cases, the actual preimage subgroup is a vector subspace;
linearity is proved from closedness and the coordinate formulas. -/
theorem AlgebraicSubgroup.exists_linear_pullback_of_affine_linear_lift
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {G : EmbeddedGroupProduct K} (H : AlgebraicSubgroup G)
    (q : V →+ G.Point) (b : G.ambient.Variable → K)
    (ell : G.ambient.Variable → V →ₗ[K] K)
    (hrep : ∀ v : V, ∀ i : G.FactorIndex,
      ∃ h : (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) ≠ 0,
        Projectivization.mk K (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) h =
          G.embedding (q v) i) :
    ∃ W : Submodule K V, ∀ v, v ∈ W ↔ q v ∈ H.carrier := by
  refine ⟨{
    carrier := {v | q v ∈ H.carrier}
    zero_mem' := by
      change q 0 ∈ H.toAddSubgroup
      rw [map_zero]
      exact H.toAddSubgroup.zero_mem
    add_mem' := ?_
    smul_mem' := ?_
  }, fun _ => Iff.rfl⟩
  · intro v w hv hw
    change q (v + w) ∈ H.toAddSubgroup
    rw [map_add]
    exact H.toAddSubgroup.add_mem hv hw
  · intro c v hv
    exact H.smul_mem_of_affine_linear_lift q b ell hrep v hv c

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
-- Reused implementation: Solutions.PhilipponAlgebraicSubgroupClosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
open Set
open scoped Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

theorem EmbeddedGroupProduct.zariski_separatelyContinuousAdd (G : EmbeddedGroupProduct K) :
    @SeparatelyContinuousAdd G.Point G.zariskiTopology _ := by
  let := G.zariskiTopology
  have hc (a : G.Point) : Continuous (fun x : G.Point => x + a) :=
    continuous_induced_rng.mpr (G.translation_regular a).continuous
  exact
    { continuous_add_const := hc _
      continuous_const_add := by intro a; simpa only [add_comm a] using hc a }

theorem EmbeddedGroupProduct.zariski_continuousNeg (G : EmbeddedGroupProduct K) :
    @ContinuousNeg G.Point G.zariskiTopology _ := by
  let := G.zariskiTopology
  exact ⟨continuous_induced_rng.mpr G.negation_regular.continuous⟩

/-- The Zariski closure of an actual additive subgroup is again an algebraic
subgroup. Only separate continuity is used; a product Zariski topology is not
silently replaced with the ordinary product of topological spaces. -/
def EmbeddedGroupProduct.algebraicClosure (G : EmbeddedGroupProduct K)
    (A : AddSubgroup G.Point) : AlgebraicSubgroup G := by
  let := G.zariskiTopology
  let := G.zariski_separatelyContinuousAdd
  let := G.zariski_continuousNeg
  have hright (x : G.Point) (hx : x ∈ closure (A : Set G.Point)) (y : G.Point) (hy : y ∈ A) :
      x + y ∈ closure (A : Set G.Point) := by
    have h := image_closure_subset_closure_image (continuous_add_const y)
      (s := (A : Set G.Point))
    apply closure_mono (t := (A : Set G.Point)) ?_ (h ⟨x, hx, rfl⟩)
    rintro _ ⟨z, hz, rfl⟩
    exact A.add_mem hz hy
  refine
    { toAddSubgroup :=
        { carrier := closure (A : Set G.Point)
          zero_mem' := subset_closure A.zero_mem
          add_mem' := ?_
          neg_mem' := ?_ }
      isClosed := isClosed_closure }
  · intro x y hx hy
    have h := image_closure_subset_closure_image (continuous_const_add x)
      (s := (A : Set G.Point))
    apply closure_minimal ?_ isClosed_closure (h ⟨y, hy, rfl⟩)
    rintro _ ⟨z, hz, rfl⟩
    exact hright x hx z hz
  · intro x hx
    have h := image_closure_subset_closure_image (continuous_neg (G := G.Point))
      (s := (A : Set G.Point))
    apply closure_mono (t := (A : Set G.Point)) ?_ (h ⟨x, hx, rfl⟩)
    rintro _ ⟨z, hz, rfl⟩
    exact A.neg_mem hz

theorem EmbeddedGroupProduct.algebraicClosure_le (G : EmbeddedGroupProduct K)
    (A : AddSubgroup G.Point) (H : AlgebraicSubgroup G) (hAH : A ≤ H.toAddSubgroup) :
    (G.algebraicClosure A).toAddSubgroup ≤ H.toAddSubgroup := by
  let := G.zariskiTopology
  exact closure_minimal hAH H.isClosed

/-- A finite-index closed subgroup of a connected algebraic group is the
whole group. The separate algebraic finiteness input is explicit. -/
theorem AlgebraicSubgroup.eq_top_of_connected_finite_quotient
    {G : EmbeddedGroupProduct K} (H : AlgebraicSubgroup G) (hH : H.IsConnected)
    (J : AddSubgroup H.toAddSubgroup)
    (hJ : @IsClosed _ (TopologicalSpace.induced Subtype.val G.zariskiTopology) (J : Set H.toAddSubgroup))
    [Finite (H.toAddSubgroup ⧸ J)] : J = ⊤ := by
  let := G.zariskiTopology
  let := G.zariski_separatelyContinuousAdd
  let := G.zariski_continuousNeg
  let : SeparatelyContinuousAdd H.toAddSubgroup :=
    separatelyContinuousAdd_induced H.toAddSubgroup.subtype
  let : ConnectedSpace H.toAddSubgroup := isConnected_iff_connectedSpace.mp hH
  let : T1Space (H.toAddSubgroup ⧸ J) := QuotientAddGroup.t1Space_iff.mpr hJ
  have hopen : IsOpen (J : Set H.toAddSubgroup) := QuotientAddGroup.discreteTopology_iff.mp inferInstance
  apply SetLike.coe_injective
  exact (show IsClopen (J : Set H.toAddSubgroup) from ⟨hJ, hopen⟩).eq_univ ⟨0, J.zero_mem⟩

end PhilipponMultiplicity
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

/-- The genuine multigraded quotient Hilbert function of a projective point is one. -/
theorem hilbertFunction_singleton (p : M.Point) (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal {p}) D = 1 := by
  classical
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let I := M.vanishingIdeal {p}
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := (aeval (M.coordinate p) : M.CoordinateRing →ₐ[K] K).toLinearMap.domRestrict V
  have hker : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ M.eval P.val p = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h
      exact M.eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_singleton p)
    · intro h
      apply Ideal.subset_span
      refine ⟨⟨D, (M.degreePiece_iff P.val D).mp P.property⟩, ?_⟩
      rintro x rfl
      exact h
  obtain ⟨Q, hQ, hQp⟩ := M.exists_form_nonzero_at p D
  have hQg : Q ∈ V := (M.degreePiece_iff Q D).mpr hQ
  have hg : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr (by
    intro c
    refine ⟨⟨(c / M.eval Q p) • Q, V.smul_mem _ hQg⟩, ?_⟩
    change MvPolynomial.eval (M.coordinate p) ((c / M.eval Q p) • Q) = c
    rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
    change (c / M.eval Q p) * M.eval Q p = c
    exact div_mul_cancel₀ _ hQp)
  let E := f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange)
  have hdim := E.finrank_eq
  have hf : LinearMap.range f = Hilbert.quotientPiece K M.factorCount M.ambientDimension I D := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  rw [hf, hg, finrank_top, Module.finrank_self] at hdim
  exact hdim

theorem hilbertPolynomial_singleton (p : M.Point) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal {p}) = 1 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, ?_⟩
  intro D _
  rw [M.hilbertFunction_singleton]
  simp

theorem degreeValue_singleton (p : M.Point) (D : M.FactorIndex → ℕ) :
    Hilbert.degreeValue K M.factorCount M.ambientDimension (M.vanishingIdeal {p}) D = 1 := by
  simp [Hilbert.degreeValue, Hilbert.degreeForm, M.hilbertPolynomial_singleton]

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
theorem hilbertDegreeForm_singleton {K : Type*} [Field K]
    (G : EmbeddedGroupProduct K) (x : G.Point) (D : G.FactorIndex → ℕ) :
    hilbertDegreeForm G {x} D = 1 := by
  unfold hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
  rw [Set.image_singleton]
  exact_mod_cast G.ambient.degreeValue_singleton (G.embedding x) D
end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponProjectiveNullstellensatz

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

theorem isClosed_zeroLocus (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus I) := by
  letI := M.zariskiTopology
  have heq : M.zeroLocus I = M.zeroLocus (M.vanishingIdeal (M.zeroLocus I)) := by
    apply Set.Subset.antisymm
    · exact fun x hx P hP => M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact fun x hx P hP => hx P (M.homogeneousIdeal_le_vanishingIdeal_zeroLocus I hI hP)
  rw [heq]
  exact M.isClosed_zeroLocus_vanishingIdeal _

/-- Multiprojective Nullstellensatz for relevant homogeneous prime ideals.
An affine zero with a zero coordinate block is killed by the product of one
variable per block; on all other affine zeros, projectivization applies. -/
theorem vanishingIdeal_zeroLocus_of_relevant_prime [IsAlgClosed K]
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    M.vanishingIdeal (M.zeroLocus q) = q := by
  classical
  letI := hq
  apply le_antisymm ?_ (M.homogeneousIdeal_le_vanishingIdeal_zeroLocus q hhom)
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  have hx (i : M.FactorIndex) : ∃ j : Fin (M.ambientDimension i + 1), X ⟨i,j⟩ ∉ q := by
    by_contra! h
    apply hrel
    apply (iInf_le (Hilbert.blockIdeal K M.factorCount M.ambientDimension) i).trans
    rw [Hilbert.blockIdeal, Ideal.span_le]
    rintro _ ⟨j,rfl⟩
    exact h j
  choose j hj using hx
  let F : M.CoordinateRing := ∏ i, X ⟨i,j i⟩
  have hF : F ∉ q := by
    intro h
    obtain ⟨i,_,hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hj i hi
  have hPF : P * F ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K q) := by
    intro v hv
    change MvPolynomial.eval v (P * F) = 0
    rw [map_mul]
    by_cases hb : ∀ i : M.FactorIndex, (fun k => v ⟨i,k⟩) ≠ 0
    · apply mul_eq_zero.mpr
      left
      let x : M.Point := fun i => Projectivization.mk K (fun k => v ⟨i,k⟩) (hb i)
      have hrep : ∀ i, ∃ h : (fun k => v ⟨i,k⟩) ≠ 0,
          Projectivization.mk K (fun k => v ⟨i,k⟩) h = x i := fun i => ⟨hb i,rfl⟩
      have hxq : x ∈ M.zeroLocus q := by
        apply (M.mem_zeroLocus_iff_homogeneous q hhom x).mpr
        intro Q hQ E hE
        exact (M.eval_eq_zero_iff_of_lift x v hrep Q E hE).mp (hv Q hQ)
      exact (M.eval_eq_zero_iff_of_lift x v hrep P D hD).mpr (hP x hxq)
    · apply mul_eq_zero.mpr
      right
      push Not at hb
      obtain ⟨i,hi⟩ := hb
      change MvPolynomial.eval v (∏ k, X ⟨k,j k⟩) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simpa only [eval_X, Pi.zero_apply] using congrFun hi (j i)
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hPF
  exact (hq.mem_or_mem hPF).resolve_right hF

theorem zeroLocus_nonempty_of_relevant_prime [IsAlgClosed K]
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    (M.zeroLocus q).Nonempty := by
  by_contra h
  have h1 : (1 : M.CoordinateRing) ∈ M.vanishingIdeal (M.zeroLocus q) :=
    Ideal.subset_span ⟨⟨0,M.isHomogeneous_one⟩,fun x hx => (h ⟨x,hx⟩).elim⟩
  rw [M.vanishingIdeal_zeroLocus_of_relevant_prime q hq hhom hrel] at h1
  exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q h1 isUnit_one)

theorem zeroLocus_irreducible_of_relevant_prime [IsAlgClosed K]
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    @IsIrreducible _ M.zariskiTopology (M.zeroLocus q) := by
  classical
  letI := M.zariskiTopology
  refine ⟨M.zeroLocus_nonempty_of_relevant_prime q hq hhom hrel,?_⟩
  intro U V hU hV ⟨x,hx,hxU⟩ ⟨y,hy,hyV⟩
  obtain ⟨B,hB,hxB,hBU⟩ := M.isTopologicalBasis_basic.mem_nhds_iff.mp (hU.mem_nhds hxU)
  obtain ⟨C,hC,hyC,hCV⟩ := M.isTopologicalBasis_basic.mem_nhds_iff.mp (hV.mem_nhds hyV)
  obtain ⟨P,D,hP,rfl⟩ := hB
  obtain ⟨Q,E,hQ,rfl⟩ := hC
  have hPq : P ∉ q := fun h => hxB (hx P h)
  have hQq : Q ∉ q := fun h => hyC (hy Q h)
  have hPQq : P * Q ∉ q := fun h => (hq.mem_or_mem h).elim hPq hQq
  have hex : ∃ z ∈ M.zeroLocus q, M.eval (P * Q) z ≠ 0 := by
    by_contra! h
    apply hPQq
    rw [← M.vanishingIdeal_zeroLocus_of_relevant_prime q hq hhom hrel]
    exact Ideal.subset_span ⟨⟨D+E,hP.mul M hQ⟩,h⟩
  obtain ⟨z,hz,hzPQ⟩ := hex
  have hzPQ' : M.eval P z ≠ 0 ∧ M.eval Q z ≠ 0 := by
    simpa only [eval,map_mul,mul_ne_zero_iff] using hzPQ
  exact ⟨z,hz,hBU hzPQ'.1,hCV hzPQ'.2⟩

/-- A locally closed set meeting a prime component is dense in that component
when its closure contains the component. This is the restriction needed for G. -/
theorem vanishingIdeal_inter_zeroLocus_of_relevant_prime [IsAlgClosed K]
    (S : Set M.Point) (hS : @IsLocallyClosed _ M.zariskiTopology S)
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
    (hSq : M.vanishingIdeal S ≤ q) (hne : (S ∩ M.zeroLocus q).Nonempty) :
    M.vanishingIdeal (S ∩ M.zeroLocus q) = q := by
  letI := M.zariskiTopology
  have hzcl : M.zeroLocus q ⊆ closure S := by
    rw [← M.zeroLocus_vanishingIdeal_eq_closure]
    exact fun x hx P hP => hx P (hSq hP)
  have hinter : M.zeroLocus q ∩ coborder S = S ∩ M.zeroLocus q := by
    ext x
    constructor
    · rintro ⟨hx,hxc⟩
      exact ⟨(closure_inter_coborder (s := S) ▸ ⟨hzcl hx,hxc⟩),hx⟩
    · rintro ⟨hxS,hx⟩
      exact ⟨hx,subset_coborder hxS⟩
  have hdense : M.zeroLocus q ⊆ closure (S ∩ M.zeroLocus q) := by
    rw [← hinter]
    apply subset_closure_inter_of_isPreirreducible_of_isOpen
      (M.zeroLocus_irreducible_of_relevant_prime q hq hhom hrel).2 hS.isOpen_coborder
    rwa [hinter]
  apply le_antisymm
  · conv_rhs => rw [← M.vanishingIdeal_zeroLocus_of_relevant_prime q hq hhom hrel]
    apply Ideal.span_le.mpr
    rintro P ⟨⟨D,hD⟩,hP⟩
    exact Ideal.subset_span ⟨⟨D,hD⟩, fun x hx =>
      (closure_minimal hP (M.isClosed_zero P D hD)) (hdense hx)⟩
  · conv_lhs => rw [← M.vanishingIdeal_zeroLocus_of_relevant_prime q hq hhom hrel]
    exact M.vanishingIdeal_antitone Set.inter_subset_right

end PhilipponMultiplicity.MultiProjectiveSpace

end
end


section
-- Reused implementation: Solutions.PhilipponStandardMonomials

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
end


section
-- Reused implementation: Solutions.PhilipponMonomialCells

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
end


section
-- Reused implementation: Solutions.PhilipponMonomialPartition

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
end


section
-- Reused implementation: Solutions.PhilipponProductDegree

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
end


section
-- Reused implementation: Solutions.PhilipponBinomialPolynomial

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
end


section
-- Reused implementation: Solutions.PhilipponHilbertFoundations

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

/-- A constructive Hilbert polynomial with its actual leading-coefficient data.
The proof applies to every homogeneous ideal, including nonreduced ideals. -/
theorem multigraded_hilbert_foundations
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    ∃ F, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I F ∧
      (∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) ∧
      (∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) →
        coeff b (homogeneousComponent F.totalDegree F) = 0) := by
  classical
  obtain ⟨s, hs⟩ := multigraded_hilbert_function_standard_monomials K M I hI
  obtain ⟨B, hB⟩ := MonomialCells.exists_bound M.factorCount M.ambientDimension s
  let J := MonomialCells.Active M.factorCount M.ambientDimension s B
  let q (b : J) (i : M.FactorIndex) := Nat.card (MonomialCells.Free B (b.val.val i)) - 1
  let a (b : J) (i : M.FactorIndex) := ∑ j, (b.val.val i j : ℕ)
  let F := ∑ b : J, BinomialPolynomial.product (q b) (a b)
  have hq (b : J) (i : M.FactorIndex) : q b i ≤ M.ambientDimension i := by
    have h := Nat.card_le_card_of_injective
      (fun x : MonomialCells.Free B (b.val.val i) => x.val) Subtype.val_injective
    rw [Nat.card_fin] at h
    dsimp [q]
    omega
  have ht := BinomialPolynomial.sum_top_coefficients q a M.ambientDimension hq
  refine ⟨F, ?_, ht⟩
  refine ⟨fun i => (M.ambientDimension i + 1) * B + 1, ?_⟩
  intro d hd
  have hd' (i : M.FactorIndex) : (M.ambientDimension i + 1) * B < d i := by
    exact Nat.lt_of_succ_le (hd i)
  have ha (b : J) (i : M.FactorIndex) : a b i ≤ d i :=
    (MonomialCells.pattern_sum_bound M.factorCount M.ambientDimension B b.val.val i).trans
      (hd' i).le
  change eval (fun i => (d i : ℚ)) (∑ b : J, BinomialPolynomial.product (q b) (a b)) = _
  rw [map_sum, hs d, MonomialCells.eventual_partition_count
    M.factorCount M.ambientDimension s B hB d hd', Nat.cast_sum]
  exact Finset.sum_congr rfl (fun b _ => BinomialPolynomial.product_eval (q b) (a b) d (ha b))

theorem multigraded_hilbert_polynomial_exists
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    ∃ F, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I F := by
  obtain ⟨F, hF, _⟩ := multigraded_hilbert_foundations K M I hI
  exact ⟨F, hF⟩

theorem multigraded_hilbert_polynomial_top_coefficients
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    (∀ b, 0 ≤ coeff b (homogeneousComponent
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I))) ∧
    (∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) →
      coeff b (homogeneousComponent
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I)) = 0) := by
  obtain ⟨F, hF, htop⟩ := multigraded_hilbert_foundations K M I hI
  rw [Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial K M.factorCount M.ambientDimension I hF]
  exact htop

end PhilipponMultiplicity

end
end


section
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

theorem projective_hilbert_polynomial_exists
    (K : Type*) [Field K] (N : ℕ) (V : ProjectiveSubvariety K N) :
    ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => N)
      ((projectiveSpace K N).vanishingIdeal V.carrierInSingleFactor) P := by
  exact multigraded_hilbert_polynomial_exists K (projectiveSpace K N) _
    (vanishingIdeal_multihomogeneous K (projectiveSpace K N) V.carrierInSingleFactor)

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponHomogeneousPrimary

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.PrimarySupport

variable {R S : Type*} [CommRing R] [CommRing S]

theorem primary_bot_of_injective (f : R →+* S) (hf : Function.Injective f)
    (h : (⊥ : Ideal S).IsPrimary) : (⊥ : Ideal R).IsPrimary := by
  have heq : (⊥ : Ideal S).comap f = ⊥ := by
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact map_eq_zero_iff f hf
  rw [← heq]
  exact h.comap f

theorem primary_bot_quotient (Q : Ideal R) (hQ : Q.IsPrimary) :
    (⊥ : Ideal (R ⧸ Q)).IsPrimary := by
  haveI : Nontrivial (R ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  refine Ideal.isPrimary_iff.mpr ⟨bot_ne_top, ?_⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hab : a * b ∈ Q := by
    simpa only [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] using hxy
  rcases (Ideal.isPrimary_iff.mp hQ).2 hab with ha | hb
  · left
    simpa only [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] using ha
  · right
    obtain ⟨n, hn⟩ := hb
    exact ⟨n, by simpa only [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] using hn⟩

/-- McCoy's theorem makes zero-primaryness stable under adjoining one variable. -/
theorem primary_bot_polynomial (hR : (⊥ : Ideal R).IsPrimary) :
    (⊥ : Ideal (Polynomial R)).IsPrimary := by
  haveI : Nontrivial R := nontrivial_of_ne (x := (0 : R)) (y := 1) (by
    intro h
    exact (Ideal.ne_top_iff_one _).mp hR.ne_top h.symm)
  refine Ideal.isPrimary_iff.mpr ⟨bot_ne_top, ?_⟩
  intro P Q hPQ
  by_cases hP : P = 0
  · exact Or.inl hP
  right
  have hQ : Q ∉ nonZeroDivisors (Polynomial R) := by
    intro hQ
    exact hP (hQ.2 P hPQ)
  obtain ⟨a, ha, h⟩ := Polynomial.notMem_nonZeroDivisors_iff.mp hQ
  have hnil : IsNilpotent Q := by
    apply Polynomial.isNilpotent_iff.mpr
    intro i
    have hzero : a * Q.coeff i = 0 := by
      simpa only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_zero] using
        congrArg (fun f : Polynomial R => f.coeff i) h
    have hm := ((Ideal.isPrimary_iff.mp hR).2 hzero).resolve_left ha
    exact hm
  exact hnil

/-- Polynomial extension in finitely many variables preserves a primary zero ideal. -/
theorem primary_bot_mvPolynomial {σ : Type*} [Finite σ]
    (hR : (⊥ : Ideal R).IsPrimary) : (⊥ : Ideal (MvPolynomial σ R)).IsPrimary := by
  classical
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ
  · intro α β _ e ih
    exact primary_bot_of_injective (MvPolynomial.renameEquiv R e.symm).toRingHom
      (MvPolynomial.renameEquiv R e.symm).injective ih
  · exact primary_bot_of_injective (MvPolynomial.isEmptyRingEquiv R PEmpty).toRingHom
      (MvPolynomial.isEmptyRingEquiv R PEmpty).injective hR
  · intro α _ ih
    exact primary_bot_of_injective (MvPolynomial.optionEquivLeft R α).toRingHom
      (MvPolynomial.optionEquivLeft R α).injective (primary_bot_polynomial ih)

open MvPolynomial
open Finsupp (weight weight_apply)
variable {σ τ : Type*} {K : Type*} [CommRing K]

/-- The coefficient of the auxiliary monomial of degree `d` is the actual
weighted homogeneous component of degree `d`. -/
def degreeTag (w : σ → (τ →₀ ℕ)) :
    MvPolynomial σ K →+* MvPolynomial τ (MvPolynomial σ K) :=
  eval₂Hom (C.comp C) (fun x => monomial (w x) (X x))

theorem degreeTag_monomial (w : σ → (τ →₀ ℕ)) (e : σ →₀ ℕ) (c : K) :
    degreeTag w (monomial e c) = monomial (weight w e) (monomial e c) := by
  classical
  simp only [degreeTag, eval₂Hom_monomial, RingHom.coe_comp, Function.comp_apply,
    monomial_pow, weight_apply, Finsupp.sum, Finsupp.prod]
  rw [← monomial_sum_prod]
  rw [monomial_eq (s := e) (a := c), C_mul_monomial]
  rfl

theorem degreeTag_coeff (w : σ → (τ →₀ ℕ)) (f : MvPolynomial σ K) (d : τ →₀ ℕ) :
    coeff d (degreeTag w f) = weightedHomogeneousComponent w d f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, coeff_add, hf, hg]
  | monomial e c =>
    rw [degreeTag_monomial, coeff_monomial]
    ext a
    simp only [coeff_weightedHomogeneousComponent, coeff_monomial]
    split_ifs <;> simp_all <;> aesop

/-- Homogeneous core expressed as the kernel of a map into a polynomial ring
with coefficients in the quotient by `Q`. -/
def weightedCore (w : σ → (τ →₀ ℕ)) (Q : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ K) :=
  RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk Q)).comp (degreeTag w))

theorem mem_weightedCore (w : σ → (τ →₀ ℕ)) (Q : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) :
    f ∈ weightedCore w Q ↔ ∀ d, weightedHomogeneousComponent w d f ∈ Q := by
  simp only [weightedCore, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
    MvPolynomial.ext_iff, coeff_map, coeff_zero, degreeTag_coeff,
    Ideal.Quotient.eq_zero_iff_mem]

theorem weightedCore_primary [Finite τ] (w : σ → (τ →₀ ℕ))
    (Q : Ideal (MvPolynomial σ K)) (hQ : Q.IsPrimary) :
    (weightedCore w Q).IsPrimary :=
  (primary_bot_mvPolynomial (σ := τ) (primary_bot_quotient Q hQ)).comap
    ((MvPolynomial.map (Ideal.Quotient.mk Q)).comp (degreeTag w))

theorem weightedCore_le (w : σ → (τ →₀ ℕ)) (Q : Ideal (MvPolynomial σ K)) :
    weightedCore w Q ≤ Q := by
  classical
  intro f hf
  have h := (mem_weightedCore w Q f).mp hf
  rw [← sum_weightedHomogeneousComponent w f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) f)]
  exact Q.sum_mem fun d _ => h d

/-- A homogeneous decomposition can be made irredundant and have distinct
radicals without losing any property closed under finite intersections. -/
theorem minimal_primary_with_property (P : Ideal R → Prop)
    (hP : ∀ s : Finset (Ideal R), (∀ J ∈ s, P J) → P (s.inf id))
    {I : Ideal R} {s : Finset (Ideal R)} (hs : s.inf id = I)
    (hsprimary : ∀ J ∈ s, J.IsPrimary) (hsP : ∀ J ∈ s, P J) :
    ∃ t : Finset (Ideal R), Submodule.IsMinimalPrimaryDecomposition I t ∧ ∀ J ∈ t, P J := by
  classical
  let t : Finset (Ideal R) :=
    (s.image fun J => s.filter fun Q => Q.radical = J.radical).image fun u => u.inf id
  have ht : t.inf id = I := by
    ext x
    simp only [t, Finset.inf_image, Submodule.mem_finsetInf, Finset.mem_filter,
      Function.comp_def, id_eq]
    rw [← hs]
    simp only [Submodule.mem_finsetInf, id_eq]
    constructor
    · intro h Q hQ
      exact h Q hQ Q ⟨hQ, rfl⟩
    · intro h J hJ Q hQ
      exact h Q hQ.1
  have htprimary : ∀ J ∈ t, J.IsPrimary := by
    intro J hJ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    apply Ideal.isPrimary_finsetInf (i := Q) (by simp [hQ])
    · intro T hT
      exact hsprimary T (Finset.mem_filter.mp hT).1
    · simp
  have htP : ∀ J ∈ t, P J := by
    intro J hJ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    exact hP _ fun T hT => hsP T (Finset.mem_filter.mp hT).1
  have htdistinct : (t : Set (Ideal R)).Pairwise
      (fun A B => (A.colon Set.univ).radical ≠ (B.colon Set.univ).radical) := by
    intro A hA B hB hne heq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hv
    have hrQ : ((s.filter fun U => U.radical = Q.radical).inf id).radical = Q.radical := by
      exact Ideal.radical_finset_inf (i := Q) (by simp [hQ]) (by simp)
    have hrT : ((s.filter fun U => U.radical = T.radical).inf id).radical = T.radical := by
      exact Ideal.radical_finset_inf (i := T) (by simp [hT]) (by simp)
    simp only [Submodule.colon_univ, hrQ, hrT] at heq
    exact hne (by simp only [heq])
  obtain ⟨u, hut, hu, humin⟩ := Submodule.decomposition_erase_inf ht
  exact ⟨u, ⟨hu, fun _ h => htprimary _ (hut h), htdistinct.mono hut, humin⟩,
    fun J hJ => htP J (hut hJ)⟩

end PhilipponMultiplicity.PrimarySupport


namespace PhilipponMultiplicity.PrimarySupport
open MvPolynomial
open Finsupp (weight weight_apply)
open Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

def blockCore (Q : Ideal M.CoordinateRing) : Ideal M.CoordinateRing :=
  weightedCore (fun x => (Finsupp.equivFunOnFinite).symm
    (blockWeight M.factorCount M.ambientDimension x)) Q

theorem blockCore_projection (f : M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    weightedHomogeneousComponent
      (fun x => (Finsupp.equivFunOnFinite).symm
        (blockWeight M.factorCount M.ambientDimension x))
      ((Finsupp.equivFunOnFinite).symm d) f =
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d f := by
  classical
  have hw (e : M.Variable →₀ ℕ) :
      weight (fun x => (Finsupp.equivFunOnFinite).symm
          (blockWeight M.factorCount M.ambientDimension x)) e =
        (Finsupp.equivFunOnFinite).symm
          (weight (blockWeight M.factorCount M.ambientDimension) e) := by
    ext i
    simp [weight_apply, Finsupp.sum, Finset.sum_apply]
  ext e
  simp only [coeff_weightedHomogeneousComponent, hw, Equiv.apply_eq_iff_eq]

theorem mem_blockCore (Q : Ideal M.CoordinateRing) (f : M.CoordinateRing) :
    f ∈ blockCore M Q ↔ ∀ d : M.FactorIndex → ℕ,
      weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d f ∈ Q := by
  rw [blockCore, mem_weightedCore]
  constructor
  · intro h d
    simpa only [blockCore_projection M] using h ((Finsupp.equivFunOnFinite).symm d)
  · intro h d
    obtain ⟨d, rfl⟩ := (Finsupp.equivFunOnFinite).symm.surjective d
    simpa only [blockCore_projection M] using h d

theorem blockCore_homogeneous (Q : Ideal M.CoordinateRing) :
    IsMultihomogeneousIdeal M (blockCore M Q) := by
  classical
  intro f hf d
  apply (mem_blockCore M Q _).mpr
  intro e
  rw [weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_mem _ f d)]
  split_ifs
  · exact (mem_blockCore M Q f).mp hf d
  · exact Q.zero_mem

theorem homogeneous_finsetInf (s : Finset (Ideal M.CoordinateRing))
    (hs : ∀ J ∈ s, IsMultihomogeneousIdeal M J) :
    IsMultihomogeneousIdeal M (s.inf id) := by
  intro f hf d
  simp only [Submodule.mem_finsetInf, id_eq] at hf ⊢
  exact fun J hJ => hs J hJ f (hf J hJ) d

theorem exists_minimal_homogeneous_primary (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    ∃ t : Finset (Ideal M.CoordinateRing),
      Submodule.IsMinimalPrimaryDecomposition I t ∧
      ∀ J ∈ t, IsMultihomogeneousIdeal M J := by
  classical
  obtain ⟨s, hs, hsprimary⟩ := Submodule.isLasker M.CoordinateRing M.CoordinateRing I
  let t := s.image (blockCore M)
  have ht : t.inf id = I := by
    apply le_antisymm
    · rw [← hs]
      apply Finset.le_inf_iff.mpr
      intro J hJ
      exact (Finset.inf_le (Finset.mem_image.mpr ⟨J, hJ, rfl⟩)).trans
        (weightedCore_le _ J)
    · apply Finset.le_inf_iff.mpr
      intro J hJ
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJ
      intro f hf
      apply (mem_blockCore M Q f).mpr
      intro d
      have hIQ : I ≤ Q := hs.symm.le.trans (Finset.inf_le hQ)
      exact hIQ (hI f hf d)
  apply minimal_primary_with_property (IsMultihomogeneousIdeal M) (homogeneous_finsetInf M) ht
  · intro J hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJ
    exact weightedCore_primary _ Q (hsprimary hQ)
  · intro J hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJ
    exact blockCore_homogeneous M Q

end PhilipponMultiplicity.PrimarySupport


namespace PhilipponMultiplicity.SectionThreeSupport
open PrimarySupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A finite minimal decomposition by actual multihomogeneous primary ideals,
over any field and including the whole-ring case with an empty family. -/
theorem exists_primaryDecomposition (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : Nonempty (PrimaryDecomposition M I) := by
  classical
  obtain ⟨s, hs, hshom⟩ := exists_minimal_homogeneous_primary M I hI
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hiInf : (⨅ i : Fin (Fintype.card s), (e i).1) = s.inf id := by
    ext f
    simp only [Submodule.mem_iInf, Submodule.mem_finsetInf, id_eq]
    constructor
    · intro h J hJ
      obtain ⟨i, hi⟩ := e.surjective ⟨J, hJ⟩
      have := h i
      simpa only [hi] using this
    · intro h i
      exact h _ (e i).2
  refine ⟨{
    count := Fintype.card s
    component := fun i => (e i).1
    primary := fun i => hs.primary (e i).2
    homogeneous := fun i => hshom _ (e i).2
    intersection_eq := hs.inf_eq.symm.trans hiInf.symm
    irredundant := ?_
    radicals_injective := ?_ }⟩
  · intro i heq
    apply hs.minimal (e i).2
    calc
      (s.erase (e i).1).inf id ≤ ⨅ j : {j : Fin (Fintype.card s) // j ≠ i},
          (e j.1).1 := by
        apply le_iInf
        intro j
        apply Finset.inf_le
        refine Finset.mem_erase.mpr ⟨?_, (e j.1).2⟩
        exact fun h => j.2 (e.injective (Subtype.ext h))
      _ = I := heq
      _ ≤ (e i).1 := hs.inf_eq.symm.le.trans (Finset.inf_le (e i).2)
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply hs.injOn I s (e i).2 (e j).2
    simpa only [Submodule.colon_univ] using hij

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponParametrizedHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Compute a genuine quotient Hilbert function through a parametrization whose
polynomial kernel agrees with the homogeneous equations of the image. -/
theorem hilbertFunction_eq_finrank_image
    {T A : Type*} [CommRing A] [Algebra K A]
    (p : T → M.Point) (φ : M.CoordinateRing →ₐ[K] A) (D : M.FactorIndex → ℕ)
    (hker : ∀ P : M.CoordinateRing, M.IsHomogeneous P D →
      (φ P = 0 ↔ ∀ t, M.eval P (p t) = 0)) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D =
      Module.finrank K ((Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        φ.toLinearMap) := by
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let I := M.vanishingIdeal (Set.range p)
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := φ.toLinearMap.domRestrict V
  have hfg : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ φ P.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hker P.val ((M.degreePiece_iff _ _).mp P.property)]
    constructor
    · intro h t
      exact M.eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_range_self t)
    · intro h
      exact Ideal.subset_span ⟨⟨D, (M.degreePiece_iff _ _).mp P.property⟩,
        by rintro x ⟨t, rfl⟩; exact h t⟩
  have hf : LinearMap.range f = V.map (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have hg : LinearMap.range g = V.map φ.toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hfg).trans g.quotKerEquivRange)).finrank_eq
  rw [hf, hg] at he
  exact he

/-- Univariate polynomial parametrizations compute the same kernel as their
projective image; arbitrary nonzero homogeneous lifts are allowed. -/
theorem hilbertFunction_eq_finrank_polynomial_image [Infinite K]
    (p : K → M.Point) (v : M.Variable → Polynomial K)
    (hrep : ∀ t i, ∃ h : (fun j => (v ⟨i, j⟩).eval t) ≠ 0,
      Projectivization.mk K (fun j => (v ⟨i, j⟩).eval t) h = p t i)
    (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D =
      Module.finrank K ((Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        (MvPolynomial.aeval v).toLinearMap) := by
  apply M.hilbertFunction_eq_finrank_image p (MvPolynomial.aeval v) D
  intro P hP
  have hev (t : K) : (MvPolynomial.aeval v P : Polynomial K).eval t =
      MvPolynomial.eval (fun j => (v j).eval t) P := by
    clear hP
    induction P using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp [hP, hQ]
    | mul_X P j hP => simp [hP]
  constructor
  · intro hz t
    apply (M.eval_eq_zero_iff_of_lift (p t) (fun j => (v j).eval t) (hrep t) P D hP).mp
    rw [← hev, hz, Polynomial.eval_zero]
  · intro hz
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_zero, hev]
    exact (M.eval_eq_zero_iff_of_lift (p t) (fun j => (v j).eval t) (hrep t) P D hP).mpr (hz t)

/-- A blockwise polynomial parametrization bounds the univariate degree of
every homogeneous section by its weighted sum of block degrees. -/
theorem polynomial_image_natDegree_le
    (v : M.Variable → Polynomial K) (δ D : M.FactorIndex → ℕ)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D) :
    (MvPolynomial.aeval v P : Polynomial K).natDegree ≤ ∑ i, D i * δ i := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  change ((Polynomial.C (MvPolynomial.coeff d P)) * _).natDegree ≤ _
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  change (d.prod (fun j n => v j ^ n)).natDegree ≤ _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ j : M.Variable, (v j ^ d j).natDegree ≤ ∑ j : M.Variable, d j * δ j.1 := by
      apply Finset.sum_le_sum
      intro j _
      exact (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hv j))
    _ = ∑ i, D i * δ i := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ y, d ⟨i, y⟩ * δ i) = _
      rw [← Finset.sum_mul, hP d hd i]

/-- A degree upper bound and lifts of the powers of X determine the full
homogeneous section image, rather than only bounding its dimension. -/
theorem polynomial_image_eq_degreeLT
    (v : M.Variable → Polynomial K) (δ D : M.FactorIndex → ℕ)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (hlift : ∀ k ≤ ∑ i, D i * δ i, ∃ P : M.CoordinateRing,
      M.IsHomogeneous P D ∧ MvPolynomial.aeval v P = Polynomial.X ^ k) :
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        (MvPolynomial.aeval v).toLinearMap =
      Polynomial.degreeLT K ((∑ i, D i * δ i) + 1) := by
  classical
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE]
    exact Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr
      (M.polynomial_image_natDegree_le v δ D hv P ((M.degreePiece_iff _ _).mp hP)))
  · rw [Polynomial.degreeLT_eq_span_X_pow, Submodule.span_le]
    intro Q hQ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨P, hP, heq⟩ := hlift k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    exact ⟨P, (M.degreePiece_iff _ _).mpr hP, heq⟩

/-- Exact Hilbert function for a polynomially parametrized projective locus
when all powers through the expected degree have homogeneous lifts. -/
theorem hilbertFunction_polynomial_parametrization [Infinite K]
    (p : K → M.Point) (v : M.Variable → Polynomial K)
    (hrep : ∀ t i, ∃ h : (fun j => (v ⟨i, j⟩).eval t) ≠ 0,
      Projectivization.mk K (fun j => (v ⟨i, j⟩).eval t) h = p t i)
    (δ D : M.FactorIndex → ℕ)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (hlift : ∀ k ≤ ∑ i, D i * δ i, ∃ P : M.CoordinateRing,
      M.IsHomogeneous P D ∧ MvPolynomial.aeval v P = Polynomial.X ^ k) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D = (∑ i, D i * δ i) + 1 := by
  rw [M.hilbertFunction_eq_finrank_polynomial_image p v hrep D,
    M.polynomial_image_eq_degreeLT v δ D hv hlift,
    (Polynomial.degreeLTEquiv K _).finrank_eq]
  simp

/-- The powers of X have homogeneous lifts for a line whose projections to
both projective factors are either constant or linear. -/
theorem binary_linear_parametrization_lifts
    (N : Fin 2 → ℕ) (v : (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).Variable →
      Polynomial K) (δ : Fin 2 → ℕ) (hδ : ∀ i, δ i ≤ 1)
    (U V : Fin 2 → (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).CoordinateRing)
    (hU : ∀ i, (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous (U i)
      (fun j => if j = i then 1 else 0))
    (hV : ∀ i, (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous (V i)
      (fun j => if j = i then 1 else 0))
    (hUeval : ∀ i, MvPolynomial.aeval v (U i) = 1)
    (hVeval : ∀ i, MvPolynomial.aeval v (V i) = Polynomial.X ^ δ i)
    (D : Fin 2 → ℕ) (k : ℕ) (hk : k ≤ ∑ i, D i * δ i) :
    ∃ P : (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).CoordinateRing,
      (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous P D ∧
        MvPolynomial.aeval v P = Polynomial.X ^ k := by
  let M : MultiProjectiveSpace K := ⟨2, by decide, N⟩
  let a := min k (D 0 * δ 0)
  let b := k - a
  have ha : a ≤ D 0 := (min_le_right _ _).trans (by simpa using Nat.mul_le_mul_left (D 0) (hδ 0))
  have hb : b ≤ D 1 := by
    have hc : b ≤ D 1 * δ 1 := by
      simp only [Fin.sum_univ_two] at hk
      dsimp [a, b]
      omega
    exact hc.trans (by simpa using Nat.mul_le_mul_left (D 1) (hδ 1))
  have hab : a + b = k := by dsimp [a, b]; omega
  have haδ : δ 0 * a = a := by
    have := hδ 0
    interval_cases h : δ 0
    · simp [a, h]
    · simp
  have hbδ : δ 1 * b = b := by
    have hc : b ≤ D 1 * δ 1 := by
      simp only [Fin.sum_univ_two] at hk
      dsimp [a, b]
      omega
    have := hδ 1
    interval_cases h : δ 1
    · have : b = 0 := by simpa [h] using hc
      simp [this]
    · simp
  let P := (V 0 ^ a * U 0 ^ (D 0 - a)) * (V 1 ^ b * U 1 ^ (D 1 - b))
  refine ⟨P, ?_, ?_⟩
  · have hp := (((hV 0).pow M a).mul M ((hU 0).pow M (D 0 - a))).mul M
      (((hV 1).pow M b).mul M ((hU 1).pow M (D 1 - b)))
    convert hp using 1
    funext i
    fin_cases i <;> simp <;> omega
  · dsimp [P]
    simp only [map_mul, map_pow, hUeval, hVeval, one_pow, mul_one, ← pow_add, ← pow_mul]
    rw [haδ, hbδ, hab]

/-- Recover the actual Hilbert polynomial of an affine line in a product of
two projective spaces from its coordinate parametrization. -/
theorem binary_linear_parametrization_hilbertPolynomial [Infinite K]
    (N : Fin 2 → ℕ) (p : K → (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).Point)
    (v : (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).Variable → Polynomial K)
    (hrep : ∀ t i, ∃ h : (fun j => (v ⟨i, j⟩).eval t) ≠ 0,
      Projectivization.mk K (fun j => (v ⟨i, j⟩).eval t) h = p t i)
    (δ : Fin 2 → ℕ) (hδ : ∀ i, δ i ≤ 1)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (U V : Fin 2 → (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).CoordinateRing)
    (hU : ∀ i, (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous (U i)
      (fun j => if j = i then 1 else 0))
    (hV : ∀ i, (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous (V i)
      (fun j => if j = i then 1 else 0))
    (hUeval : ∀ i, MvPolynomial.aeval v (U i) = 1)
    (hVeval : ∀ i, MvPolynomial.aeval v (V i) = Polynomial.X ^ δ i) :
    Hilbert.hilbertPolynomial K 2 N
      ((MultiProjectiveSpace.mk 2 (by decide) N).vanishingIdeal (Set.range p)) =
        MvPolynomial.C (δ 0 : ℚ) * MvPolynomial.X 0 +
          MvPolynomial.C (δ 1 : ℚ) * MvPolynomial.X 1 + 1 := by
  let M : MultiProjectiveSpace K := ⟨2, by decide, N⟩
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, ?_⟩
  intro D _
  rw [M.hilbertFunction_polynomial_parametrization p v hrep δ D hv
    (binary_linear_parametrization_lifts N v δ hδ U V hU hV hUeval hVeval D)]
  change _ = (((∑ i : Fin 2, D i * δ i) + 1 : ℕ) : ℚ)
  simp [Fin.sum_univ_two, mul_comm]

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] {p : ℕ} {N : Fin p → ℕ}

/-- A nonzero linear top part of a Hilbert polynomial is exactly its degree form. -/
theorem degreeForm_of_hilbertPolynomial_linear
    (I : Ideal (CoordinateRing K p N)) (R : MvPolynomial (Fin p) ℚ)
    (hR : R.IsHomogeneous 1) (hne : R ≠ 0)
    (hP : hilbertPolynomial K p N I = R + 1) :
    degreeForm K p N I = R := by
  have hd : (R + 1).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
    · exact hR.totalDegree hne
    · simp [hR.totalDegree hne]
  simp only [degreeForm, hP, hd, Nat.factorial_one, Nat.cast_one, one_smul, map_add]
  rw [MvPolynomial.homogeneousComponent_eq_self hR,
    MvPolynomial.homogeneousComponent_eq_zero 1 1 (by simp : (1 : MvPolynomial (Fin p) ℚ).totalDegree < 1), add_zero]

end PhilipponMultiplicity.Hilbert
end
end


section
-- Reused implementation: Solutions.SeparatedFunctionProducts

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace SeparatedFunctionProducts

variable {K ι : Type*} [Field K] [Fintype ι]
  {X κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- Linear independence of functions is preserved by taking products in
separate variables. The underlying sets need not be finite or nonempty. -/
theorem linearIndependent (f : ∀ i, κ i → X i → K)
    (hf : ∀ i, LinearIndependent K (f i)) :
    LinearIndependent K (fun j : ∀ i, κ i => fun x : ∀ i, X i => ∏ i, f i (j i) (x i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let L : MultilinearMap K (fun i => κ i → K) K :=
    ∑ k : ∀ i, κ i, c k •
      (MultilinearMap.mkPiRing K ι 1).compLinearMap
        (fun i => LinearMap.proj (k i))
  have hL : L = 0 := by
    apply MultilinearMap.ext_of_span_eq_top
      (fun i => span_flip_eq_top_iff_linearIndependent.mpr (hf i))
    intro x
    have h := congrFun hc x
    simpa [L, MultilinearMap.sum_apply, MultilinearMap.smul_apply,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply,
      LinearMap.proj_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      flip] using h
  have h := DFunLike.congr_fun hL (fun i => Pi.single (j i) (1 : K))
  simpa [L, MultilinearMap.sum_apply, MultilinearMap.smul_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply,
    LinearMap.proj_apply, Pi.single_apply, Fintype.prod_ite_zero,
    ← funext_iff, smul_eq_mul] using h

/-- The space spanned by separated products has dimension equal to the product
of the dimensions of the individual spaces of functions. -/
theorem finrank_span_products (W : ∀ i, Submodule K (X i → K))
    [∀ i, Module.Finite K (W i)] :
    Module.finrank K (Submodule.span K
      (Set.range (fun w : ∀ i, W i => fun x : ∀ i, X i => ∏ i, (w i).val (x i)))) =
      ∏ i, Module.finrank K (W i) := by
  classical
  let b (i : ι) := Module.finBasis K (W i)
  let μ : MultilinearMap K (fun i => W i) ((∀ i, X i) → K) :=
    MultilinearMap.pi (fun x => (MultilinearMap.mkPiRing K ι 1).compLinearMap
      (fun i => (LinearMap.proj (x i)).comp (W i).subtype))
  have hμeval (w : ∀ i, W i) : μ w = fun x => ∏ i, (w i).val (x i) := by
    ext x
    simp [μ, MultilinearMap.mkPiRing_apply]
  let S := Submodule.span K (Set.range
    (fun j : ∀ i, Fin (Module.finrank K (W i)) => μ (fun i => b i (j i))))
  have hμ (w : ∀ i, W i) : μ w ∈ S := by
    have hz : S.mkQ.compMultilinearMap μ = 0 := by
      apply Module.Basis.ext_multilinear b
      intro j
      change S.mkQ (μ (fun i => b i (j i))) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span (Set.mem_range_self j)
    have h := DFunLike.congr_fun hz w
    exact (Submodule.Quotient.mk_eq_zero S).mp h
  have hspan : Submodule.span K (Set.range
      (fun w : ∀ i, W i => fun x : ∀ i, X i => ∏ i, (w i).val (x i))) = S := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      change (fun x => ∏ i, (w i).val (x i)) ∈ S
      rw [← hμeval w]
      exact hμ w
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply Submodule.subset_span
      refine ⟨fun i => b i (j i), ?_⟩
      ext x
      simp [μ, MultilinearMap.mkPiRing_apply]
  rw [hspan]
  have hlin (i : ι) : LinearIndependent K (fun j => (b i j : X i → K)) :=
    (b i).linearIndependent.map' (W i).subtype (Submodule.ker_subtype _)
  have hprod := linearIndependent (fun i j => (b i j : X i → K)) hlin
  have hprod' : LinearIndependent K
      (fun j : ∀ i, Fin (Module.finrank K (W i)) => μ (fun i => b i (j i))) := by
    simpa only [hμeval] using hprod
  rw [show Module.finrank K S = Fintype.card (∀ i, Fin (Module.finrank K (W i)))
    from finrank_span_eq_card hprod']
  simp [Fintype.card_pi]

end SeparatedFunctionProducts

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

def evaluationMap {X : Type*} (p : X → M.Point) : M.CoordinateRing →ₐ[K] (X → K) :=
  AlgHom.pi (fun x => MvPolynomial.aeval (M.coordinate (p x)))

@[simp] theorem evaluationMap_apply {X : Type*} (p : X → M.Point)
    (P : M.CoordinateRing) (x : X) : M.evaluationMap p P x = M.eval P (p x) := rfl

def sectionSpace {X : Type*} (p : X → M.Point) (D : M.FactorIndex → ℕ) :
    Submodule K (X → K) :=
  (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
    (M.evaluationMap p).toLinearMap

instance sectionSpace_finite {X : Type*} (p : X → M.Point) (D : M.FactorIndex → ℕ) :
    Module.Finite K (M.sectionSpace p D) := by
  unfold sectionSpace
  infer_instance

theorem hilbertFunction_eq_sectionSpace {X : Type*} (p : X → M.Point)
    (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D = Module.finrank K (M.sectionSpace p D) := by
  apply M.hilbertFunction_eq_finrank_image p (M.evaluationMap p) D
  intro P _
  exact funext_iff

def includeBlock (i : M.FactorIndex) :
    (projectiveSpace K (M.ambientDimension i)).Variable → M.Variable :=
  fun v => ⟨i, v.2⟩

theorem homogeneous_includeBlock (i : M.FactorIndex)
    {P : (projectiveSpace K (M.ambientDimension i)).CoordinateRing} {d : ℕ}
    (hP : (projectiveSpace K (M.ambientDimension i)).IsHomogeneous P (fun _ => d)) :
    M.IsHomogeneous (rename (M.includeBlock i) P) (Pi.single i d) := by
  classical
  have h := hP.eval₂_blocks M (projectiveSpace K (M.ambientDimension i))
    (fun v => X (M.includeBlock i v)) (fun _ => Pi.single i 1)
    (fun v => by
      convert M.isHomogeneous_X (M.includeBlock i v) using 1
      ext j
      simp [includeBlock, Pi.single_apply])
  convert h using 1
  · rw [rename_eq_aeval]
    rfl
  · funext j
    simp [Pi.single_apply, projectiveSpace]

theorem sectionSpace_product (X : M.FactorIndex → Type*)
    (p : ∀ i, X i → Projectivization K (Fin (M.ambientDimension i + 1) → K))
    (D : M.FactorIndex → ℕ) :
    M.sectionSpace (fun x i => p i (x i)) D =
      Submodule.span K (Set.range (fun w : ∀ i,
        (projectiveSpace K (M.ambientDimension i)).sectionSpace
          (fun x _ => p i x) (fun _ => D i) =>
        fun x : ∀ i, X i => ∏ i, (w i).val (x i))) := by
  classical
  let W (i : M.FactorIndex) := (projectiveSpace K (M.ambientDimension i)).sectionSpace
    (fun x _ => p i x) (fun _ => D i)
  let S := Submodule.span K (Set.range
    (fun w : ∀ i, W i => fun x : ∀ i, X i => ∏ i, (w i).val (x i)))
  change _ = S
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    have hPD := (M.degreePiece_iff P D).mp hP
    rw [P.as_sum, map_sum]
    apply S.sum_mem
    intro a ha
    let a' (i : M.FactorIndex) : (projectiveSpace K (M.ambientDimension i)).Variable →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun v => a ⟨i, v.2⟩)
    have hmono (i : M.FactorIndex) :
        (projectiveSpace K (M.ambientDimension i)).IsHomogeneous
          (monomial (a' i) (1 : K)) (fun _ => D i) := by
      intro b hb j
      have hb' : b = a' i := Finset.mem_singleton.mp (support_monomial_subset hb)
      subst b
      simpa [a', projectiveSpace] using hPD a ha i
    let w (i : M.FactorIndex) : W i :=
      ⟨(projectiveSpace K (M.ambientDimension i)).evaluationMap (fun x _ => p i x)
          (monomial (a' i) 1),
        ⟨monomial (a' i) 1,
          ((projectiveSpace K (M.ambientDimension i)).degreePiece_iff _ _).mpr (hmono i), rfl⟩⟩
    have hw : (fun x : ∀ i, X i => ∏ i, (w i).val (x i)) ∈ S :=
      Submodule.subset_span (Set.mem_range_self w)
    convert S.smul_mem (coeff a P) hw using 1
    ext x
    change M.eval (monomial a (coeff a P)) (fun i => p i (x i)) = _
    simp only [eval, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    simp [w, evaluationMap_apply, eval, eval_monomial, a', coordinate,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma, projectiveSpace]
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    have hrep (i : M.FactorIndex) :
        ∃ Q : (projectiveSpace K (M.ambientDimension i)).CoordinateRing,
          (projectiveSpace K (M.ambientDimension i)).IsHomogeneous Q (fun _ => D i) ∧
          (projectiveSpace K (M.ambientDimension i)).evaluationMap (fun x _ => p i x) Q =
            (w i).val := by
      obtain ⟨Q, hQ, heq⟩ := (w i).property
      exact ⟨Q, ((projectiveSpace K (M.ambientDimension i)).degreePiece_iff _ _).mp hQ, heq⟩
    choose Q hQ heq using hrep
    refine ⟨∏ i, rename (M.includeBlock i) (Q i), ?_, ?_⟩
    · apply (M.degreePiece_iff _ _).mpr
      have h := M.isHomogeneous_prod Finset.univ (fun i => rename (M.includeBlock i) (Q i))
        (fun i => Pi.single i (D i)) (fun i _ => M.homogeneous_includeBlock i (hQ i))
      convert h using 1
      ext j
      simp [Pi.single_apply]
    · ext x
      change M.eval (∏ i, rename (M.includeBlock i) (Q i)) (fun i => p i (x i)) = _
      simp only [eval, map_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [← heq i]
      simp only [evaluationMap_apply, eval, eval_rename]
      congr 1

/-- Exact multiplicativity of the quotient Hilbert function for products of
projective sets, before any Hilbert-polynomial existence theorem is used. -/
theorem hilbertFunction_product (X : M.FactorIndex → Type*)
    (p : ∀ i, X i → Projectivization K (Fin (M.ambientDimension i + 1) → K))
    (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range (fun x : ∀ i, X i => fun i => p i (x i)))) D =
      ∏ i, Hilbert.hilbertFunction K 1 (fun _ => M.ambientDimension i)
        ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
          (Set.range (fun x : X i => fun _ => p i x))) (fun _ => D i) := by
  rw [M.hilbertFunction_eq_sectionSpace, M.sectionSpace_product,
    SeparatedFunctionProducts.finrank_span_products]
  apply Finset.prod_congr rfl
  intro i _
  exact ((projectiveSpace K (M.ambientDimension i)).hilbertFunction_eq_sectionSpace
    (fun x _ => p i x) (fun _ => D i)).symm

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open SectionThree

theorem product_projective_hilbert_function (K : Type*) [Field K]
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (d : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (productCarrier M V)) d =
      ∏ i, Hilbert.hilbertFunction K 1 (fun _ => M.ambientDimension i)
        ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
          (V i).carrierInSingleFactor) (fun _ => d i) := by
  have hi (i : M.FactorIndex) :
      Set.range (fun x : (V i).carrier => fun _ : Fin 1 => x.val) =
        (V i).carrierInSingleFactor := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have hp : Set.range (fun x : ∀ i, (V i).carrier => fun i => (x i).val) =
      productCarrier M V := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩ i
      exact (v i).property
    · intro h
      exact ⟨fun i => ⟨x i, h i⟩, rfl⟩
  have h := M.hilbertFunction_product
    (fun i => (V i).carrier) (fun _ x => x.val) d
  rw [hp] at h
  refine h.trans (Finset.prod_congr rfl ?_)
  intro i _
  exact congrArg (fun S => Hilbert.hilbertFunction K 1 (fun _ => M.ambientDimension i)
    ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal S) (fun _ => d i)) (hi i)

/-- Existence for the ordinary projective factors and the proved exact Hilbert
function identity determine the multigraded Hilbert polynomial of the product. -/
theorem product_projective_hilbert_polynomial_of_exists (K : Type*) [Field K]
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (hexists : ∀ i, ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => M.ambientDimension i)
      ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
        (V i).carrierInSingleFactor) P) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) =
      ∏ i, MvPolynomial.rename (fun _ : Fin 1 => i)
        (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor)) := by
  classical
  have hspec (i : M.FactorIndex) := Hilbert.hilbertPolynomial_spec
    K 1 (fun _ => M.ambientDimension i)
    ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
      (V i).carrierInSingleFactor) (hexists i)
  choose d₀ hd₀ using hspec
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun i => d₀ i 0, ?_⟩
  intro d hd
  rw [map_prod, product_projective_hilbert_function, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_rename]
  apply hd₀ i (fun _ => d i)
  intro j
  fin_cases j
  exact hd i

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponColonHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem component_mul_homogeneous
    {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (Q : M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)
      (P * Q) =
    P * weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d Q := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hP' : P ∈ weightedHomogeneousSubmodule K w D :=
    (M.degreePiece_iff P D).mpr hP
  have hh := DirectSum.coe_decompose_mul_add_of_left_mem
    (weightedHomogeneousSubmodule K w) (b := Q) (j := d) hP'
  change ((MvPolynomial.decompose' K w (P * Q)) (D + d) : M.CoordinateRing) =
    P * ((MvPolynomial.decompose' K w Q) d : M.CoordinateRing) at hh
  simpa only [MvPolynomial.decompose'_apply] using hh

instance quotientPiece_finite_colon (I : Ideal M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    Module.Finite K (quotientPiece K M.factorCount M.ambientDimension I d) := by
  unfold quotientPiece
  infer_instance

/-- Colon by a multihomogeneous element preserves the actual grading. -/
theorem homogeneous_colon (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I.colon {P}) := by
  intro Q hQ d
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hQ ⊢
  have h := hI (P * Q) (by simpa [mul_comm] using hQ) (D + d)
  rw [component_mul_homogeneous M hP Q d, mul_comm] at h
  exact h

/-- The cyclic exact sequence, with the multiplication kernel removed by
passing to the colon quotient, works without a regularity hypothesis. -/
theorem hilbertFunction_colon_add
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension
        (I ⊔ Ideal.span {P}) (D + d) +
      hilbertFunction K M.factorCount M.ambientDimension (I.colon {P}) d =
    hilbertFunction K M.factorCount M.ambientDimension I (D + d) := by
  classical
  let J := I ⊔ Ideal.span {P}
  let C := I.colon {P}
  let U := quotientPiece K M.factorCount M.ambientDimension C d
  let W := quotientPiece K M.factorCount M.ambientDimension I (D + d)
  let V := quotientPiece K M.factorCount M.ambientDimension J (D + d)
  let mulP : (M.CoordinateRing ⧸ C) →ₗ[K] (M.CoordinateRing ⧸ I) :=
    (C.restrictScalars K).liftQ
      ((Ideal.Quotient.mkₐ K I).toLinearMap.comp (LinearMap.mulLeft K P)) (by
        intro Q hQ
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        change Q ∈ I.colon {P} at hQ
        change P * Q ∈ I
        simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hQ)
  have mulP_mk (Q : M.CoordinateRing) :
      mulP (Ideal.Quotient.mk C Q) = Ideal.Quotient.mk I (P * Q) := rfl
  have mulP_inj : Function.Injective mulP := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hx)
  let f : U →ₗ[K] W :=
    (mulP.domRestrict U).codRestrict W (by
      rintro ⟨x, Q, hQ, rfl⟩
      exact ⟨P * Q, ((M.degreePiece_iff P D).mpr hP).mul hQ, rfl⟩)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact mulP_inj (congrArg Subtype.val hxy)
  let q : (M.CoordinateRing ⧸ I) →ₐ[K] (M.CoordinateRing ⧸ J) :=
    Ideal.quotientMapₐ J (AlgHom.id K M.CoordinateRing) (by
      intro x hx
      exact (le_sup_left : I ≤ J) hx)
  let g : W →ₗ[K] V :=
    (q.toLinearMap.domRestrict W).codRestrict V (by
      rintro ⟨x, Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩)
  have hsurj : Function.Surjective g := by
    rintro ⟨x, Q, hQ, rfl⟩
    exact ⟨⟨Ideal.Quotient.mk I Q, ⟨Q, hQ, rfl⟩⟩, rfl⟩
  have hker : LinearMap.ker g = LinearMap.range f := by
    ext x
    constructor
    · intro hx
      obtain ⟨Q, hQ, hQx⟩ := x.property
      have hQJ : Q ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hx' := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
        change q x.val = 0 at hx'
        rw [← hQx] at hx'
        exact hx'
      obtain ⟨a, b, hb, heq⟩ :=
        Ideal.mem_span_singleton_sup.mp (show Q ∈ Ideal.span {P} ⊔ I by
          simpa only [sup_comm] using hQJ)
      let a' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) d a
      let b' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) (D + d) b
      have hb' : b' ∈ I := hI b hb (D + d)
      have hproj : P * a' + b' = Q := by
        have hh := congrArg
          (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)) heq
        rw [map_add, mul_comm a P, component_mul_homogeneous M hP a d,
          IsWeightedHomogeneous.weightedHomogeneousComponent_same hQ] at hh
        exact hh
      refine ⟨⟨Ideal.Quotient.mk C a', ⟨a', weightedHomogeneousComponent_mem _ _ _, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      change Ideal.Quotient.mk I (P * a') = x.val
      change Ideal.Quotient.mk I Q = x.val at hQx
      rw [← hQx, ← hproj, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb', add_zero]
    · rintro ⟨y, rfl⟩
      obtain ⟨Q, hQ, hQy⟩ := y.property
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change q (mulP y.val) = 0
      rw [← hQy]
      change Ideal.Quotient.mk J (P * Q) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact J.mul_mem_right Q ((le_sup_right : Ideal.span {P} ≤ J)
        (Ideal.subset_span (Set.mem_singleton P)))
  have hdim := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
    LinearMap.finrank_range_of_inj hinj] at hdim
  exact hdim

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponPrimeFiltration

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_sup_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I ⊔ Ideal.span {P}) := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI f hf d
  have hPg : (Ideal.span {P}).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro f hf
    have heq : f = P := Set.mem_singleton_iff.mp hf
    subst f
    exact ⟨D, (M.degreePiece_iff P D).mpr hP⟩
  intro f hf d
  exact weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d

/-- The homogeneous product criterion also detects ordinary primality for
the block grading. A lexicographic order is used only to apply that criterion. -/
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

/-- A proper homogeneous quotient contains a shifted homogeneous cyclic
submodule whose annihilator is prime. This is the prime-filtration step. -/
theorem exists_homogeneous_prime_colon (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hne : I ≠ ⊤) :
    ∃ P : M.CoordinateRing, ∃ D : M.FactorIndex → ℕ,
      M.IsHomogeneous P D ∧ P ∉ I ∧ (I.colon {P}).IsPrime := by
  classical
  let S : Ideal M.CoordinateRing → Prop :=
    fun J => ∃ P D, M.IsHomogeneous P D ∧ P ∉ I ∧ J = I.colon {P}
  have hS : ∃ J, S J := by
    refine ⟨I.colon {(1 : M.CoordinateRing)}, 1, 0, ?_, ?_, rfl⟩
    · exact (M.degreePiece_iff 1 0).mp (isWeightedHomogeneous_one K _)
    · exact (Ideal.ne_top_iff_one I).mp hne
  obtain ⟨J, hJ, hmax⟩ := exists_maximal_of_wellFoundedGT S hS
  obtain ⟨P, D, hP, hPI, rfl⟩ := hJ
  refine ⟨P, D, hP, hPI, prime_of_homogeneous_products M _
    (homogeneous_colon M I hI P D hP) ?_ ?_⟩
  · simpa using hPI
  · intro A B hA hB hAB
    by_cases hBP : B * P ∈ I
    · exact Or.inr (Submodule.mem_colon_singleton.mpr hBP)
    · left
      obtain ⟨E, hB⟩ := hB
      have hBP_hom : M.IsHomogeneous (B * P) (E + D) := by
        exact (M.degreePiece_iff (B * P) (E + D)).mp
          (((M.degreePiece_iff B E).mpr hB).mul ((M.degreePiece_iff P D).mpr hP))
      have hle : I.colon {P} ≤ I.colon {B * P} := by
        intro x hx
        rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx ⊢
        simpa only [mul_left_comm] using I.mul_mem_left B hx
      have hge := hmax ⟨B * P, E + D, hBP_hom, hBP, rfl⟩ hle
      apply hge
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hAB ⊢
      simpa only [mul_assoc] using hAB

/-- A finite chain from a homogeneous ideal to the unit ideal, with each
successive quotient generated by one homogeneous element and having prime
annihilator. Thus every cyclic factor is a shifted prime quotient. -/
theorem homogeneous_prime_filtration (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    ∃ n : ℕ, ∃ J : Fin (n + 1) → Ideal M.CoordinateRing,
      ∃ P : Fin n → M.CoordinateRing, ∃ D : Fin n → M.FactorIndex → ℕ,
      J 0 = I ∧ J (Fin.last n) = ⊤ ∧
      (∀ j, IsMultihomogeneousIdeal M (J j)) ∧
      (∀ j, M.IsHomogeneous (P j) (D j) ∧ P j ∉ J j.castSucc ∧
        J j.succ = J j.castSucc ⊔ Ideal.span {P j} ∧
        ((J j.castSucc).colon {P j}).IsPrime) := by
  classical
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    by_cases htop : I = ⊤
    · subst I
      refine ⟨0, fun _ => ⊤, Fin.elim0, Fin.elim0, rfl, rfl, ?_, ?_⟩
      · intro j f hf d
        trivial
      · intro j; exact Fin.elim0 j
    · obtain ⟨P, D, hP, hPI, hprime⟩ := exists_homogeneous_prime_colon M I hI htop
      have hlt : I < I ⊔ Ideal.span {P} := by
        apply lt_of_le_of_ne le_sup_left
        intro heq
        apply hPI
        rw [heq]
        exact (le_sup_right : Ideal.span {P} ≤ I ⊔ Ideal.span {P})
          (Ideal.subset_span (Set.mem_singleton P))
      obtain ⟨n, J, Q, E, hfirst, hlast, hhom, hstep⟩ :=
        ih _ hlt (homogeneous_sup_span M I hI P D hP)
      refine ⟨n + 1, Fin.cons I J, Fin.cons P Q, Fin.cons D E, rfl, ?_, ?_, ?_⟩
      · change J (Fin.last n) = ⊤
        exact hlast
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact hI
        · exact hhom i
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero] using
            (show M.IsHomogeneous P D ∧ P ∉ I ∧ J 0 = I ⊔ Ideal.span {P} ∧
              (I.colon {P}).IsPrime from ⟨hP, hPI, hfirst, hprime⟩)
        · simpa only [Fin.cons_succ, Fin.castSucc_succ] using hstep i

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponFiltrationPolynomial

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertPolynomial_top :
    hilbertPolynomial K M.factorCount M.ambientDimension (⊤ : Ideal M.CoordinateRing) = 0 := by
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, fun d hd => ?_⟩
  simp only [map_zero, hilbertFunction]
  letI : Subsingleton (quotientPiece K M.factorCount M.ambientDimension
      (⊤ : Ideal M.CoordinateRing) d) := inferInstance
  rw [Module.finrank_zero_of_subsingleton]
  rfl

theorem hilbertPolynomial_colon_add
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    hilbertPolynomial K M.factorCount M.ambientDimension I =
      hilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) +
        aeval (fun i => X i - C (D i : ℚ))
          (hilbertPolynomial K M.factorCount M.ambientDimension (I.colon {P})) := by
  let J := I ⊔ Ideal.span {P}
  let Q := I.colon {P}
  obtain ⟨a, ha⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension J
    (multigraded_hilbert_polynomial_exists K M J (homogeneous_sup_span M I hI P D hP))
  obtain ⟨b, hb⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q (homogeneous_colon M I hI P D hP))
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨D + a + b, fun n hn => ?_⟩
  have hDn : ∀ i, D i ≤ n i := by intro i; have := hn i; change D i + a i + b i ≤ n i at this; omega
  have han : ∀ i, a i ≤ n i := by intro i; have := hn i; change D i + a i + b i ≤ n i at this; omega
  have hbsub : ∀ i, b i ≤ (n - D) i := by
    intro i; have := hn i; change D i + a i + b i ≤ n i at this; change b i ≤ n i - D i; omega
  have hnsub : D + (n - D) = n := by
    funext i; exact Nat.add_sub_of_le (hDn i)
  have heval (F : MvPolynomial M.FactorIndex ℚ) :
      eval (fun i => (n i : ℚ)) (aeval (fun i => X i - C (D i : ℚ)) F) =
        eval (fun i => (((n - D) i : ℕ) : ℚ)) F := by
    clear ha hb
    induction F using MvPolynomial.induction_on with
    | C c => simp
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F i hF =>
      simp only [map_mul, hF, aeval_X, map_sub, eval_X, eval_C]
      simp only [Pi.sub_apply, Nat.cast_sub (hDn i)]
  rw [map_add, heval, ha n han, hb (n - D) hbsub]
  have h := hilbertFunction_colon_add M I hI P D hP (n - D)
  rw [hnsub] at h
  exact_mod_cast h

/-- A finite prime filtration gives a sum of shifted prime Hilbert polynomials.
The chain is supplied explicitly, so the result also applies to every later
chosen filtration, not only to a particular existence witness. -/
theorem hilbertPolynomial_filtration_sum (n : ℕ)
    (J : Fin (n + 1) → Ideal M.CoordinateRing)
    (P : Fin n → M.CoordinateRing) (D : Fin n → M.FactorIndex → ℕ)
    (hhom : ∀ j, IsMultihomogeneousIdeal M (J j))
    (hstep : ∀ j, M.IsHomogeneous (P j) (D j) ∧
      J j.succ = J j.castSucc ⊔ Ideal.span {P j})
    (hlast : J (Fin.last n) = ⊤) :
    hilbertPolynomial K M.factorCount M.ambientDimension (J 0) =
      ∑ j, aeval (fun i => X i - C (D j i : ℚ))
        (hilbertPolynomial K M.factorCount M.ambientDimension
          ((J j.castSucc).colon {P j})) := by
  induction n with
  | zero =>
    have heq : J 0 = ⊤ := hlast
    rw [heq]
    simpa using hilbertPolynomial_top M
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have htail := ih (fun j => J j.succ) (fun j => P j.succ) (fun j => D j.succ)
      (fun j => hhom j.succ) (fun j => by simpa using hstep j.succ) hlast
    have hfirst := hilbertPolynomial_colon_add M (J 0) (hhom 0) (P 0) (D 0) (hstep 0).1
    have hzero : J (Fin.succ 0) = J 0 ⊔ Ideal.span {P 0} := (hstep 0).2
    rw [← hzero] at hfirst
    rw [htail] at hfirst
    simpa only [Fin.castSucc_zero, Fin.castSucc_succ, add_comm] using hfirst

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponFiniteDifference

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.FiniteDifference
variable {ι : Type*} [Fintype ι]

def shift (D : ι → ℚ) : MvPolynomial ι ℚ →ₐ[ℚ] MvPolynomial ι ℚ :=
  aeval (fun i => X i - C (D i))

def deriv (D : ι → ℚ) : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
  ∑ i, D i • (pderiv i).toLinearMap

theorem deriv_apply (D : ι → ℚ) (F : MvPolynomial ι ℚ) :
    deriv D F = ∑ i, D i • pderiv i F := by
  simp only [deriv, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem deriv_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (i : ι) :
    deriv D (F * X i) = deriv D F * X i + D i • F := by
  classical
  simp only [deriv_apply, pderiv_mul, pderiv_X, MvPolynomial.smul_eq_C_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  simp [Pi.single_apply, mul_ite, mul_assoc]

private theorem PhilipponFiniteDifference_component_mul_X (F : MvPolynomial ι ℚ) (i : ι) (n : ℕ) :
    homogeneousComponent (n + 1) (F * X i) = homogeneousComponent n F * X i := by
  classical
  letI := weightedGradedAlgebra ℚ (1 : ι → ℕ)
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule ℚ (1 : ι → ℕ))
    (a := F) (i := n) (isHomogeneous_X ℚ i)
  change ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) (F * X i)) (n + 1) : MvPolynomial ι ℚ) =
    ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) F) n : MvPolynomial ι ℚ) * X i at h
  simpa only [MvPolynomial.decompose'_apply, homogeneousComponent] using h

private theorem PhilipponFiniteDifference_degree_le_pred_of_top_zero (F : MvPolynomial ι ℚ) (n : ℕ)
    (hdegree : F.totalDegree ≤ n) (hzero : homogeneousComponent n F = 0) :
    F.totalDegree ≤ n - 1 := by
  classical
  apply Finset.sup_le
  intro d hd
  have hdn : d.degree ≤ n := (le_totalDegree hd).trans hdegree
  have hne : d.degree ≠ n := by
    intro heq
    have hh := congrArg (coeff d) hzero
    simp only [coeff_homogeneousComponent, heq, if_pos rfl, coeff_zero] at hh
    exact (mem_support_iff.mp hd) hh
  change d.degree ≤ n - 1
  omega

private def PhilipponFiniteDifference_Expansion (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ) : Prop :=
  (shift D F).totalDegree ≤ n ∧ homogeneousComponent n (shift D F) = F ∧
    (∀ k, n = k + 1 → homogeneousComponent k (shift D F) = -deriv D F)

private theorem PhilipponFiniteDifference_expansion_C (D : ι → ℚ) (c : ℚ) : PhilipponFiniteDifference_Expansion D (C c) 0 := by
  simp [PhilipponFiniteDifference_Expansion, shift]

private theorem PhilipponFiniteDifference_expansion_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ)
    (hF : F.IsHomogeneous n) (h : PhilipponFiniteDifference_Expansion D F n) (i : ι) :
    PhilipponFiniteDifference_Expansion D (F * X i) (n + 1) := by
  classical
  rcases h with ⟨hdeg, htop, hnext⟩
  have hs : shift D (F * X i) = shift D F * X i - D i • shift D F := by
    simp only [shift, map_mul, aeval_X, mul_sub, MvPolynomial.smul_eq_C_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add_right hdeg 1)
    · exact (totalDegree_smul_le _ _).trans (hdeg.trans (Nat.le_succ n))
  · rw [hs, map_sub, map_smul, PhilipponFiniteDifference_component_mul_X, htop,
      homogeneousComponent_eq_zero _ _ (by omega : (shift D F).totalDegree < n + 1)]
    simp
  · intro k hk
    have hkn : k = n := by omega
    subst k
    rw [hs, map_sub, map_smul, htop, deriv_mul_X]
    cases n with
    | zero =>
      have hconst : F = C (coeff 0 F) := by
        exact (homogeneousComponent_eq_self hF).symm.trans
          (MvPolynomial.homogeneousComponent_zero F)
      have hd : deriv D F = 0 := by
        nth_rw 1 [hconst]
        simp [deriv]
      have hz : coeff (0 : ι →₀ ℕ) (shift D F * X i) = 0 := by
        simpa using (MvPolynomial.coeff_mul_X' (0 : ι →₀ ℕ) i (shift D F))
      simp [hd, homogeneousComponent_zero, hz]
    | succ n =>
      rw [PhilipponFiniteDifference_component_mul_X, hnext n rfl]
      simp only [neg_mul, neg_add_rev, sub_eq_add_neg]
      ac_rfl

private theorem PhilipponFiniteDifference_expansion_monomial (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    PhilipponFiniteDifference_Expansion D (monomial a c) a.degree := by
  classical
  induction a using Finsupp.induction with
  | zero => simpa using PhilipponFiniteDifference_expansion_C D c
  | @single_add i k a hia hk ih =>
    have haux : ∀ k, PhilipponFiniteDifference_Expansion D (monomial (Finsupp.single i k + a) c)
        ((Finsupp.single i k + a).degree) := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        have heq : monomial (Finsupp.single i (k + 1) + a) c =
            monomial (Finsupp.single i k + a) c * X i := by
          simp only [monomial_single_add, pow_succ]
          ring
        rw [heq]
        have hh := PhilipponFiniteDifference_expansion_mul_X D (monomial (Finsupp.single i k + a) c)
          (Finsupp.single i k + a).degree (isHomogeneous_monomial c rfl) ihk i
        simpa only [map_add, Finsupp.degree_single, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hh
    exact haux k

private theorem PhilipponFiniteDifference_monomial_difference (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree - 1 ∧
    (a.degree = 0 → monomial a c - shift D (monomial a c) = 0) ∧
    (0 < a.degree → homogeneousComponent (a.degree - 1)
      (monomial a c - shift D (monomial a c)) = deriv D (monomial a c)) := by
  obtain ⟨hdeg, htop, hnext⟩ := PhilipponFiniteDifference_expansion_monomial D a c
  have hhom := isHomogeneous_monomial (σ := ι) c (show a.degree = a.degree from rfl)
  have hbd : (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree :=
    (totalDegree_sub _ _).trans (max_le hhom.totalDegree_le hdeg)
  refine ⟨PhilipponFiniteDifference_degree_le_pred_of_top_zero _ _ hbd ?_, ?_, ?_⟩
  · rw [map_sub, homogeneousComponent_eq_self hhom, htop, sub_self]
  · intro ha
    have hconst : monomial a c = C (coeff 0 (monomial a c)) :=
      (homogeneousComponent_eq_self (ha ▸ hhom)).symm.trans
        (MvPolynomial.homogeneousComponent_zero _)
    conv_lhs => rw [hconst]
    simp [shift]
  · intro ha
    rw [map_sub, homogeneousComponent_of_mem hhom,
      if_neg (by omega), hnext (a.degree - 1) (by omega)]
    simp

/-- Translation subtracts the top degree, and its next homogeneous part is
the directional derivative of the old top part. -/
theorem top_difference (D : ι → ℚ) (F : MvPolynomial ι ℚ) (a : ℕ)
    (ha : 0 < a) (hF : F.totalDegree ≤ a) :
    (F - shift D F).totalDegree ≤ a - 1 ∧
    homogeneousComponent (a - 1) (F - shift D F) =
      deriv D (homogeneousComponent a F) := by
  classical
  let δ : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
    LinearMap.id - (shift D).toLinearMap
  have hδ : δ F = F - shift D F := rfl
  have hsum : F - shift D F = ∑ d ∈ F.support, δ (monomial d (coeff d F)) := by
    rw [← hδ, ← map_sum]
    congr 1
    exact F.as_sum
  have hterm (d : ι →₀ ℕ) (hd : d ∈ F.support) :
      (δ (monomial d (coeff d F))).totalDegree ≤ a - 1 ∧
      homogeneousComponent (a - 1) (δ (monomial d (coeff d F))) =
        deriv D (homogeneousComponent a (monomial d (coeff d F))) := by
    obtain ⟨hdeg, hz, ht⟩ := PhilipponFiniteDifference_monomial_difference D d (coeff d F)
    have hda : d.degree ≤ a := (le_totalDegree hd).trans hF
    refine ⟨hdeg.trans (Nat.sub_le_sub_right hda 1), ?_⟩
    change homogeneousComponent (a - 1) (monomial d (coeff d F) - shift D (monomial d (coeff d F))) = _
    by_cases heq : d.degree = a
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_pos heq.symm, ← heq]
      exact ht (heq ▸ ha)
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_neg (Ne.symm heq), map_zero]
      by_cases hd0 : d.degree = 0
      · rw [hz hd0, map_zero]
      · exact homogeneousComponent_eq_zero _ _ (by omega)
  constructor
  · rw [hsum]
    exact (totalDegree_finsetSum _ _).trans (Finset.sup_le (fun d hd => (hterm d hd).1))
  · rw [hsum, map_sum]
    conv_rhs => rw [F.as_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun d hd => (hterm d hd).2)

theorem coeff_deriv (D : ι → ℚ) (F : MvPolynomial ι ℚ) (b : ι →₀ ℕ) :
    coeff b (deriv D F) =
      ∑ i, D i * (coeff (b + Finsupp.single i 1) F * (b i + 1 : ℚ)) := by
  classical
  rw [deriv_apply]
  change coeff b (∑ i, D i • pderiv i F) = _
  simp only [coeff_sum, coeff_smul, smul_eq_mul, coeff_pderiv]

theorem deriv_ne_zero (D : ι → ℚ) (hD : ∀ i, 0 < D i)
    (F : MvPolynomial ι ℚ) (a : ℕ) (ha : 0 < a)
    (hF : F.IsHomogeneous a) (hne : F ≠ 0)
    (hcoeff : ∀ b, 0 ≤ coeff b F) : deriv D F ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := exists_coeff_ne_zero hne
  have hba : b.degree = a := by
    by_contra h
    exact hb (hF.coeff_eq_zero h)
  have hsum : 0 < ∑ i, b i := by
    simpa only [← Finsupp.degree_eq_sum, hba] using ha
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hsum
  let c := b - Finsupp.single i 1
  have hc : c + Finsupp.single i 1 = b := by
    apply tsub_add_cancel_of_le
    exact Finsupp.single_le_iff.mpr (by omega)
  have hpos : 0 < coeff c (deriv D F) := by
    rw [coeff_deriv]
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hD j).le (mul_nonneg (hcoeff _) (by positivity))
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [hc]
      exact mul_pos (hD i) (mul_pos (lt_of_le_of_ne (hcoeff b) (Ne.symm hb)) (by positivity))
  intro hz
  rw [hz, coeff_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- Positive equation degrees prevent cancellation of the new leading part. -/
theorem difference_degree (D : ι → ℚ) (hD : ∀ i, 0 < D i)
    (F : MvPolynomial ι ℚ) (ha : 0 < F.totalDegree)
    (hcoeff : ∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) :
    (F - shift D F).totalDegree = F.totalDegree - 1 ∧
    homogeneousComponent (F - shift D F).totalDegree (F - shift D F) =
      deriv D (homogeneousComponent F.totalDegree F) := by
  obtain ⟨hdeg, htop⟩ := top_difference D F F.totalDegree ha le_rfl
  have hne : homogeneousComponent F.totalDegree F ≠ 0 := by
    intro hz
    have hh := PhilipponFiniteDifference_degree_le_pred_of_top_zero F F.totalDegree le_rfl hz
    omega
  have hdne := deriv_ne_zero D hD _ F.totalDegree ha
    (homogeneousComponent_isHomogeneous _ _) hne hcoeff
  have hge : F.totalDegree - 1 ≤ (F - shift D F).totalDegree := by
    by_contra h
    have hz := homogeneousComponent_eq_zero (F.totalDegree - 1) (F - shift D F)
      (lt_of_not_ge h)
    exact hdne (htop.symm.trans hz)
  have heq := le_antisymm hdeg hge
  exact ⟨heq, heq ▸ htop⟩

theorem eval_deriv_monomial (D d : ι → ℚ) (hd : ∀ i, d i ≠ 0)
    (b : ι →₀ ℕ) (c : ℚ) :
    eval d (deriv D (monomial b c)) =
      c * (∑ i, (b i : ℚ) * D i / d i) * ∏ i, d i ^ b i := by
  classical
  have hev (i : ι) : eval d (pderiv i (monomial b c)) =
      (b i : ℚ) * eval d (monomial b c) / d i := by
    apply (eq_div_iff (hd i)).mpr
    have hh := congrArg (eval d) (X_mul_pderiv_monomial (i := i) (m := b) (r := c))
    simpa only [map_mul, eval_X, map_nsmul, nsmul_eq_mul, map_natCast, mul_comm] using hh
  rw [deriv_apply]
  change eval d (∑ i, D i • pderiv i (monomial b c)) = _
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, hev, eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eval_deriv_self (D : ι → ℚ) (F : MvPolynomial ι ℚ) (a : ℕ)
    (hF : F.IsHomogeneous a) : eval D (deriv D F) = (a : ℚ) * eval D F := by
  classical
  have hh := congrArg (eval D) hF.sum_X_mul_pderiv
  rw [deriv_apply]
  change eval D (∑ i, D i • pderiv i F) = _
  simpa only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_X, map_nsmul,
    nsmul_eq_mul, map_natCast] using hh

end PhilipponMultiplicity.FiniteDifference

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertDimension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem shift_top (D : ι → ℚ) (F : MvPolynomial ι ℚ) :
    homogeneousComponent F.totalDegree (FiniteDifference.shift D F) =
      homogeneousComponent F.totalDegree F ∧
    (FiniteDifference.shift D F).totalDegree = F.totalDegree := by
  classical
  by_cases hz : F.totalDegree = 0
  · have hc := totalDegree_eq_zero_iff_eq_C.mp hz
    rw [hc]
    simp [FiniteDifference.shift]
  · have hp : 0 < F.totalDegree := Nat.pos_of_ne_zero hz
    have hdiff := (FiniteDifference.top_difference D F F.totalDegree hp le_rfl).1
    have hzero : homogeneousComponent F.totalDegree (F - FiniteDifference.shift D F) = 0 :=
      homogeneousComponent_eq_zero _ _ (by omega)
    rw [map_sub, sub_eq_zero] at hzero
    refine ⟨hzero.symm, le_antisymm ?_ ?_⟩
    · have heq : FiniteDifference.shift D F = F - (F - FiniteDifference.shift D F) := by abel
      nth_rw 1 [heq]
      exact (totalDegree_sub _ _).trans (max_le le_rfl (by omega))
    · by_contra hlt
      have hc := homogeneousComponent_eq_zero F.totalDegree (FiniteDifference.shift D F)
        (lt_of_not_ge hlt)
      rw [← hzero] at hc
      have ht : homogeneousComponent F.totalDegree F ≠ 0 := by
        have hne : F ≠ 0 := by intro h; apply hz; rw [h, totalDegree_zero]
        obtain ⟨e, he, hed⟩ := Finset.exists_mem_eq_sup F.support
          (support_nonempty.mpr hne) Finsupp.degree
        change F.totalDegree = e.degree at hed
        intro h
        have hx := congrArg (coeff e) h
        rw [coeff_homogeneousComponent, if_pos hed.symm, coeff_zero] at hx
        exact (mem_support_iff.mp he) hx
      exact ht hc

theorem component_nonneg (F : MvPolynomial ι ℚ)
    (hF : ∀ e, 0 ≤ coeff e (homogeneousComponent F.totalDegree F))
    (n : ℕ) (hn : F.totalDegree ≤ n) (e : ι →₀ ℕ) :
    0 ≤ coeff e (homogeneousComponent n F) := by
  by_cases heq : n = F.totalDegree
  · simpa only [heq] using hF e
  · rw [homogeneousComponent_eq_zero n F (by omega), coeff_zero]

theorem totalDegree_le_add_of_top_nonneg (F G : MvPolynomial ι ℚ)
    (hF : ∀ e, 0 ≤ coeff e (homogeneousComponent F.totalDegree F))
    (hG : ∀ e, 0 ≤ coeff e (homogeneousComponent G.totalDegree G)) :
    F.totalDegree ≤ (F + G).totalDegree := by
  classical
  have aux (A B : MvPolynomial ι ℚ)
      (hA : ∀ e, 0 ≤ coeff e (homogeneousComponent A.totalDegree A))
      (hB : ∀ e, 0 ≤ coeff e (homogeneousComponent B.totalDegree B))
      (hle : B.totalDegree ≤ A.totalDegree) : A.totalDegree ≤ (A + B).totalDegree := by
    by_cases hz : A = 0
    · simp [hz]
    obtain ⟨e, he, hed⟩ := Finset.exists_mem_eq_sup A.support (support_nonempty.mpr hz) Finsupp.degree
    change A.totalDegree = e.degree at hed
    have hc : 0 < coeff e (homogeneousComponent A.totalDegree A) := by
      apply lt_of_le_of_ne (hA e)
      rw [coeff_homogeneousComponent, if_pos hed.symm]
      exact Ne.symm (mem_support_iff.mp he)
    have hpos : 0 < coeff e (homogeneousComponent A.totalDegree (A + B)) := by
      rw [map_add, coeff_add]
      exact add_pos_of_pos_of_nonneg hc (component_nonneg B hB _ hle e)
    by_contra hlt
    rw [homogeneousComponent_eq_zero _ _ (lt_of_not_ge hlt), coeff_zero] at hpos
    exact (lt_irrefl 0) hpos
  rcases le_total G.totalDegree F.totalDegree with hle | hle
  · exact aux F G hF hG hle
  · exact hle.trans (by simpa only [add_comm] using aux G F hG hF hle)

end PhilipponMultiplicity.ComponentDegree

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem idealDimension_sup_span_le (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    idealDimension M (I ⊔ Ideal.span {P}) ≤ idealDimension M I := by
  unfold idealDimension
  rw [hilbertPolynomial_colon_add M I hI P D hP]
  apply ComponentDegree.totalDegree_le_add_of_top_nonneg
  · exact (multigraded_hilbert_polynomial_top_coefficients K M _
      (homogeneous_sup_span M I hI P D hP)).1
  · have hs := ComponentDegree.shift_top (fun i => (D i : ℚ))
      (hilbertPolynomial K M.factorCount M.ambientDimension (I.colon {P}))
    change ∀ e, 0 ≤ coeff e (homogeneousComponent
      (FiniteDifference.shift _ _).totalDegree (FiniteDifference.shift _ _))
    rw [hs.2, hs.1]
    exact (multigraded_hilbert_polynomial_top_coefficients K M _
      (homogeneous_colon M I hI P D hP)).1

theorem homogeneous_component_outside (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J)
    (hnot : ¬ J ≤ I) :
    ∃ P D, M.IsHomogeneous P D ∧ P ∈ J ∧ P ∉ I := by
  classical
  obtain ⟨f, hfJ, hfI⟩ := Set.not_subset.mp hnot
  let w := blockWeight M.factorCount M.ambientDimension
  have hsome : ∃ d, weightedHomogeneousComponent w d f ∉ I := by
    by_contra! h
    apply hfI
    rw [← sum_weightedHomogeneousComponent w f]
    rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    exact I.sum_mem (fun d _ => h d)
  obtain ⟨d, hd⟩ := hsome
  exact ⟨_, d, (M.degreePiece_iff _ d).mp (weightedHomogeneousComponent_mem _ _ _),
    hJ f hfJ d, hd⟩

/-- Hilbert dimension is antitone under inclusion of actual homogeneous ideals. -/
theorem idealDimension_antitone (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J) (hle : I ≤ J) :
    idealDimension M J ≤ idealDimension M I := by
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    by_cases heq : I = J
    · simp [heq]
    · have hnot : ¬ J ≤ I := fun h => heq (le_antisymm hle h)
      obtain ⟨P, D, hP, hPJ, hPI⟩ := homogeneous_component_outside M I J hI hJ hnot
      have hlt : I < I ⊔ Ideal.span {P} := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro h
        apply hPI
        rw [h]
        exact (le_sup_right : Ideal.span {P} ≤ I ⊔ Ideal.span {P})
          (Ideal.subset_span (Set.mem_singleton P))
      have hsub : I ⊔ Ideal.span {P} ≤ J := by
        apply sup_le hle
        rwa [Ideal.span_singleton_le_iff_mem]
      exact (ih _ hlt (homogeneous_sup_span M I hI P D hP) hsub).trans
        (idealDimension_sup_span_le M I hI P D hP)

end PhilipponMultiplicity.Hilbert

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

theorem hilbertFunction_antitone (I J : Ideal M.CoordinateRing) (hIJ : I ≤ J)
    (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension J d ≤
      hilbertFunction K M.factorCount M.ambientDimension I d := by
  let q := Ideal.quotientMapₐ J (AlgHom.id K M.CoordinateRing) hIJ
  let f : quotientPiece K M.factorCount M.ambientDimension I d →ₗ[K]
      quotientPiece K M.factorCount M.ambientDimension J d :=
    (q.toLinearMap.domRestrict _).codRestrict _ (by
      rintro ⟨x, P, hP, rfl⟩
      exact ⟨P, hP, rfl⟩)
  apply LinearMap.finrank_le_finrank_of_surjective (f := f)
  rintro ⟨x, P, hP, rfl⟩
  exact ⟨⟨Ideal.Quotient.mk I P, ⟨P, hP, rfl⟩⟩, rfl⟩

theorem hilbertPolynomial_zero_of_le (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hIJ : I ≤ J)
    (hz : hilbertPolynomial K M.factorCount M.ambientDimension I = 0) :
    hilbertPolynomial K M.factorCount M.ambientDimension J = 0 := by
  have hex := hilbertPolynomial_spec K M.factorCount M.ambientDimension I
    (multigraded_hilbert_polynomial_exists K M I hI)
  rw [hz] at hex
  obtain ⟨a, ha⟩ := hex
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨a, fun d hd => ?_⟩
  have hzero : hilbertFunction K M.factorCount M.ambientDimension I d = 0 := by
    have h := ha d hd
    simpa using h.symm
  have hJzero : hilbertFunction K M.factorCount M.ambientDimension J d = 0 :=
    Nat.eq_zero_of_le_zero (hzero ▸ hilbertFunction_antitone M I J hIJ d)
  rw [map_zero, hJzero, Nat.cast_zero]

theorem relevant_variables (Q : Ideal M.CoordinateRing)
    (hQ : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ v : ∀ i, Fin (M.ambientDimension i + 1), ∀ i, X ⟨i, v i⟩ ∉ Q := by
  classical
  have hx (i : M.FactorIndex) : ∃ j : Fin (M.ambientDimension i + 1), X ⟨i, j⟩ ∉ Q := by
    by_contra! h
    apply hQ
    apply (iInf_le (blockIdeal K M.factorCount M.ambientDimension) i).trans
    rw [blockIdeal, Ideal.span_le]
    rintro x ⟨j, rfl⟩
    exact h j
  exact Classical.axiomOfChoice hx

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

theorem variable_product_notMem (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (v : ∀ i, Fin (M.ambientDimension i + 1)) (hv : ∀ i, X ⟨i, v i⟩ ∉ Q)
    (d : M.FactorIndex → ℕ) : (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) ∉ Q := by
  classical
  letI := hQ
  intro h
  obtain ⟨i, hi, hip⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hv i (hQ.mem_of_pow_mem _ hip)

/-- A relevant homogeneous prime has a nonzero actual Hilbert polynomial. -/
theorem relevant_prime_hilbertPolynomial_ne_zero (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    hilbertPolynomial K M.factorCount M.ambientDimension Q ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := relevant_variables M Q hrel
  intro hz
  have hex := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q hhom)
  rw [hz] at hex
  obtain ⟨d, hd⟩ := hex
  let P : M.CoordinateRing := ∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i
  have hP : P ∉ Q := variable_product_notMem M Q hQ v hv d
  let x : quotientPiece K M.factorCount M.ambientDimension Q d :=
    ⟨Ideal.Quotient.mk Q P, P, (M.degreePiece_iff P d).mpr (variable_product_homogeneous M v d), rfl⟩
  have hx : x ≠ 0 := by
    intro h
    exact hP (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val h))
  letI : Nontrivial (quotientPiece K M.factorCount M.ambientDimension Q d) :=
    ⟨⟨x, 0, hx⟩⟩
  have hpos := Module.finrank_pos (R := K)
    (M := quotientPiece K M.factorCount M.ambientDimension Q d)
  have heq := hd d (fun _ => le_rfl)
  change (MvPolynomial.eval _ (0 : MvPolynomial M.FactorIndex ℚ)) = _ at heq
  rw [map_zero] at heq
  have hzero : hilbertFunction K M.factorCount M.ambientDimension Q d = 0 := by exact_mod_cast heq.symm
  exact (Nat.ne_of_gt hpos) hzero

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponIrrelevantHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_mem_blockIdeal (i : M.FactorIndex) (d : M.FactorIndex → ℕ)
    (hd : 0 < d i) (P : M.CoordinateRing) (hP : M.IsHomogeneous P d) :
    P ∈ blockIdeal K M.factorCount M.ambientDimension i := by
  classical
  have hset : Set.range (fun j : Fin (M.ambientDimension i + 1) =>
        (X ⟨i, j⟩ : M.CoordinateRing)) =
      X '' {x : M.Variable | x.1 = i} := by
    ext f
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨⟨i, j⟩, rfl, rfl⟩
    · rintro ⟨⟨k, j⟩, hk, rfl⟩
      change k = i at hk
      subst k
      exact ⟨j, rfl⟩
  unfold blockIdeal
  rw [hset, mem_ideal_span_X_image]
  intro e he
  have hsum : ∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ = d i := hP e he i
  have hsome : ∃ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ ≠ 0 := by
    by_contra! h
    have hz : ∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ = 0 := by simp [h]
    omega
  obtain ⟨j, hj⟩ := hsome
  exact ⟨⟨i, j⟩, rfl, hj⟩

theorem hilbertPolynomial_zero_of_blockIdeal_le (I : Ideal M.CoordinateRing)
    (i : M.FactorIndex) (hI : blockIdeal K M.factorCount M.ambientDimension i ≤ I) :
    hilbertPolynomial K M.factorCount M.ambientDimension I = 0 := by
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => 1, fun d hd => ?_⟩
  have hz : quotientPiece K M.factorCount M.ambientDimension I d = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨P, hP, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hI (homogeneous_mem_blockIdeal M i d (hd i) P ((M.degreePiece_iff P d).mp hP))
  rw [map_zero, hilbertFunction, hz, finrank_bot, Nat.cast_zero]

/-- An irrelevant prime has zero multiprojective Hilbert polynomial, including
the zero-dimensional boundary case in the natural total-degree convention. -/
theorem irrelevant_prime_hilbertPolynomial_zero (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hirr : ¬ IsRelevant K M.factorCount M.ambientDimension Q) :
    hilbertPolynomial K M.factorCount M.ambientDimension Q = 0 := by
  classical
  have hle : irrelevantIdeal K M.factorCount M.ambientDimension ≤ Q := not_not.mp hirr
  have hfin : Finset.univ.inf (blockIdeal K M.factorCount M.ambientDimension) ≤ Q := by
    simpa only [irrelevantIdeal, Finset.inf_eq_iInf, Finset.mem_univ, iInf_true] using hle
  obtain ⟨i, hi, hblock⟩ := hQ.inf_le'.mp hfin
  exact hilbertPolynomial_zero_of_blockIdeal_le M Q i hblock

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponPrimeDimension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Proper inclusion between relevant homogeneous primes strictly lowers
the Hilbert dimension. -/
theorem relevant_prime_dimension_strict (Q R : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hR : R.IsPrime)
    (hQhom : IsMultihomogeneousIdeal M Q) (hRhom : IsMultihomogeneousIdeal M R)
    (hRrel : IsRelevant K M.factorCount M.ambientDimension R) (hlt : Q < R) :
    idealDimension M R < idealDimension M Q := by
  classical
  have hQrel : IsRelevant K M.factorCount M.ambientDimension Q :=
    fun h => hRrel (h.trans hlt.le)
  obtain ⟨f, D, hfhom, hfR, hfQ⟩ := homogeneous_component_outside M Q R hQhom hRhom hlt.not_ge
  obtain ⟨v, hv⟩ := relevant_variables M Q hQrel
  let B : M.CoordinateRing := ∏ i, (X ⟨i, v i⟩ : M.CoordinateRing)
  have hBhom : M.IsHomogeneous B (fun _ => 1) := by
    simpa only [pow_one] using variable_product_homogeneous M v (fun _ => 1)
  have hBQ : B ∉ Q := by
    simpa only [pow_one] using variable_product_notMem M Q hQ v hv (fun _ => 1)
  let P := f * B
  let E : M.FactorIndex → ℕ := D + (fun _ => 1)
  have hP : M.IsHomogeneous P E := (M.degreePiece_iff _ _).mp
    (((M.degreePiece_iff f D).mpr hfhom).mul ((M.degreePiece_iff B _).mpr hBhom))
  have hPQ : P ∉ Q := fun h => (hQ.mem_or_mem h).elim hfQ hBQ
  have hPR : P ∈ R := R.mul_mem_right B hfR
  have hcolon : Q.colon {P} = Q := by
    apply le_antisymm _ Ideal.le_colon
    intro x hx
    exact (hQ.mem_or_mem (Submodule.mem_colon_singleton.mp hx)).resolve_right hPQ
  let F := hilbertPolynomial K M.factorCount M.ambientDimension Q
  let J := Q ⊔ Ideal.span {P}
  have hJhom := homogeneous_sup_span M Q hQhom P E hP
  have hJR : J ≤ R := by
    apply sup_le hlt.le
    rwa [Ideal.span_singleton_le_iff_mem]
  have hpoly : hilbertPolynomial K M.factorCount M.ambientDimension J =
      F - FiniteDifference.shift (fun i => (E i : ℚ)) F := by
    have h := hilbertPolynomial_colon_add M Q hQhom P E hP
    rw [hcolon] at h
    exact eq_sub_of_add_eq h.symm
  have hpos : 0 < F.totalDegree := by
    by_contra hz
    have hzero : F.totalDegree = 0 := by omega
    have hconst := totalDegree_eq_zero_iff_eq_C.mp hzero
    have hJzero : hilbertPolynomial K M.factorCount M.ambientDimension J = 0 := by
      rw [hpoly, hconst]
      simp [FiniteDifference.shift]
    exact relevant_prime_hilbertPolynomial_ne_zero M R hR hRhom hRrel
      (hilbertPolynomial_zero_of_le M J R hJhom hJR hJzero)
  have hdrop := (FiniteDifference.difference_degree (fun i => (E i : ℚ))
    (fun i => by dsimp [E]; positivity) F hpos
    (multigraded_hilbert_polynomial_top_coefficients K M Q hQhom).1).1
  have hdim := idealDimension_antitone M J R hJhom hRhom hJR
  change (hilbertPolynomial K M.factorCount M.ambientDimension R).totalDegree ≤
    (hilbertPolynomial K M.factorCount M.ambientDimension J).totalDegree at hdim
  rw [hpoly, hdrop] at hdim
  change (hilbertPolynomial K M.factorCount M.ambientDimension R).totalDegree < F.totalDegree
  omega

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponMinimalPrimeHomogeneous

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Every actual minimal prime of a multihomogeneous ideal is multihomogeneous. -/
theorem minimalPrime_homogeneous (I Q : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hQ : Q ∈ I.minimalPrimes) :
    IsMultihomogeneousIdeal M Q := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hproj (f : M.CoordinateRing) (d : Lex (M.FactorIndex → ℕ)) :
      weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (ofLex d) f := by
    ext e
    simp only [coeff_weightedHomogeneousComponent]
    rfl
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply, hproj]
    exact hI f hf (ofLex d)
  let C := Q.homogeneousCore (weightedHomogeneousSubmodule K w)
  have hCprime : C.toIdeal.IsPrime := hQ.1.1.homogeneousCore
  have hCQ : C.toIdeal ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hIC : I ≤ C.toIdeal := by
    rw [← hIg.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hQ.1.2
  have heq : C.toIdeal = Q := le_antisymm hCQ (hQ.2 ⟨hCprime, hIC⟩ hCQ)
  intro f hf d
  rw [← heq] at hf ⊢
  have h := weightedHomogeneousComponent_mem_of_mem K w C.isHomogeneous hf (toLex d)
  rwa [hproj] at h

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponDimensionSlice

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComponentSelection

theorem finite_iInf_le_prime {R ι : Type*} [CommRing R] [Finite ι]
    (A : ι → Ideal R) (q : Ideal R) (hq : q.IsPrime) :
    (⨅ i, A i) ≤ q ↔ ∃ i, A i ≤ q := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Finset.mem_univ, true_and] using
    (hq.inf_le' (s := Finset.univ) (f := A))

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem dimensionAtLeast_le_prime_iff (J q : Ideal M.CoordinateRing)
    (hq : q.IsPrime) (b : ℕ) :
    dimensionAtLeast M J b ≤ q ↔
      ∃ p : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J,
        Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal ∧
        b ≤ idealDimension M p.1.asIdeal ∧ p.1.asIdeal ≤ q := by
  classical
  unfold dimensionAtLeast
  rw [finite_iInf_le_prime]
  · constructor
    · rintro ⟨p, hp⟩
      split_ifs at hp with h
      · refine ⟨p, h.1, h.2, ?_⟩
        rw [← Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2]
        exact hq.radical_le_iff.mpr hp
      · exact (hq.ne_top (top_unique hp)).elim
    · rintro ⟨p, hr, hd, hp⟩
      refine ⟨p, ?_⟩
      rw [if_pos ⟨hr, hd⟩]
      exact (Ideal.le_radical.trans (le_of_eq
        (Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2))).trans hp
  · exact hq

/-- Fact A: agreement of the higher-dimensional supports makes the
dimension-b isolated primary components monotone. -/
theorem dimensionSlice_mono (J J' : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJ' : IsMultihomogeneousIdeal M J')
    (hle : J ≤ J') (b : ℕ)
    (heq : (dimensionAtLeast M J (b + 1)).radical =
      (dimensionAtLeast M J' (b + 1)).radical) :
    dimensionSlice M J b ≤ dimensionSlice M J' b := by
  classical
  unfold dimensionSlice
  refine le_iInf fun q => ?_
  split_ifs with hq
  · letI : q.1.asIdeal.IsPrime := q.1.isPrime
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (hle.trans q.2.1.2)
    have hprel : Hilbert.IsRelevant K M.factorCount M.ambientDimension p :=
      fun h => hq.1 (h.trans hpq)
    have hphom := Hilbert.minimalPrime_homogeneous M J p hJ hp
    have hqhom := Hilbert.minimalPrime_homogeneous M J' q.1.asIdeal hJ' q.2
    have hdim := Hilbert.idealDimension_antitone M p q.1.asIdeal hphom hqhom hpq
    have hpdim : idealDimension M p = b := by
      by_contra hne
      have hb : b + 1 ≤ idealDimension M p := by omega
      have hhigh : dimensionAtLeast M J (b + 1) ≤ q.1.asIdeal :=
        (dimensionAtLeast_le_prime_iff M J q.1.asIdeal q.1.isPrime _).mpr
          ⟨⟨⟨p, hp.1.1⟩, hp⟩, hprel, hb, hpq⟩
      have hhigh' : dimensionAtLeast M J' (b + 1) ≤ q.1.asIdeal := by
        apply q.1.isPrime.radical_le_iff.mp
        rw [← heq]
        exact q.1.isPrime.radical_le_iff.mpr hhigh
      obtain ⟨s, _, hs, hsq⟩ :=
        (dimensionAtLeast_le_prime_iff M J' q.1.asIdeal q.1.isPrime _).mp hhigh'
      have hsEq : s.1.asIdeal = q.1.asIdeal :=
        le_antisymm hsq (q.2.2 s.2.1 hsq)
      rw [hsEq, hq.2] at hs
      omega
    have hpEq : p = q.1.asIdeal := by
      by_contra hne
      have hs := Hilbert.relevant_prime_dimension_strict M p q.1.asIdeal
        hp.1.1 q.1.isPrime hphom hqhom hq.1 (lt_of_le_of_ne hpq hne)
      rw [hpdim, hq.2] at hs
      omega
    have hqJ : q.1.asIdeal ∈ J.minimalPrimes := hpEq ▸ hp
    apply le_trans (b := Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1)
    · apply iInf_le_of_le (⟨q.1, hqJ⟩ :
        Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
      exact le_of_eq (if_pos hq)
    · exact Ideal.comap_mono (Ideal.map_mono hle)
  · exact le_top

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponBoundedAvoidance

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K)

/-- The equation-selection step on p. 367: bounded generators yield one
equation of the exact requested multidegree avoiding every selected relevant prime. -/
theorem exists_bounded_homogeneous_avoiding {ι : Type*} [Finite ι]
    (I₀ : Ideal M.CoordinateRing) (m : ℕ) (P : Fin m → M.CoordinateRing)
    (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (q : ι → Ideal M.CoordinateRing) (hq : ∀ i, (q i).IsPrime)
    (hrel : ∀ i, Hilbert.IsRelevant K M.factorCount M.ambientDimension (q i))
    (hI₀ : ∀ i, I₀ ≤ q i)
    (havoid : ∀ i, ¬ I₀ ⊔ Ideal.span (Set.range P) ≤ q i) :
    ∃ f : M.CoordinateRing, f ∈ Ideal.span (Set.range P) ∧
      M.IsHomogeneous f D ∧ ∀ i, f ∉ q i := by
  classical
  let W : Submodule K M.CoordinateRing :=
    Hilbert.degreePiece K M.factorCount M.ambientDimension D ⊓
      (Ideal.span (Set.range P)).restrictScalars K
  let V : ι → Submodule K W := fun i => ((q i).restrictScalars K).comap W.subtype
  have hproper : ∀ i, V i ≠ ⊤ := by
    intro i htop
    have hj : ∃ j, P j ∉ q i := by
      by_contra! hh
      apply havoid i
      refine sup_le (hI₀ i) (Ideal.span_le.mpr ?_)
      rintro f ⟨j, rfl⟩
      exact hh j
    obtain ⟨j, hj⟩ := hj
    obtain ⟨E, heD, hE⟩ := hP j
    obtain ⟨v, hv⟩ := Hilbert.relevant_variables M (q i) (hrel i)
    let B : M.CoordinateRing := ∏ k, (X ⟨k, v k⟩ : M.CoordinateRing) ^ (D k - E k)
    have hB := Hilbert.variable_product_homogeneous M v (fun k => D k - E k)
    have hBout := Hilbert.variable_product_notMem M (q i) (hq i) v hv
      (fun k => D k - E k)
    have hdeg : E + (fun k => D k - E k) = D := by
      funext k
      have := heD k
      simp only [Pi.add_apply]
      omega
    have hfhom : M.IsHomogeneous (P j * B) D := by
      rw [← hdeg]
      exact (M.degreePiece_iff _ _).mp
        (hE.mul ((M.degreePiece_iff _ _).mpr hB))
    have hfspan : P j * B ∈ Ideal.span (Set.range P) :=
      (Ideal.span (Set.range P)).mul_mem_right B (Ideal.subset_span (Set.mem_range_self j))
    let f : W := ⟨P j * B, (M.degreePiece_iff _ _).mpr hfhom, hfspan⟩
    have hfmem : f ∈ V i := htop.symm ▸ Submodule.mem_top
    have hmem : P j * B ∈ q i := hfmem
    exact ((hq i).mem_or_mem hmem).elim hj hBout
  have hnot : (⋃ i, (V i : Set W)) ≠ Set.univ := by
    intro h
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hproper i hi
  obtain ⟨f, hf⟩ := (Set.ne_univ_iff_exists_notMem _).mp hnot
  refine ⟨f.1, f.2.2, (M.degreePiece_iff _ _).mp f.2.1, ?_⟩
  intro i hi
  exact hf (Set.mem_iUnion.mpr ⟨i, hi⟩)

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponComponentPartition

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComponentSelection
variable {R : Type*} [CommRing R]

theorem minimalPrime_of_between {J I q : Ideal R}
    (hq : q ∈ J.minimalPrimes) (hJI : J ≤ I) (hIq : I ≤ q) :
    q ∈ I.minimalPrimes :=
  ⟨⟨hq.1.1, hIq⟩, fun r hr hrq => hq.2 ⟨hr.1, hJI.trans hr.2⟩ hrq⟩

theorem le_associatedPrime {I q : Ideal R}
    (hq : q ∈ associatedPrimes R (R ⧸ I)) : I ≤ q := by
  simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using
    hq.annihilator_le

theorem minimalPrime_isAssociated [IsNoetherianRing R] {I q : Ideal R}
    (hq : q ∈ I.minimalPrimes) : q ∈ associatedPrimes R (R ⧸ I) := by
  apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R (R ⧸ I)
  simpa only [Ideal.annihilator_quotient] using hq

theorem radical_eq_of_prime_containment (A B : Ideal R)
    (h : ∀ q : Ideal R, q.IsPrime → (A ≤ q ↔ B ≤ q)) : A.radical = B.radical := by
  rw [Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext q
  exact ⟨fun hq => ⟨(h q hq.2).mp hq.1, hq.2⟩,
    fun hq => ⟨(h q hq.2).mpr hq.1, hq.2⟩⟩

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Fact B, in the actual associated-prime and minimal-prime definitions. -/
theorem component_partition_primes (J I : Ideal M.CoordinateRing) (hle : J ≤ I) :
    (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I),
      ∃ p ∈ J.minimalPrimes, p ≤ q) ∧
    (∀ p ∈ J.minimalPrimes,
      p ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → ¬ I ≤ p) := by
  constructor
  · intro q hq
    letI := hq.isPrime
    exact Ideal.exists_minimalPrimes_le (hle.trans (le_associatedPrime hq))
  · intro p hp hn hIp
    exact hn (minimalPrime_isAssociated (minimalPrime_of_between hp hle hIp))

private theorem PhilipponComponentPartition_selected_primary_le_prime_iff (J q : Ideal M.CoordinateRing)
    (hq : q.IsPrime)
    (s : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J → Prop)
    [DecidablePred s] :
    (⨅ p, if s p then Hilbert.primaryComponent K M.factorCount M.ambientDimension J p.1
      else ⊤) ≤ q ↔ ∃ p, s p ∧ p.1.asIdeal ≤ q := by
  classical
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
  rw [← Finset.inf_univ_eq_iInf, hq.inf_le']
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp⟩
    split_ifs at hp with hs
    · refine ⟨p, hs, ?_⟩
      rw [← Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2]
      exact hq.radical_le_iff.mpr hp
    · exact (hq.ne_top (top_unique hp)).elim
  · rintro ⟨p, hs, hp⟩
    refine ⟨p, ?_⟩
    rw [if_pos hs]
    exact (Ideal.le_radical.trans (le_of_eq
      (Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2))).trans hp

/-- Fact C: the cut separates into the discarded cut and the retained support;
the retained minimal primes remain isolated after the cut. -/
theorem component_partition_cut (J I : Ideal M.CoordinateRing) (hle : J ≤ I)
    (P : M.CoordinateRing) (hP : P ∈ I) :
    (J ⊔ Ideal.span {P}).radical =
      (discardedPart M J I ⊔ Ideal.span {P}).radical ⊓ (retainedPart M J I).radical ∧
    ∀ q ∈ J.minimalPrimes,
      q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      q ∈ (J ⊔ Ideal.span {P}).minimalPrimes := by
  classical
  constructor
  · rw [← Ideal.radical_inf]
    apply radical_eq_of_prime_containment
    intro q hq
    letI := hq
    simp only [hq.inf_le, sup_le_iff, Ideal.span_singleton_le_iff_mem]
    have hd := PhilipponComponentPartition_selected_primary_le_prime_iff M J q hq
      (fun p => p.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))
    have hr := PhilipponComponentPartition_selected_primary_le_prime_iff M J q hq
      (fun p => p.1.asIdeal ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))
    unfold discardedPart retainedPart
    constructor
    · rintro ⟨hJq, hPq⟩
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hJq
      let p' : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J :=
        ⟨⟨p, hp.1.1⟩, hp⟩
      by_cases ha : p ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)
      · exact Or.inr (hr.mpr ⟨p', ha, hpq⟩)
      · exact Or.inl ⟨hd.mpr ⟨p', ha, hpq⟩, hPq⟩
    · rintro (⟨hD, hPq⟩ | hR)
      · obtain ⟨p, _, hpq⟩ := hd.mp hD
        exact ⟨p.2.1.2.trans hpq, hPq⟩
      · obtain ⟨p, hp, hpq⟩ := hr.mp hR
        exact ⟨p.2.1.2.trans hpq, hpq (le_associatedPrime hp hP)⟩
  · intro q hq ha
    apply minimalPrime_of_between hq le_sup_left
    apply sup_le hq.1.2
    rw [Ideal.span_singleton_le_iff_mem]
    exact le_associatedPrime ha hP

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponPrimeAvoidanceReuse
set_option autoImplicit false

theorem Ideal.exists_mem_forall_not_mem_of_forall_not_le
    {R : Type*} [CommRing R] (J : Ideal R) (S : Finset (Ideal R))
    (hS : ∀ P ∈ S, P.IsPrime) (h : ∀ P ∈ S, ¬ J ≤ P) :
    ∃ i ∈ J, ∀ P ∈ S, i ∉ P := by
  classical
  by_contra hcon
  push_neg at hcon

  have hsub : ((J : Set R) ⊆ ⋃ P ∈ (↑S : Set (Ideal R)), ((id P : Ideal R) : Set R)) := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := hcon x hx
    exact Set.mem_biUnion hP hxP
  rcases S.eq_empty_or_nonempty with hS0 | ⟨P₀, hP₀⟩
  ·
    obtain ⟨P, hP, -⟩ := hcon 0 J.zero_mem
    rw [hS0] at hP; exact absurd hP (Finset.notMem_empty P)
  · obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime P₀ P₀ (fun P hP _ _ => hS P hP)).mp hsub
    exact h P hP hle

end


section
-- Reused implementation: Solutions.PhilipponEmbeddedAvoidance

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.ComponentSelection

/-- Avoiding the radicals of primary factors gives an actual regular
element in the quotient by their intersection. -/
theorem regular_quotient_iInf {R ι : Type*} [CommRing R]
    (Q : ι → Ideal R) (s : ι → Prop) (hQ : ∀ i, (Q i).IsPrimary)
    (x : R) (hx : ∀ i, s i → x ∉ (Q i).radical) :
    IsRegular (Ideal.Quotient.mk (⨅ i, if s i then Q i else ⊤) x) := by
  classical
  let A : Ideal R := ⨅ i, if s i then Q i else ⊤
  apply (Commute.isRegular_iff (fun y => mul_comm _ y)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change r ∈ A
  have hxr : x * r ∈ A := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  simp only [A, Submodule.mem_iInf] at hxr ⊢
  intro i
  split_ifs with hi
  · have hmem : x * r ∈ Q i := by simpa only [if_pos hi] using hxr i
    exact ((Ideal.isPrimary_iff.mp (hQ i)).2 (mul_comm x r ▸ hmem)).resolve_right (hx i hi)
  · trivial

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.SectionThreeSupport
open ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Fact D: one element removes all embedded components and is a
non-zero-divisor on the entire isolated intersection. -/
theorem exists_embedded_regular (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) :
    ∃ Q ∈ D.embeddedIntersection,
      IsRegular (Ideal.Quotient.mk D.isolatedIntersection Q) := by
  classical
  let S : Finset (Ideal M.CoordinateRing) :=
    (Finset.univ.filter D.IsIsolated).image (fun i => (D.component i).radical)
  have hS : ∀ p ∈ S, p.IsPrime := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Ideal.isPrime_radical (D.primary i)
  have havoid : ∀ p ∈ S, ¬ D.embeddedIntersection ≤ p := by
    intro p hp hle
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    have his : D.IsIsolated i := (Finset.mem_filter.mp hi).2
    have hpprime := Ideal.isPrime_radical (D.primary i)
    obtain ⟨j, hj⟩ := (finite_iInf_le_prime _ _ hpprime).mp hle
    split_ifs at hj with hjemb
    · have hrad : (D.component j).radical ≤ (D.component i).radical :=
        hpprime.radical_le_iff.mpr hj
      have hIj : I ≤ D.component j := D.intersection_eq.le.trans (iInf_le _ j)
      have hback := his.2 ⟨Ideal.isPrime_radical (D.primary j),
        hIj.trans Ideal.le_radical⟩ hrad
      have hji : j = i := D.radicals_injective (le_antisymm hrad hback)
      exact hjemb (hji ▸ his)
    · exact hpprime.ne_top (top_unique hj)
  obtain ⟨Q, hQ, havoidQ⟩ :=
    Ideal.exists_mem_forall_not_mem_of_forall_not_le D.embeddedIntersection S hS havoid
  refine ⟨Q, hQ, ?_⟩
  apply regular_quotient_iInf D.component D.IsIsolated D.primary Q
  intro i hi
  apply havoidQ _
  exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponRegularComponentCut

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
variable {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K)

/-- The cut used in the descending induction: it lies in the original equation
ideal, has exact multidegree D, and is regular on the selected discarded components. -/
theorem exists_regular_component_cut {ι : Type*} [Finite ι]
    (I₀ J : Ideal M.CoordinateRing) (hI₀J : I₀ ≤ J)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (hJI : J ≤ I₀ ⊔ Ideal.span (Set.range P))
    (q : ι → Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
    (hrel : ∀ i, Hilbert.IsRelevant K M.factorCount M.ambientDimension (q i).1.asIdeal)
    (hdiscard : ∀ i, (q i).1.asIdeal ∉ associatedPrimes M.CoordinateRing
      (M.CoordinateRing ⧸ (I₀ ⊔ Ideal.span (Set.range P)))) :
    ∃ f : M.CoordinateRing, f ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous f D ∧
      (∀ i, f ∉ (q i).1.asIdeal) ∧
      IsRegular (Ideal.Quotient.mk
        (⨅ i, Hilbert.primaryComponent K M.factorCount M.ambientDimension J (q i).1) f) := by
  have hb := (component_partition_primes M J (I₀ ⊔ Ideal.span (Set.range P)) hJI).2
  obtain ⟨f, hf, hhom, hout⟩ := exists_bounded_homogeneous_avoiding M I₀ m P D hP
    (fun i => (q i).1.asIdeal) (fun i => (q i).1.isPrime) hrel
    (fun i => hI₀J.trans (q i).2.1.2)
    (fun i => hb _ (q i).2 (hdiscard i))
  refine ⟨f, hf, hhom, hout, ?_⟩
  classical
  apply (Commute.isRegular_iff (fun y => mul_comm _ y)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hfr : f * r ∈ (⨅ i, Hilbert.primaryComponent K M.factorCount M.ambientDimension J (q i).1) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    exact hz
  simp only [Submodule.mem_iInf] at hfr ⊢
  intro i
  have hprimary := Hilbert.primaryComponent_isPrimary K M.factorCount M.ambientDimension J
    (q i).1 (q i).2
  have hnot : f ∉ (Hilbert.primaryComponent K M.factorCount M.ambientDimension J (q i).1).radical := by
    rw [Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J (q i).1 (q i).2]
    exact hout i
  exact ((Ideal.isPrimary_iff.mp hprimary).2 (mul_comm f r ▸ hfr i)).resolve_right hnot

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponDescendingInduction

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Above the dimension bound for discarded components, the actual relevant
minimal-prime sets of the intermediate and final ideals agree. -/
theorem high_minimalPrimes_eq (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I) (b : ℕ)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ b)
    (q : Ideal M.CoordinateRing)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
    (hdim : b < idealDimension M q) :
    q ∈ J.minimalPrimes ↔ q ∈ I.minimalPrimes := by
  constructor
  · intro hq
    have hassoc : q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) := by
      by_contra hn
      exact (not_le_of_gt hdim) (hbound q hq hrel hn)
    exact minimalPrime_of_between hq hJI (le_associatedPrime hassoc)
  · intro hq
    letI := hq.1.1
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (hJI.trans hq.1.2)
    have hprel : Hilbert.IsRelevant K M.factorCount M.ambientDimension p :=
      fun h => hrel (h.trans hpq)
    have hpdim := Hilbert.idealDimension_antitone M p q
      (Hilbert.minimalPrime_homogeneous M J p hJ hp)
      (Hilbert.minimalPrime_homogeneous M I q hI hq) hpq
    have hassoc : p ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) := by
      by_contra hn
      have := hbound p hp hprel hn
      omega
    have heq : p = q := le_antisymm hpq (hq.2 ⟨hp.1.1, le_associatedPrime hassoc⟩ hpq)
    exact heq ▸ hp

/-- The geometric invariant in Proposition 3.3 follows from the actual
dimension bound on discarded relevant components. -/
theorem dimensionAtLeast_radical_eq_of_discarded_bound (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I) (b : ℕ)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ b)
    (c : ℕ) (hbc : b < c) :
    (dimensionAtLeast M J c).radical = (dimensionAtLeast M I c).radical := by
  apply radical_eq_of_prime_containment
  intro q hq
  rw [dimensionAtLeast_le_prime_iff M J q hq c,
    dimensionAtLeast_le_prime_iff M I q hq c]
  constructor
  · rintro ⟨p, hr, hd, hpq⟩
    have hp := (high_minimalPrimes_eq M J I hJ hI hJI b hbound p.1.asIdeal hr
      (hbc.trans_le hd)).mp p.2
    exact ⟨⟨p.1, hp⟩, hr, hd, hpq⟩
  · rintro ⟨p, hr, hd, hpq⟩
    have hp := (high_minimalPrimes_eq M J I hJ hI hJI b hbound p.1.asIdeal hr
      (hbc.trans_le hd)).mpr p.2
    exact ⟨⟨p.1, hp⟩, hr, hd, hpq⟩

/-- One avoiding cut lowers the dimension bound on every discarded relevant
component by one. Retained components are treated by minimality, not by an
assumed decomposition or numerical dimension formula. -/
theorem cut_discarded_dimension_le (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hPI : P ∈ I) (b : ℕ)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ b + 1)
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q) :
    ∀ q ∈ (J ⊔ Ideal.span {P}).minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ b := by
  intro q hq hrel hnot
  letI := hq.1.1
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hq.1.2)
  have hprel : Hilbert.IsRelevant K M.factorCount M.ambientDimension p :=
    fun h => hrel (h.trans hpq)
  have hPq : P ∈ q := hq.1.2
    ((le_sup_right : Ideal.span {P} ≤ J ⊔ Ideal.span {P})
      (Ideal.subset_span (Set.mem_singleton P)))
  have hpnot : p ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) := by
    intro ha
    have hcutp : J ⊔ Ideal.span {P} ≤ p := by
      apply sup_le hp.1.2
      rw [Ideal.span_singleton_le_iff_mem]
      exact le_associatedPrime ha hPI
    have heq : p = q := le_antisymm hpq (hq.2 ⟨hp.1.1, hcutp⟩ hpq)
    exact hnot (heq ▸ ha)
  have hne : p ≠ q := fun heq => havoid p hp hprel hpnot (heq ▸ hPq)
  have hlt := Hilbert.relevant_prime_dimension_strict M p q hp.1.1 hq.1.1
    (Hilbert.minimalPrime_homogeneous M J p hJ hp)
    (Hilbert.minimalPrime_homogeneous M (J ⊔ Ideal.span {P}) q
      (Hilbert.homogeneous_sup_span M J hJ P D hP) hq)
    hrel (lt_of_le_of_ne hpq hne)
  have := hbound p hp hprel hpnot
  omega

private def PhilipponDescendingInduction_DiscardedBound (J I : Ideal M.CoordinateRing) (b : ℕ) : Prop :=
  ∀ q ∈ J.minimalPrimes, Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
    q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → idealDimension M q ≤ b

private def PhilipponDescendingInduction_CutStep (I E : Ideal M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (J J' : Ideal M.CoordinateRing) (f : M.CoordinateRing) : Prop :=
  J' = J ⊔ Ideal.span {f} ∧ f ∈ E ∧ M.IsHomogeneous f D ∧
  (∀ q ∈ J.minimalPrimes, Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
    q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → f ∉ q) ∧
  IsRegular (Ideal.Quotient.mk
    (⨅ q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J //
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)},
      Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1.1) f)

theorem homogeneous_sup_equations (I₀ : Ideal M.CoordinateRing)
    (hI₀ : IsMultihomogeneousIdeal M I₀) (m : ℕ) (P : Fin m → M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    IsMultihomogeneousIdeal M (I₀ ⊔ Ideal.span (Set.range P)) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hIg : I₀.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I₀
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI₀ f hf d
  have hPg : (Ideal.span (Set.range P)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    rintro f ⟨j, rfl⟩
    obtain ⟨d, _, hd⟩ := hP j
    exact ⟨d, hd⟩
  intro f hf d
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d

private theorem PhilipponDescendingInduction_exists_cut_chain_aux [Infinite K]
    (I₀ : Ideal M.CoordinateRing) (m : ℕ) (P : Fin m → M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (b : ℕ) (J : Ideal M.CoordinateRing) (hJ : IsMultihomogeneousIdeal M J)
    (hI₀J : I₀ ≤ J) (hJI : J ≤ I₀ ⊔ Ideal.span (Set.range P))
    (hb : PhilipponDescendingInduction_DiscardedBound M J (I₀ ⊔ Ideal.span (Set.range P)) b) :
    ∃ C : ℕ → Ideal M.CoordinateRing, ∃ F : ℕ → M.CoordinateRing,
      C 0 = J ∧
      (∀ t ≤ b, IsMultihomogeneousIdeal M (C t) ∧ I₀ ≤ C t ∧
        C t ≤ I₀ ⊔ Ideal.span (Set.range P) ∧
        PhilipponDescendingInduction_DiscardedBound M (C t) (I₀ ⊔ Ideal.span (Set.range P)) (b - t)) ∧
      (∀ t < b, PhilipponDescendingInduction_CutStep M (I₀ ⊔ Ideal.span (Set.range P))
        (Ideal.span (Set.range P)) D (C t) (C (t + 1)) (F t)) := by
  induction b generalizing J with
  | zero =>
    refine ⟨fun _ => J, fun _ => 0, rfl, ?_, ?_⟩
    · intro t ht
      exact ⟨hJ, hI₀J, hJI, by simpa using hb⟩
    · intro t ht
      omega
  | succ b ih =>
    let I := I₀ ⊔ Ideal.span (Set.range P)
    let S := {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J //
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)}
    obtain ⟨f, hf, hfh, hfa, hfr⟩ := exists_regular_component_cut M I₀ J hI₀J m P D hP hJI
      (fun q : S => q.1) (fun q => q.2.1) (fun q => q.2.2)
    have havoid (q : Ideal M.CoordinateRing) (hq : q ∈ J.minimalPrimes)
        (hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
        (hn : q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)) : f ∉ q :=
      hfa ⟨⟨⟨q, hq.1.1⟩, hq⟩, hr, hn⟩
    let J' := J ⊔ Ideal.span {f}
    have hJ'h : IsMultihomogeneousIdeal M J' := Hilbert.homogeneous_sup_span M J hJ f D hfh
    have hI₀J' : I₀ ≤ J' := hI₀J.trans le_sup_left
    have hfI : f ∈ I := (le_sup_right : Ideal.span (Set.range P) ≤ I) hf
    have hJ'I : J' ≤ I := by
      apply sup_le hJI
      rwa [Ideal.span_singleton_le_iff_mem]
    have hb' : PhilipponDescendingInduction_DiscardedBound M J' I b :=
      cut_discarded_dimension_le M J I hJ hJI f D hfh hfI b hb havoid
    obtain ⟨C, F, hC0, hC, hF⟩ := ih J' hJ'h hI₀J' hJ'I hb'
    refine ⟨fun t => Nat.casesOn t J C, fun t => Nat.casesOn t f F, rfl, ?_, ?_⟩
    · intro t ht
      cases t with
      | zero => exact ⟨hJ, hI₀J, hJI, by simpa using hb⟩
      | succ t => simpa only [Nat.succ_sub_succ_eq_sub] using hC t (by omega)
    · intro t ht
      cases t with
      | zero => exact ⟨hC0, hf, hfh, havoid, hfr⟩
      | succ t => exact hF t (by omega)

/-- Constructs the actual dimension-descending part of Proposition 3.3.
The chain contains a cuts, where a is the initial Hilbert dimension; every
equation has the prescribed degree and is regular on the discarded relevant
primary components. Numerical degree-sum bounds are separate assertions. -/
theorem exists_descending_cut_chain_core [Infinite K]
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    let I := I₀ ⊔ Ideal.span (Set.range P)
    let a := idealDimension M I₀
    ∃ J : ℕ → Ideal M.CoordinateRing, ∃ F : ℕ → M.CoordinateRing,
      J 0 = I₀ ∧
      (∀ t ≤ a, IsMultihomogeneousIdeal M (J t) ∧ I₀ ≤ J t ∧ J t ≤ I ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
          idealDimension M q ≤ a - t) ∧
        (∀ c, a - t < c →
          (dimensionAtLeast M (J t) c).radical = (dimensionAtLeast M I c).radical)) ∧
      (∀ t < a, J (t + 1) = J t ⊔ Ideal.span {F t} ∧
        F t ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous (F t) D ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → F t ∉ q) ∧
        IsRegular (Ideal.Quotient.mk
          (⨅ q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension (J t) //
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
            q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)},
            Hilbert.primaryComponent K M.factorCount M.ambientDimension (J t) q.1.1) (F t))) ∧
      (∀ b, dimensionSlice M (J a) b ≤ dimensionSlice M I b) := by
  let I := I₀ ⊔ Ideal.span (Set.range P)
  let a := idealDimension M I₀
  have hI : IsMultihomogeneousIdeal M I := homogeneous_sup_equations M I₀ hI₀ m P D hP
  have hb : PhilipponDescendingInduction_DiscardedBound M I₀ I a := by
    intro q hq _ _
    exact Hilbert.idealDimension_antitone M I₀ q hI₀
      (Hilbert.minimalPrime_homogeneous M I₀ q hI₀ hq) hq.1.2
  obtain ⟨J, F, hJ0, hJ, hF⟩ := PhilipponDescendingInduction_exists_cut_chain_aux M I₀ m P D hP a I₀ hI₀ le_rfl le_sup_left hb
  refine ⟨J, F, hJ0, ?_, hF, ?_⟩
  · intro t ht
    obtain ⟨hJh, hlow, hupp, hbound⟩ := hJ t ht
    exact ⟨hJh, hlow, hupp, hbound,
      dimensionAtLeast_radical_eq_of_discarded_bound M (J t) I hJh hI hupp (a - t) hbound⟩
  · intro b
    obtain ⟨hJh, _, hupp, hbound⟩ := hJ a le_rfl
    apply dimensionSlice_mono M (J a) I hJh hI hupp b
    exact dimensionAtLeast_radical_eq_of_discarded_bound M (J a) I hJh hI hupp (a - a)
      hbound (b + 1) (by omega)

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponColonLength

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.ComponentLength
variable {R : Type*} [CommRing R]

/-- Length additivity for the actual cyclic colon exact sequence, allowing
infinite lengths and zero divisors. -/
theorem quotient_length_colon_add (I : Ideal R) (P : R) :
    Module.length R (R ⧸ I) = Module.length R (R ⧸ I.colon {P}) +
      Module.length R (R ⧸ (I ⊔ Ideal.span {P})) := by
  let C := I.colon {P}
  let J := I ⊔ Ideal.span {P}
  let f : (R ⧸ C) →ₗ[R] (R ⧸ I) := C.liftQ
    (I.mkQ.comp (LinearMap.mulLeft R P)) (by
      intro Q hQ
      change Ideal.Quotient.mk I (P * Q) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change Q ∈ I.colon {P} at hQ
      change P * Q ∈ I
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hQ)
  let g : (R ⧸ I) →ₗ[R] (R ⧸ J) := Submodule.factor (show I ≤ J from le_sup_left)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hx)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk I Q, rfl⟩
  have hexact : Function.Exact f g := by
    intro x
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk J Q = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hQ
      obtain ⟨a, b, hb, heq⟩ := Ideal.mem_span_singleton_sup.mp
        (show Q ∈ Ideal.span {P} ⊔ I by simpa only [sup_comm] using hQ)
      refine ⟨Ideal.Quotient.mk C a, ?_⟩
      change Ideal.Quotient.mk I (P * a) = Ideal.Quotient.mk I Q
      rw [← heq, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, mul_comm]
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hqa : Q - P * a ∈ I := by
        apply Ideal.Quotient.eq.mp
        exact hy.symm
      have hpa : P * a ∈ J := J.mul_mem_right a
        ((le_sup_right : Ideal.span {P} ≤ J) (Ideal.subset_span (Set.mem_singleton P)))
      simpa only [sub_add_cancel] using J.add_mem ((le_sup_left : I ≤ J) hqa) hpa
  exact Module.length_eq_add_of_exact f g hf hg hexact

/-- Localization commutes with colon by one element. -/
theorem localization_map_colon (S : Submonoid R) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization S A] (I : Ideal R) (P : R) :
    (I.colon {P}).map (algebraMap R A) =
      (I.map (algebraMap R A)).colon {algebraMap R A P} := by
  ext z
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
  rw [IsLocalization.mk'_mem_map_algebraMap_iff, Submodule.mem_colon_singleton,
    smul_eq_mul, ← IsLocalization.mk'_one (M := S) (S := A) P,
    ← IsLocalization.mk'_mul, mul_one, IsLocalization.mk'_mem_map_algebraMap_iff]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc]

end PhilipponMultiplicity.ComponentLength

end
end


section
-- Reused implementation: Solutions.PhilipponFiltrationLength

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem localLength_colon_add (I : Ideal M.CoordinateRing) (P : M.CoordinateRing)
    (q : PrimeSpectrum M.CoordinateRing) :
    localLength K M.factorCount M.ambientDimension I q =
      localLength K M.factorCount M.ambientDimension (I.colon {P}) q +
      localLength K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) q := by
  unfold localLength
  rw [ComponentLength.quotient_length_colon_add _ (algebraMap _ (Localization.AtPrime q.asIdeal) P),
    ← ComponentLength.localization_map_colon q.asIdeal.primeCompl,
    Ideal.map_sup, Ideal.map_span, Set.image_singleton]

theorem localLength_filtration_sum (n : ℕ)
    (J : Fin (n + 1) → Ideal M.CoordinateRing) (P : Fin n → M.CoordinateRing)
    (hstep : ∀ j, J j.succ = J j.castSucc ⊔ Ideal.span {P j})
    (hlast : J (Fin.last n) = ⊤) (q : PrimeSpectrum M.CoordinateRing) :
    localLength K M.factorCount M.ambientDimension (J 0) q =
      ∑ j, localLength K M.factorCount M.ambientDimension ((J j.castSucc).colon {P j}) q := by
  induction n with
  | zero =>
    have heq : J 0 = ⊤ := hlast
    rw [heq]
    rw [Fin.sum_univ_zero, localLength, Ideal.map_top]
    exact Module.length_eq_zero
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have htail := ih (fun j => J j.succ) (fun j => P j.succ)
      (fun j => by simpa using hstep j.succ) hlast
    have hfirst := localLength_colon_add M (J 0) (P 0) q
    have hzero : J (Fin.succ 0) = J 0 ⊔ Ideal.span {P 0} := hstep 0
    rw [← hzero, htail] at hfirst
    simpa only [Fin.castSucc_zero, Fin.castSucc_succ] using hfirst

theorem localLength_prime_at_minimal (I Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hIQ : I ≤ Q) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    localLength K M.factorCount M.ambientDimension Q q = if Q = q.asIdeal then 1 else 0 := by
  classical
  by_cases heq : Q = q.asIdeal
  · rw [if_pos heq, heq, localLength, IsLocalization.AtPrime.map_eq_maximalIdeal]
    letI : IsSimpleModule (Localization.AtPrime q.asIdeal)
        ((Localization.AtPrime q.asIdeal) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
    exact Module.length_eq_one _ _
  · rw [if_neg heq, localLength]
    have hnot : ¬ Q ≤ q.asIdeal := by
      intro hle
      exact heq (le_antisymm hle (hq.2 ⟨hQ, hIQ⟩ hle))
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le _ hnot]
    exact Module.length_eq_zero

/-- At every actual minimal prime, the number of matching prime factors in
any finite cyclic prime filtration is exactly the actual generic length. -/
theorem localLength_eq_filtration_count (I : Ideal M.CoordinateRing) (n : ℕ)
    (J : Fin (n + 1) → Ideal M.CoordinateRing) (P : Fin n → M.CoordinateRing)
    (hfirst : J 0 = I) (hlast : J (Fin.last n) = ⊤)
    (hstep : ∀ j, J j.succ = J j.castSucc ⊔ Ideal.span {P j})
    (hprime : ∀ j, ((J j.castSucc).colon {P j}).IsPrime)
    (q : PrimeSpectrum M.CoordinateRing) (hq : q.asIdeal ∈ I.minimalPrimes) :
    (localLength K M.factorCount M.ambientDimension I q).toNat =
      ∑ j, if (J j.castSucc).colon {P j} = q.asIdeal then 1 else 0 := by
  classical
  have hmono : Monotone J := Fin.monotone_iff_le_succ.mpr (fun j => by
    rw [hstep j]; exact le_sup_left)
  have hIQ (j : Fin n) : I ≤ (J j.castSucc).colon {P j} := by
    rw [← hfirst]
    exact (hmono (Fin.zero_le _)).trans Ideal.le_colon
  have hsum := localLength_filtration_sum M n J P hstep hlast q
  rw [hfirst] at hsum
  simp_rw [localLength_prime_at_minimal M I _ (hprime _) (hIQ _) q hq] at hsum
  have hcast : localLength K M.factorCount M.ambientDimension I q =
      ((∑ j, if (J j.castSucc).colon {P j} = q.asIdeal then 1 else 0 : ℕ) : ℕ∞) := by
    simpa using hsum
  rw [hcast, ENat.toNat_natCast]

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponComponentFormula

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem shift_component_of_le (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ)
    (hn : F.totalDegree ≤ n) :
    homogeneousComponent n (FiniteDifference.shift D F) = homogeneousComponent n F := by
  have hs := shift_top D F
  by_cases heq : n = F.totalDegree
  · rw [heq]; exact hs.1
  · rw [homogeneousComponent_eq_zero n F (by omega),
      homogeneousComponent_eq_zero n (FiniteDifference.shift D F) (by omega)]

end PhilipponMultiplicity.ComponentDegree

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem top_dimensional_prime_is_minimal (I Q : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hQ : Q.IsPrime)
    (hQhom : IsMultihomogeneousIdeal M Q) (hIQ : I ≤ Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q)
    (hdim : idealDimension M Q = idealDimension M I) : Q ∈ I.minimalPrimes := by
  letI := hQ
  obtain ⟨R, hR, hRQ⟩ := Ideal.exists_minimalPrimes_le hIQ
  have hRhom := minimalPrime_homogeneous M I R hI hR
  have hIR := idealDimension_antitone M I R hI hRhom hR.1.2
  have heq : R = Q := by
    by_contra hne
    have hlt := relevant_prime_dimension_strict M R Q hR.1.1 hQ hRhom hQhom hrel
      (lt_of_le_of_ne hRQ hne)
    omega
  rwa [← heq]

theorem filtration_top_contribution (I Q : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hQ : Q.IsPrime)
    (hQhom : IsMultihomogeneousIdeal M Q) (hIQ : I ≤ Q)
    (D d : M.FactorIndex → ℕ) :
    eval (fun i => (d i : ℚ))
      (( (idealDimension M I).factorial : ℚ) •
        homogeneousComponent (idealDimension M I)
          (FiniteDifference.shift (fun i => (D i : ℚ))
            (hilbertPolynomial K M.factorCount M.ambientDimension Q))) =
      if IsRelevant K M.factorCount M.ambientDimension Q ∧
          idealDimension M Q = idealDimension M I then idealDegreeValue M Q d else 0 := by
  classical
  have hle := idealDimension_antitone M I Q hI hQhom hIQ
  rw [ComponentDegree.shift_component_of_le _ _ _ hle]
  by_cases hrel : IsRelevant K M.factorCount M.ambientDimension Q
  · by_cases hdim : idealDimension M Q = idealDimension M I
    · rw [if_pos ⟨hrel, hdim⟩, ← hdim]
      rfl
    · rw [if_neg (fun h => hdim h.2), homogeneousComponent_eq_zero _ _
        (show (hilbertPolynomial K M.factorCount M.ambientDimension Q).totalDegree <
          idealDimension M I by change idealDimension M Q < _; omega), smul_zero, map_zero]
  · rw [if_neg (fun h => hrel h.1), irrelevant_prime_hilbertPolynomial_zero M Q hQ hrel,
      map_zero, smul_zero, map_zero]

/-- Associativity of the actual multiprojective degree form, proved from
a homogeneous prime filtration and its localized generic lengths. -/
theorem component_length_formula (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (d : M.FactorIndex → ℕ) :
    idealDegreeValue M I d = topComponentLengthSum M I d := by
  classical
  obtain ⟨n, J, P, D, hfirst, hlast, hhom, hstep⟩ := homogeneous_prime_filtration M I hI
  let Q (j : Fin n) := (J j.castSucc).colon {P j}
  have hQprime (j : Fin n) : (Q j).IsPrime := (hstep j).2.2.2
  have hQhom (j : Fin n) : IsMultihomogeneousIdeal M (Q j) :=
    homogeneous_colon M _ (hhom j.castSucc) _ _ (hstep j).1
  have hmono : Monotone J := Fin.monotone_iff_le_succ.mpr (fun j => by
    rw [(hstep j).2.2.1]; exact le_sup_left)
  have hIQ (j : Fin n) : I ≤ Q j := by
    rw [← hfirst]
    exact (hmono (Fin.zero_le _)).trans Ideal.le_colon
  let T := MinimalComponent K M.factorCount M.ambientDimension I
  letI := Fintype.ofFinite T
  let relevantTop (R : Ideal M.CoordinateRing) : Prop :=
    IsRelevant K M.factorCount M.ambientDimension R ∧ idealDimension M R = idealDimension M I
  let w (q : T) : ℚ := if relevantTop q.val.asIdeal then idealDegreeValue M q.val.asIdeal d else 0
  have hdelta (j : Fin n) :
      (if relevantTop (Q j) then idealDegreeValue M (Q j) d else 0) =
        ∑ q : T, if Q j = q.val.asIdeal then w q else 0 := by
    by_cases hqual : relevantTop (Q j)
    · let q₀ : T := ⟨⟨Q j, hQprime j⟩,
        top_dimensional_prime_is_minimal M I (Q j) hI (hQprime j) (hQhom j) (hIQ j)
          hqual.1 hqual.2⟩
      rw [Finset.sum_eq_single q₀]
      · simp only [q₀, w, if_pos hqual, if_true]
      · intro q hq hne
        apply if_neg
        intro heq
        apply hne
        apply Subtype.ext
        exact PrimeSpectrum.ext heq.symm
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    · rw [if_neg hqual]
      symm
      apply Finset.sum_eq_zero
      intro q hq
      by_cases heq : Q j = q.val.asIdeal
      · rw [if_pos heq]
        dsimp [w]
        exact if_neg (fun h => hqual (heq ▸ h))
      · exact if_neg heq
  have hpoly := hilbertPolynomial_filtration_sum M n J P D hhom
    (fun j => ⟨(hstep j).1, (hstep j).2.2.1⟩) hlast
  rw [hfirst] at hpoly
  have hvalue : idealDegreeValue M I d = ∑ j, ∑ q : T, if Q j = q.val.asIdeal then w q else 0 := by
    change eval _ (( (idealDimension M I).factorial : ℚ) •
      homogeneousComponent (idealDimension M I) (hilbertPolynomial K M.factorCount M.ambientDimension I)) = _
    rw [hpoly, map_sum, Finset.smul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact (filtration_top_contribution M I (Q j) hI (hQprime j) (hQhom j) (hIQ j)
      (D j) d).trans (hdelta j)
  rw [hvalue, Finset.sum_comm]
  unfold topComponentLengthSum
  apply Finset.sum_congr rfl
  intro q hq
  have hlength := localLength_eq_filtration_count M I n J P hfirst hlast
    (fun j => (hstep j).2.2.1) hQprime q.val q.property
  rw [hlength]
  change (∑ j : Fin n, if Q j = q.val.asIdeal then w q else 0) =
    if relevantTop q.val.asIdeal then
      ((∑ j : Fin n, if Q j = q.val.asIdeal then 1 else 0 : ℕ) : ℚ) *
        idealDegreeValue M q.val.asIdeal d else 0
  rw [Nat.cast_sum]
  by_cases hqual : relevantTop q.val.asIdeal
  · rw [if_pos hqual, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases heq : Q j = q.val.asIdeal <;> simp [heq, w, hqual]
  · rw [if_neg hqual]
    apply Finset.sum_eq_zero
    intro j hj
    simp [w, hqual]

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity
open SectionThree

theorem lemma_3_2
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hNontrivial : IsNontrivialIdeal M I)
    (d : M.FactorIndex → ℕ) (hd : ∀ i, 1 ≤ d i) :
    idealDegreeValue M I d = topComponentLengthSum M I d := by
  exact Hilbert.component_length_formula M I hI d

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponDegreeMonotonicity

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem eval_nonneg_of_coeff_nonneg (F : MvPolynomial ι ℚ)
    (hF : ∀ e, 0 ≤ coeff e F) (d : ι → ℕ) : 0 ≤ eval (fun i => (d i : ℚ)) F := by
  classical
  rw [eval_eq]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hF e)
    (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)

end PhilipponMultiplicity.ComponentDegree

namespace PhilipponMultiplicity.Hilbert
open SectionThree ComponentDegree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem degreeValue_sup_span_le (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hdim : idealDimension M (I ⊔ Ideal.span {P}) = idealDimension M I)
    (d : M.FactorIndex → ℕ) :
    idealDegreeValue M (I ⊔ Ideal.span {P}) d ≤ idealDegreeValue M I d := by
  let Q := I.colon {P}
  let F := hilbertPolynomial K M.factorCount M.ambientDimension Q
  have hQhom := homogeneous_colon M I hI P D hP
  have hQdim := idealDimension_antitone M I Q hI hQhom Ideal.le_colon
  have hcoeff := component_nonneg F
    (multigraded_hilbert_polynomial_top_coefficients K M Q hQhom).1
    (idealDimension M I) hQdim
  have hnonneg := eval_nonneg_of_coeff_nonneg _ hcoeff d
  have hpoly := hilbertPolynomial_colon_add M I hI P D hP
  have hcomp := congrArg (homogeneousComponent (idealDimension M I)) hpoly
  rw [map_add] at hcomp
  have hshift := shift_component_of_le (fun i => (D i : ℚ)) F (idealDimension M I) hQdim
  simp only [FiniteDifference.shift] at hshift
  rw [hshift] at hcomp
  change eval _ (degreeForm K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P})) ≤
    eval _ (degreeForm K M.factorCount M.ambientDimension I)
  unfold degreeForm
  change eval _ (((idealDimension M (I ⊔ Ideal.span {P})).factorial : ℚ) •
      homogeneousComponent (idealDimension M (I ⊔ Ideal.span {P}))
        (hilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}))) ≤
    eval _ (((idealDimension M I).factorial : ℚ) •
      homogeneousComponent (idealDimension M I) (hilbertPolynomial K M.factorCount M.ambientDimension I))
  rw [hdim, hcomp, smul_add, map_add]
  have hscaled : 0 ≤ eval (fun i => (d i : ℚ))
      (((idealDimension M I).factorial : ℚ) • homogeneousComponent (idealDimension M I) F) := by
    rw [smul_eq_C_mul, map_mul, eval_C]
    exact mul_nonneg (Nat.cast_nonneg _) hnonneg
  exact le_add_of_nonneg_right hscaled

/-- Inclusion cannot increase the normalized Hilbert degree when the two
actual Hilbert dimensions agree. This is the comparison used after Lemma 3.2. -/
theorem degreeValue_antitone_of_dimension_eq (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J)
    (hle : I ≤ J) (hdim : idealDimension M I = idealDimension M J)
    (d : M.FactorIndex → ℕ) : idealDegreeValue M J d ≤ idealDegreeValue M I d := by
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    by_cases heq : I = J
    · simp [heq]
    · obtain ⟨P, D, hP, hPJ, hPI⟩ := homogeneous_component_outside M I J hI hJ
        (fun h => heq (le_antisymm hle h))
      have hlt : I < I ⊔ Ideal.span {P} := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro h
        apply hPI
        rw [h]
        exact (le_sup_right : Ideal.span {P} ≤ I ⊔ Ideal.span {P})
          (Ideal.subset_span (Set.mem_singleton P))
      have hsub : I ⊔ Ideal.span {P} ≤ J := by
        apply sup_le hle
        rwa [Ideal.span_singleton_le_iff_mem]
      have hmid := homogeneous_sup_span M I hI P D hP
      have hd₁ := idealDimension_antitone M I (I ⊔ Ideal.span {P}) hI hmid le_sup_left
      have hd₂ := idealDimension_antitone M (I ⊔ Ideal.span {P}) J hmid hJ hsub
      have hmd : idealDimension M (I ⊔ Ideal.span {P}) = idealDimension M I := by omega
      exact (ih _ hlt hmid hsub (hmd.trans hdim)).trans
        (degreeValue_sup_span_le M I hI P D hP hmd d)

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponInductionEndpoint

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- At the last stage, every relevant component of the final ideal was
already an isolated component of the intermediate ideal. -/
theorem relevant_minimalPrimes_subset_of_discarded_zero (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ 0)
    (q : Ideal M.CoordinateRing) (hq : q ∈ I.minimalPrimes)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    q ∈ J.minimalPrimes := by
  letI := hq.1.1
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (hJI.trans hq.1.2)
  have hprel : Hilbert.IsRelevant K M.factorCount M.ambientDimension p :=
    fun h => hrel (h.trans hpq)
  have heq : p = q := by
    by_cases ha : p ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)
    · exact le_antisymm hpq (hq.2 ⟨hp.1.1, le_associatedPrime ha⟩ hpq)
    · by_contra hne
      have hs := Hilbert.relevant_prime_dimension_strict M p q hp.1.1 hq.1.1
        (Hilbert.minimalPrime_homogeneous M J p hJ hp)
        (Hilbert.minimalPrime_homogeneous M I q hI hq) hrel (lt_of_le_of_ne hpq hne)
      have := hbound p hp hprel ha
      omega
  exact heq ▸ hp

private theorem PhilipponInductionEndpoint_reduced_primaryComponent (I : Ideal M.CoordinateRing)
    (q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I.radical) :
    Hilbert.primaryComponent K M.factorCount M.ambientDimension I.radical q.1 = q.1.asIdeal := by
  have hq : q.1.asIdeal ∈ I.minimalPrimes := by
    simpa only [Ideal.radical_minimalPrimes] using q.2
  change (I.radical.map (algebraMap M.CoordinateRing (Localization.AtPrime q.1.asIdeal))).comap
    (algebraMap M.CoordinateRing (Localization.AtPrime q.1.asIdeal)) = q.1.asIdeal
  rw [IsLocalization.map_radical q.1.asIdeal.primeCompl,
    Ideal.comap_radical]
  exact Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension I q.1 hq

private theorem PhilipponInductionEndpoint_reduced_componentSum (I : Ideal M.CoordinateRing)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I.radical U D = (by
      classical
      letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
      exact ∑ q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I,
        if Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
          Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U then
          Hilbert.degreeValue K M.factorCount M.ambientDimension q.1.asIdeal D else 0) := by
  classical
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I.radical)
  let e : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I.radical ≃
      Hilbert.MinimalComponent K M.factorCount M.ambientDimension I :=
    Equiv.subtypeEquivRight fun q => by rw [Ideal.radical_minimalPrimes]
  unfold componentHilbertSum Hilbert.componentSum
  apply Fintype.sum_equiv e
  intro q
  rw [PhilipponInductionEndpoint_reduced_primaryComponent M I q]
  rfl

private theorem PhilipponInductionEndpoint_degreeValue_nonneg (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (D : M.FactorIndex → ℕ) :
    0 ≤ Hilbert.degreeValue K M.factorCount M.ambientDimension I D := by
  unfold Hilbert.degreeValue Hilbert.degreeForm
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
  apply mul_nonneg (Nat.cast_nonneg _)
  exact ComponentDegree.eval_nonneg_of_coeff_nonneg _
    (multigraded_hilbert_polynomial_top_coefficients K M I hI).1 D

private theorem PhilipponInductionEndpoint_sum_le_of_finset_injection {α β : Type*} (s : Finset α) (t : Finset β)
    (f : s → β) (hf : Function.Injective f) (hft : ∀ x, f x ∈ t)
    (a : α → ℚ) (b : β → ℚ) (hval : ∀ x, a x.1 = b (f x))
    (hn : ∀ y ∈ t, 0 ≤ b y) : ∑ x ∈ s, a x ≤ ∑ y ∈ t, b y := by
  classical
  calc
    _ = ∑ x ∈ s.attach, a x.1 := (Finset.sum_attach s a).symm
    _ = ∑ x ∈ s.attach, b (f x) := Finset.sum_congr rfl (fun x _ => hval x)
    _ = ∑ y ∈ s.attach.image f, b y := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro y hy; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy; exact hft x)
      (fun y hy _ => hn y hy)

/-- The radical component-sum comparison at the endpoint of the descending
induction. The degree bound for the cuts themselves is not assumed or proved
here: only the final comparison of I with the last intermediate ideal. -/
theorem radical_componentSum_le_of_discarded_zero (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ 0)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I.radical U D ≤ componentHilbertSum M J.radical U D := by
  classical
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
  let s := Finset.univ.filter fun q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I =>
    Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U
  let t := Finset.univ.filter fun q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J =>
    Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U
  let f : s → Hilbert.MinimalComponent K M.factorCount M.ambientDimension J := fun q =>
    ⟨q.1.1, relevant_minimalPrimes_subset_of_discarded_zero M J I hJ hI hJI hbound q.1.1.asIdeal
      q.1.2 (Finset.mem_filter.mp q.2).2.1⟩
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J => x.1) h
  have hft (q : s) : f q ∈ t :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp q.2).2⟩
  rw [PhilipponInductionEndpoint_reduced_componentSum M I U D, PhilipponInductionEndpoint_reduced_componentSum M J U D]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  change (∑ q ∈ s, Hilbert.degreeValue K M.factorCount M.ambientDimension q.1.asIdeal D) ≤
    ∑ q ∈ t, Hilbert.degreeValue K M.factorCount M.ambientDimension q.1.asIdeal D
  exact PhilipponInductionEndpoint_sum_le_of_finset_injection s t f hf hft _ _ (fun _ => rfl) (fun q _ =>
    PhilipponInductionEndpoint_degreeValue_nonneg M q.1.asIdeal (Hilbert.minimalPrime_homogeneous M J q.1.asIdeal hJ q.2) D)

/-- The finite geometric chain and the final radical component comparison.
The two per-cut degree-sum estimates and the scheme-theoretic endpoint
comparison remain separate parts of Proposition 3.3. -/
theorem exists_descending_cut_chain [Infinite K]
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    let I := I₀ ⊔ Ideal.span (Set.range P)
    let a := idealDimension M I₀
    ∃ J : ℕ → Ideal M.CoordinateRing, ∃ F : ℕ → M.CoordinateRing,
      J 0 = I₀ ∧
      (∀ t ≤ a, IsMultihomogeneousIdeal M (J t) ∧ I₀ ≤ J t ∧ J t ≤ I ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
          idealDimension M q ≤ a - t) ∧
        (∀ c, a - t < c →
          (dimensionAtLeast M (J t) c).radical = (dimensionAtLeast M I c).radical)) ∧
      (∀ t < a, J (t + 1) = J t ⊔ Ideal.span {F t} ∧
        F t ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous (F t) D ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → F t ∉ q) ∧
        IsRegular (Ideal.Quotient.mk
          (⨅ q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension (J t) //
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
            q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)},
            Hilbert.primaryComponent K M.factorCount M.ambientDimension (J t) q.1.1) (F t))) ∧
      (∀ b, dimensionSlice M (J a) b ≤ dimensionSlice M I b) ∧
      (∀ (U : MaximalOpenLocus M) (d : M.FactorIndex → ℕ),
        componentHilbertSum M I.radical U d ≤ componentHilbertSum M (J a).radical U d)  := by
  let I := I₀ ⊔ Ideal.span (Set.range P)
  let a := idealDimension M I₀
  obtain ⟨J, F, hJ0, hJ, hF, hslice⟩ := exists_descending_cut_chain_core M I₀ hI₀ m P D hP
  refine ⟨J, F, hJ0, hJ, hF, hslice, ?_⟩
  intro U d
  obtain ⟨hJh, _, hJI, hbound, _⟩ := hJ a le_rfl
  exact radical_componentSum_le_of_discarded_zero M (J a) I hJh
    (homogeneous_sup_equations M I₀ hI₀ m P D hP) hJI
    (by simpa only [a, I, Nat.sub_self] using hbound) U d

end PhilipponMultiplicity.SectionThreeSupport


end
end


section
-- Reused implementation: Solutions.PhilipponPrimaryComponentDegree

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.PrimaryComponentSupport

private theorem PhilipponPrimaryComponentDegree_localization_map_iInf {R ι : Type*} [CommRing R] [Finite ι]
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (Q : ι → Ideal R) :
    (⨅ i, Q i).map (algebraMap R A) = ⨅ i, (Q i).map (algebraMap R A) := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Function.comp_def, IsLocalization.mapFrameHom_apply]
    using map_finset_inf (IsLocalization.mapFrameHom S A) Finset.univ Q

open SectionThree SectionThreeSupport ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The canonical contraction from a minimal-prime localization equals the
corresponding member of any minimal primary decomposition. -/
theorem primaryComponent_eq_decomposition (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    ∃ i : Fin D.count, (D.component i).radical = q.asIdeal ∧
      Hilbert.primaryComponent K M.factorCount M.ambientDimension I q = D.component i := by
  classical
  obtain ⟨i, hi⟩ := (finite_iInf_le_prime D.component q.asIdeal q.isPrime).mp
    (D.intersection_eq.symm.le.trans hq.1.2)
  have hrad (j : Fin D.count) (hj : D.component j ≤ q.asIdeal) :
      (D.component j).radical = q.asIdeal := by
    have hle := q.isPrime.radical_le_iff.mpr hj
    have hI : I ≤ (D.component j).radical :=
      (D.intersection_eq.le.trans (iInf_le D.component j)).trans Ideal.le_radical
    exact le_antisymm hle (hq.2 ⟨Ideal.isPrime_radical (D.primary j), hI⟩ hle)
  have hri := hrad i hi
  let A := Localization.AtPrime q.asIdeal
  let f := algebraMap M.CoordinateRing A
  have hmap : I.map f = (D.component i).map f := by
    apply (congrArg (Ideal.map f) D.intersection_eq).trans
    rw [PhilipponPrimaryComponentDegree_localization_map_iInf q.asIdeal.primeCompl A]
    apply le_antisymm (iInf_le _ i)
    refine le_iInf fun j => ?_
    by_cases heq : j = i
    · subst j; exact le_rfl
    · have hnot : ¬ D.component j ≤ q.asIdeal := by
        intro hj
        exact heq (D.radicals_injective ((hrad j hj).trans hri.symm))
      rw [IsLocalization.AtPrime.map_eq_top_of_not_le (S := A) hnot]
      exact le_top
  refine ⟨i, hri, ?_⟩
  change (I.map f).comap f = D.component i
  rw [hmap]
  exact IsLocalization.under_map_of_isPrimary_disjoint q.asIdeal.primeCompl A (D.primary i)
    (Set.disjoint_left.mpr fun x hx hxI => hx (hi hxI))

end PhilipponMultiplicity.PrimaryComponentSupport

namespace PhilipponMultiplicity.Hilbert
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Isolated primary components of a multihomogeneous ideal are themselves
multihomogeneous, for the canonical localized-component definition. -/
theorem primaryComponent_homogeneous (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    IsMultihomogeneousIdeal M (primaryComponent K M.factorCount M.ambientDimension I q) := by
  obtain ⟨D⟩ := exists_primaryDecomposition M I hI
  obtain ⟨i, _, heq⟩ := PrimaryComponentSupport.primaryComponent_eq_decomposition M I D q hq
  rw [heq]
  exact D.homogeneous i

/-- Hilbert dimension depends only on support: containment in the radical
already gives the usual reversed dimension inequality. -/
theorem idealDimension_le_of_le_radical (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J)
    (hle : I ≤ J.radical) : idealDimension M J ≤ idealDimension M I := by
  classical
  obtain ⟨n, A, P, D, hfirst, hlast, hhom, hstep⟩ := homogeneous_prime_filtration M J hJ
  have hmono : Monotone A := Fin.monotone_iff_le_succ.mpr fun j => by
    rw [(hstep j).2.2.1]; exact le_sup_left
  have hbound (j : Fin n) :
      idealDimension M ((A j.castSucc).colon {P j}) ≤ idealDimension M I := by
    have hprime := (hstep j).2.2.2
    have hJQ : J ≤ (A j.castSucc).colon {P j} := by
      rw [← hfirst]
      exact (hmono (Fin.zero_le _)).trans Ideal.le_colon
    exact idealDimension_antitone M I _ hI
      (homogeneous_colon M _ (hhom j.castSucc) _ _ (hstep j).1)
      (hle.trans (hprime.radical_le_iff.mpr hJQ))
  unfold idealDimension
  rw [← hfirst, hilbertPolynomial_filtration_sum M n A P D hhom
    (fun j => ⟨(hstep j).1, (hstep j).2.2.1⟩) hlast]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  change (FiniteDifference.shift (fun i => (D j i : ℚ))
    (hilbertPolynomial K M.factorCount M.ambientDimension ((A j.castSucc).colon {P j}))).totalDegree ≤ _
  rw [(ComponentDegree.shift_top _ _).2]
  exact hbound j

theorem idealDimension_eq_of_radical_eq (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J)
    (heq : I.radical = J.radical) : idealDimension M I = idealDimension M J := by
  apply le_antisymm
  · exact idealDimension_le_of_le_radical M J I hJ hI (Ideal.le_radical.trans heq.symm.le)
  · exact idealDimension_le_of_le_radical M I J hI hJ (Ideal.le_radical.trans heq.le)

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponSchemeEndpoint

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.PrimaryComponentSupport

private theorem PhilipponSchemeEndpoint_sum_le_of_finset_injection {α β : Type*} (s : Finset α) (t : Finset β)
    (f : s → β) (hf : Function.Injective f) (hft : ∀ x, f x ∈ t)
    (a : α → ℚ) (b : β → ℚ) (hval : ∀ x, a x.1 ≤ b (f x))
    (hn : ∀ y ∈ t, 0 ≤ b y) : ∑ x ∈ s, a x ≤ ∑ y ∈ t, b y := by
  classical
  calc
    _ = ∑ x ∈ s.attach, a x.1 := (Finset.sum_attach s a).symm
    _ ≤ ∑ x ∈ s.attach, b (f x) := Finset.sum_le_sum (fun x _ => hval x)
    _ = ∑ y ∈ s.attach.image f, b y := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro y hy; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy; exact hft x)
      (fun y hy _ => hn y hy)

open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem degreeValue_nonneg (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (D : M.FactorIndex → ℕ) :
    0 ≤ Hilbert.degreeValue K M.factorCount M.ambientDimension I D := by
  unfold Hilbert.degreeValue Hilbert.degreeForm
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
  apply mul_nonneg (Nat.cast_nonneg _)
  exact ComponentDegree.eval_nonneg_of_coeff_nonneg _
    (multigraded_hilbert_polynomial_top_coefficients K M I hI).1 D

end PhilipponMultiplicity.PrimaryComponentSupport

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem primaryComponent_degreeValue_antitone (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I) (q : PrimeSpectrum M.CoordinateRing)
    (hqJ : q.asIdeal ∈ J.minimalPrimes) (hqI : q.asIdeal ∈ I.minimalPrimes)
    (D : M.FactorIndex → ℕ) :
    degreeValue K M.factorCount M.ambientDimension
        (primaryComponent K M.factorCount M.ambientDimension I q) D ≤
      degreeValue K M.factorCount M.ambientDimension
        (primaryComponent K M.factorCount M.ambientDimension J q) D := by
  have hJh := primaryComponent_homogeneous M J hJ q hqJ
  have hIh := primaryComponent_homogeneous M I hI q hqI
  have hle : primaryComponent K M.factorCount M.ambientDimension J q ≤
      primaryComponent K M.factorCount M.ambientDimension I q :=
    Ideal.comap_mono (Ideal.map_mono hJI)
  have hdim := idealDimension_eq_of_radical_eq M _ _ hJh hIh
    ((primaryComponent_radical K M.factorCount M.ambientDimension J q hqJ).trans
      (primaryComponent_radical K M.factorCount M.ambientDimension I q hqI).symm)
  exact degreeValue_antitone_of_dimension_eq M _ _ hJh hIh hle hdim D

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree PrimaryComponentSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Componentwise degree comparison retains the actual primary multiplicities.
The hypothesis is only on minimal primes that contribute to the chosen locus. -/
theorem componentSum_le_of_relevant_minimalPrimes (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I) (U : MaximalOpenLocus M)
    (hmin : ∀ q ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U → q ∈ J.minimalPrimes)
    (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I U D ≤ componentHilbertSum M J U D := by
  classical
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
  let s := Finset.univ.filter fun q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I =>
    Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U
  let t := Finset.univ.filter fun q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J =>
    Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U
  let f : s → Hilbert.MinimalComponent K M.factorCount M.ambientDimension J := fun q =>
    ⟨q.1.1, hmin q.1.1.asIdeal q.1.2
      (Finset.mem_filter.mp q.2).2.1 (Finset.mem_filter.mp q.2).2.2⟩
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J => x.1) h
  have hft (q : s) : f q ∈ t :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp q.2).2⟩
  unfold componentHilbertSum Hilbert.componentSum
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  change (∑ q ∈ s, Hilbert.degreeValue K M.factorCount M.ambientDimension
      (Hilbert.primaryComponent K M.factorCount M.ambientDimension I q.1) D) ≤
    ∑ q ∈ t, Hilbert.degreeValue K M.factorCount M.ambientDimension
      (Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1) D
  exact PhilipponSchemeEndpoint_sum_le_of_finset_injection s t f hf hft _ _
    (fun q => Hilbert.primaryComponent_degreeValue_antitone M J I hJ hI hJI q.1.1 (f q).2 q.1.2 D)
    (fun q _ => degreeValue_nonneg M _ (Hilbert.primaryComponent_homogeneous M J hJ q.1 q.2) D)

/-- The scheme-theoretic endpoint of Proposition 3.3's descending induction.
Unlike the radical endpoint, this bounds the degrees of the actual primary
components, including their multiplicities. -/
theorem componentSum_le_of_discarded_zero (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ 0)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I U D ≤ componentHilbertSum M J U D := by
  exact componentSum_le_of_relevant_minimalPrimes M J I hJ hI hJI U
    (fun q hq hrel _ =>
      relevant_minimalPrimes_subset_of_discarded_zero M J I hJ hI hJI hbound q hq hrel) D

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponEquidimensionalDegree

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem localLength_primaryComponent (I : Ideal M.CoordinateRing)
    (q : PrimeSpectrum M.CoordinateRing) :
    localLength K M.factorCount M.ambientDimension
        (primaryComponent K M.factorCount M.ambientDimension I q) q =
      localLength K M.factorCount M.ambientDimension I q := by
  unfold localLength primaryComponent
  rw [IsLocalization.map_under q.asIdeal.primeCompl]

/-- A canonical primary component has its support's degree multiplied by
the original quotient's actual generic local length. -/
theorem primaryComponent_degreeValue_eq_localLength (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes)
    (hrel : IsRelevant K M.factorCount M.ambientDimension q.asIdeal)
    (d : M.FactorIndex → ℕ) :
    idealDegreeValue M (primaryComponent K M.factorCount M.ambientDimension I q) d =
      ((localLength K M.factorCount M.ambientDimension I q).toNat : ℚ) *
        idealDegreeValue M q.asIdeal d := by
  classical
  let Q := primaryComponent K M.factorCount M.ambientDimension I q
  have hQ := primaryComponent_homogeneous M I hI q hq
  have hp := primaryComponent_isPrimary K M.factorCount M.ambientDimension I q hq
  have hr := primaryComponent_radical K M.factorCount M.ambientDimension I q hq
  have hmin : Q.minimalPrimes = {q.asIdeal} := by
    rw [Ideal.minimalPrimes_eq_subsingleton hp, hr]
  have hdim : idealDimension M q.asIdeal = idealDimension M Q :=
    (idealDimension_eq_of_radical_eq M Q q.asIdeal hQ
      (minimalPrime_homogeneous M I q.asIdeal hI hq)
      (hr.trans q.isPrime.radical.symm)).symm
  let T := MinimalComponent K M.factorCount M.ambientDimension Q
  let q₀ : T := ⟨q, by rw [hmin]; exact Set.mem_singleton _⟩
  have heq (r : T) : r = q₀ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    simpa only [hmin, Set.mem_singleton_iff] using r.2
  have hformula := component_length_formula M Q hQ d
  unfold topComponentLengthSum at hformula
  rw [Finset.sum_eq_single q₀] at hformula
  · rw [if_pos ⟨hrel, hdim⟩] at hformula
    exact hformula.trans (congrArg (fun n : ℕ∞ => (n.toNat : ℚ) * idealDegreeValue M q.asIdeal d)
      (localLength_primaryComponent M I q))
  · intro r _ hne
    exact (hne (heq r)).elim
  · simp

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- On an equidimensional relevant support, selecting an open locus cannot
increase the total Hilbert degree. All canonical primary multiplicities remain. -/
theorem componentSum_le_degreeValue_of_equidimensional (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ q ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q = idealDimension M I)
    (U : MaximalOpenLocus M) (d : M.FactorIndex → ℕ) :
    componentHilbertSum M I U d ≤ idealDegreeValue M I d := by
  classical
  rw [Hilbert.component_length_formula M I hI d]
  unfold componentHilbertSum Hilbert.componentSum topComponentLengthSum
  apply Finset.sum_le_sum
  intro q _
  by_cases hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal
  · by_cases hu : Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U
    · rw [if_pos ⟨hr, hu⟩, if_pos ⟨hr, hdim q.1.asIdeal q.2 hr⟩]
      exact le_of_eq (Hilbert.primaryComponent_degreeValue_eq_localLength M I hI q.1 q.2 hr d)
    · have hn : ¬ (Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
          Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U) := fun h => hu h.2
      rw [if_neg hn, if_pos ⟨hr, hdim q.1.asIdeal q.2 hr⟩]
      exact mul_nonneg (Nat.cast_nonneg _)
        (PrimaryComponentSupport.degreeValue_nonneg M _
          (Hilbert.minimalPrime_homogeneous M I q.1.asIdeal hI q.2) d)
  · rw [if_neg (fun h => hr h.1), if_neg (fun h => hr h.1)]

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponHypersurfaceHilbert

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
namespace Hilbert

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

private theorem PhilipponHypersurfaceHilbert_component_mul_homogeneous
    {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (Q : M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)
      (P * Q) =
    P * weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d Q := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hP' : P ∈ weightedHomogeneousSubmodule K w D :=
    (M.degreePiece_iff P D).mpr hP
  have hh := DirectSum.coe_decompose_mul_add_of_left_mem
    (weightedHomogeneousSubmodule K w) (b := Q) (j := d) hP'
  change ((MvPolynomial.decompose' K w (P * Q)) (D + d) : M.CoordinateRing) =
    P * ((MvPolynomial.decompose' K w Q) d : M.CoordinateRing) at hh
  simpa only [MvPolynomial.decompose'_apply] using hh

instance quotientPiece_finite (I : Ideal M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    Module.Finite K (quotientPiece K M.factorCount M.ambientDimension I d) := by
  unfold quotientPiece
  infer_instance

/-- The actual short exact sequence for multiplication by a regular
multihomogeneous equation, in each multidegree. -/
theorem hilbertFunction_hypersurface_add
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P)) (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension
        (I ⊔ Ideal.span {P}) (D + d) +
      hilbertFunction K M.factorCount M.ambientDimension I d =
    hilbertFunction K M.factorCount M.ambientDimension I (D + d) := by
  classical
  let J := I ⊔ Ideal.span {P}
  let W := fun n => quotientPiece K M.factorCount M.ambientDimension I n
  let V := quotientPiece K M.factorCount M.ambientDimension J (D + d)
  let f : W d →ₗ[K] W (D + d) :=
    ((LinearMap.mulLeft K (Ideal.Quotient.mk I P)).domRestrict (W d)).codRestrict
      (W (D + d)) (by
        rintro ⟨x, Q, hQ, rfl⟩
        refine ⟨P * Q, ?_, ?_⟩
        · exact ((M.degreePiece_iff P D).mpr hP :
            P.IsWeightedHomogeneous (blockWeight M.factorCount M.ambientDimension) D).mul hQ
        · exact map_mul (Ideal.Quotient.mk I) P Q)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hregular.left (congrArg Subtype.val hxy)
  let q : (M.CoordinateRing ⧸ I) →ₐ[K] (M.CoordinateRing ⧸ J) :=
    Ideal.quotientMapₐ J (AlgHom.id K M.CoordinateRing) (by
      intro x hx
      exact (le_sup_left : I ≤ J) hx)
  let g : W (D + d) →ₗ[K] V :=
    (q.toLinearMap.domRestrict (W (D + d))).codRestrict V (by
      rintro ⟨x, Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩)
  have hsurj : Function.Surjective g := by
    rintro ⟨x, Q, hQ, rfl⟩
    exact ⟨⟨Ideal.Quotient.mk I Q, ⟨Q, hQ, rfl⟩⟩, rfl⟩
  have hker : LinearMap.ker g = LinearMap.range f := by
    ext x
    constructor
    · intro hx
      obtain ⟨Q, hQ, hQx⟩ := x.property
      have hQJ : Q ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hx' := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
        change q x.val = 0 at hx'
        rw [← hQx] at hx'
        exact hx'
      obtain ⟨a, b, hb, heq⟩ :=
        Ideal.mem_span_singleton_sup.mp (show Q ∈ Ideal.span {P} ⊔ I by
          simpa only [sup_comm] using hQJ)
      let a' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) d a
      let b' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) (D + d) b
      have hb' : b' ∈ I := hI b hb (D + d)
      have hproj : P * a' + b' = Q := by
        have hh := congrArg
          (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)) heq
        rw [map_add, mul_comm a P, PhilipponHypersurfaceHilbert_component_mul_homogeneous M hP a d,
          IsWeightedHomogeneous.weightedHomogeneousComponent_same hQ] at hh
        exact hh
      refine ⟨⟨Ideal.Quotient.mk I a', ⟨a', ?_, rfl⟩⟩, ?_⟩
      · exact weightedHomogeneousComponent_mem _ _ _
      · apply Subtype.ext
        change Ideal.Quotient.mk I P * Ideal.Quotient.mk I a' = x.val
        change Ideal.Quotient.mk I Q = x.val at hQx
        rw [← hQx, ← hproj, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb', add_zero,
          map_mul]
    · rintro ⟨y, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change q (Ideal.Quotient.mk I P * y.val) = 0
      rw [map_mul]
      have hP0 : q (Ideal.Quotient.mk I P) = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact (le_sup_right : Ideal.span {P} ≤ J) (Ideal.subset_span (Set.mem_singleton P))
      rw [hP0, zero_mul]
  have hdim := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
    LinearMap.finrank_range_of_inj hinj] at hdim
  exact hdim

/-- The finite-difference Hilbert polynomial follows from the exact sequence;
the premise is an actual eventual Hilbert polynomial, not an assigned degree. -/
theorem IsHilbertPolynomial.hypersurface
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P))
    (F : MvPolynomial M.FactorIndex ℚ)
    (hF : IsHilbertPolynomial K M.factorCount M.ambientDimension I F) :
    IsHilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P})
      (F - aeval (fun i => X i - C (D i : ℚ)) F) := by
  obtain ⟨b, hb⟩ := hF
  refine ⟨D + b, fun n hn => ?_⟩
  have hDn : ∀ i, D i ≤ n i := fun i => (Nat.le_add_right _ _).trans (hn i)
  have hbn : ∀ i, b i ≤ n i := fun i => (Nat.le_add_left _ _).trans (hn i)
  have hbsub : ∀ i, b i ≤ n i - D i := by
    intro i
    have := hn i
    change D i + b i ≤ n i at this
    omega
  have hnsub : D + (n - D) = n := by
    funext i
    exact Nat.add_sub_of_le (hDn i)
  have heval : eval (fun i => (n i : ℚ)) (aeval (fun i => X i - C (D i : ℚ)) F) =
      eval (fun i => (((n - D) i : ℕ) : ℚ)) F := by
    have hc : (fun i => ((n i : ℚ) - D i)) = (fun i => (((n - D) i : ℕ) : ℚ)) := by
      funext i
      simp [Nat.cast_sub (hDn i)]
    clear hb
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F i hF =>
        simp only [map_mul, hF, aeval_X, map_sub, eval_X, eval_C]
        rw [congrFun hc i]
  rw [map_sub, heval, hb n hbn, hb (n - D) hbsub]
  have hdim := hilbertFunction_hypersurface_add M I hI P D hP hregular (n - D)
  rw [hnsub] at hdim
  exact_mod_cast (show
    (hilbertFunction K M.factorCount M.ambientDimension I n : ℚ) -
      hilbertFunction K M.factorCount M.ambientDimension I (n - D) =
      hilbertFunction K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) n by
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) hdim
    push_cast at hcast
    linarith)

end Hilbert
end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponRegularCutDegree

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem idealDimension_le_of_minimalPrimes (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (b : ℕ)
    (hb : ∀ q ∈ I.minimalPrimes, IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q ≤ b) : idealDimension M I ≤ b := by
  classical
  obtain ⟨n, A, P, D, hfirst, hlast, hhom, hstep⟩ := homogeneous_prime_filtration M I hI
  have hmono : Monotone A := Fin.monotone_iff_le_succ.mpr fun j => by
    rw [(hstep j).2.2.1]; exact le_sup_left
  unfold idealDimension
  rw [← hfirst, hilbertPolynomial_filtration_sum M n A P D hhom
    (fun j => ⟨(hstep j).1, (hstep j).2.2.1⟩) hlast]
  apply totalDegree_finsetSum_le
  intro j _
  let Q := (A j.castSucc).colon {P j}
  have hQ := (hstep j).2.2.2
  have hQhom := homogeneous_colon M _ (hhom j.castSucc) _ _ (hstep j).1
  change (FiniteDifference.shift (fun i => (D j i : ℚ))
      (hilbertPolynomial K M.factorCount M.ambientDimension Q)).totalDegree ≤ b
  by_cases hr : IsRelevant K M.factorCount M.ambientDimension Q
  · have hIQ : I ≤ Q := by
      rw [← hfirst]
      exact (hmono (Fin.zero_le _)).trans Ideal.le_colon
    letI : Q.IsPrime := hQ
    obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le hIQ
    have hprel : IsRelevant K M.factorCount M.ambientDimension p := fun h => hr (h.trans hpQ)
    rw [(ComponentDegree.shift_top _ _).2]
    exact (idealDimension_antitone M p Q (minimalPrime_homogeneous M I p hI hp)
      hQhom hpQ).trans (hb p hp hprel)
  · rw [irrelevant_prime_hilbertPolynomial_zero M Q hQ hr, map_zero, totalDegree_zero]
    exact Nat.zero_le b

/-- The numerical hypersurface identity at the equation's own degree does
not require positive degree entries once the actual dimension drop is known. -/
theorem regular_cut_degreeValue_of_dimension (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P))
    (hdim : idealDimension M (I ⊔ Ideal.span {P}) + 1 = idealDimension M I) :
    idealDegreeValue M (I ⊔ Ideal.span {P}) D = idealDegreeValue M I D := by
  classical
  let F := hilbertPolynomial K M.factorCount M.ambientDimension I
  let a := F.totalDegree
  let Q := F - FiniteDifference.shift (fun i => (D i : ℚ)) F
  have ha : 0 < a := by change 0 < idealDimension M I; omega
  have hpoly : hilbertPolynomial K M.factorCount M.ambientDimension
      (I ⊔ Ideal.span {P}) = Q :=
    hilbertPolynomial_eq_of_isHilbertPolynomial _ _ _ _
      (IsHilbertPolynomial.hypersurface M I hI P D hP hregular F
        (hilbertPolynomial_spec _ _ _ _ (multigraded_hilbert_polynomial_exists K M I hI)))
  have hdegree : Q.totalDegree = a - 1 := by
    change (hilbertPolynomial K M.factorCount M.ambientDimension
      (I ⊔ Ideal.span {P})).totalDegree + 1 = a at hdim
    rw [hpoly] at hdim
    omega
  have htop := (FiniteDifference.top_difference (fun i => (D i : ℚ)) F a ha le_rfl).2
  unfold idealDegreeValue degreeValue degreeForm
  rw [hpoly]
  change eval _ ((Q.totalDegree.factorial : ℚ) • homogeneousComponent Q.totalDegree Q) =
    eval _ ((a.factorial : ℚ) • homogeneousComponent a F)
  rw [hdegree, htop, MvPolynomial.smul_eq_C_mul, map_mul, eval_C,
    FiniteDifference.eval_deriv_self _ _ _ (homogeneousComponent_isHomogeneous _ _),
    MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
  have haeq : a = (a - 1) + 1 := by omega
  have hfac : ((a - 1).factorial : ℚ) * (a : ℚ) = (a.factorial : ℚ) := by
    have hh := Nat.factorial_succ (a - 1)
    rw [← haeq] at hh
    exact_mod_cast (Nat.mul_comm _ _).trans hh.symm
  rw [← mul_assoc, hfac]

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

private theorem PhilipponRegularCutDegree_componentSum_eq_zero_of_no_relevant_minimalPrimes (I : Ideal M.CoordinateRing)
    (h : ¬ ∃ q ∈ I.minimalPrimes, Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) : componentHilbertSum M I U D = 0 := by
  classical
  unfold componentHilbertSum Hilbert.componentSum
  apply Finset.sum_eq_zero
  intro q _
  exact if_neg (fun hr => h ⟨q.1.asIdeal, q.2, hr.1⟩)

/-- The numerical one-cut bound, with the remaining geometric assertion
about dimensions exposed explicitly. Zero degree entries and empty cuts
are included, and the sum keeps the actual primary multiplicities. -/
theorem componentSum_regular_cut_le_of_dimensions (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P))
    (hcut : ∀ q ∈ (I ⊔ Ideal.span {P}).minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q + 1 = idealDimension M I)
    (U : MaximalOpenLocus M) :
    componentHilbertSum M (I ⊔ Ideal.span {P}) U D ≤ idealDegreeValue M I D := by
  classical
  let J := I ⊔ Ideal.span {P}
  have hJ := Hilbert.homogeneous_sup_span M I hI P D hP
  by_cases hex : ∃ q ∈ J.minimalPrimes, Hilbert.IsRelevant K M.factorCount M.ambientDimension q
  · obtain ⟨q, hq, hr⟩ := hex
    have hqdim := hcut q hq hr
    have hup : idealDimension M J ≤ idealDimension M I - 1 :=
      Hilbert.idealDimension_le_of_minimalPrimes M J hJ _ (by
        intro p hp hpr
        have := hcut p hp hpr
        omega)
    have hlo := Hilbert.idealDimension_antitone M J q hJ
      (Hilbert.minimalPrime_homogeneous M J q hJ hq) hq.1.2
    have hdim : idealDimension M J + 1 = idealDimension M I := by omega
    have hequi : ∀ p ∈ J.minimalPrimes,
        Hilbert.IsRelevant K M.factorCount M.ambientDimension p →
        idealDimension M p = idealDimension M J := by
      intro p hp hpr
      have := hcut p hp hpr
      omega
    exact (componentSum_le_degreeValue_of_equidimensional M J hJ hequi U D).trans_eq
      (Hilbert.regular_cut_degreeValue_of_dimension M I hI P D hP hregular hdim)
  · rw [PhilipponRegularCutDegree_componentSum_eq_zero_of_no_relevant_minimalPrimes M J hex U D]
    exact PrimaryComponentSupport.degreeValue_nonneg M I hI D

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponGroupPrimeComponents

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

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

theorem MultiProjectiveSpace.relevant_of_zeroLocus_nonempty {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (hne : (M.zeroLocus I).Nonempty) :
    Hilbert.IsRelevant K M.factorCount M.ambientDimension I := by
  classical
  obtain ⟨x,hx⟩ := hne
  have hj (i : M.FactorIndex) : ∃ j, (x i).rep j ≠ 0 := by
    simpa only [ne_eq,funext_iff,Pi.zero_apply,not_forall] using
      (Projectivization.rep_nonzero (x i))
  choose j hj using hj
  let F : M.CoordinateRing := ∏ i, X ⟨i,j i⟩
  have hF : F ∈ Hilbert.irrelevantIdeal K M.factorCount M.ambientDimension := by
    apply Ideal.mem_iInf.mpr
    intro i
    apply Ideal.prod_mem _ (Finset.mem_univ i)
    exact Ideal.subset_span ⟨j i,rfl⟩
  intro hle
  have hz := hx F (hle hF)
  have hneF : M.eval F x ≠ 0 := by
    change MvPolynomial.eval (M.coordinate x) (∏ i, X ⟨i,j i⟩) ≠ 0
    simp only [map_prod,eval_X,MultiProjectiveSpace.coordinate]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hj i)
  exact hneF hz

variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem isClosed_idealZeroLocusOnGroup (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) :
    @IsClosed _ G.zariskiTopology (idealZeroLocusOnGroup G I) := by
  letI := G.ambient.zariskiTopology
  letI := G.zariskiTopology
  exact (G.ambient.isClosed_zeroLocus I hI).preimage continuous_induced_dom

/-- A prime component meeting the locally closed embedded group keeps its
entire homogeneous prime ideal on restriction to that group. -/
theorem vanishingIdeal_group_prime [IsAlgClosed K] (q : Ideal G.CoordinateRing)
    (hq : q.IsPrime) (hhom : IsMultihomogeneousIdeal G.ambient q)
    (hGq : G.vanishingIdeal Set.univ ≤ q) (hmeet : ComponentMeetsGroup G q) :
    G.vanishingIdeal (idealZeroLocusOnGroup G q) = q := by
  have heq : G.embedding '' idealZeroLocusOnGroup G q =
      Set.range G.embedding ∩ G.ambient.zeroLocus q := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,rfl⟩,hy⟩
    · rintro ⟨⟨y,rfl⟩,hy⟩
      exact ⟨y,hy,rfl⟩
  change G.ambient.vanishingIdeal _ = q
  rw [heq]
  obtain ⟨x,hx⟩ := hmeet
  apply G.ambient.vanishingIdeal_inter_zeroLocus_of_relevant_prime
    (Set.range G.embedding) G.embedding_locallyClosed q hq hhom
    (G.ambient.relevant_of_zeroLocus_nonempty q ⟨G.embedding x,hx⟩)
  · simpa only [EmbeddedGroupProduct.vanishingIdeal,Set.image_univ] using hGq
  · exact ⟨G.embedding x,⟨x,rfl⟩,hx⟩

theorem exists_minimalPrime_at_group_zero (I : Ideal G.CoordinateRing)
    (x : G.Point) (hx : x ∈ idealZeroLocusOnGroup G I) :
    ∃ q ∈ I.minimalPrimes, x ∈ idealZeroLocusOnGroup G q := by
  let e := MvPolynomial.eval (G.ambient.coordinate (G.embedding x))
  letI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨q,hq,hqe⟩ := Ideal.exists_minimalPrimes_le
    (show I ≤ RingHom.ker e from hx)
  exact ⟨q,hq,hqe⟩

/-- All components of the actual zero set arise from minimal primes meeting G. -/
theorem group_vanishingIdeal_eq_components [IsAlgClosed K]
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (hGI : G.vanishingIdeal Set.univ ≤ I) :
    G.vanishingIdeal (idealZeroLocusOnGroup G I) =
      ⨅ q : {q : Ideal G.CoordinateRing // q ∈ I.minimalPrimes ∧ ComponentMeetsGroup G q},
        q.val := by
  let J := ⨅ q : {q : Ideal G.CoordinateRing //
    q ∈ I.minimalPrimes ∧ ComponentMeetsGroup G q}, q.val
  have hJ : IsMultihomogeneousIdeal G.ambient J := by
    intro P hP D
    apply Ideal.mem_iInf.mpr
    intro q
    exact Hilbert.minimalPrime_homogeneous G.ambient I q.val hI q.property.1
      P (Ideal.mem_iInf.mp hP q) D
  apply le_antisymm
  · apply le_iInf
    intro q
    rw [← vanishingIdeal_group_prime G q.val q.property.1.isPrime
      (Hilbert.minimalPrime_homogeneous G.ambient I q.val hI q.property.1)
      (hGI.trans q.property.1.le) q.property.2]
    apply G.ambient.vanishingIdeal_antitone
    apply Set.image_mono
    exact fun x hx P hP => hx P (q.property.1.le hP)
  · change J ≤ _
    rw [G.ambient.homogeneousIdeal_eq_span J hJ]
    apply Ideal.span_le.mpr
    rintro P ⟨hP,D,hD⟩
    apply Ideal.subset_span
    refine ⟨⟨D,hD⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨q,hq,hxq⟩ := exists_minimalPrime_at_group_zero G I x hx
    exact hxq P (Ideal.mem_iInf.mp hP ⟨q,hq,x,hxq⟩)

theorem varietyDimension_mono {V W : Set G.Point} (h : V ⊆ W) :
    varietyDimension G V ≤ varietyDimension G W := by
  exact Hilbert.idealDimension_antitone G.ambient (G.vanishingIdeal W) (G.vanishingIdeal V)
    (vanishingIdeal_multihomogeneous K _ _) (vanishingIdeal_multihomogeneous K _ _)
    (G.ambient.vanishingIdeal_antitone (Set.image_mono h))

/-- A nonempty group zero set has a maximal-dimensional minimal prime meeting
the group. The dimension is the degree of its actual multigraded Hilbert polynomial. -/
theorem exists_maximal_group_component [IsAlgClosed K]
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (hGI : G.vanishingIdeal Set.univ ≤ I)
    (hne : (idealZeroLocusOnGroup G I).Nonempty) :
    ∃ q ∈ I.minimalPrimes, ComponentMeetsGroup G q ∧
      varietyDimension G (idealZeroLocusOnGroup G q) =
        varietyDimension G (idealZeroLocusOnGroup G I) := by
  classical
  let ι := {q : Ideal G.CoordinateRing // q ∈ I.minimalPrimes ∧ ComponentMeetsGroup G q}
  have hfinite : {q : Ideal G.CoordinateRing |
      q ∈ I.minimalPrimes ∧ ComponentMeetsGroup G q}.Finite :=
    (I.finite_minimalPrimes_of_isNoetherianRing).subset (fun _ h => h.1)
  letI : Fintype ι := hfinite.fintype
  obtain ⟨x,hx⟩ := hne
  obtain ⟨p,hp,hpx⟩ := exists_minimalPrime_at_group_zero G I x hx
  letI : Nonempty ι := ⟨⟨p,hp,x,hpx⟩⟩
  obtain ⟨q,_,hmax⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι)
    Finset.univ_nonempty (fun q => SectionThree.idealDimension G.ambient q.val)
  have hall (p : ι) : SectionThree.idealDimension G.ambient p.val ≤
      SectionThree.idealDimension G.ambient q.val := by
    rw [← hmax]
    exact Finset.le_sup (f := fun q : ι => SectionThree.idealDimension G.ambient q.val)
      (Finset.mem_univ p)
  let J := G.vanishingIdeal (idealZeroLocusOnGroup G I)
  have hJ : IsMultihomogeneousIdeal G.ambient J := vanishingIdeal_multihomogeneous K _ _
  have heq : J = ⨅ p : ι, p.val := group_vanishingIdeal_eq_components G I hI hGI
  refine ⟨q.val,q.property.1,q.property.2,?_⟩
  change SectionThree.idealDimension G.ambient (G.vanishingIdeal _) =
    SectionThree.idealDimension G.ambient J
  rw [vanishingIdeal_group_prime G q.val q.property.1.isPrime
    (Hilbert.minimalPrime_homogeneous G.ambient I q.val hI q.property.1)
    (hGI.trans q.property.1.le) q.property.2]
  apply le_antisymm
  · apply Hilbert.idealDimension_antitone G.ambient J q.val hJ
      (Hilbert.minimalPrime_homogeneous G.ambient I q.val hI q.property.1)
    rw [heq]
    exact iInf_le _ q
  · apply Hilbert.idealDimension_le_of_minimalPrimes G.ambient J hJ
    intro r hr _
    have hle : (⨅ p : ι, p.val) ≤ r := heq ▸ hr.le
    obtain ⟨p,_,hpr⟩ := hr.isPrime.inf_le'.mp
      (show (Finset.univ : Finset ι).inf (fun p => p.val) ≤ r by
        simpa only [Finset.inf_univ_eq_iInf] using hle)
    exact (Hilbert.idealDimension_antitone G.ambient p.val r
      (Hilbert.minimalPrime_homogeneous G.ambient I p.val hI p.property.1)
      (Hilbert.minimalPrime_homogeneous G.ambient J r hJ hr) hpr).trans (hall p)

/-- The common-component step on p. 380. Equality of actual geometric Hilbert
dimensions turns containment between the two selected minimal primes into equality. -/
theorem exists_common_maximal_group_component [IsAlgClosed K]
    (I J : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hJ : IsMultihomogeneousIdeal G.ambient J)
    (hGI : G.vanishingIdeal Set.univ ≤ I) (hGJ : G.vanishingIdeal Set.univ ≤ J)
    (hne : (idealZeroLocusOnGroup G J).Nonempty)
    (hsub : idealZeroLocusOnGroup G J ⊆ idealZeroLocusOnGroup G I)
    (hdim : varietyDimension G (idealZeroLocusOnGroup G I) =
      varietyDimension G (idealZeroLocusOnGroup G J)) :
    ∃ q ∈ I.minimalPrimes, q ∈ J.minimalPrimes ∧ ComponentMeetsGroup G q ∧
      varietyDimension G (idealZeroLocusOnGroup G q) =
        varietyDimension G (idealZeroLocusOnGroup G I) := by
  obtain ⟨q,hq,hmeet,hqdim⟩ := exists_maximal_group_component G J hJ hGJ hne
  have hqhom := Hilbert.minimalPrime_homogeneous G.ambient J q hJ hq
  have hqeq := vanishingIdeal_group_prime G q hq.isPrime hqhom (hGJ.trans hq.le) hmeet
  have hIq : I ≤ q := by
    rw [← hqeq, G.ambient.homogeneousIdeal_eq_span I hI]
    apply Ideal.span_le.mpr
    rintro P ⟨hP,D,hD⟩
    apply Ideal.subset_span
    refine ⟨⟨D,hD⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact hsub (fun Q hQ => hx Q (hq.le hQ)) P hP
  letI := hq.isPrime
  obtain ⟨p,hp,hpq⟩ := Ideal.exists_minimalPrimes_le hIq
  have hpmeet : ComponentMeetsGroup G p := by
    obtain ⟨x,hx⟩ := hmeet
    exact ⟨x,fun P hP => hx P (hpq hP)⟩
  have hphom := Hilbert.minimalPrime_homogeneous G.ambient I p hI hp
  have hpeq := vanishingIdeal_group_prime G p hp.isPrime hphom (hGI.trans hp.le) hpmeet
  have heq : p = q := by
    by_contra hnepq
    obtain ⟨x,hx⟩ := hmeet
    have hlt := Hilbert.relevant_prime_dimension_strict G.ambient p q hp.isPrime hq.isPrime
      hphom hqhom (G.ambient.relevant_of_zeroLocus_nonempty q ⟨G.embedding x,hx⟩)
      (lt_of_le_of_ne hpq hnepq)
    have hpdim := varietyDimension_mono G
      (show idealZeroLocusOnGroup G p ⊆ idealZeroLocusOnGroup G I from
        fun x hx P hP => hx P (hp.le hP))
    change SectionThree.idealDimension G.ambient (G.vanishingIdeal _) ≤ _ at hpdim
    rw [hpeq] at hpdim
    change SectionThree.idealDimension G.ambient (G.vanishingIdeal _) = _ at hqdim
    rw [hqeq] at hqdim
    omega
  subst p
  exact ⟨q,hp,hq,hmeet,hqdim.trans hdim.symm⟩

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzLattice

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
open scoped BigOperators
open Submodule
noncomputable section

namespace PhilipponMultiplicity.MWLattice

def rationalVector {m : ℕ} : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ℚ) where
  toFun v i := v i
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

def integerCube (m : ℕ) (S : ℝ) : Set (Fin m → ℤ) :=
  {v | ∀ i, 0 ≤ v i ∧ (v i : ℝ) ≤ S}

theorem integerCube_finite (m : ℕ) (S : ℝ) : (integerCube m S).Finite := by
  apply (Set.Finite.pi (fun _ : Fin m =>
    (Set.finite_Icc (0 : ℤ) ⌊S⌋))).subset
  intro v hv i _
  exact ⟨(hv i).1, (Int.le_floor).mpr (hv i).2⟩

/-- Standard coordinate directions contain a basis of every rational quotient. -/
theorem coordinate_quotient_basis {m : ℕ} (W : Submodule ℚ (Fin m → ℚ)) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → Fin m), Function.Injective f ∧
      Fintype.card ι + Module.finrank ℚ W = m ∧
      LinearIndependent ℚ (fun i => W.mkQ (Pi.single (f i) 1)) := by
  classical
  let v (i : Fin m) := W.mkQ (Pi.single i 1)
  have hspan : span ℚ (Set.range v) = ⊤ := by
    have h := (Pi.basisFun ℚ (Fin m)).span_eq
    have hm := congrArg (Submodule.map W.mkQ) h
    simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr W.mkQ_surjective, Function.comp_def,
      Pi.basisFun_apply, v] using hm
  obtain ⟨ι,f,hf,hsp,hli⟩ := exists_linearIndependent' ℚ v
  letI : Finite ι := Finite.of_injective f hf
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨ι,inferInstance,f,hf,?_,hli⟩
  have hc := Module.finrank_eq_card_basis (Module.Basis.span hli)
  rw [hsp,hspan,finrank_top] at hc
  have hd := W.finrank_quotient_add_finrank
  simpa only [hc, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hd

/-- A cube larger than its image produces a relation outside any prescribed
rational subspace, with no loss in the coordinate bound. -/
theorem short_relation_outside
    {M : Type*} [AddCommGroup M] {m : ℕ}
    (f : (Fin m → ℤ) →+ M) (W : Submodule ℚ (Fin m → ℚ))
    (B S : ℝ) (hB : 0 ≤ B) (hBS : B ≤ S)
    (hcard : (((f '' integerCube m S).ncard : ℕ) : ℝ) <
      ((⌊B⌋₊+1 : ℕ) : ℝ) ^ (m - Module.finrank ℚ W)) :
    ∃ v : Fin m → ℤ, f v = 0 ∧ rationalVector v ∉ W ∧
      ∀ i, |(v i : ℝ)| ≤ B := by
  classical
  obtain ⟨ι,inst,fidx,hidx,hdim,hlin⟩ := coordinate_quotient_basis W
  letI := inst
  let C := ι → Fin (⌊B⌋₊+1)
  let vec (a : C) : Fin m → ℤ := ∑ j, (a j).val • Pi.single (fidx j) (1 : ℤ)
  have heval (a : C) (j : ι) : vec a (fidx j) = (a j).val := by
    simp [vec, Finset.sum_apply, Pi.single_apply, hidx.eq_iff]
  have heval0 (a : C) (i : Fin m) (hi : i ∉ Set.range fidx) : vec a i = 0 := by
    have hh (j : ι) : fidx j ≠ i := fun h => hi ⟨j,h⟩
    simp [vec, Finset.sum_apply, Pi.single_apply, hh]
  have hvec (a : C) (i : Fin m) : 0 ≤ vec a i ∧ (vec a i : ℝ) ≤ B := by
    by_cases hi : i ∈ Set.range fidx
    · obtain ⟨j,rfl⟩ := hi
      rw [heval]
      constructor
      · positivity
      · exact_mod_cast (Nat.le_floor_iff hB).mp (Nat.le_of_lt_succ (a j).isLt)
    · rw [heval0 a i hi]
      simpa using hB
  let F (a : C) : f '' integerCube m S :=
    ⟨f (vec a),vec a,fun i => ⟨(hvec a i).1,(hvec a i).2.trans hBS⟩,rfl⟩
  letI : Fintype (f '' integerCube m S) :=
    ((integerCube_finite m S).image f).fintype
  have hdim' : Fintype.card ι = m - Module.finrank ℚ W := by omega
  have hc : Fintype.card (f '' integerCube m S) < Fintype.card C := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hcard
    simp only [C, Fintype.card_fun, Fintype.card_fin, hdim']
    exact_mod_cast hcard
  obtain ⟨a,b,hab,hFab⟩ := Fintype.exists_ne_map_eq_of_card_lt F hc
  have hf : f (vec a) = f (vec b) := congrArg Subtype.val hFab
  refine ⟨vec a - vec b,by rw [map_sub,hf,sub_self],?_,?_⟩
  · intro hmem
    apply hab
    have hq : W.mkQ (rationalVector (vec a)) = W.mkQ (rationalVector (vec b)) := by
      apply sub_eq_zero.mp
      rw [← map_sub, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero W).mpr hmem
    have hcast (c : C) : rationalVector (vec c) =
        ∑ j, ((c j).val : ℚ) • Pi.single (fidx j) 1 := by
      ext i
      simp [rationalVector, vec, Finset.sum_apply, Pi.single_apply]
    rw [hcast,hcast,map_sum,map_sum] at hq
    simp only [map_smul] at hq
    have hab' := hlin.fintypeLinearCombination_injective hq
    funext j
    apply Fin.ext
    exact_mod_cast congrFun hab' j
  · intro i
    have ha := hvec a i
    have hb := hvec b i
    change |((vec a i - vec b i : ℤ) : ℝ)| ≤ B
    rw [Int.cast_sub,abs_le]
    have ha0 : (0 : ℝ) ≤ vec a i := by exact_mod_cast ha.1
    have hb0 : (0 : ℝ) ≤ vec b i := by exact_mod_cast hb.1
    constructor <;> linarith

/-- Iterated pigeonhole counting supplies the different bounds on successive
independent relations. The quotient need not be torsion-free. -/
theorem independent_relations_up_to
    {M : Type*} [AddCommGroup M] {m r : ℕ}
    (f : (Fin m → ℤ) →+ M) (X θ : ℝ) (hX : 1 ≤ X)
    (hcount : ((f '' integerCube m (X ^ θ)).ncard : ℝ) ≤ X ^ r)
    (k : ℕ) (hk : k ≤ m)
    (hexponents : ∀ j < k, (r : ℝ) / ((m : ℝ) - j) ≤ θ) :
    ∃ σ : Fin k → (Fin m → ℤ),
      (∀ j, f (σ j) = 0) ∧
      LinearIndependent ℚ (fun j => rationalVector (σ j)) ∧
      ∀ j : Fin k, ∀ i : Fin m,
        |(σ j i : ℝ)| ≤ X ^ ((r : ℝ) / ((m : ℝ) - j.val)) := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0,fun j => Fin.elim0 j,?_,fun j => Fin.elim0 j⟩
    exact linearIndependent_empty_type
  | succ k ih =>
    obtain ⟨σ,hσ,hlin,hbound⟩ := ih (by omega) (fun j hj => hexponents j (by omega))
    let W := span ℚ (Set.range (fun j => rationalVector (σ j)))
    have hW : Module.finrank ℚ W = k := by
      simpa only [W,Fintype.card_fin] using finrank_span_eq_card hlin
    have hkm : k < m := by omega
    have hden : 0 < (m : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkm)
    let B : ℝ := X ^ ((r : ℝ) / ((m : ℝ) - k))
    have hB : 0 < B := Real.rpow_pos_of_pos (by linarith) _
    have hBS : B ≤ X ^ θ := Real.rpow_le_rpow_of_exponent_le hX
      (hexponents k (by omega))
    have hpower : B ^ (m-k) = X ^ r := by
      dsimp only [B]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ X),
        Nat.cast_sub (by omega : k ≤ m), div_mul_cancel₀ _ hden.ne']
      exact Real.rpow_natCast X r
    have hstrict : X ^ r < ((⌊B⌋₊+1 : ℕ) : ℝ) ^ (m-k) := by
      rw [← hpower]
      apply pow_lt_pow_left₀ (by exact_mod_cast Nat.lt_floor_add_one B) hB.le
      omega
    obtain ⟨v,hv,hvW,hvbound⟩ := short_relation_outside f W B (X ^ θ) hB.le hBS
      (by rw [hW]; exact hcount.trans_lt hstrict)
    have hcast : (fun j : Fin (k+1) => rationalVector
        ((Fin.snoc σ v : Fin (k+1) → (Fin m → ℤ)) j)) =
        Fin.snoc (fun j => rationalVector (σ j)) (rationalVector v) := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
    refine ⟨Fin.snoc σ v,?_,?_,?_⟩
    · intro j
      exact Fin.lastCases (by simpa using hv) (fun i => by simpa using hσ i) j
    · rw [hcast]
      exact hlin.finSnoc hvW
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.snoc_last,Fin.val_last] using hvbound
      · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hbound i

/-- The least integer crossing the rank threshold is positive and at most m;
all preceding pigeonhole cubes fit inside the original sampling cube. -/
theorem threshold_index (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (θ : ℝ) (hθ : (r : ℝ) / m ≤ θ) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ (m : ℝ) < k + (r : ℝ) / θ ∧
      ∀ j < k, (r : ℝ) / ((m : ℝ) - j) ≤ θ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ht : 0 < θ := (div_pos hrR hmR).trans_le hθ
  have hex : ∃ k : ℕ, (m : ℝ) < k + (r : ℝ) / θ :=
    ⟨m,by linarith [div_pos hrR ht]⟩
  let k := Nat.find hex
  have hk : (m : ℝ) < k + (r : ℝ) / θ := Nat.find_spec hex
  have hkm : k ≤ m := Nat.find_min' hex (by linarith [div_pos hrR ht])
  have hkpos : 1 ≤ k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz,Nat.cast_zero,zero_add] at hk
    have h1 := (lt_div_iff₀ ht).mp hk
    have h2 := (div_le_iff₀ hmR).mp hθ
    nlinarith
  refine ⟨k,hkpos,hkm,hk,?_⟩
  intro j hj
  have hjm : j < m := lt_of_lt_of_le hj hkm
  have hden : 0 < (m : ℝ) - j := sub_pos.mpr (by exact_mod_cast hjm)
  have hmin : (j : ℝ) + (r : ℝ) / θ ≤ m := le_of_not_gt (Nat.find_min hex hj)
  apply (div_le_iff₀ hden).mpr
  have hdiv : (r : ℝ) / θ ≤ (m : ℝ) - j := by linarith
  have hh := (div_le_iff₀ ht).mp hdiv
  nlinarith

/-- A finite quotient of an integer cube yields all lattice conclusions of
Masser--Wüstholz, with the exact coordinate bounds and strict rank inequality. -/
theorem relations_of_cube_image_bound
    {M : Type*} [AddCommGroup M] {m r : ℕ}
    (f : (Fin m → ℤ) →+ M) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (X θ : ℝ) (hX : 1 ≤ X) (hθ : (r : ℝ) / m ≤ θ)
    (hcount : ((f '' integerCube m (X ^ θ)).ncard : ℝ) ≤ X ^ r) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ (m : ℝ) < k + (r : ℝ) / θ ∧
      ∃ σ : Fin k → LinearMap.ker f.toIntLinearMap,
        k ≤ Module.finrank ℤ (LinearMap.ker f.toIntLinearMap) ∧
        LinearIndependent ℤ (fun j => (σ j).val) ∧
        ∀ j : Fin k, ∀ i : Fin m,
          |((σ j).val i : ℝ)| ≤ X ^ ((r : ℝ) / ((m : ℝ) - j.val)) := by
  obtain ⟨k,hk,hkm,hstrict,hexp⟩ := threshold_index m r hm hr θ hθ
  obtain ⟨σ,hσ,hlin,hbound⟩ := independent_relations_up_to f X θ hX hcount k hkm hexp
  have hZ : LinearIndependent ℤ σ := LinearIndependent.of_comp rationalVector
    (hlin.restrict_scalars' ℤ)
  let τ (j : Fin k) : LinearMap.ker f.toIntLinearMap := ⟨σ j,hσ j⟩
  have hτ : LinearIndependent ℤ τ :=
    LinearIndependent.of_comp (LinearMap.ker f.toIntLinearMap).subtype hZ
  refine ⟨k,hk,hkm,hstrict,τ,?_,hZ,hbound⟩
  simpa only [Fintype.card_fin] using hτ.fintype_card_le_finrank

def combinationHom {K : Type*} [Field K] {G : EmbeddedGroupProduct K}
    {m : ℕ} (γ : Fin m → G.Point) : (Fin m → ℤ) →+ G.Point where
  toFun := integerCombination γ
  map_zero' := by simp [integerCombination]
  map_add' a b := by simp [integerCombination,add_zsmul,Finset.sum_add_distrib]

theorem integerCube_image_eq_grid {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
    {m : ℕ} (γ : Fin m → G.Point) (S : ℝ) :
    combinationHom γ '' integerCube m S = samplingGrid γ S := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨fun i => (v i).toNat,?_,?_⟩
    · intro i
      have heq : ((v i).toNat : ℝ) = (v i : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (hv i).1
      rw [heq]
      exact (hv i).2
    · change (∑ i, (v i) • γ i) = ∑ i, (v i).toNat • γ i
      apply Finset.sum_congr rfl
      intro i _
      calc
        (v i) • γ i = ((v i).toNat : ℤ) • γ i := by
          rw [Int.toNat_of_nonneg (hv i).1]
        _ = (v i).toNat • γ i := natCast_zsmul _ _
  · rintro ⟨a,ha,rfl⟩
    refine ⟨fun i => (a i : ℤ),fun i => ⟨by positivity,by exact_mod_cast ha i⟩,?_⟩
    change (∑ i, (a i : ℤ) • γ i) = ∑ i, a i • γ i
    simp only [natCast_zsmul]

/-- Identify cosets with fibers of the quotient map; no torsion-free assumption. -/
theorem quotient_image_ncard {M : Type*} [AddCommGroup M]
    (H : AddSubgroup M) (S : Set M) :
    ((QuotientAddGroup.mk' H) '' S).ncard =
      (((fun x => (fun y => x+y) '' (H : Set M))) '' S).ncard := by
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
      rw [map_add,show q z = 0 from (QuotientAddGroup.eq_zero_iff z).mpr hz,add_zero]
    · intro hy
      have hz : y-x ∈ H := (QuotientAddGroup.eq_zero_iff (y-x)).mp (by
        change q (y-x) = 0
        rw [map_sub,show q y = q x from hy,sub_self])
      exact ⟨y-x,hz,by abel_nf⟩
  simp_rw [hcoset]
  change (q '' S).ncard = ((fiber ∘ q) '' S).ncard
  simp only [Function.comp_def]
  rw [← Set.image_image fiber q S,Set.ncard_image_of_injective _ hf]

/-- The complete lattice output attached to a geometric grid-coset estimate. -/
theorem relations_of_grid_coset_bound
    {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K} {m r : ℕ}
    (γ : Fin m → G.Point) (H : AlgebraicSubgroup G)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (X θ : ℝ) (hX : 1 ≤ X)
    (hθ : (r : ℝ) / m ≤ θ)
    (hcount : (((fun g => PhilipponMultiplicity.translate g H.carrier) ''
      samplingGrid γ (X ^ θ)).ncard : ℝ) ≤ X ^ r) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ (m : ℝ) < k + (r : ℝ) / θ ∧
      ∃ Z : Submodule ℤ (Fin m → ℤ), k ≤ Module.finrank ℤ Z ∧
        (∀ v ∈ Z, integerCombination γ v ∈ H.carrier) ∧
        ∃ σ : Fin k → Z,
          LinearIndependent ℤ (fun j => (σ j).val) ∧
          ∀ j : Fin k, ∀ i : Fin m,
            |((σ j).val i : ℝ)| ≤ X ^ ((r : ℝ) / ((m : ℝ) - j.val)) := by
  let f := (QuotientAddGroup.mk' H.toAddSubgroup).comp (combinationHom γ)
  have hc : ((f '' integerCube m (X ^ θ)).ncard : ℝ) ≤ X ^ r := by
    change (((QuotientAddGroup.mk' H.toAddSubgroup ∘ combinationHom γ) ''
      integerCube m (X ^ θ)).ncard : ℝ) ≤ _
    simp only [Function.comp_def]
    rw [← Set.image_image (QuotientAddGroup.mk' H.toAddSubgroup) (combinationHom γ)
      (integerCube m (X ^ θ)),integerCube_image_eq_grid,quotient_image_ncard]
    exact hcount
  obtain ⟨k,hk,hkm,hstrict,σ,hrank,hlin,hbound⟩ :=
    relations_of_cube_image_bound f hm hr X θ hX hθ hc
  refine ⟨k,hk,hkm,hstrict,LinearMap.ker f.toIntLinearMap,hrank,?_,σ,hlin,hbound⟩
  intro v hv
  exact (QuotientAddGroup.eq_zero_iff _).mp hv

end PhilipponMultiplicity.MWLattice
end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzGlobalization

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MWGlobalization

/-- Some color occurs above every finite set, with respect to inclusion. -/
theorem exists_cofinal_color {X C : Type*} [Finite C] (color : Finset X → C) :
    ∃ c, ∀ s : Finset X, ∃ t, s ⊆ t ∧ color t = c := by
  classical
  letI := Fintype.ofFinite C
  by_contra h
  push Not at h
  choose s hs using h
  let t := Finset.univ.biUnion s
  exact hs (color t) t (by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨color t, Finset.mem_univ _, hx⟩) rfl

variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

def equationIdeal (Q : Finset G.CoordinateRing) : Ideal G.CoordinateRing :=
  G.vanishingIdeal Set.univ ⊔ Ideal.span (Q : Set G.CoordinateRing)

theorem equationIdeal_homogeneous (Q : Finset G.CoordinateRing)
    (hQ : ∀ P ∈ Q, ∃ D, G.ambient.IsHomogeneous P D) :
    IsMultihomogeneousIdeal G.ambient (equationIdeal G Q) := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    simpa [equationIdeal,EmbeddedGroupProduct.vanishingIdeal] using vanishingIdeal_multihomogeneous K G.ambient
      (G.embedding '' Set.univ)
  | @insert P Q hPQ ih =>
    obtain ⟨D,hD⟩ := hQ P (Finset.mem_insert_self P Q)
    have hh := Hilbert.homogeneous_sup_span G.ambient (equationIdeal G Q)
      (ih (fun F hF => hQ F (Finset.mem_insert_of_mem hF))) P D hD
    simpa only [equationIdeal,Finset.coe_insert,Ideal.span_insert,
      sup_assoc,sup_left_comm,sup_comm] using hh

theorem zero_equationIdeal (Q : Finset G.CoordinateRing) :
    idealZeroLocusOnGroup G (equationIdeal G Q) =
      {x | ∀ P ∈ Q, G.ambient.eval P (G.embedding x) = 0} := by
  ext x
  constructor
  · intro hx P hP
    exact hx P ((show Ideal.span (Q : Set G.CoordinateRing) ≤ equationIdeal G Q from
      le_sup_right) (Ideal.subset_span hP))
  · intro hx
    have hle : equationIdeal G Q ≤
        RingHom.ker (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
      apply sup_le
      · intro P hP
        exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal hP ⟨x,Set.mem_univ x,rfl⟩
      · exact Ideal.span_le.mpr hx
    exact hle

/-- Finite choice followed by the ascending chain condition globalizes local
dimension bounds. The selected equations keep their original degree bound. -/
theorem finite_choice_globalization [IsAlgClosed K]
    {C : Type*} [Finite C] (good : C → Prop) (A : C → AddSubgroup G.Point)
    (d : C → ℕ) (B : ℝ)
    (hlocal : ∀ s : Finset G.Point, ∃ c, good c ∧
      ∃ Q : Finset G.CoordinateRing,
        (∀ P ∈ Q, ∃ D : G.FactorIndex → ℕ,
          G.ambient.IsHomogeneous P D ∧ ∀ i, (D i : ℝ) ≤ B) ∧
        (∀ x ∈ A c, ∀ P ∈ Q, G.ambient.eval P (G.embedding x) = 0) ∧
        ∀ q ∈ (equationIdeal G Q).minimalPrimes,
          (∃ x ∈ s, x ∈ idealZeroLocusOnGroup G q) →
          varietyDimension G (idealZeroLocusOnGroup G q) ≤ d c) :
    ∃ c, good c ∧ ∃ V : GroupSubvariety G,
      (A c : Set G.Point) ⊆ V.carrier ∧ varietyDimension G V.carrier ≤ d c ∧
      DefinedByEquations G V.carrier B := by
  classical
  letI := G.zariskiTopology
  choose color hgood Q hdegree hvanish hdim using hlocal
  obtain ⟨c,hcofinal⟩ := exists_cofinal_color color
  let S : Set G.CoordinateRing := {P | ∃ s, color s = c ∧ P ∈ Q s}
  have hfg : (Submodule.span G.CoordinateRing S).FG := IsNoetherian.noetherian _
  obtain ⟨F,hFS,hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp hfg
  have hFdegree (P : G.CoordinateRing) (hP : P ∈ F) :
      ∃ D : G.FactorIndex → ℕ,
        G.ambient.IsHomogeneous P D ∧ ∀ i, (D i : ℝ) ≤ B := by
    obtain ⟨s,_,hs⟩ := hFS hP
    exact hdegree s P hs
  have hFhom := equationIdeal_homogeneous G F (fun P hP =>
    ⟨(hFdegree P hP).choose,(hFdegree P hP).choose_spec.1⟩)
  have hclosed := isClosed_idealZeroLocusOnGroup G (equationIdeal G F) hFhom
  let V : GroupSubvariety G :=
    ⟨idealZeroLocusOnGroup G (equationIdeal G F),hclosed.isLocallyClosed⟩
  have hAV : (A c : Set G.Point) ⊆ V.carrier := by
    intro x hx
    change x ∈ idealZeroLocusOnGroup G (equationIdeal G F)
    rw [zero_equationIdeal]
    intro P hP
    obtain ⟨s,hs,hPs⟩ := hFS hP
    exact hvanish s x (hs ▸ hx) P hPs
  have hle (s : Finset G.Point) (hs : color s = c) :
      equationIdeal G (Q s) ≤ equationIdeal G F := by
    apply sup_le_sup_left
    change Submodule.span G.CoordinateRing (Q s : Set G.CoordinateRing) ≤
      Submodule.span G.CoordinateRing (F : Set G.CoordinateRing)
    rw [← hspan]
    exact Submodule.span_mono (fun P hP => ⟨s,hs,hP⟩)
  obtain ⟨s,_,hs⟩ := hcofinal ∅
  refine ⟨c,hs ▸ hgood s,V,hAV,?_,F,hFdegree,zero_equationIdeal G F⟩
  obtain ⟨q,hq,⟨x,hx⟩,heq⟩ := exists_maximal_group_component G (equationIdeal G F)
    hFhom le_sup_left ⟨0,hAV (A c).zero_mem⟩
  obtain ⟨t,hxt,ht⟩ := hcofinal {x}
  letI := hq.isPrime
  obtain ⟨p,hp,hpq⟩ := Ideal.exists_minimalPrimes_le ((hle t ht).trans hq.le)
  have hxp : x ∈ idealZeroLocusOnGroup G p := fun P hP => hx P (hpq hP)
  have hpdim := hdim t p hp ⟨x,hxt (Finset.mem_singleton_self x),hxp⟩
  rw [ht] at hpdim
  change varietyDimension G (idealZeroLocusOnGroup G (equationIdeal G F)) ≤ d c
  rw [← heq]
  exact (varietyDimension_mono G
    (show idealZeroLocusOnGroup G q ⊆ idealZeroLocusOnGroup G p from
      fun y hy P hP => hy P (hpq hP))).trans hpdim

theorem coset_count_mono (A H : AddSubgroup G.Point) (hAH : A ≤ H)
    (S : Set G.Point) (hS : S.Finite) :
    ((fun g => translate g (H : Set G.Point)) '' S).ncard ≤
      ((fun g => translate g (A : Set G.Point)) '' S).ncard := by
  unfold translate
  rw [← MWLattice.quotient_image_ncard,← MWLattice.quotient_image_ncard]
  let f := QuotientAddGroup.map A H (AddMonoidHom.id G.Point) hAH
  have heq : (QuotientAddGroup.mk' H) '' S =
      f '' ((QuotientAddGroup.mk' A) '' S) := by
    rw [Set.image_image]
    rfl
  rw [heq]
  exact Set.ncard_image_le (hS.image _)

theorem definedByEquations_isClosed {V : Set G.Point} {B : ℝ}
    (hV : DefinedByEquations G V B) : @IsClosed _ G.zariskiTopology V := by
  obtain ⟨Q,hQ,hV⟩ := hV
  rw [hV,← zero_equationIdeal]
  exact isClosed_idealZeroLocusOnGroup G _ (equationIdeal_homogeneous G Q
    (fun P hP => ⟨(hQ P hP).choose,(hQ P hP).choose_spec.1⟩))

theorem bounded_vectors_finite (m : ℕ) (R : ℝ) :
    {v : Fin m → ℤ | ∀ i, |(v i : ℝ)| ≤ R}.Finite := by
  apply (Set.Finite.pi (fun _ : Fin m => Set.finite_Icc ⌈-R⌉ ⌊R⌋)).subset
  intro v hv i _
  exact ⟨Int.ceil_le.mpr (abs_le.mp (hv i)).1,Int.le_floor.mpr (abs_le.mp (hv i)).2⟩

end PhilipponMultiplicity.MWGlobalization

end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzGeometricAssembly
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u

theorem geometric_coset_bound_of_local_prime_estimate
    (hlocal : ∀
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (htranslation : MWTranslationBound (singleGroupProduct E) a)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0})
    (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 1 ≤ R)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)),
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * R),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∀ Γ : Submodule ℤ G.Point, Γ.FG → (∀ i, γ i ∈ Γ) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ relations : Finset (Fin m → ℤ), (∀ v ∈ relations, ∀ i, |(v i : ℝ)| ≤ R) ∧
        let A := (Submodule.span ℤ
          (integerCombination γ '' (relations : Set (Fin m → ℤ)))).toAddSubgroup
        ((((fun g => translate g (A : Set G.Point)) '' samplingGrid γ R).ncard : ℝ) ≤
          ((D : ℝ) / c) ^ r) ∧
        ∃ Q : Finset G.CoordinateRing,
          (∀ F ∈ Q, ∃ d : G.FactorIndex → ℕ,
            G.ambient.IsHomogeneous F d ∧
              ∀ i, (d i : ℝ) ≤ (a : ℝ) ^ G.dimension * (D : ℝ)) ∧
          (∀ x ∈ A, ∀ F ∈ Q, G.ambient.eval F (G.embedding x) = 0) ∧
          ∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (Q : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) →
            varietyDimension G (idealZeroLocusOnGroup G q) ≤ G.dimension - r)
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (htranslation : MWTranslationBound (singleGroupProduct E) a)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0})
    (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 1 ≤ R)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)) :
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * R),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ H : AlgebraicSubgroup G, varietyDimension G H.carrier ≤ G.dimension - r ∧
        ((((fun g => translate g H.carrier) '' samplingGrid γ R).ncard : ℝ) ≤
          ((D : ℝ) / c) ^ r) ∧
        ∃ V : GroupSubvariety G, H.carrier ⊆ V.carrier ∧
          varietyDimension G V.carrier ≤ G.dimension - r ∧
          DefinedByEquations G V.carrier ((a : ℝ) ^ G.dimension * (D : ℝ)) := by
  classical
  dsimp only
  intro hvanish hnonzero
  let G := singleGroupProduct E
  letI := G.zariskiTopology
  letI := hK.isAlgClosed
  let c : ℝ := 1 / ((a : ℝ)^G.dimension * (b : ℝ)^(E.ambientDimension-G.dimension))
  let X : ℝ := (D : ℝ) / c
  let B : ℝ := (a : ℝ)^G.dimension * (D : ℝ)
  let vectors := (MWGlobalization.bounded_vectors_finite m R).toFinset
  let labels := (Finset.range (G.dimension+1)).product vectors.powerset
  let C := {l // l ∈ labels}
  let A (l : C) : AddSubgroup G.Point :=
    (Submodule.span ℤ (integerCombination γ '' (l.val.2 : Set (Fin m → ℤ)))).toAddSubgroup
  let good (l : C) : Prop := 1 ≤ l.val.1 ∧ l.val.1 ≤ G.dimension ∧
    ((((fun g => translate g (A l : Set G.Point)) '' samplingGrid γ R).ncard : ℝ) ≤ X ^ l.val.1)
  have hfiniteLocal (s : Finset G.Point) : ∃ l : C, good l ∧
      ∃ Q : Finset G.CoordinateRing,
        (∀ F ∈ Q, ∃ d : G.FactorIndex → ℕ,
          G.ambient.IsHomogeneous F d ∧ ∀ i, (d i : ℝ) ≤ B) ∧
        (∀ x ∈ A l, ∀ F ∈ Q, G.ambient.eval F (G.embedding x) = 0) ∧
        ∀ q ∈ (MWGlobalization.equationIdeal G Q).minimalPrimes,
          (∃ x ∈ s, x ∈ idealZeroLocusOnGroup G q) →
          varietyDimension G (idealZeroLocusOnGroup G q) ≤ G.dimension - l.val.1 := by
    let seeds := s ∪ Finset.univ.image γ
    let Γ := Submodule.span ℤ (seeds : Set G.Point)
    have hfg : Γ.FG := ⟨seeds,rfl⟩
    have hγ (i : Fin m) : γ i ∈ Γ := Submodule.subset_span
      (Finset.mem_union_right s (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
    obtain ⟨r,hr,hrn,relations,hrelations,hcount,Q,hQ,hAQ,hqdim⟩ :=
      hlocal K hK E hn hconnected a b ha hb htranslation hclosure m D hm hD
        γ R hR P hP hvanish hnonzero Γ hfg hγ
    have hl : (r,relations) ∈ labels := by
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hrn),Finset.mem_powerset.mpr ?_⟩
      intro v hv
      exact (MWGlobalization.bounded_vectors_finite m R).mem_toFinset.mpr (hrelations v hv)
    refine ⟨⟨(r,relations),hl⟩,⟨hr,hrn,hcount⟩,Q,hQ,hAQ,?_⟩
    intro q hq hx
    obtain ⟨x,hxs,hxq⟩ := hx
    exact hqdim q hq ⟨x,Submodule.subset_span (Finset.mem_union_left _ hxs),hxq⟩
  obtain ⟨l,hl,V,hAV,hVdim,hVeq⟩ :=
    MWGlobalization.finite_choice_globalization G good A
      (fun l => G.dimension - l.val.1) B hfiniteLocal
  let H := G.algebraicClosure (A l)
  have hAH : A l ≤ H.toAddSubgroup := subset_closure
  have hHV : H.carrier ⊆ V.carrier :=
    closure_minimal hAV (MWGlobalization.definedByEquations_isClosed G hVeq)
  have hgrid : (samplingGrid γ R).Finite := by
    rw [← MWLattice.integerCube_image_eq_grid]
    exact (MWLattice.integerCube_finite m R).image _
  have hcount := MWGlobalization.coset_count_mono G (A l) H.toAddSubgroup hAH
    (samplingGrid γ R) hgrid
  refine ⟨l.val.1,hl.1,hl.2.1,H,(varietyDimension_mono G hHV).trans hVdim,?_,
    V,hHV,hVdim,hVeq⟩
  exact (show (_ : ℝ) ≤ _ by exact_mod_cast hcount).trans hl.2.2

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (htranslation : MWTranslationBound (singleGroupProduct E) a)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0})
    (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 1 ≤ R)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)) :
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * R),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ H : AlgebraicSubgroup G, varietyDimension G H.carrier ≤ G.dimension - r ∧
        ((((fun g => _root_.PhilipponMultiplicity.translate g H.carrier) '' samplingGrid γ R).ncard : ℝ) ≤
          ((D : ℝ) / c) ^ r) ∧
        ∃ V : GroupSubvariety G, H.carrier ⊆ V.carrier ∧
          varietyDimension G V.carrier ≤ G.dimension - r ∧
          DefinedByEquations G V.carrier ((a : ℝ) ^ G.dimension * (D : ℝ)) := by
  exact geometric_coset_bound_of_local_prime_estimate
    (@masser_wustholz_local_prime_estimate) K hK E hn hconnected a b ha hb
    htranslation hclosure m D hm hD γ R hR P hP
