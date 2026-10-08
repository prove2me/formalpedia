-- Prove2me | solution 1 for PhilipponMultiplicity.exists_open_preserving_point_local_isolated_equations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T13:01:05.672925+00:00
-- url     : https://prove2.me/submissions/a68ca74e-aa4a-4916-a028-a285e6c10ab8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_finite_local_mixed_slices
import Definitions.Def_P2M_Util
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Spectrum.Prime.Jacobson


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

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosedPointSmoothness

/-- On an open subset of a finite type affine scheme over a field, smoothness
can be tested on points closed in the ambient affine scheme. -/
theorem smooth_on_open_of_maximal
    (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R]
    (U : Set (PrimeSpectrum R)) (hU : IsOpen U)
    (h : ∀ q ∈ U, q.asIdeal.IsMaximal → Algebra.IsSmoothAt K q.asIdeal) :
    ∀ q ∈ U, Algebra.IsSmoothAt K q.asIdeal := by
  letI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K) (B := R)
  letI : Algebra.FinitePresentation K R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  intro q hq
  by_contra hn
  obtain ⟨m, ⟨hmU, hmns⟩, hmclosed⟩ := nonempty_inter_closedPoints
    (Z := U \ Algebra.smoothLocus K R) ⟨q, hq, hn⟩
    (hU.isLocallyClosed.inter Algebra.isOpen_smoothLocus.isClosed_compl.isLocallyClosed)
  exact hmns (h m hmU ((PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mp hmclosed))

/-- Smoothness is unchanged by commuting quotient and localization. The
equivalence respects the ground field, not just the underlying rings. -/
theorem point_local_iff_quotient_local
    {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
    Algebra.FormallySmooth K
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ↔
      Algebra.IsSmoothAt K (p.map (Ideal.Quotient.mk I)) := by
  letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  letI : IsScalarTower K (R ⧸ I)
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.FormallySmooth.iff_of_equiv
    ((AlgebraicGroupCM.localizedQuotientEquiv I p hIp).restrictScalars K)

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The punctured multicone is open: in each finite coordinate block at least
one coordinate must remain outside the prime. -/
theorem isOpen_punctured_quotient (I : Ideal M.CoordinateRing) :
    IsOpen {q : PrimeSpectrum (M.CoordinateRing ⧸ I) |
      ∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
        Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite (fun i => isOpen_iUnion (fun j =>
    (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩))).isOpen))

/-- Hilbert's Nullstellensatz identifies every closed point of the quotient
with an actual coordinate tuple satisfying its equations and block conditions. -/
theorem maximal_is_point [IsAlgClosed K]
    (I : Ideal M.CoordinateRing) (q : PrimeSpectrum (M.CoordinateRing ⧸ I))
    (hq : q.asIdeal.IsMaximal)
    (hblocks : ∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
      Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) :
    ∃ v : M.Variable → K,
      (∀ i : M.FactorIndex,
        (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) ∧
      (∀ P ∈ I, MvPolynomial.eval v P = 0) ∧
      q.asIdeal = (MvPolynomial.vanishingIdeal K {v}).map (Ideal.Quotient.mk I) := by
  letI : q.asIdeal.IsMaximal := hq
  let p := q.asIdeal.comap (Ideal.Quotient.mk I)
  have hp : p.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨v, hv⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hp
  have hIp : I ≤ p := by
    intro P hP
    change Ideal.Quotient.mk I P ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hP]
    exact q.asIdeal.zero_mem
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := hblocks i
    intro hz
    apply hj
    change MvPolynomial.X ⟨i,j⟩ ∈ p
    rw [hv]
    have hvj := congrFun hz j
    simpa [MvPolynomial.vanishingIdeal] using hvj
  · intro P hP
    have hm := hIp hP
    rw [hv] at hm
    simpa [MvPolynomial.vanishingIdeal] using hm
  · rw [← hv]
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q.asIdeal).symm

/-- Smoothness at actual nonzero-block tuples controls every prime of the
punctured multicone, including its nonclosed points. -/
theorem smooth_punctured_of_pointwise [IsAlgClosed K]
    (I : Ideal M.CoordinateRing)
    (h : ∀ v : M.Variable → K,
      (∀ i : M.FactorIndex,
        (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
      (∀ P ∈ I, MvPolynomial.eval v P = 0) →
      Algebra.FormallySmooth K
        ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
          I.map (algebraMap M.CoordinateRing
            (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) :
    ∀ q : PrimeSpectrum (M.CoordinateRing ⧸ I),
      (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
        Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
      Algebra.IsSmoothAt K q.asIdeal := by
  apply smooth_on_open_of_maximal K (M.CoordinateRing ⧸ I) _
    (isOpen_punctured_quotient M I)
  intro q hq hmax
  obtain ⟨v, hv, hIv, hqv⟩ := maximal_is_point M I q hmax hq
  have hIp : I ≤ MvPolynomial.vanishingIdeal K {v} := by
    intro P hP
    simpa [MvPolynomial.vanishingIdeal] using hIv P hP
  have hs := (point_local_iff_quotient_local (K := K) I
    (MvPolynomial.vanishingIdeal K {v}) hIp).mp (h v hv hIv)
  simpa only [← hqv] using hs

end PhilipponMultiplicity.ClosedPointSmoothness

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AffineJacobian.LocalSmoothness
open MvPolynomial

/-- A finite polynomial presentation is smooth wherever its chosen Jacobian
minor is nonzero. This allows arbitrary relative dimension. -/
theorem isSmoothAt_of_jacobian_not_mem
    {B C ι τ : Type*} [CommRing B] [CommRing C] [Algebra B C]
    [Finite ι] [Finite τ] (P : Algebra.PreSubmersivePresentation B C ι τ)
    (q : Ideal C) [q.IsPrime] (hq : P.jacobian ∉ q) : Algebra.IsSmoothAt B q := by
  letI : Algebra.FinitePresentation B C := P.finitePresentation_of_isFinite
  let j := P.jacobian
  let D := Localization.Away j
  let Q := (Algebra.PreSubmersivePresentation.localizationAway D j).comp P
  have hunit : IsUnit Q.jacobian := by
    change IsUnit ((Algebra.PreSubmersivePresentation.localizationAway D j).comp P).jacobian
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian]
    exact (IsLocalization.Away.algebraMap_isUnit j).mul
      (IsLocalization.Away.algebraMap_isUnit j)
  let Q' : Algebra.SubmersivePresentation B D (Unit ⊕ ι) (Unit ⊕ τ) :=
    { Q with jacobian_isUnit := hunit }
  letI : Algebra.IsStandardSmooth B D := Q'.isStandardSmooth
  have hsub : (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum C)) ⊆
      Algebra.smoothLocus B C :=
    Algebra.basicOpen_subset_smoothLocus_iff.mpr inferInstance
  exact hsub (show (⟨q, inferInstance⟩ : PrimeSpectrum C) ∈ PrimeSpectrum.basicOpen j from hq)

/-- The explicit derivative minor is the Jacobian of the naive quotient
presentation. Its nonvanishing at a point yields smoothness at that point. -/
theorem smooth_quotient_of_minor
    {K σ : Type*} [Field K] [Finite σ]
    (r : ℕ) (F : Fin r → MvPolynomial σ K) (e : Fin r ↪ σ)
    (a : σ → K) (hF : ∀ i, eval a (F i) = 0)
    (hdet : eval a (Matrix.of (fun i j : Fin r => pderiv (e i) (F j))).det ≠ 0) :
    let I := Ideal.span (Set.range F)
    Algebra.FormallySmooth K
      ((Localization.AtPrime (vanishingIdeal K {a})) ⧸
        I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a})))) := by
  classical
  let I := Ideal.span (Set.range F)
  let p := vanishingIdeal K {a}
  have hIp : I ≤ p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simpa [p,vanishingIdeal] using hF i
  let q := p.map (Ideal.Quotient.mk I)
  letI : q.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  let P : Algebra.PreSubmersivePresentation K ((MvPolynomial σ K) ⧸ I) σ (Fin r) :=
    { Algebra.Presentation.naive (v := F) with map := e, map_inj := e.injective }
  have hmatrix : P.jacobiMatrix = Matrix.of (fun i j : Fin r => pderiv (e i) (F j)) := by
    ext i j
    rw [P.jacobiMatrix_apply]
    rfl
  have hmap : algebraMap P.Ring ((MvPolynomial σ K) ⧸ I) = Ideal.Quotient.mk I := by
    rw [P.algebraMap_eq]
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [RingHom.coe_coe, aeval_C]
      rfl
    · intro i
      simp only [RingHom.coe_coe, aeval_X]
      rfl
  have hq : P.jacobian ∉ q := by
    rw [P.jacobian_eq_jacobiMatrix_det,hmatrix,hmap]
    intro h
    have hp := (Ideal.mem_quotient_iff_mem hIp).mp h
    apply hdet
    simpa [p,vanishingIdeal] using hp
  have hs := isSmoothAt_of_jacobian_not_mem P q hq
  exact (PhilipponMultiplicity.ClosedPointSmoothness.point_local_iff_quotient_local
    (K := K) I p hIp).mpr hs

/-- Equality of the actual localized ideals transfers the Jacobian criterion
to a local generating family, without asserting global ideal generation. -/
theorem smooth_local_quotient_of_generators
    {K σ : Type*} [Field K] [Finite σ]
    (J : Ideal (MvPolynomial σ K)) (a : σ → K)
    (r : ℕ) (F : Fin r → MvPolynomial σ K) (e : Fin r ↪ σ)
    (hF : ∀ i, eval a (F i) = 0)
    (hgen : (Ideal.span (Set.range F)).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a}))) =
      J.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a}))))
    (hdet : eval a (Matrix.of (fun i j : Fin r => pderiv (e i) (F j))).det ≠ 0) :
    Algebra.FormallySmooth K
      ((Localization.AtPrime (vanishingIdeal K {a})) ⧸
        J.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a})))) := by
  have hs := smooth_quotient_of_minor r F e a hF hdet
  exact (Algebra.FormallySmooth.iff_of_equiv
    (Ideal.quotientEquivAlgOfEq K hgen)).mp hs

end AffineJacobian.LocalSmoothness
end

end


section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap

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

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.PrimeAvoidance

/-- Only associated primes contained in the localization prime can obstruct
regularity after localization. -/
theorem regular_atPrime_of_avoids_associatedPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (a : R)
    (h : ∀ q ∈ associatedPrimes R R, q ≤ p → a ∉ q) :
    IsSMulRegular (Localization.AtPrime p)
      (algebraMap R (Localization.AtPrime p) a) := by
  let S := Localization.AtPrime p
  by_contra hn
  have hm : algebraMap R S a ∈ ⋃ q ∈ associatedPrimes S S, (q : Set S) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hn
  obtain ⟨q, hq, ha⟩ := Set.mem_iUnion₂.mp hm
  have hqa : q.comap (algebraMap R S) ∈ associatedPrimes R R :=
    Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      p.primeCompl (Algebra.linearMap R S) q hq (IsNoetherian.noetherian _)
  have hle : q.comap (algebraMap R S) ≤ p := by
    have hd := (IsLocalization.disjoint_under_iff p.primeCompl S q).mpr hq.1.ne_top
    simpa only [Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.disjoint_compl_left_iff_subset] using! hd
  exact h _ hqa hle ha

/-- Quotienting and localizing transfer associated-prime avoidance to the
precise ideal-membership injectivity condition used in a mixed cut flag. -/
theorem mul_mem_localized_of_avoids_associatedPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) (a : R)
    (h : ∀ q ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      q ≤ p.map (Ideal.Quotient.mk I) → Ideal.Quotient.mk I a ∉ q) :
    ∀ x : Localization.AtPrime p,
      algebraMap R (Localization.AtPrime p) a * x ∈
        I.map (algebraMap R (Localization.AtPrime p)) →
      x ∈ I.map (algebraMap R (Localization.AtPrime p)) := by
  let Q := R ⧸ I
  let q := p.map (Ideal.Quotient.mk I)
  letI : q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa using hIp)
  let S := Localization.AtPrime p
  let J := I.map (algebraMap R S)
  let e := AlgebraicGroupCM.localizedQuotientEquiv I p hIp
  have hr := regular_atPrime_of_avoids_associatedPrimes q (Ideal.Quotient.mk I a) h
  have hecoeff := e.commutes (Ideal.Quotient.mk I a)
  change e (Ideal.Quotient.mk J (algebraMap R S a)) =
    algebraMap Q (Localization.AtPrime q) (Ideal.Quotient.mk I a) at hecoeff
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk J x = 0
  apply e.injective
  apply hr
  change algebraMap Q (Localization.AtPrime q) (Ideal.Quotient.mk I a) *
      e (Ideal.Quotient.mk J x) =
    algebraMap Q (Localization.AtPrime q) (Ideal.Quotient.mk I a) * e 0
  rw [map_zero, mul_zero, ← hecoeff, ← map_mul, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

end PrimeAvoidance

namespace MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A prime below the evaluation prime of a nonzero-block point still
contains no entire coordinate block. -/
theorem nonzero_blocks_below_evaluation
    (I : Ideal M.CoordinateRing) (v : M.Variable → K)
    (hI : ∀ P ∈ I, MvPolynomial.eval v P = 0)
    (hv : ∀ i : M.FactorIndex,
      (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0)
    (q : Ideal (M.CoordinateRing ⧸ I))
    (hq : q ≤ (MvPolynomial.vanishingIdeal K {v}).map (Ideal.Quotient.mk I)) :
    ∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
      Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q := by
  have hIp : I ≤ MvPolynomial.vanishingIdeal K {v} := by
    intro P hP
    simpa [MvPolynomial.vanishingIdeal] using hI P hP
  intro i
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (hv i)
  refine ⟨j, fun hc => hj ?_⟩
  have hm := (Ideal.mem_quotient_iff_mem hIp).mp (hq hc)
  simpa [MvPolynomial.vanishingIdeal] using hm

/-- Avoiding the associated primes on the punctured multicone makes a cut
injective in every geometric point-local quotient. -/
theorem point_local_injective_of_associated_prime_avoidance
    (I : Ideal M.CoordinateRing) (P : M.CoordinateRing)
    (h : ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ I) (M.CoordinateRing ⧸ I),
      (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
        Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q) →
      Ideal.Quotient.mk I P ∉ q)
    (v : M.Variable → K)
    (hv : ∀ i : M.FactorIndex,
      (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0)
    (hI : ∀ Q ∈ I, MvPolynomial.eval v Q = 0) :
    let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
    let f := algebraMap M.CoordinateRing R
    ∀ Q : R, f P * Q ∈ I.map f → Q ∈ I.map f := by
  apply PrimeAvoidance.mul_mem_localized_of_avoids_associatedPrimes
  · intro Q hQ
    simpa [MvPolynomial.vanishingIdeal] using hI Q hQ
  · intro q hq hle
    exact h q hq (M.nonzero_blocks_below_evaluation I v hI hv q hle)

/-- Smoothness on the punctured affine multicone gives regularity of the
ordinary point-local quotient, with all scaling directions retained. -/
theorem point_local_regular_of_smooth_punctured_cone
    (I : Ideal M.CoordinateRing)
    (h : ∀ q : PrimeSpectrum (M.CoordinateRing ⧸ I),
      (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
        Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
      Algebra.IsSmoothAt K q.asIdeal)
    (v : M.Variable → K)
    (hv : ∀ i : M.FactorIndex,
      (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0)
    (hI : ∀ P ∈ I, MvPolynomial.eval v P = 0) :
    let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
    IsRegularLocalRing (R ⧸ I.map (algebraMap M.CoordinateRing R)) := by
  let p := MvPolynomial.vanishingIdeal K {v}
  have hIp : I ≤ p := by
    intro P hP
    simpa [p, MvPolynomial.vanishingIdeal] using hI P hP
  let q := p.map (Ideal.Quotient.mk I)
  letI : q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa using hIp)
  letI : Algebra.IsSmoothAt K q := h ⟨q, inferInstance⟩
    (M.nonzero_blocks_below_evaluation I v hI hv q le_rfl)
  letI : Algebra.FinitePresentation K (M.CoordinateRing ⧸ I) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : IsRegularLocalRing (Localization.AtPrime q) :=
    AlgebraicGroupCM.regularAt_of_smoothAt K (M.CoordinateRing ⧸ I) q
  exact IsRegularLocalRing.of_ringEquiv
    (R := Localization.AtPrime q)
    (AlgebraicGroupCM.localizedQuotientEquiv I p hIp).symm.toRingEquiv

end MultiProjectiveSpace
end PhilipponMultiplicity

end

end


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

private theorem coordinate_ratio {K : Type*} [Field K] {ι : Type*}
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
    exact (coordinate_ratio heq (j i) (hj i)).1
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
      exact (coordinate_ratio heq (j v.1) (hjz v.1)).2 v.2
    rw [hcoords, M.eval_block_scale P D hP]
  have hgP : AnalyticAt K (fun z => MvPolynomial.eval (g z) P) x := by
    change AnalyticAt K (fun z => aeval (g z) P) x
    exact AnalyticAt.aeval_mvPolynomial hg P
  exact (jetOrder_congr hfg).trans (jetOrder_mul_unit hgP hu hux)

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

def projection : M.CoordinateRing →+* MvPolynomial M.FactorIndex K :=
  eval₂Hom C (fun j => C (a j / a ⟨j.1,b j.1⟩) * X j.1)

theorem projection_equation (hb : ∀ i, a ⟨i,b i⟩ ≠ 0) (j : M.Variable) :
    projection M a b (equation M a b j) = 0 := by
  simp [projection, equation, hb]

theorem kernel_projection (hb : ∀ i, a ⟨i,b i⟩ ≠ 0) :
    RingHom.ker (projection M a b) = ideal M a b := by
  classical
  let I := ideal M a b
  let q := Ideal.Quotient.mk I
  let s : MvPolynomial M.FactorIndex K →+* M.CoordinateRing :=
    eval₂Hom C (fun i => X ⟨i,b i⟩)
  have heq : (q.comp s).comp (projection M a b) = q := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [projection, s]
    · intro j
      have h : q (equation M a b j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
      have h' : q (X j) = q (C (a j / a ⟨j.1,b j.1⟩)) * q (X ⟨j.1,b j.1⟩) :=
        sub_eq_zero.mp (by simpa only [equation, map_sub, map_mul] using h)
      simpa [projection, s] using h'.symm
  apply le_antisymm
  · intro P hP
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q P = 0
    rw [← heq]
    change q (s (projection M a b P)) = 0
    rw [show projection M a b P = 0 from hP, map_zero, map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact projection_equation M a b hb j

theorem ideal_prime (hb : ∀ i, a ⟨i,b i⟩ ≠ 0) : (ideal M a b).IsPrime := by
  rw [← kernel_projection M a b hb]
  exact RingHom.ker_isPrime _

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

theorem ideal_homogeneous : IsMultihomogeneousIdeal M (ideal M a b) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hh : (ideal M a b).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    rintro P ⟨j,rfl⟩
    exact ⟨Pi.single j.1 1, (M.degreePiece_iff _ _).mpr (equation_homogeneous M a b j)⟩
  intro P hP D
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP D

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

theorem ideal_relevant (hb : ∀ i, a ⟨i,b i⟩ ≠ 0) :
    Hilbert.IsRelevant K M.factorCount M.ambientDimension (ideal M a b) := by
  classical
  let H : M.CoordinateRing := ∏ i, X ⟨i,b i⟩
  have hH : H ∈ Hilbert.irrelevantIdeal K M.factorCount M.ambientDimension := by
    apply Ideal.mem_iInf.mpr
    intro i
    apply Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    exact Ideal.subset_span ⟨b i,rfl⟩
  have hle : ideal M a b ≤ RingHom.ker (eval a) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact equation_eval M a b hb j
  intro h
  have hz : eval a H = 0 := hle (h hH)
  have hn : eval a H ≠ 0 := by simpa [H] using Finset.prod_ne_zero_iff.mpr (fun i _ => hb i)
  exact hn hz

theorem vanishingIdeal_singleton_eq [IsAlgClosed K]
    (hb : ∀ i, a ⟨i,b i⟩ ≠ 0) (x : M.Point)
    (hrep : ∀ i, ∃ h : (fun j => a ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => a ⟨i,j⟩) h = x i) :
    M.vanishingIdeal {x} = ideal M a b := by
  rw [← zeroLocus_eq_singleton M a b hb x hrep]
  exact M.vanishingIdeal_zeroLocus_of_relevant_prime _ (ideal_prime M a b hb)
    (ideal_homogeneous M a b) (ideal_relevant M a b hb)

/-- The equations transverse to the blockwise scaling directions have an
identity Jacobian minor, so the point cone is smooth at its representative. -/
theorem local_smooth (hb : ∀ i, a ⟨i,b i⟩ ≠ 0) :
    Algebra.FormallySmooth K
      ((Localization.AtPrime (vanishingIdeal K {a})) ⧸
        (ideal M a b).map (algebraMap M.CoordinateRing
          (Localization.AtPrime (vanishingIdeal K {a})))) := by
  classical
  let S := {j : M.Variable // j.2 ≠ b j.1}
  let r := Fintype.card S
  let e : Fin r ↪ M.Variable := (Fintype.equivFin S).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩
  let F : Fin r → M.CoordinateRing := fun i => equation M a b (e i)
  have hnon (i : Fin r) (k : M.FactorIndex) : e i ≠ ⟨k,b k⟩ := by
    intro he
    have h : (e i).2 ≠ b (e i).1 := ((Fintype.equivFin S).symm i).property
    have h' : ∀ j : M.Variable, j.2 ≠ b j.1 → j ≠ ⟨k,b k⟩ := by
      rintro ⟨i,j⟩ hj heq
      cases heq
      exact hj rfl
    exact h' (e i) h he
  have hgen : Ideal.span (Set.range F) = ideal M a b := by
    apply le_antisymm
    · exact Ideal.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact Ideal.subset_span ⟨e i,rfl⟩)
    · apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      by_cases hj : j.2 = b j.1
      · have he : j = ⟨j.1,b j.1⟩ := Sigma.ext rfl (heq_of_eq hj)
        have hz : equation M a b j = 0 := by rw [he]; simp [equation, hb]
        rw [hz]
        exact Ideal.zero_mem _
      · let s : S := ⟨j,hj⟩
        have he : e ((Fintype.equivFin S) s) = j := by simp [e, s]
        rw [← he]
        exact Ideal.subset_span ⟨(Fintype.equivFin S) s,rfl⟩
  have hmatrix : Matrix.of (fun i j : Fin r => pderiv (e i) (F j)) = 1 := by
    apply Matrix.ext
    intro i j
    change pderiv (e i) (F j) = if i = j then 1 else 0
    simp only [F, equation, map_sub, pderiv_C_mul, pderiv_X, Pi.single_apply]
    rw [if_neg (Ne.symm (hnon i (e j).1)), mul_zero, sub_zero]
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl]
    · rw [if_neg (fun h => hij (e.injective h).symm), if_neg hij]
  exact AffineJacobian.LocalSmoothness.smooth_local_quotient_of_generators
    (ideal M a b) a r F e (fun i => equation_eval M a b hb (e i))
    (by rw [hgen]) (by rw [hmatrix]; simp)

theorem local_regular (hb : ∀ i, a ⟨i,b i⟩ ≠ 0) :
    IsRegularLocalRing
      ((Localization.AtPrime (vanishingIdeal K {a})) ⧸
        (ideal M a b).map (algebraMap M.CoordinateRing
          (Localization.AtPrime (vanishingIdeal K {a})))) := by
  let I := ideal M a b
  let p := vanishingIdeal K {a}
  have hIp : I ≤ p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    simpa [p,vanishingIdeal] using equation_eval M a b hb j
  let q := p.map (Ideal.Quotient.mk I)
  letI : q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa using hIp)
  letI : Algebra.IsSmoothAt K q :=
    (ClosedPointSmoothness.point_local_iff_quotient_local I p hIp).mp (local_smooth M a b hb)
  letI : Algebra.FinitePresentation K (M.CoordinateRing ⧸ I) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : IsRegularLocalRing (Localization.AtPrime q) :=
    AlgebraicGroupCM.regularAt_of_smoothAt K (M.CoordinateRing ⧸ I) q
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime q)
    (AlgebraicGroupCM.localizedQuotientEquiv I p hIp).symm.toRingEquiv

end PhilipponMultiplicity.PointConeLinear
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.FiniteLocalSlice
variable {K : Type*} [Field K]

/-- The evaluation maximal ideal is generated by the coordinate differences. -/
theorem vanishingIdeal_eq_span {σ : Type*} (v : σ → K) :
    vanishingIdeal K {v} = Ideal.span (Set.range (fun j : σ => X j - C (v j))) := by
  classical
  let I : Ideal (MvPolynomial σ K) := Ideal.span (Set.range (fun j => X j - C (v j)))
  let q := Ideal.Quotient.mk I
  have heq : (q.comp C).comp (eval v) = q := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp
    · intro j
      have h : q (X j - C (v j)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
      simpa only [RingHom.comp_apply, eval_X] using
        (sub_eq_zero.mp (by simpa only [map_sub] using h)).symm
  apply le_antisymm
  · intro P hP
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q P = 0
    rw [← heq]
    change q (C (eval v P)) = 0
    rw [show eval v P = 0 from (mem_vanishingIdeal_singleton_iff v P).mp hP,
      map_zero, map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact (mem_vanishingIdeal_singleton_iff v _).mpr (by simp)

/-- Evaluation extends to the local ring at a rational affine point. -/
def localEval {σ : Type*} (v : σ → K) :
    Localization.AtPrime (vanishingIdeal K {v}) →ₐ[K] K :=
  IsLocalization.liftAlgHom (M := (vanishingIdeal K {v}).primeCompl)
    (f := aeval v) (fun s => isUnit_iff_ne_zero.mpr
      (fun h => s.property ((mem_vanishingIdeal_singleton_iff v s.val).mpr h)))

@[simp] theorem localEval_algebraMap {σ : Type*} (v : σ → K) (P : MvPolynomial σ K) :
    localEval v (algebraMap _ (Localization.AtPrime (vanishingIdeal K {v})) P) = eval v P := by
  simp [localEval]

theorem localEval_kernel {σ : Type*} (v : σ → K) :
    RingHom.ker (localEval v) = (vanishingIdeal K {v}).map
      (algebraMap _ (Localization.AtPrime (vanishingIdeal K {v}))) := by
  have h : (RingHom.ker (localEval v)).under (MvPolynomial σ K) = vanishingIdeal K {v} := by
    ext P
    simp only [Ideal.mem_comap, RingHom.mem_ker, localEval_algebraMap,
      mem_vanishingIdeal_singleton_iff]
    rfl
  exact (IsLocalization.map_under (vanishingIdeal K {v}).primeCompl
    (Localization.AtPrime (vanishingIdeal K {v})) _).symm.trans
      (congrArg (Ideal.map (algebraMap (MvPolynomial σ K)
        (Localization.AtPrime (vanishingIdeal K {v})))) h)

/-- Finiteness over a field ascends across the nilpotent kernel of the
residue map of a Noetherian algebra. -/
theorem finite_of_radical_eq_kernel {R : Type*} [CommRing R] [IsNoetherianRing R]
    [Algebra K R] (f : R →ₐ[K] K) (I : Ideal R)
    (hI : I.radical = RingHom.ker f) : Module.Finite K (R ⧸ I) := by
  let g : (R ⧸ I) →ₐ[K] K := Ideal.Quotient.liftₐ I f
    (Ideal.le_radical.trans hI.le)
  have hg : Function.Surjective g := by
    intro k
    exact ⟨algebraMap K (R ⧸ I) k, by simp⟩
  have hnil : RingHom.ker g ≤ nilradical (R ⧸ I) := by
    intro z hz
    obtain ⟨w,rfl⟩ := Ideal.Quotient.mk_surjective z
    have hw : w ∈ I.radical := hI.ge hz
    obtain ⟨n,hn⟩ := hw
    exact ⟨n, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hn⟩
  exact Module.finite_of_surjective_of_ker_le_nilradical g hg hnil
    (IsNoetherian.noetherian _)

/-- A quotient of an affine point-local ring with maximal radical is finite
over the coefficient field, retaining its nilpotents. -/
theorem finite_of_local_radical {σ : Type*} [Finite σ] (v : σ → K)
    (I : Ideal (Localization.AtPrime (vanishingIdeal K {v})))
    (hI : I.radical = (vanishingIdeal K {v}).map
      (algebraMap _ (Localization.AtPrime (vanishingIdeal K {v})))) :
    Module.Finite K ((Localization.AtPrime (vanishingIdeal K {v})) ⧸ I) := by
  exact finite_of_radical_eq_kernel (localEval v) I (hI.trans (localEval_kernel v).symm)

variable (M : MultiProjectiveSpace K)

/-- Fixing one nonzero coordinate in each block cuts the point cone down to
its affine evaluation maximal ideal. -/
theorem point_cone_sup_slice [IsAlgClosed K]
    (x : M.Point) (v : M.Variable → K)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hb : ∀ i, v ⟨i,b i⟩ = 1)
    (hrep : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) :
    M.vanishingIdeal {x} ⊔
      Ideal.span (Set.range (fun i : M.FactorIndex =>
        (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)) =
      vanishingIdeal K {v} := by
  classical
  have hne : ∀ i, v ⟨i,b i⟩ ≠ 0 := fun i => by rw [hb i]; exact one_ne_zero
  rw [PointConeLinear.vanishingIdeal_singleton_eq M v b hne x hrep]
  apply le_antisymm
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact (mem_vanishingIdeal_singleton_iff v _).mpr
        (PointConeLinear.equation_eval M v b hne j)
    · apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact (mem_vanishingIdeal_singleton_iff v _).mpr (by simp [hb])
  · rw [vanishingIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change X j - C (v j) ∈ _
    have heq : X j - C (v j) = PointConeLinear.equation M v b j +
        C (v j) * (X (⟨j.1,b j.1⟩ : M.Variable) - 1) := by
      simp only [PointConeLinear.equation, hb, div_one]
      ring
    rw [heq]
    apply Ideal.add_mem
    · exact (show PointConeLinear.ideal M v b ≤ _ from le_sup_left)
        (Ideal.subset_span ⟨j,rfl⟩)
    · apply Ideal.mul_mem_left
      exact (show Ideal.span (Set.range (fun i : M.FactorIndex =>
        (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)) ≤ _ from le_sup_right)
          (Ideal.subset_span ⟨j.1,rfl⟩)

/-- The actual mixed equations, supplemented by pivot normalizations, define
a finite local algebra whenever their cone radical is the point-cone ideal. -/
theorem finite_slice_of_local_radical [IsAlgClosed K]
    (I : Ideal M.CoordinateRing) (x : M.Point) (v : M.Variable → K)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hb : ∀ i, v ⟨i,b i⟩ = 1)
    (hrep : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i)
    (hrad : (I.map (algebraMap M.CoordinateRing
        (Localization.AtPrime (vanishingIdeal K {v})))).radical =
      (M.vanishingIdeal {x}).map (algebraMap M.CoordinateRing
        (Localization.AtPrime (vanishingIdeal K {v})))) :
    Module.Finite K ((Localization.AtPrime (vanishingIdeal K {v})) ⧸
      (I ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
        (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
        (algebraMap M.CoordinateRing (Localization.AtPrime (vanishingIdeal K {v})))) := by
  let L := Localization.AtPrime (vanishingIdeal K {v})
  let f : M.CoordinateRing →+* L := algebraMap _ _
  let N : Ideal M.CoordinateRing := Ideal.span (Set.range (fun i : M.FactorIndex =>
    (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))
  have heq : (M.vanishingIdeal {x}).map f ⊔ N.map f = (vanishingIdeal K {v}).map f := by
    rw [← Ideal.map_sup]
    exact congrArg (Ideal.map f) (point_cone_sup_slice M x v b hb hrep)
  apply finite_of_local_radical
  change ((I ⊔ N).map f).radical = (vanishingIdeal K {v}).map f
  have hprime : ((vanishingIdeal K {v}).map f).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime (vanishingIdeal K {v}) le_rfl
  apply le_antisymm
  · apply (Ideal.radical_mono (show (I ⊔ N).map f ≤ (vanishingIdeal K {v}).map f from ?_)).trans
      hprime.isRadical.radical.le
    rw [Ideal.map_sup, ← heq]
    exact sup_le_sup (Ideal.le_radical.trans hrad.le) le_rfl
  · rw [← heq]
    apply sup_le
    · rw [← hrad]
      exact Ideal.radical_mono (Ideal.map_mono le_sup_left)
    · exact (Ideal.map_mono le_sup_right).trans Ideal.le_radical

/-- Every projective point admits a representative with one coordinate in
each block equal to one. -/
theorem exists_normalized_representative (x : M.Point) :
    ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
    ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
      ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
        Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i := by
  classical
  choose b hb using fun i => Function.ne_iff.mp (x i).rep_nonzero
  have hb' : ∀ i, (x i).rep (b i) ≠ 0 := hb
  let v : M.Variable → K := fun j => (x j.1).rep j.2 / (x j.1).rep (b j.1)
  have hv : ∀ i, v ⟨i,b i⟩ = 1 := fun i => div_self (hb' i)
  refine ⟨b,v,hv,?_⟩
  intro i
  have hn : (fun j => v ⟨i,j⟩) ≠ 0 := by
    intro h
    exact one_ne_zero ((hv i).symm.trans (congrFun h (b i)))
  refine ⟨hn,?_⟩
  apply Eq.trans ?_ (x i).mk_rep
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨((x i).rep (b i))⁻¹,?_⟩
  funext j
  simp only [v, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

end PhilipponMultiplicity.FiniteLocalSlice
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem isolated_equation_persistence_of_finite_local_slices
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
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
          Module.Finite K ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
            ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
              Ideal.span (Set.range (fun i : M.FactorIndex =>
                (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                (algebraMap M.CoordinateRing
                  (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0})) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S, ∀ v : M.Variable → K,
        (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
          Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) →
        ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length).map
          (algebraMap M.CoordinateRing
            (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).radical =
          (M.vanishingIdeal {x}).map (algebraMap M.CoordinateRing
            (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  letI : IsAlgClosed K := by
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
  intro M W hW hirr α hα hdim l hl c₀ S hS hSZ hrad
  apply hgeometry M W hW hirr α hα hdim l hl c₀ S hS hSZ
  intro x hx
  obtain ⟨b,v,hb,hrep⟩ := FiniteLocalSlice.exists_normalized_representative M x
  exact ⟨b,v,hb,hrep,FiniteLocalSlice.finite_slice_of_local_radical M
    (MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) x v b hb hrep
    (hrad x hx v hrep)⟩

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

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
      (∀ x ∈ S, ∀ v : M.Variable → K,
        (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
          Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) →
        ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length).map
          (algebraMap M.CoordinateRing
            (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).radical =
          (M.vanishingIdeal {x}).map (algebraMap M.CoordinateRing
            (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  exact isolated_equation_persistence_of_finite_local_slices K hK
    (exists_open_preserving_finite_local_mixed_slices K hK)
