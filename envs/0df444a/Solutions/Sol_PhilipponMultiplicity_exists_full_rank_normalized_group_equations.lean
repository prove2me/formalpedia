-- Prove2me | solution 1 for PhilipponMultiplicity.exists_full_rank_normalized_group_equations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-03T17:17:58.929992+00:00
-- url     : https://prove2.me/submissions/1ddac829-532e-492a-b563-06fb4d9fd27f

import Theorems.Thm_AffineJacobian_exists_local_equations_of_regular_local_ring
import Definitions.Def_P2M_Util
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

section FullRankBundle0

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
end FullRankBundle0

section FullRankBundle1

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
end FullRankBundle1

section FullRankBundle2

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
end FullRankBundle2

section FullRankBundle3

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
end FullRankBundle3

section FullRankBundle4

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
end FullRankBundle4

section FullRankBundle5

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
end FullRankBundle5

section FullRankBundle6

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
end FullRankBundle6

section FullRankBundle7

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
end FullRankBundle7

section FullRankBundle8

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
end FullRankBundle8

section FullRankBundle9

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
end FullRankBundle9

section FullRankBundle10

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
end FullRankBundle10

section FullRankBundle11

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
end FullRankBundle11

section FullRankBundle12

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
end FullRankBundle12

section FullRankBundle13

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
end FullRankBundle13

section FullRankBundle14

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
end FullRankBundle14

section FullRankBundle15

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
end FullRankBundle15

section FullRankBundle16

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
end FullRankBundle16

section FullRankBundle17

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
end FullRankBundle17

section FullRankBundle18

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
end FullRankBundle18

section FullRankBundle19

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
end FullRankBundle19

section FullRankBundle20

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
end FullRankBundle20

section FullRankBundle21

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
end FullRankBundle21

section FullRankBundle22

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
end FullRankBundle22

section FullRankBundle23

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
end FullRankBundle23

section FullRankBundle24

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
end FullRankBundle24

section FullRankBundle25

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
end FullRankBundle25

section FullRankBundle26

set_option autoImplicit false
noncomputable section
namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K]

/-- A nonzero homogeneous lift of an actual group point, using only a field. -/
structure GroupHomogeneousRepresentative (G : EmbeddedGroupProduct K) where
  point : G.Point
  coordinates : G.ambient.Variable → K
  nonzero : ∀ i : G.FactorIndex, (fun j => coordinates ⟨i, j⟩) ≠ 0
  represents : ∀ i : G.FactorIndex,
    Projectivization.mk K (fun j => coordinates ⟨i, j⟩) (nonzero i) = G.embedding point i

/-- Every group point has a homogeneous representative; the retention
intersection consequently ranges over a genuine nonempty family. -/
def representativeOfPoint (G : EmbeddedGroupProduct K) (x : G.Point) :
    GroupHomogeneousRepresentative G where
  point := x
  coordinates := G.ambient.coordinate (G.embedding x)
  nonzero i := (G.embedding x i).rep_nonzero
  represents i := (G.embedding x i).mk_rep

def representativeEvaluation (G : EmbeddedGroupProduct K)
    (x : GroupHomogeneousRepresentative G) : G.CoordinateRing →+* K :=
  MvPolynomial.eval x.coordinates

theorem representativeEvaluation_surjective (G : EmbeddedGroupProduct K)
    (x : GroupHomogeneousRepresentative G) :
    Function.Surjective (representativeEvaluation G x) := by
  intro a
  exact ⟨MvPolynomial.C a, MvPolynomial.eval_C (f := x.coordinates) a⟩

/-- The actual maximal ideal of a chosen homogeneous representative. -/
def representativeMaximalIdeal (G : EmbeddedGroupProduct K)
    (x : GroupHomogeneousRepresentative G) : MaximalSpectrum G.CoordinateRing where
  asIdeal := RingHom.ker (representativeEvaluation G x)
  isMaximal := RingHom.ker_isMaximal_of_surjective _ (representativeEvaluation_surjective G x)


end PhilipponMultiplicity.AlgebraicCone
end
end FullRankBundle26

section FullRankBundle27

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K]

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

end PhilipponMultiplicity.AlgebraicCone

end
end FullRankBundle27

section FullRankBundle28

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
end FullRankBundle28

section FullRankBundle29

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

end FullRankBundle29

section FullRankBundle30

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
end FullRankBundle30

section FullRankBundle31

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
end FullRankBundle31

section FullRankBundle32

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
open AlgebraicGroupCM
variable {K : Type*} [Field K] [IsAlgClosed K]

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

end PhilipponMultiplicity.AlgebraicCone

end
end FullRankBundle32

section FullRankBundle33

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped Topology
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K] [IsAlgClosed K]

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

end PhilipponMultiplicity.AlgebraicCone
end
end FullRankBundle33

section FullRankBundle34

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K] (G : EmbeddedGroupProduct K)

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

end PhilipponMultiplicity.AlgebraicCone
end
end FullRankBundle34

section FullRankBundle35

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K] (G : EmbeddedGroupProduct K)

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

end PhilipponMultiplicity.AlgebraicCone
end
end FullRankBundle35

section FullRankBundle36

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K] (G : EmbeddedGroupProduct K)

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

end PhilipponMultiplicity.AlgebraicCone
end
end FullRankBundle36

section FullRankBundle37

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K] (G : EmbeddedGroupProduct K)

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

end PhilipponMultiplicity.AlgebraicCone
end
end FullRankBundle37

section FullRankBundle38

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Filter
open scoped Topology
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K] (G : EmbeddedGroupProduct K)

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

end PhilipponMultiplicity.AlgebraicCone
end
end FullRankBundle38

section FullRankBundle39

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K] [IsAlgClosed K]

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

end PhilipponMultiplicity.AlgebraicCone
end
end FullRankBundle39

section FullRankBundle40

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
end FullRankBundle40

section FullRankBundle41

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
end FullRankBundle41

section FullRankBundle42

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
open AlgebraicGroupCM
variable {K : Type*} [Field K]

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

end PhilipponMultiplicity.AlgebraicCone

end
end FullRankBundle42

section FullRankBundle43

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K] [IsAlgClosed K]

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

end PhilipponMultiplicity.AlgebraicCone

end
end FullRankBundle43

section FullRankBundle44

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Translation transports regularity from the existing regular point to every lift. -/
theorem regular_local_ring_at_representative (G : EmbeddedGroupProduct K)
    (r : GroupHomogeneousRepresentative G) :
    IsRegularLocalRing (RepresentativeLocalRing G r) := by
  obtain ⟨s,hs⟩ := exists_regular_group_representative G
  letI := hs
  obtain ⟨e⟩ := group_local_rings_equiv G s r
  exact IsRegularLocalRing.of_ringEquiv (R := RepresentativeLocalRing G s) e

/-- Choose normalized homogeneous coordinates of the identity. -/
theorem exists_normalized_identity (G : EmbeddedGroupProduct K) :
    ∃ (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (r : GroupHomogeneousRepresentative G),
      r.point = 0 ∧ ∀ i, r.coordinates ⟨i,c i⟩ = 1 := by
  classical
  choose c hc using fun i : G.FactorIndex =>
    Function.ne_iff.mp (G.embedding 0 i).rep_nonzero
  refine ⟨c, representativeFromScales G c 0 (fun _ => 1), rfl, ?_⟩
  intro i
  have h := representativeFromScales_pivot G c 0 (fun _ => 1) i
  simpa only [conePivotAt_eq G c 0 i (hc i), Units.val_one] using h

end PhilipponMultiplicity.AlgebraicCone

end
end FullRankBundle44

section FullRankBundle45

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.AlgebraicJacobian
variable {K σ : Type*} [Field K] [Fintype σ]

def differential (P : MvPolynomial σ K) (a v : σ → K) : K :=
  ∑ j, eval a (pderiv j P) * v j

theorem differential_add_vector (P : MvPolynomial σ K) (a v w : σ → K) :
    differential P a (v + w) = differential P a v + differential P a w := by
  simp only [differential, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem differential_add (P Q : MvPolynomial σ K) (a v : σ → K) :
    differential (P + Q) a v = differential P a v + differential Q a v := by
  simp only [differential, map_add, add_mul, Finset.sum_add_distrib]

theorem differential_mul (P Q : MvPolynomial σ K) (a v : σ → K) :
    differential (P * Q) a v =
      eval a P * differential Q a v + eval a Q * differential P a v := by
  simp only [differential, pderiv_mul, map_add, map_mul,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

@[simp] theorem differential_zero (a v : σ → K) : differential 0 a v = 0 := by
  simp [differential]

@[simp] theorem differential_X_sub_one (j : σ) (a v : σ → K) :
    differential (X j - 1) a v = v j := by
  classical
  simp [differential, pderiv_X, Pi.single_apply]

variable (M : MultiProjectiveSpace K)

/-- Euler's identity in one projective block. -/
theorem block_euler (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (i : M.FactorIndex) :
    ∑ j : Fin (M.ambientDimension i + 1), X ⟨i,j⟩ * pderiv ⟨i,j⟩ P = D i • P := by
  classical
  let w : M.Variable → ℕ := fun v => if v.1 = i then 1 else 0
  have hw : P.IsWeightedHomogeneous w (D i) := by
    intro d hd
    rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
    simpa [w, smul_eq_mul, Finset.sum_ite_irrel] using
      hP d (mem_support_iff.mpr hd) i
  have he := hw.sum_weight_X_mul_pderiv
  rw [Fintype.sum_sigma] at he
  simpa [w, Finset.sum_ite_irrel] using he

/-- A block scaling is tangent to every equation of a homogeneous vanishing ideal. -/
theorem differential_block_scaling_eq_zero (S : Set M.Point)
    (a : M.Variable → K)
    (ha : ∀ P ∈ M.vanishingIdeal S, eval a P = 0)
    (P : M.CoordinateRing) (hP : P ∈ M.vanishingIdeal S)
    (z : M.FactorIndex → K) :
    differential P a (fun v => z v.1 * a v) = 0 := by
  classical
  have hgen (Q : M.CoordinateRing)
      (hQ : (∃ D, M.IsHomogeneous Q D) ∧ ∀ x ∈ S, M.eval Q x = 0) :
      differential Q a (fun v => z v.1 * a v) = 0 := by
    obtain ⟨⟨D, hD⟩, hv⟩ := hQ
    have hQa : eval a Q = 0 := ha Q (Ideal.subset_span ⟨⟨D,hD⟩,hv⟩)
    have hblock (i : M.FactorIndex) :
        ∑ j : Fin (M.ambientDimension i + 1),
          eval a (pderiv ⟨i,j⟩ Q) * a ⟨i,j⟩ = 0 := by
      have he := congrArg (eval a) (block_euler M Q D hD i)
      simpa only [map_sum, map_mul, eval_X, map_nsmul, hQa, nsmul_zero, mul_comm]
        using he
    unfold differential
    rw [Fintype.sum_sigma]
    apply Finset.sum_eq_zero
    intro i _
    calc
      (∑ j : Fin (M.ambientDimension i + 1),
          eval a (pderiv ⟨i,j⟩ Q) * (z i * a ⟨i,j⟩)) =
          z i * ∑ j, eval a (pderiv ⟨i,j⟩ Q) * a ⟨i,j⟩ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      _ = 0 := by rw [hblock, mul_zero]
  induction hP using Submodule.span_induction with
  | mem Q hQ => exact hgen Q hQ
  | zero => exact differential_zero _ _
  | add Q R hQ hR ihQ ihR => rw [differential_add, ihQ, ihR, add_zero]
  | smul R Q hQ ih =>
      change differential (R * Q) a _ = 0
      rw [differential_mul, ih, ha Q hQ, mul_zero, zero_mul, add_zero]

/-- Appending one normalization equation in each block preserves full row rank. -/
theorem append_pivots_surjective (S : Set M.Point)
    (a : M.Variable → K)
    (ha : ∀ P ∈ M.vanishingIdeal S, eval a P = 0)
    (c : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hc : ∀ i, a ⟨i,c i⟩ = 1)
    {r : ℕ} (P : Fin r → M.CoordinateRing)
    (hP : ∀ j, P j ∈ M.vanishingIdeal S)
    (hJ : Function.Surjective (fun v : M.Variable → K => fun j => differential (P j) a v)) :
    Function.Surjective (fun v : M.Variable → K => fun j : Fin r ⊕ M.FactorIndex =>
      differential (Sum.elim P (fun i => X ⟨i,c i⟩ - 1) j) a v) := by
  intro y
  obtain ⟨v,hv⟩ := hJ (fun j => y (Sum.inl j))
  let z : M.FactorIndex → K := fun i => y (Sum.inr i) - v ⟨i,c i⟩
  refine ⟨v + (fun j => z j.1 * a j), ?_⟩
  funext j
  cases j with
  | inl j =>
      change differential (P j) a (v + _) = _
      rw [differential_add_vector,
        differential_block_scaling_eq_zero M S a ha (P j) (hP j) z, add_zero]
      exact congrFun hv j
  | inr i =>
      simp only [Sum.elim_inr, differential_X_sub_one, Pi.add_apply, hc, mul_one, z]
      ring

end PhilipponMultiplicity.AlgebraicJacobian

end
end FullRankBundle45

section FullRankBundle46

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.AlgebraicCone
open AlgebraicJacobian

/-- The general regular-point Jacobian criterion supplies cone equations.
The geometric carrier comparison and transverse normalization are proved here. -/
theorem full_rank_equations_of_regular_point_criterion
    (K : Type*) [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K)
    (hjac : ∀ (I : Ideal G.CoordinateRing) (a : G.ambient.Variable → K)
      (m : MaximalSpectrum G.CoordinateRing),
      m.asIdeal = RingHom.ker (eval a) → I.IsRadical → I ≤ m.asIdeal →
      IsRegularLocalRing ((Localization.AtPrime m.asIdeal) ⧸
        I.map (algebraMap G.CoordinateRing (Localization.AtPrime m.asIdeal))) →
      ∃ (r : ℕ) (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing),
        (∀ i, P i ∈ I) ∧ eval a H ≠ 0 ∧
        Function.Surjective (fun v : G.ambient.Variable → K => fun i : Fin r =>
          ∑ j, eval a (pderiv j (P i)) * v j) ∧
        (∀ v : G.ambient.Variable → K, eval v H ≠ 0 →
          ((∀ i, eval v (P i) = 0) ↔ ∀ Q ∈ I, eval v Q = 0))) :
    ∃ (r : ℕ)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (a : G.ambient.Variable → K)
      (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing),
      (∀ i, a ⟨i, c i⟩ = 1) ∧
      (∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i) ∧
      eval a H ≠ 0 ∧ (∀ i, eval a (P i) = 0) ∧
      Function.Surjective (fun v : G.ambient.Variable → K => fun i : Fin r =>
        ∑ j, eval a (pderiv j (P i)) * v j) ∧
      (∀ v : G.ambient.Variable → K, eval v H ≠ 0 →
        ((∀ i, eval v (P i) = 0) ↔
          ((∀ i, v ⟨i, c i⟩ = 1) ∧
            ∃ x : G.Point, ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
              Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i))) := by
  classical
  obtain ⟨c,s,hs0,hsc⟩ := exists_normalized_identity G
  have ha (Q : G.CoordinateRing) (hQ : Q ∈ G.vanishingIdeal Set.univ) :
      eval s.coordinates Q = 0 := groupIdeal_le_representative G s hQ
  obtain ⟨r,P,H,hPI,hH,hJ,hzero⟩ := hjac (G.vanishingIdeal Set.univ) s.coordinates
    (representativeMaximalIdeal G s) rfl (G.ambient.vanishingIdeal_isRadical _)
    (groupIdeal_le_representative G s) (regular_local_ring_at_representative G s)
  obtain ⟨B,hB,hcarrier⟩ := exists_representative_cone_denominator G s
  let n := Fintype.card (Fin r ⊕ G.FactorIndex)
  let e : Fin n ≃ (Fin r ⊕ G.FactorIndex) := (Fintype.equivFin _).symm
  let Q : Fin n → G.CoordinateRing := fun j =>
    Sum.elim P (fun i => X ⟨i,c i⟩ - 1) (e j)
  have hQzero (v : G.ambient.Variable → K) :
      (∀ j, eval v (Q j) = 0) ↔
        ((∀ j, eval v (P j) = 0) ∧ ∀ i, v ⟨i,c i⟩ = 1) := by
    constructor
    · intro hv
      constructor
      · intro j
        simpa only [Q, e.apply_symm_apply, Sum.elim_inl] using hv (e.symm (Sum.inl j))
      · intro i
        simpa only [Q, e.apply_symm_apply, Sum.elim_inr, map_sub, eval_X,
          map_one, sub_eq_zero] using hv (e.symm (Sum.inr i))
    · rintro ⟨hP,hc⟩ j
      dsimp only [Q]
      cases e j with
      | inl k => exact hP k
      | inr i => simpa only [Sum.elim_inr, map_sub, eval_X, map_one, sub_eq_zero] using hc i
  have hQJ : Function.Surjective (fun v : G.ambient.Variable → K => fun j : Fin n =>
      ∑ k, eval s.coordinates (pderiv k (Q j)) * v k) := by
    intro y
    obtain ⟨v,hv⟩ := append_pivots_surjective G.ambient (G.embedding '' Set.univ)
      s.coordinates ha c hsc P hPI hJ (fun j => y (e.symm j))
    refine ⟨v, ?_⟩
    funext j
    change differential (Q j) s.coordinates v = y j
    simpa only [Q, e.symm_apply_apply] using! congrFun hv (e j)
  refine ⟨n,c,s.coordinates,Q,H * B,hsc,?_,?_,?_,hQJ,?_⟩
  · intro i
    exact ⟨s.nonzero i, by rw [s.represents,hs0]⟩
  · rw [map_mul]
    exact mul_ne_zero hH hB
  · exact (hQzero s.coordinates).mpr ⟨fun j => ha _ (hPI j),hsc⟩
  · intro v hv
    rw [map_mul, mul_ne_zero_iff] at hv
    constructor
    · intro hQ
      obtain ⟨hP,hc⟩ := (hQzero v).mp hQ
      obtain ⟨t,ht⟩ := hcarrier v ((hzero v hv.1).mp hP) hv.2
      refine ⟨hc,t.point,?_⟩
      intro i
      have h : ∃ hn : (fun j => t.coordinates ⟨i,j⟩) ≠ 0,
          Projectivization.mk K (fun j => t.coordinates ⟨i,j⟩) hn = G.embedding t.point i :=
        ⟨t.nonzero i,t.represents i⟩
      simpa only [ht] using h
    · rintro ⟨hc,x,hx⟩
      choose hn hrep using hx
      let t : GroupHomogeneousRepresentative G := ⟨x,v,hn,hrep⟩
      exact (hQzero v).mpr ⟨fun j => groupIdeal_le_representative G t (hPI j),hc⟩

end PhilipponMultiplicity.AlgebraicCone

end
end FullRankBundle46

open PhilipponMultiplicity

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (G : EmbeddedGroupProduct K) :
    ∃ (r : ℕ)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (a : G.ambient.Variable → K)
      (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing),
      (∀ i, a ⟨i, c i⟩ = 1) ∧
      (∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i) ∧
      MvPolynomial.eval a H ≠ 0 ∧
      (∀ i, MvPolynomial.eval a (P i) = 0) ∧
      Function.Surjective (fun v : G.ambient.Variable → K => fun i : Fin r =>
        ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (P i)) * v j) ∧
      (∀ v : G.ambient.Variable → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ((∀ i, v ⟨i, c i⟩ = 1) ∧
            ∃ x : G.Point, ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
              Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i))) := by
  exact AlgebraicCone.full_rank_equations_of_regular_point_criterion K G
    (AffineJacobian.exists_local_equations_of_regular_local_ring K G.ambient.Variable)
