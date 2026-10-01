-- Prove2me | solution 1 for PhilipponMultiplicity.masser_wustholz_unpointed_prime_orbit
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T06:57:32.651988+00:00
-- url     : https://prove2.me/submissions/1cc6534f-267b-486e-863e-764d1b39b880

import Theorems.Thm_PhilipponMultiplicity_masser_wustholz_stationary_retained_ideal
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Differential
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_HilbertGrowth
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.KrullDimension

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
-- Reused implementation: Solutions.PhilipponSectionFiveDifferentialContainment
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

/-- Pointwise vanishing of a homogeneous ideal gives containment in the
homogeneous vanishing ideal, although arbitrary evaluation kernels need not
be multihomogeneous. -/
theorem homogeneousIdeal_le_group_vanishingIdeal
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (V : Set G.Point) (h : ∀ x ∈ V, ∀ P ∈ I, G.ambient.eval P (G.embedding x) = 0) :
    I ≤ G.vanishingIdeal V := by
  rw [G.ambient.homogeneousIdeal_eq_span I hI]
  apply Ideal.span_le.mpr
  rintro P ⟨hP,D,hD⟩
  apply Ideal.subset_span
  refine ⟨⟨D,hD⟩,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact h x hx P hP


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

theorem varietyDimension_mono {V W : Set G.Point} (h : V ⊆ W) :
    varietyDimension G V ≤ varietyDimension G W := by
  exact Hilbert.idealDimension_antitone G.ambient (G.vanishingIdeal W) (G.vanishingIdeal V)
    (vanishingIdeal_multihomogeneous K _ _) (vanishingIdeal_multihomogeneous K _ _)
    (G.ambient.vanishingIdeal_antitone (Set.image_mono h))


end PhilipponMultiplicity
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

variable {K : Type*} [Field K]

theorem MultiProjectiveSpace.vanishingIdeal_isPrime_of_isIrreducible
    (M : MultiProjectiveSpace K) (S : Set M.Point)
    (hS : @IsIrreducible _ M.zariskiTopology S) : (M.vanishingIdeal S).IsPrime := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  apply Hilbert.prime_of_homogeneous_products M _ (vanishingIdeal_multihomogeneous K M S)
  · intro htop
    obtain ⟨x,hx⟩ := hS.nonempty
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal
      (show (1 : M.CoordinateRing) ∈ M.vanishingIdeal S by rw [htop]; trivial) hx
    exact one_ne_zero (by simpa only [MultiProjectiveSpace.eval,map_one] using hz)
  · rintro P Q ⟨D,hP⟩ ⟨E,hQ⟩ hPQ
    by_contra! hn
    have hnzero (R : M.CoordinateRing) (d : M.FactorIndex → ℕ)
        (hR : M.IsHomogeneous R d) (hRI : R ∉ M.vanishingIdeal S) :
        (S ∩ {x | M.eval R x ≠ 0}).Nonempty := by
      by_contra hz
      apply hRI
      exact Ideal.subset_span ⟨⟨d,hR⟩,fun x hx => by
        by_contra hxR
        exact hz ⟨x,hx,hxR⟩⟩
    obtain ⟨x,hx,hxP,hxQ⟩ := hS.2 _ _ (M.isOpen_basic P D hP)
      (M.isOpen_basic Q E hQ) (hnzero P D hP hn.1) (hnzero Q E hQ hn.2)
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal hPQ hx
    exact (mul_ne_zero hxP hxQ) (by simpa only [MultiProjectiveSpace.eval,map_mul] using hz)


end PhilipponMultiplicity
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

def pivotPolynomial (b : CoordinateChart G) (D : G.FactorIndex → ℕ) : G.CoordinateRing :=
  ∏ i, X ⟨i, b i⟩ ^ D i

theorem pivotPolynomial_homogeneous (b : CoordinateChart G) (D : G.FactorIndex → ℕ) :
    G.ambient.IsHomogeneous (pivotPolynomial b D) D :=
  Hilbert.variable_product_homogeneous G.ambient b D

theorem pivotPolynomial_eval_ne_zero (b : CoordinateChart G) (D : G.FactorIndex → ℕ)
    (x : G.Point) (hx : x ∈ chartDomain G b) :
    G.ambient.eval (pivotPolynomial b D) (G.embedding x) ≠ 0 := by
  classical
  simp only [pivotPolynomial, MultiProjectiveSpace.eval, map_prod, map_pow, eval_X]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hx i))


end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Reused implementation: Solutions.PhilipponStabilizerIsolation
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity

variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
open OperatorSupport

theorem group_zeroLocus_vanishingIdeal_of_isClosed (V : Set G.Point)
    (hV : @IsClosed _ G.zariskiTopology V) :
    idealZeroLocusOnGroup G (G.vanishingIdeal V) = V := by
  letI := G.ambient.zariskiTopology
  letI := G.zariskiTopology
  have heq : closure V = idealZeroLocusOnGroup G (G.vanishingIdeal V) := by
    ext x
    change x ∈ @closure _ (TopologicalSpace.induced G.embedding G.ambient.zariskiTopology) V ↔ _
    rw [closure_induced]
    change G.embedding x ∈ closure (G.embedding '' V) ↔
      G.embedding x ∈ G.ambient.zeroLocus (G.ambient.vanishingIdeal (G.embedding '' V))
    rw [G.ambient.zeroLocus_vanishingIdeal_eq_closure]
  exact heq.symm.trans hV.closure_eq

theorem isIrreducible_of_group_vanishingIdeal_prime [CompleteSpace K]
    (V : Set G.Point) (hne : V.Nonempty) (hq : (G.vanishingIdeal V).IsPrime) :
    @IsIrreducible _ G.zariskiTopology V := by
  letI := G.zariskiTopology
  refine ⟨hne,?_⟩
  intro U W hU hW ⟨x,hx,hxU⟩ ⟨y,hy,hyW⟩
  obtain ⟨P,D,hP,hPx,hPU⟩ := exists_basic_subset U hU x hxU
  obtain ⟨Q,E,hQ,hQy,hQW⟩ := exists_basic_subset W hW y hyW
  have hPI : P ∉ G.vanishingIdeal V := fun h => hPx
    (G.ambient.eval_eq_zero_of_mem_vanishingIdeal h ⟨x,hx,rfl⟩)
  have hQI : Q ∉ G.vanishingIdeal V := fun h => hQy
    (G.ambient.eval_eq_zero_of_mem_vanishingIdeal h ⟨y,hy,rfl⟩)
  have hPQ : P*Q ∉ G.vanishingIdeal V := fun h => (hq.mem_or_mem h).elim hPI hQI
  have hex : ∃ z ∈ V, G.ambient.eval (P*Q) (G.embedding z) ≠ 0 := by
    by_contra! h
    apply hPQ
    apply Ideal.subset_span
    refine ⟨⟨D+E,hP.mul G.ambient hQ⟩,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact h z hz
  obtain ⟨z,hz,hzPQ⟩ := hex
  have hzPQ' : G.ambient.eval P (G.embedding z) ≠ 0 ∧
      G.ambient.eval Q (G.embedding z) ≠ 0 := by
    simpa only [MultiProjectiveSpace.eval,map_mul,mul_ne_zero_iff] using hzPQ
  exact ⟨z,hz,hPU hzPQ'.1,hQW hzPQ'.2⟩

theorem isIrreducible_group_prime_zeroLocus [CompleteSpace K] [IsAlgClosed K]
    (q : Ideal G.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal G.ambient q)
    (hGq : G.vanishingIdeal Set.univ ≤ q) (hmeet : ComponentMeetsGroup G q) :
    @IsIrreducible _ G.zariskiTopology (idealZeroLocusOnGroup G q) := by
  apply isIrreducible_of_group_vanishingIdeal_prime (idealZeroLocusOnGroup G q) hmeet
  rwa [vanishingIdeal_group_prime G q hq hhom hGq hmeet]

theorem group_vanishingIdeal_prime_of_isIrreducible (V : Set G.Point)
    (hV : @IsIrreducible _ G.zariskiTopology V) : (G.vanishingIdeal V).IsPrime := by
  letI := G.ambient.zariskiTopology
  letI := G.zariskiTopology
  exact G.ambient.vanishingIdeal_isPrime_of_isIrreducible _
    (hV.image G.embedding continuous_induced_dom.continuousOn)


end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponFiniteBasicCover

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity

/-- A nonvanishing cover by finite-variable polynomials has a finite subcover,
even on an arbitrary subset of affine coordinate tuples. -/
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

/-- Every open cover of an arbitrary multiprojective locus admits a finite
subcover. This supplies the finite family needed for uniform chart degrees. -/
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
-- Reused implementation: Solutions.PhilipponTranslationGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [Field K] (G : EmbeddedGroupProduct K)

theorem EmbeddedGroupProduct.continuous_translation (g : G.Point) :
    @Continuous _ _ G.zariskiTopology G.zariskiTopology (fun x : G.Point => g+x) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have hh : Continuous (fun x : G.Point => x+g) :=
    continuous_induced_rng.mpr (G.translation_regular g).continuous
  simpa only [add_comm] using hh

/-- Translation is a homeomorphism for the specified polynomial Zariski
topology. No topological-group instance is assumed. -/
def EmbeddedGroupProduct.translationHomeomorph (g : G.Point) :
    @Homeomorph G.Point G.Point G.zariskiTopology G.zariskiTopology := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact {
    toEquiv :=
      { toFun := fun x => g+x
        invFun := fun x => -g+x
        left_inv := fun x => by simp only [← add_assoc,neg_add_cancel,zero_add]
        right_inv := fun x => by simp only [← add_assoc,add_neg_cancel,zero_add] }
    continuous_toFun := G.continuous_translation g
    continuous_invFun := G.continuous_translation (-g) }

theorem isLocallyClosed_translate (g : G.Point) (V : Set G.Point)
    (hV : @IsLocallyClosed _ G.zariskiTopology V) :
    @IsLocallyClosed _ G.zariskiTopology (translate g V) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  have heq : translate g V = (fun x : G.Point => -g+x) ⁻¹' V := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,← add_assoc,neg_add_cancel,zero_add] using hy
    · intro hx
      exact ⟨-g+x,hx,by simp only [← add_assoc,add_neg_cancel,zero_add]⟩
  rw [heq]
  exact hV.preimage (G.continuous_translation (-g))

/-- Translation preserves the actual topological Krull dimension of every
subspace. Identifying it with the mission's Hilbert dimension is a separate
algebraic-geometric step in Lemma 4.5. -/
theorem topologicalKrullDim_translate (g : G.Point) (V : Set G.Point) :
    @topologicalKrullDim V (@TopologicalSpace.induced V G.Point Subtype.val G.zariskiTopology) =
      @topologicalKrullDim (translate g V)
        (@TopologicalSpace.induced (translate g V) G.Point Subtype.val G.zariskiTopology) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  let e := (G.translationHomeomorph g).image V
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

theorem PolynomialTranslationChart.pullback_homogeneous {g : G.Point}
    (chart : PolynomialTranslationChart G g) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P)
      (fun i => chart.degree i * D i) := by
  classical
  have hh := hP.eval₂_blocks G.ambient G.ambient chart.coordinates
    (fun j i => if i=j then chart.degree i else 0) chart.homogeneous
  simpa [mul_ite,mul_comm] using hh

theorem PolynomialTranslationChart.pullback_eval_zero_iff {g : G.Point}
    (chart : PolynomialTranslationChart G g) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) (hx : x ∈ chart.domain) :
    G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P) (G.embedding x) = 0 ↔
      G.ambient.eval P (G.embedding (g+x)) = 0 := by
  have heval : G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P) (G.embedding x) =
      MvPolynomial.eval (fun v => G.ambient.eval (chart.coordinates v) (G.embedding x)) P := by
    dsimp only [MultiProjectiveSpace.eval]
    rw [← MvPolynomial.eval_assoc]
    rfl
  rw [heval]
  exact G.ambient.eval_eq_zero_iff_of_lift (G.embedding (g+x))
    (fun v => G.ambient.eval (chart.coordinates v) (G.embedding x))
    (chart.represents x hx) P D hP

end PhilipponMultiplicity

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
local instance : TopologicalSpace G.Point := G.zariskiTopology
local instance : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology

/-- One polynomial weight supported in an exclusive open piece of each
irreducible component, together with a valid polynomial translation chart. -/
structure SeparatingCharts (V : Set G.Point) {g : G.Point}
    (atlas : PolynomialTranslationAtlas G g) where
  Index : Type u
  finite : Fintype Index
  component : Index → Set V
  irreducible : ∀ i, IsIrreducible (component i)
  covers : ∀ x : V, ∃ i, x ∈ component i
  chart : Index → atlas.Index
  weight : Index → G.CoordinateRing
  degree : Index → G.FactorIndex → ℕ
  homogeneous : ∀ i, G.ambient.IsHomogeneous (weight i) (degree i)
  point : Index → V
  point_mem : ∀ i, point i ∈ component i
  nonzero : ∀ i, G.ambient.eval (weight i) (G.embedding (point i).val) ≠ 0
  support_chart : ∀ i (x : V), G.ambient.eval (weight i) (G.embedding x.val) ≠ 0 →
    x.val ∈ (atlas.chart (chart i)).domain
  zero_other : ∀ i j, i ≠ j → ∀ x : V, x ∈ component i →
    G.ambient.eval (weight j) (G.embedding x.val) = 0
  pivot : Index → CoordinateChart G
  point_pivot : ∀ i, (point i).val ∈ chartDomain G (pivot i)

attribute [instance] SeparatingCharts.finite

theorem exists_separating_charts (V : Set G.Point) {g : G.Point}
    (atlas : PolynomialTranslationAtlas G g) : Nonempty (SeparatingCharts V atlas) := by
  classical
  letI : NoetherianSpace G.Point := G.ambient.noetherian_induced G.embedding
  let C := irreducibleComponents V
  have hC : C.Finite := NoetherianSpace.finite_irreducibleComponents
  letI : Fintype C := hC.fintype
  have hdata (i : C) : ∃ x : V, x ∈ i.val ∧ ∃ a : atlas.Index,
      ∃ P : G.CoordinateRing, ∃ D : G.FactorIndex → ℕ,
        G.ambient.IsHomogeneous P D ∧ G.ambient.eval P (G.embedding x.val) ≠ 0 ∧
          (∀ y : V, G.ambient.eval P (G.embedding y.val) ≠ 0 →
            y.val ∈ (atlas.chart a).domain ∧ ∀ j : C, j ≠ i → y ∉ j.val) := by
    let O : Set V := (⋃₀ (C \ {i.val}))ᶜ
    have hO : IsOpen O := by
      dsimp only [O]
      rw [Set.sUnion_eq_biUnion,isOpen_compl_iff]
      exact hC.sdiff.isClosed_biUnion (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)
    have hclosure : closure O = i.val := closure_sUnion_irreducibleComponents_sdiff_singleton hC i.val i.property
    have hOne : O.Nonempty := by
      rw [← closure_nonempty_iff,hclosure]
      exact i.property.1.nonempty
    obtain ⟨x,hx⟩ := hOne
    obtain ⟨a,ha⟩ := atlas.covers x.val
    obtain ⟨W,hW,heq⟩ := isOpen_induced_iff.mp (hO.inter
      ((atlas.chart a).domain_open.preimage continuous_subtype_val))
    have hxW : x.val ∈ W := by
      change x ∈ Subtype.val ⁻¹' W
      rw [heq]
      exact ⟨hx,ha⟩
    obtain ⟨P,D,hP,hPx,hPW⟩ := OperatorSupport.exists_basic_subset W hW x.val hxW
    refine ⟨x,?_,a,P,D,hP,hPx,?_⟩
    · rw [← hclosure]
      exact subset_closure hx
    · intro y hy
      have hyO : y ∈ O ∩ {q : V | q.val ∈ (atlas.chart a).domain} := by
        change y ∈ O ∩ Subtype.val ⁻¹' (atlas.chart a).domain
        rw [← heq]
        exact hPW hy
      refine ⟨hyO.2,?_⟩
      intro j hji hj
      apply hyO.1
      exact Set.mem_sUnion.mpr ⟨j.val,⟨j.property,by
        simp only [Set.mem_singleton_iff]
        exact fun h => hji (Subtype.ext h)⟩,hj⟩
  choose x hx a P D hP hn hs using hdata
  choose b hb using fun i => OperatorSupport.exists_chartDomain (x i).val
  refine ⟨⟨C,inferInstance,(fun i => i.val),(fun i => i.property.1),?_,a,P,D,hP,x,hx,hn,
    (fun i y hy => (hs i y hy).1),?_,b,hb⟩⟩
  · intro y
    exact ⟨⟨irreducibleComponent y,irreducibleComponent_mem_irreducibleComponents y⟩,mem_irreducibleComponent⟩
  · intro i j hij y hy
    by_contra hn
    exact (hs j y hn).2 i hij hy

end PhilipponMultiplicity.TranslationSupport
end
end


section
-- Reused implementation: Solutions.PhilipponProductHilbertExistence

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_empty (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal ∅) D = 0 := by
  have h := M.hilbertFunction_eq_sectionSpace (fun x : Empty => isEmptyElim x) D
  have hr : Set.range (fun x : Empty => (isEmptyElim x : M.Point)) = ∅ := by
    ext x
    simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
    rintro ⟨e, _⟩
    exact isEmptyElim e
  have hf : Module.finrank K (M.sectionSpace (fun x : Empty => isEmptyElim x) D) = 0 :=
    Module.finrank_eq_zero_of_subsingleton K _
  rw [hr, hf] at h
  exact h

theorem hilbertPolynomial_empty :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
      (M.vanishingIdeal ∅) = 0 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, fun D _ => ?_⟩
  rw [M.hilbertFunction_empty]
  simp

theorem hilbertFunction_pos {S : Set M.Point} (hS : S.Nonempty)
    (D : M.FactorIndex → ℕ) :
    0 < Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) D := by
  classical
  obtain ⟨x, hx⟩ := hS
  obtain ⟨Q, hQ, hQx⟩ := M.exists_form_nonzero_at x D
  let I := M.vanishingIdeal S
  let W := Hilbert.quotientPiece K M.factorCount M.ambientDimension I D
  let q : W := ⟨Ideal.Quotient.mk I Q,
    ⟨Q, (M.degreePiece_iff Q D).mpr hQ, rfl⟩⟩
  have hq : q ≠ 0 := by
    intro h
    have hz : Ideal.Quotient.mk I Q = 0 := congrArg Subtype.val h
    have hm : Q ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact hQx (M.eval_eq_zero_of_mem_vanishingIdeal hm hx)
  letI : Nontrivial W := nontrivial_of_ne q 0 hq
  letI : Module.Finite K W := by
    dsimp [W, Hilbert.quotientPiece]
    infer_instance
  exact Module.finrank_pos

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open SectionThree

/-- Positivity prevents cancellation by an identically zero factor. Fixing all
other degrees then recovers a factor's eventual polynomial from a product's. -/
theorem factor_hilbert_polynomial_exists_of_product
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (hne : ∀ i, (V i).carrier.Nonempty)
    (hprod : ∃ P, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension
      (M.vanishingIdeal (productCarrier M V)) P) (i : M.FactorIndex) :
    ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => M.ambientDimension i)
      ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
        (V i).carrierInSingleFactor) P := by
  classical
  obtain ⟨P, N, hP⟩ := hprod
  let f (j : M.FactorIndex) (n : ℕ) := Hilbert.hilbertFunction K 1
    (fun _ => M.ambientDimension j)
    ((projectiveSpace K (M.ambientDimension j)).vanishingIdeal
      (V j).carrierInSingleFactor) (fun _ => n)
  have hf (j : M.FactorIndex) (n : ℕ) : 0 < f j n := by
    exact (projectiveSpace K (M.ambientDimension j)).hilbertFunction_pos
      ((hne j).image (fun x => fun _ => x)) (fun _ => n)
  let c : ℚ := ∏ j ∈ Finset.univ.erase i, (f j (N j) : ℚ)
  have hc : c ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast (hf j (N j)).ne'
  let zvar (j : M.FactorIndex) : MvPolynomial (Fin 1) ℚ :=
    if j = i then X 0 else C (N j : ℚ)
  refine ⟨C c⁻¹ * eval₂ C zvar P, fun _ => N i, ?_⟩
  intro d hd
  let e := Function.update N i (d 0)
  have he (j : M.FactorIndex) : N j ≤ e j := by
    by_cases hj : j = i
    · subst j
      simpa [e] using hd 0
    · simp [e, hj]
  have hPe := hP e he
  rw [product_projective_hilbert_function] at hPe
  have heval : eval (fun j => (d j : ℚ)) (eval₂ C zvar P) =
      eval (fun j => (e j : ℚ)) P := by
    rw [eval_eval₂]
    congr 1
    · ext r
      simp
    · funext j
      by_cases hj : j = i <;> simp [zvar, e, hj]
  rw [map_mul, eval_C, heval, hPe, Nat.cast_prod]
  change c⁻¹ * (∏ j, (f j (e j) : ℚ)) = _
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (f j (e j) : ℚ)) (Finset.mem_univ i)]
  have herase : (∏ j ∈ Finset.univ.erase i, (f j (e j) : ℚ)) = c := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [e, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [herase]
  have hd' : d = fun _ => d 0 := funext (fun j => congrArg d (Fin.eq_zero j))
  rw [hd']
  change c⁻¹ * ((f i (e i) : ℚ) * c) = (f i (d 0) : ℚ)
  simp only [e, Function.update_self]
  field_simp

/-- The zero-fallback convention is compatible with products. If a product
polynomial exists, nonempty factor Hilbert functions recover all factor
polynomials; if all factor polynomials exist, their product exists. -/
theorem product_projective_hilbert_polynomial (K : Type*) [Field K]
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i)) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) =
      ∏ i, MvPolynomial.rename (fun _ : Fin 1 => i)
        (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor)) := by
  classical
  by_cases hne : ∀ i, (V i).carrier.Nonempty
  · by_cases hprod : ∃ P, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) P
    · exact product_projective_hilbert_polynomial_of_exists K M V
        (factor_hilbert_polynomial_exists_of_product K M V hne hprod)
    · rw [Hilbert.hilbertPolynomial_eq_zero_of_not_exists _ _ _ _ hprod]
      have hn : ¬ ∀ i, ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor) P := by
        intro h
        have hspec (i : M.FactorIndex) := Hilbert.hilbertPolynomial_spec
          K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor) (h i)
        choose N hN using hspec
        apply hprod
        refine ⟨∏ i, rename (fun _ : Fin 1 => i)
          (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
            ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
              (V i).carrierInSingleFactor)), fun i => N i 0, ?_⟩
        intro d hd
        rw [map_prod, product_projective_hilbert_function, Nat.cast_prod]
        apply Finset.prod_congr rfl
        intro i _
        rw [eval_rename]
        apply hN i
        intro j
        fin_cases j
        exact hd i
      push Not at hn
      obtain ⟨i, hi⟩ := hn
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Hilbert.hilbertPolynomial_eq_zero_of_not_exists _ _ _ _ (by simpa using hi), map_zero]
  · push Not at hne
    obtain ⟨i, hi⟩ := hne
    have hiempty : (V i).carrier = ∅ := hi
    have hprodempty : productCarrier M V = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxi := hx i
      rwa [hiempty] at hxi
    have hsingleempty : (V i).carrierInSingleFactor = ∅ := by
      simp [ProjectiveSubvariety.carrierInSingleFactor, hiempty]
    rw [hprodempty, M.hilbertPolynomial_empty]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hsingleempty]
    have hz : Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
        ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal ∅) = 0 :=
      (projectiveSpace K (M.ambientDimension i)).hilbertPolynomial_empty
    rw [hz, map_zero]

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponTranslationPullback

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set MvPolynomial TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A linear map of homogeneous equations with the same vanishing kernel
compares the actual quotient Hilbert functions. -/
theorem hilbertFunction_le_of_linear_pullback (S T : Set M.Point)
    (D E : M.FactorIndex → ℕ) (L : M.CoordinateRing →ₗ[K] M.CoordinateRing)
    (hhom : ∀ P, M.IsHomogeneous P D → M.IsHomogeneous (L P) E)
    (hker : ∀ P, M.IsHomogeneous P D →
      ((∀ x ∈ S, M.eval P x = 0) ↔ ∀ x ∈ T, M.eval (L P) x = 0)) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal T) E := by
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let W := Hilbert.degreePiece K M.factorCount M.ambientDimension E
  let I := M.vanishingIdeal S
  let J := M.vanishingIdeal T
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let q := (Ideal.Quotient.mkₐ K J).toLinearMap
  let g := (q.comp L).domRestrict V
  have hmem (U : Set M.Point) (P : M.CoordinateRing) (d : M.FactorIndex → ℕ)
      (hP : M.IsHomogeneous P d) :
      P ∈ M.vanishingIdeal U ↔ ∀ x ∈ U, M.eval P x = 0 := by
    constructor
    · intro h x hx
      exact M.eval_eq_zero_of_mem_vanishingIdeal h hx
    · intro h
      exact Ideal.subset_span ⟨⟨d,hP⟩,h⟩
  have hfg : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ Ideal.Quotient.mk J (L P.val) = 0
    have hP := (M.degreePiece_iff _ _).mp P.property
    rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.Quotient.eq_zero_iff_mem,
      hmem S P.val D hP,hmem T (L P.val) E (hhom _ hP)]
    exact hker _ hP
  have hf : LinearMap.range f = V.map (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P,rfl⟩
      exact ⟨P.val,P.property,rfl⟩
    · rintro ⟨P,hP,rfl⟩
      exact ⟨⟨P,hP⟩,rfl⟩
  have hg : LinearMap.range g ≤ W.map q := by
    rintro _ ⟨P,rfl⟩
    exact ⟨L P.val,(M.degreePiece_iff _ _).mpr
      (hhom _ ((M.degreePiece_iff _ _).mp P.property)),rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hfg).trans g.quotKerEquivRange)).finrank_eq
  rw [hf] at he
  letI : Module.Finite K (Hilbert.quotientPiece K M.factorCount M.ambientDimension J E) := by
    dsimp [Hilbert.quotientPiece]
    infer_instance
  exact he.trans_le (Submodule.finrank_mono hg)

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.TranslationSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
local instance : TopologicalSpace G.Point := G.zariskiTopology
local instance : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
open OperatorSupport

variable {V : Set G.Point} {g : G.Point} {atlas : PolynomialTranslationAtlas G g}

def SeparatingCharts.shift (s : SeparatingCharts V atlas) (k : G.FactorIndex) : ℕ :=
  ∑ i, s.degree i k

theorem SeparatingCharts.degree_le_shift (s : SeparatingCharts V atlas)
    (i : s.Index) (k : G.FactorIndex) : s.degree i k ≤ s.shift k := by
  classical
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (s.degree j k)) (Finset.mem_univ i)

def SeparatingCharts.padding (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (i : s.Index) (k : G.FactorIndex) : ℕ :=
  s.shift k - s.degree i k + (c k - (atlas.chart (s.chart i)).degree k) * D k

def SeparatingCharts.pullback (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) : G.CoordinateRing →ₗ[K] G.CoordinateRing :=
  ∑ i, (LinearMap.mulLeft K (s.weight i * pivotPolynomial (s.pivot i) (s.padding c D i))).comp
    (MvPolynomial.aeval (atlas.chart (s.chart i)).coordinates).toLinearMap

theorem SeparatingCharts.pullback_apply (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (P : G.CoordinateRing) :
    s.pullback c D P = ∑ i, s.weight i * pivotPolynomial (s.pivot i) (s.padding c D i) *
      MvPolynomial.eval₂ MvPolynomial.C (atlas.chart (s.chart i)).coordinates P := by
  simp only [SeparatingCharts.pullback,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem SeparatingCharts.pullback_homogeneous (s : SeparatingCharts V atlas)
    (c : G.FactorIndex → ℕ) (hc : ∀ a k, (atlas.chart a).degree k ≤ c k)
    (D : G.FactorIndex → ℕ) (P : G.CoordinateRing) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (s.pullback c D P) (fun k => c k * D k + s.shift k) := by
  classical
  rw [s.pullback_apply]
  apply (G.ambient.degreePiece_iff _ _).mp
  apply Submodule.sum_mem
  intro i _
  apply (G.ambient.degreePiece_iff _ _).mpr
  have ht := ((s.homogeneous i).mul G.ambient
    (pivotPolynomial_homogeneous (s.pivot i) (s.padding c D i))).mul G.ambient
    ((atlas.chart (s.chart i)).pullback_homogeneous G P D hP)
  convert ht using 1
  funext k
  have h₁ := s.degree_le_shift i k
  have h₂ := Nat.mul_le_mul_right (D k) (hc (s.chart i) k)
  simp only [Pi.add_apply,SeparatingCharts.padding,Nat.sub_mul]
  omega

theorem SeparatingCharts.eval_pullback (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (P : G.CoordinateRing) (x : G.Point) :
    G.ambient.eval (s.pullback c D P) (G.embedding x) =
      ∑ i, G.ambient.eval (s.weight i) (G.embedding x) *
        G.ambient.eval (pivotPolynomial (s.pivot i) (s.padding c D i)) (G.embedding x) *
        G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C
          (atlas.chart (s.chart i)).coordinates P) (G.embedding x) := by
  rw [s.pullback_apply]
  simp only [MultiProjectiveSpace.eval,map_sum,map_mul]

/-- The component weights remove invalid charts, while an exclusive dense
open subset of each component prevents cancellation in the reverse direction. -/
theorem SeparatingCharts.pullback_vanishing_iff (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (P : G.CoordinateRing) (hP : G.ambient.IsHomogeneous P D) :
    (∀ x ∈ translate g V, G.ambient.eval P (G.embedding x) = 0) ↔
      ∀ x ∈ V, G.ambient.eval (s.pullback c D P) (G.embedding x) = 0 := by
  classical
  constructor
  · intro h x hx
    rw [s.eval_pullback]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : G.ambient.eval (s.weight i) (G.embedding x) = 0
    · rw [hi,zero_mul,zero_mul]
    · have hz := ((atlas.chart (s.chart i)).pullback_eval_zero_iff G P D hP x
        (s.support_chart i ⟨x,hx⟩ hi)).mpr (h (g+x) ⟨x,hx,rfl⟩)
      rw [hz,mul_zero]
  · intro h y hy
    obtain ⟨x,hx,rfl⟩ := hy
    let Z : Set V := {x | G.ambient.eval P (G.embedding (g+x.val)) = 0}
    have he : Continuous (G.embedding : G.Point → G.ambient.Point) := continuous_induced_dom
    have hv : Continuous (Subtype.val : V → G.Point) := continuous_subtype_val
    have hZ : IsClosed Z := (G.ambient.isClosed_zero P D hP).preimage
      (he.comp ((G.continuous_translation g).comp hv))
    obtain ⟨i,hi⟩ := s.covers ⟨x,hx⟩
    suffices hs : s.component i ⊆ Z by
      exact hs (a := (⟨x,hx⟩ : V)) hi
    let U : Set V := {x | G.ambient.eval (s.weight i) (G.embedding x.val) ≠ 0} ∩
      Subtype.val ⁻¹' chartDomain G (s.pivot i)
    have hU : IsOpen U := ((G.ambient.isOpen_basic (s.weight i) (s.degree i)
      (s.homogeneous i)).preimage (he.comp hv)).inter
      ((chartDomain_isOpen (s.pivot i)).preimage hv)
    have hdense : s.component i ⊆ closure (s.component i ∩ U) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen (s.irreducible i).2 hU
        ⟨s.point i,s.point_mem i,s.nonzero i,s.point_pivot i⟩
    apply hdense.trans
    apply closure_minimal _ hZ
    intro z hz
    have heval := h z.val z.property
    rw [s.eval_pullback,Finset.sum_eq_single i] at heval
    · have hzpull : G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C
          (atlas.chart (s.chart i)).coordinates P) (G.embedding z.val) = 0 :=
        (mul_eq_zero.mp heval).resolve_left (mul_ne_zero hz.2.1
          (pivotPolynomial_eval_ne_zero (s.pivot i) (s.padding c D i) z.val hz.2.2))
      exact ((atlas.chart (s.chart i)).pullback_eval_zero_iff G P D hP z.val
        (s.support_chart i z hz.2.1)).mp hzpull
    · intro j _ hji
      rw [s.zero_other i j hji.symm z hz.1,zero_mul,zero_mul]
    · simp

/-- A bounded translation atlas induces a uniform shifted comparison of
homogeneous quotient dimensions. The shift is independent of the input degree. -/
theorem translated_hilbertFunction_le (V : Set G.Point) (g : G.Point)
    (c : G.FactorIndex → ℕ) (atlas : PolynomialTranslationAtlas G g)
    (hc : ∀ a k, (atlas.chart a).degree k ≤ c k) :
    ∃ E : G.FactorIndex → ℕ, ∀ D : G.FactorIndex → ℕ,
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal (translate g V)) D ≤
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal V) (fun k => c k * D k + E k) := by
  obtain ⟨s⟩ := exists_separating_charts V atlas
  refine ⟨s.shift,fun D => ?_⟩
  apply G.ambient.hilbertFunction_le_of_linear_pullback
    (G.embedding '' translate g V) (G.embedding '' V) D _ (s.pullback c D)
    (fun P hP => s.pullback_homogeneous c hc D P hP)
  intro P hP
  simpa only [Set.forall_mem_image] using s.pullback_vanishing_iff c D P hP

end PhilipponMultiplicity.TranslationSupport

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertPieceGrowth

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- For a relevant homogeneous prime, multiplying by a selected nonzero
coordinate in each block makes the actual Hilbert function monotone. -/
theorem hilbertFunction_mono_relevant_prime (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    Monotone (hilbertFunction K M.factorCount M.ambientDimension Q) := by
  classical
  obtain ⟨v, hv⟩ := relevant_variables M Q hrel
  intro d e hde
  let P : M.CoordinateRing := ∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ (e - d) i
  have hP : M.IsHomogeneous P (e - d) := variable_product_homogeneous M v (e - d)
  have hPnot : P ∉ Q := variable_product_notMem M Q hQ v hv (e - d)
  have hcolon : Q.colon {P} = Q := by
    apply le_antisymm ?_ Ideal.le_colon
    intro f hf
    have hmul : f * P ∈ Q := by
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hf
    exact (hQ.mem_or_mem hmul).resolve_right hPnot
  have h := hilbertFunction_colon_add M Q hhom P (e - d) hP d
  rw [hcolon, tsub_add_cancel_of_le hde] at h
  omega

/-- One fixed shift bounds every graded piece by a value of the eventual
Hilbert polynomial, including degrees on coordinate boundaries. -/
theorem hilbertFunction_le_shifted_polynomial_relevant_prime
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ d₀ : M.FactorIndex → ℕ, ∀ d : M.FactorIndex → ℕ,
      (hilbertFunction K M.factorCount M.ambientDimension Q d : ℚ) ≤
        eval (fun i => ((d + d₀) i : ℚ))
          (hilbertPolynomial K M.factorCount M.ambientDimension Q) := by
  obtain ⟨d₀, hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q hhom)
  refine ⟨d₀, fun d => ?_⟩
  rw [hd₀ (d + d₀) (fun i => Nat.le_add_left _ _)]
  exact_mod_cast hilbertFunction_mono_relevant_prime M Q hQ hhom hrel
    (show d ≤ d + d₀ from fun i => Nat.le_add_right _ _)

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertFiltration

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

private def PhilipponHilbertFiltration_quotientProjection (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (d : M.FactorIndex → ℕ) :
    (M.CoordinateRing ⧸ I) →ₗ[K] (M.CoordinateRing ⧸ I) :=
  (I.restrictScalars K).liftQ
    ((Ideal.Quotient.mkₐ K I).toLinearMap.comp
      (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d)) (by
        intro P hP
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI P hP d))

private theorem PhilipponHilbertFiltration_quotientProjection_on_piece (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (d e : M.FactorIndex → ℕ)
    {x : M.CoordinateRing ⧸ I} (hx : x ∈ quotientPiece K M.factorCount M.ambientDimension I e) :
    PhilipponHilbertFiltration_quotientProjection M I hI d x = if d = e then x else 0 := by
  classical
  obtain ⟨P, hP, rfl⟩ := hx
  change Ideal.Quotient.mk I
    (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d P) = _
  rw [weightedHomogeneousComponent_of_mem hP]
  split_ifs <;> simp

/-- Distinct actual multidegree pieces of a homogeneous quotient are independent. -/
theorem quotientPiece_iSupIndep (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    iSupIndep (quotientPiece K M.factorCount M.ambientDimension I) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hz d hd
  have h := congrArg (PhilipponHilbertFiltration_quotientProjection M I hI d) hz
  rw [map_sum, map_zero] at h
  have heq : (∑ e ∈ s, PhilipponHilbertFiltration_quotientProjection M I hI d (v e)) = v d := by
    rw [Finset.sum_eq_single d]
    · simpa using PhilipponHilbertFiltration_quotientProjection_on_piece M I hI d d (hv d hd)
    · intro e he hed
      rw [PhilipponHilbertFiltration_quotientProjection_on_piece M I hI d e (hv e he), if_neg (Ne.symm hed)]
    · exact fun hn => False.elim (hn hd)
  exact heq.symm.trans h

instance finite_piece_sum (I : Ideal M.CoordinateRing) (s : Finset (M.FactorIndex → ℕ)) :
    Module.Finite K (⨆ d ∈ s, quotientPiece K M.factorCount M.ambientDimension I d :
      Submodule K (M.CoordinateRing ⧸ I)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : (⨆ d ∈ (∅ : Finset (M.FactorIndex → ℕ)),
        quotientPiece K M.factorCount M.ambientDimension I d :
        Submodule K (M.CoordinateRing ⧸ I)) = ⊥ := by simp
    rw [hz]
    infer_instance
  | @insert d s hd ih =>
    rw [Finset.iSup_insert]
    let := ih
    infer_instance

/-- The actual dimension of a finite sum of quotient pieces is their dimension sum. -/
theorem finrank_quotientPiece_sum (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (s : Finset (M.FactorIndex → ℕ)) :
    Module.finrank K (⨆ d ∈ s, quotientPiece K M.factorCount M.ambientDimension I d :
      Submodule K (M.CoordinateRing ⧸ I)) =
      ∑ d ∈ s, hilbertFunction K M.factorCount M.ambientDimension I d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert d s hd ih =>
    rw [Finset.iSup_insert, Finset.sum_insert hd]
    have hdis := (quotientPiece_iSupIndep M I hI).disjoint_biSup (y := (s : Set _)) hd
    have hzero : quotientPiece K M.factorCount M.ambientDimension I d ⊓
        (⨆ e ∈ s, quotientPiece K M.factorCount M.ambientDimension I e) = ⊥ := by
      simpa only [Finset.mem_coe] using hdis.eq_bot
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (quotientPiece K M.factorCount M.ambientDimension I d)
      (⨆ e ∈ s, quotientPiece K M.factorCount M.ambientDimension I e)
    rw [hzero, finrank_bot, add_zero, ih] at hdim
    exact hdim

theorem mem_multidegreesLe (n : ℕ) (d : M.FactorIndex → ℕ) :
    d ∈ multidegreesLe M n ↔ ∑ i, d i ≤ n := by
  classical
  simp only [multidegreesLe, Finset.mem_filter, Finset.mem_Iic]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro i
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h

theorem sum_blockWeight (e : M.Variable →₀ ℕ) :
    (∑ i, (Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e) i) = e.degree := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => M.blockWeight_apply e i)

theorem restrictTotalDegree_eq_piece_sum (n : ℕ) :
    restrictTotalDegree M.Variable K n =
      ⨆ d ∈ multidegreesLe M n, degreePiece K M.factorCount M.ambientDimension d := by
  classical
  apply le_antisymm
  · intro P hP
    have hdeg := (mem_restrictTotalDegree M.Variable n P).mp hP
    have hsum : (∑ e ∈ P.support, monomial e (coeff e P)) ∈
        ⨆ d ∈ multidegreesLe M n, degreePiece K M.factorCount M.ambientDimension d := by
      apply Submodule.sum_mem
      intro e he
      let d := Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e
      have hd : d ∈ multidegreesLe M n := (mem_multidegreesLe M n d).mpr (by
        rw [sum_blockWeight]
        exact (le_totalDegree he).trans hdeg)
      apply Submodule.mem_iSup_of_mem d
      apply Submodule.mem_iSup_of_mem hd
      exact isWeightedHomogeneous_monomial _ _ _ rfl
    simpa only [← P.as_sum] using hsum
  · refine iSup_le fun d => iSup_le fun hd => ?_
    intro P hP
    apply (mem_restrictTotalDegree M.Variable n P).mpr
    exact (M.homogeneous_total ((M.degreePiece_iff P d).mp hP)).totalDegree_le.trans
      ((mem_multidegreesLe M n d).mp hd)

theorem degreeFiltration_eq_piece_sum (I : Ideal M.CoordinateRing) (n : ℕ) :
    degreeFiltration M I n =
      ⨆ d ∈ multidegreesLe M n, quotientPiece K M.factorCount M.ambientDimension I d := by
  unfold degreeFiltration
  rw [restrictTotalDegree_eq_piece_sum]
  simp only [Submodule.map_iSup, quotientPiece]

instance degreeFiltration_finite (I : Ideal M.CoordinateRing) (n : ℕ) :
    Module.Finite K (degreeFiltration M I n) := by
  unfold degreeFiltration
  infer_instance

/-- The standard total-degree filtration counts the actual multigraded pieces. -/
theorem cumulativeHilbertFunction_eq_sum (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (n : ℕ) :
    cumulativeHilbertFunction M I n =
      ∑ d ∈ multidegreesLe M n, hilbertFunction K M.factorCount M.ambientDimension I d := by
  unfold cumulativeHilbertFunction
  rw [degreeFiltration_eq_piece_sum, finrank_quotientPiece_sum M I hI]

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertGrowthBounds

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The diagonal Hilbert function bounds the dimension of the actual
total-degree filtration, with explicit constants and no eventual threshold. -/
theorem cumulativeHilbertFunction_diagonal_bounds
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) (n : ℕ) :
    cumulativeHilbertFunction M Q n ≤
        (n + 1) ^ M.factorCount *
          hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) ∧
      (n + 1) ^ M.factorCount *
          hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) ≤
        cumulativeHilbertFunction M Q (2 * M.factorCount * n) := by
  classical
  let H := hilbertFunction K M.factorCount M.ambientDimension Q
  have hmono : Monotone H := hilbertFunction_mono_relevant_prime M Q hQ hhom hrel
  have hic : (Finset.Iic (fun _ : M.FactorIndex => n)).card = (n + 1) ^ M.factorCount := by
    simp [Pi.card_Iic, Nat.card_Iic, MultiProjectiveSpace.FactorIndex]
  have hcc : (Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n)).card =
      (n + 1) ^ M.factorCount := by
    have hnat : 2 * n + 1 - n = n + 1 := by omega
    simp [Pi.card_Icc, Nat.card_Icc, hnat, MultiProjectiveSpace.FactorIndex]
  constructor
  · rw [cumulativeHilbertFunction_eq_sum M Q hhom]
    calc
      ∑ d ∈ multidegreesLe M n, H d ≤ ∑ d ∈ Finset.Iic (fun _ => n), H d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro _ _ _; exact Nat.zero_le _
      _ ≤ ∑ _d ∈ Finset.Iic (fun _ : M.FactorIndex => n), H (fun _ => n) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hmono (Finset.mem_Iic.mp hd)
      _ = (n + 1) ^ M.factorCount * H (fun _ => n) := by
        rw [Finset.sum_const, nsmul_eq_mul, hic]
        simp
  · rw [cumulativeHilbertFunction_eq_sum M Q hhom]
    have hsub : Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n) ⊆
        multidegreesLe M (2 * M.factorCount * n) := by
      intro d hd
      apply (mem_multidegreesLe M _ d).mpr
      have h := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => (Finset.mem_Icc.mp hd).2 i)
      have hs : (∑ _i : M.FactorIndex, 2 * n) = 2 * M.factorCount * n := by
        simp [MultiProjectiveSpace.FactorIndex]
        ring
      exact h.trans_eq hs
    calc
      (n + 1) ^ M.factorCount * H (fun _ => n) =
          ∑ _d ∈ Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n), H (fun _ => n) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcc]
        simp
      _ ≤ ∑ d ∈ Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n), H d := by
        apply Finset.sum_le_sum
        intro d hd
        exact hmono (Finset.mem_Icc.mp hd).1
      _ ≤ ∑ d ∈ multidegreesLe M (2 * M.factorCount * n), H d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro _ _ _; exact Nat.zero_le _

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponDiagonalHilbert

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert

theorem diagonalPolynomial_eq_sum {ι : Type*} (F : MvPolynomial ι ℚ) :
    eval₂ Polynomial.C (fun _ => Polynomial.X) F =
      ∑ e ∈ F.support, Polynomial.monomial e.degree (coeff e F) := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [eval₂_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval₂_monomial]
  have hp : e.prod (fun _ k => (Polynomial.X : Polynomial ℚ) ^ k) =
      Polynomial.X ^ e.degree := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [hp, Polynomial.C_mul_X_pow_eq_monomial]

/-- Nonnegative top coefficients prevent cancellation on the diagonal. -/
theorem diagonalPolynomial_degree_and_leadingCoeff {ι : Type*}
    (F : MvPolynomial ι ℚ) (hF : F ≠ 0)
    (hpos : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F) :
    (eval₂ Polynomial.C (fun _ => Polynomial.X) F).natDegree = F.totalDegree ∧
      0 < (eval₂ Polynomial.C (fun _ => Polynomial.X) F).leadingCoeff := by
  classical
  let P := eval₂ Polynomial.C (fun _ => Polynomial.X) F
  have hle : P.natDegree ≤ F.totalDegree := by
    dsimp only [P]
    rw [diagonalPolynomial_eq_sum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro e he
    exact (Polynomial.natDegree_monomial_le (coeff e F)).trans (le_totalDegree he)
  have hcoef : 0 < P.coeff F.totalDegree := by
    dsimp only [P]
    rw [diagonalPolynomial_eq_sum, Polynomial.finsetSum_coeff]
    obtain ⟨e, he, hdeg⟩ := Finset.exists_mem_eq_sup F.support
      (support_nonempty.mpr hF) Finsupp.degree
    change F.totalDegree = e.degree at hdeg
    have hdeg' : e.degree = F.totalDegree := hdeg.symm
    apply Finset.sum_pos'
    · intro b hb
      rw [Polynomial.coeff_monomial]
      split_ifs with h
      · exact hpos b h
      · exact le_rfl
    · refine ⟨e, he, ?_⟩
      rw [Polynomial.coeff_monomial, if_pos hdeg']
      exact lt_of_le_of_ne (hpos e hdeg') (Ne.symm (mem_support_iff.mp he))
  have hdeg : P.natDegree = F.totalDegree :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (ne_of_gt hcoef))
  refine ⟨hdeg, ?_⟩
  change 0 < P.leadingCoeff
  simpa only [Polynomial.leadingCoeff, hdeg] using hcoef

theorem diagonalPolynomial_eval {ι : Type*} (F : MvPolynomial ι ℚ) (x : ℚ) :
    (eval₂ Polynomial.C (fun _ => Polynomial.X) F).eval x = eval (fun _ => x) F := by
  classical
  rw [diagonalPolynomial_eq_sum, Polynomial.eval_finsetSum]
  conv_rhs => rw [F.as_sum]
  rw [eval_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Polynomial.eval_monomial, eval_monomial, Finsupp.prod,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

/-- The diagonal of the actual Hilbert function eventually has precisely
the original total degree and a positive leading coefficient. -/
theorem exists_diagonal_hilbertPolynomial
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ P : Polynomial ℚ, P.natDegree = SectionThree.idealDimension M Q ∧
      0 < P.leadingCoeff ∧ ∃ N : ℕ, ∀ n ≥ N,
        P.eval (n : ℚ) =
          (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) := by
  classical
  let F := hilbertPolynomial K M.factorCount M.ambientDimension Q
  have hF : F ≠ 0 := relevant_prime_hilbertPolynomial_ne_zero M Q hQ hhom hrel
  have htop : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F := by
    intro e he
    have h := (multigraded_hilbert_polynomial_top_coefficients K M Q hhom).1 e
    rwa [coeff_homogeneousComponent, if_pos he] at h
  obtain ⟨hdeg, hpos⟩ := diagonalPolynomial_degree_and_leadingCoeff F hF htop
  refine ⟨eval₂ Polynomial.C (fun _ => Polynomial.X) F, hdeg, hpos, ?_⟩
  obtain ⟨d₀, hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q hhom)
  refine ⟨Finset.univ.sup d₀, fun n hn => ?_⟩
  rw [diagonalPolynomial_eval]
  apply hd₀
  intro i
  exact (Finset.le_sup (Finset.mem_univ i)).trans hn

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertGrowthExponent

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert

theorem polynomial_eventually_two_sided (P : Polynomial ℚ) (hpos : 0 < P.leadingCoeff) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℚ) ^ P.natDegree ≤ P.eval (n : ℚ) ∧
        P.eval (n : ℚ) ≤ C * (n : ℚ) ^ P.natDegree := by
  have hP : P ≠ 0 := by
    intro hz
    simpa [hz] using hpos
  have hdegree : P.degree = (Polynomial.X ^ P.natDegree : Polynomial ℚ).degree := by
    rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hP]
  have hlim := P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (Polynomial.X ^ P.natDegree) hdegree
  have hlim' : Tendsto (fun n : ℕ => P.eval (n : ℚ) / (n : ℚ) ^ P.natDegree)
      atTop (𝓝 P.leadingCoeff) := by
    simpa [Function.comp_def] using hlim.comp (tendsto_natCast_atTop_atTop (R := ℚ))
  have hlo := (tendsto_order.mp hlim').1 (P.leadingCoeff / 2) (by linarith)
  have hhi := (tendsto_order.mp hlim').2 (2 * P.leadingCoeff) (by linarith)
  refine ⟨P.leadingCoeff / 2, 2 * P.leadingCoeff, by positivity, by positivity, ?_⟩
  filter_upwards [hlo, hhi, eventually_ge_atTop 1] with n hnlo hnhi hn
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp := pow_pos hnpos P.natDegree
  exact ⟨(le_div_iff₀ hp).mp hnlo.le, (div_le_iff₀ hp).mp hnhi.le⟩

/-- The Hilbert-polynomial side of the prime dimension comparison:
the actual quotient filtration has matching polynomial growth bounds. -/
theorem cumulativeHilbertFunction_polynomial_bounds
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      c * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) ≤
          (cumulativeHilbertFunction M Q (2 * M.factorCount * n) : ℚ) ∧
        (cumulativeHilbertFunction M Q n : ℚ) ≤
          C * ((n + 1 : ℕ) : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) := by
  obtain ⟨P, hdeg, hpos, N₀, hP⟩ := exists_diagonal_hilbertPolynomial M Q hQ hhom hrel
  obtain ⟨c, C, hc, hC, hbounds⟩ := polynomial_eventually_two_sided P hpos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbounds
  refine ⟨c, C, hc, hC, max N N₀, fun n hn => ?_⟩
  have hp := hN n ((le_max_left N N₀).trans hn)
  rw [hP n ((le_max_right N N₀).trans hn), hdeg] at hp
  obtain ⟨hupper, hlower⟩ := cumulativeHilbertFunction_diagonal_bounds M Q hQ hhom hrel n
  have hu : (cumulativeHilbertFunction M Q n : ℚ) ≤
      ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
        (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) := by
    exact_mod_cast hupper
  have hl : ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
        (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) ≤
      (cumulativeHilbertFunction M Q (2 * M.factorCount * n) : ℚ) := by
    exact_mod_cast hlower
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hn1 : (n : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.le_succ n
  have hpow (b : ℕ) : (n : ℚ) ^ b ≤ ((n + 1 : ℕ) : ℚ) ^ b :=
    pow_le_pow_left₀ hn0 hn1 b
  constructor
  · calc
      c * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) =
          (n : ℚ) ^ M.factorCount * (c * (n : ℚ) ^ SectionThree.idealDimension M Q) := by
        rw [pow_add]; ring
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (c * (n : ℚ) ^ SectionThree.idealDimension M Q) :=
        mul_le_mul_of_nonneg_right (hpow M.factorCount) (by positivity)
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) :=
        mul_le_mul_of_nonneg_left hp.1 (by positivity)
      _ ≤ _ := hl
  · calc
      (cumulativeHilbertFunction M Q n : ℚ) ≤ _ := hu
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (C * (n : ℚ) ^ SectionThree.idealDimension M Q) :=
        mul_le_mul_of_nonneg_left hp.2 (by positivity)
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (C * ((n + 1 : ℕ) : ℚ) ^ SectionThree.idealDimension M Q) := by
        gcongr
      _ = _ := by rw [pow_add]; ring

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponGrowthExponentComparison

set_option autoImplicit false
set_option maxHeartbeats 500000
open Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert

/-- The elementary final comparison of polynomial growth exponents. -/
theorem exponent_le_of_eventual_power_bound {a b : ℕ} {c C : ℚ}
    (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, c * (n : ℚ) ^ a ≤ C * (n : ℚ) ^ b) : a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C / c) (max (N : ℚ) 1))
  have hnN : N ≤ n := by
    exact_mod_cast le_of_lt ((le_max_left (N : ℚ) 1).trans (le_max_right _ _) |>.trans_lt hn)
  have hn1 : (1 : ℚ) < n :=
    ((le_max_right (N : ℚ) 1).trans (le_max_right _ _)).trans_lt hn
  have hnpos : (0 : ℚ) < n := lt_trans zero_lt_one hn1
  have hpow : (n : ℚ) ^ (b + 1) ≤ (n : ℚ) ^ a :=
    pow_le_pow_right₀ hn1.le hba
  have hprod : (c * n) * (n : ℚ) ^ b ≤ C * (n : ℚ) ^ b := by
    calc
      (c * n) * (n : ℚ) ^ b = c * (n : ℚ) ^ (b + 1) := by rw [pow_succ]; ring
      _ ≤ c * (n : ℚ) ^ a := mul_le_mul_of_nonneg_left hpow hc.le
      _ ≤ _ := hN n hnN
  have hcn : c * n ≤ C := (mul_le_mul_iff_left₀ (pow_pos hnpos b)).mp hprod
  have hlarge : C < c * n := by
    have := (le_max_left (C / c) (max (N : ℚ) 1)).trans_lt hn
    have := (div_lt_iff₀ hc).mp this
    simpa [mul_comm] using this
  exact (not_lt_of_ge hcn) hlarge

/-- Linear changes of the filtration index do not change its growth exponent. -/
theorem exponent_le_of_scaled_filtration_bounds
    (f : ℕ → ℕ) {a b L : ℕ} {c C : ℚ} (hL : 0 < L) (hc : 0 < c) (hC : 0 ≤ C)
    (hlo : ∀ᶠ n : ℕ in atTop, c * (n : ℚ) ^ a ≤ (f (L * n) : ℚ))
    (hhi : ∀ᶠ n : ℕ in atTop, (f n : ℚ) ≤ C * ((n + 1 : ℕ) : ℚ) ^ b) : a ≤ b := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hlo
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hhi
  apply exponent_le_of_eventual_power_bound hc (C := C * ((L + 1 : ℕ) : ℚ) ^ b)
  apply eventually_atTop.mpr
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans ((le_max_left _ _).trans hn)
  have hn₂ : N₂ ≤ L * n :=
    ((le_max_right N₁ N₂).trans ((le_max_left _ _).trans hn)).trans
      (Nat.le_mul_of_pos_left n hL)
  have hnpos : 1 ≤ n := (le_max_right _ _).trans hn
  have hscale : ((L * n + 1 : ℕ) : ℚ) ≤ ((L + 1 : ℕ) : ℚ) * n := by
    exact_mod_cast (show L * n + 1 ≤ (L + 1) * n by nlinarith)
  calc
    c * (n : ℚ) ^ a ≤ (f (L * n) : ℚ) := hN₁ n hn₁
    _ ≤ C * ((L * n + 1 : ℕ) : ℚ) ^ b := hN₂ (L * n) hn₂
    _ ≤ C * (((L + 1 : ℕ) : ℚ) * n) ^ b :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale b) hC
    _ = (C * ((L + 1 : ℕ) : ℚ) ^ b) * (n : ℚ) ^ b := by rw [mul_pow]; ring

theorem degreeFiltration_mono {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) : Monotone (degreeFiltration M I) := by
  intro m n hmn
  apply Submodule.map_mono
  intro P hP
  apply (MvPolynomial.mem_restrictTotalDegree M.Variable n P).mpr
  exact ((MvPolynomial.mem_restrictTotalDegree M.Variable m P).mp hP).trans hmn

theorem cumulativeHilbertFunction_mono {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) : Monotone (cumulativeHilbertFunction M I) := by
  intro m n hmn
  exact Submodule.finrank_mono (degreeFiltration_mono M I hmn)

/-- A checked reduction with the remaining normalization-based growth theorem
as an explicit hypothesis. This does not assume a Hilbert-dimension formula. -/
theorem relevant_prime_krull_dimension_of_normalization_growth
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q)
    (hNoether : ∃ r L : ℕ, 0 < L ∧
      ringKrullDim (M.CoordinateRing ⧸ Q) = ((r : ℕ) : WithBot ℕ∞) ∧
      ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
        c * (n : ℚ) ^ r ≤ (cumulativeHilbertFunction M Q (L * n) : ℚ) ∧
        (cumulativeHilbertFunction M Q n : ℚ) ≤ C * ((n + 1 : ℕ) : ℚ) ^ r) :
    ringKrullDim (M.CoordinateRing ⧸ Q) =
      ((SectionThree.idealDimension M Q + M.factorCount : ℕ) : WithBot ℕ∞) := by
  obtain ⟨r, L, hL, hr, c₁, C₁, hc₁, hC₁, N₁, h₁⟩ := hNoether
  obtain ⟨c₂, C₂, hc₂, hC₂, N₂, h₂⟩ :=
    cumulativeHilbertFunction_polynomial_bounds M Q hQ hhom hrel
  have hu₁ : ∀ᶠ n : ℕ in atTop, (cumulativeHilbertFunction M Q n : ℚ) ≤
      C₁ * ((n + 1 : ℕ) : ℚ) ^ r :=
    eventually_atTop.mpr ⟨N₁, fun n hn => (h₁ n hn).2⟩
  have hu₂ : ∀ᶠ n : ℕ in atTop, (cumulativeHilbertFunction M Q n : ℚ) ≤
      C₂ * ((n + 1 : ℕ) : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) :=
    eventually_atTop.mpr ⟨N₂, fun n hn => (h₂ n hn).2⟩
  have hlo₁ : ∀ᶠ n : ℕ in atTop, c₁ * (n : ℚ) ^ r ≤
      (cumulativeHilbertFunction M Q (L * n) : ℚ) :=
    eventually_atTop.mpr ⟨N₁, fun n hn => (h₁ n hn).1⟩
  have hlo₂ : ∀ᶠ n : ℕ in atTop,
      c₂ * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) ≤
        (cumulativeHilbertFunction M Q ((2 * M.factorCount + 1) * n) : ℚ) := by
    apply eventually_atTop.mpr
    refine ⟨N₂, fun n hn => (h₂ n hn).1.trans ?_⟩
    exact_mod_cast cumulativeHilbertFunction_mono M Q
      (show 2 * M.factorCount * n ≤ (2 * M.factorCount + 1) * n by nlinarith)
  have ha := exponent_le_of_scaled_filtration_bounds (cumulativeHilbertFunction M Q)
    (by omega : 0 < 2 * M.factorCount + 1) hc₂ hC₁.le hlo₂ hu₁
  have hb := exponent_le_of_scaled_filtration_bounds (cumulativeHilbertFunction M Q)
    hL hc₁ hC₂.le hlo₁ hu₂
  rw [hr, le_antisymm hb ha]

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertRays

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {ι : Type*} [Fintype ι]

/-- Restrict a multivariate polynomial to an affine ray. -/
def rayPolynomial (F : MvPolynomial ι ℚ) (a E : ι → ℚ) : Polynomial ℚ :=
  eval₂ Polynomial.C (fun i => Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) F

def rayTerm (a E : ι → ℚ) (e : ι →₀ ℕ) (r : ℚ) : Polynomial ℚ :=
  Polynomial.C r * ∏ i, (Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) ^ e i

theorem rayPolynomial_eq_sum (F : MvPolynomial ι ℚ) (a E : ι → ℚ) :
    rayPolynomial F a E = ∑ e ∈ F.support, rayTerm a E e (coeff e F) := by
  classical
  simp only [rayPolynomial,MvPolynomial.eval₂_eq,rayTerm]
  apply Finset.sum_congr rfl
  intro e _
  change Polynomial.C _ * e.prod (fun i n =>
      (Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) ^ n) = _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem rayTerm_degree_and_leadingCoeff (a E : ι → ℚ) (ha : ∀ i, a i ≠ 0)
    (e : ι →₀ ℕ) (r : ℚ) (hr : r ≠ 0) :
    (rayTerm a E e r).natDegree = e.degree ∧
      (rayTerm a E e r).leadingCoeff = r * ∏ i, (a i) ^ e i := by
  classical
  have hn (i : ι) : Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i) ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_linear (ha i),Polynomial.natDegree_zero] at this
    omega
  constructor
  · rw [rayTerm,Polynomial.natDegree_C_mul hr,
      Polynomial.natDegree_prod Finset.univ _ (fun i _ => pow_ne_zero _ (hn i))]
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_linear (ha _),mul_one]
    change (∑ i, e i) = e.sum (fun _ n => n)
    exact (Finsupp.sum_fintype e (fun _ n => n) (fun _ => rfl)).symm
  · simp only [rayTerm,Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_prod,Polynomial.leadingCoeff_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.leadingCoeff_linear (ha i)]

theorem rayPolynomial_natDegree_le (F : MvPolynomial ι ℚ) (a E : ι → ℚ)
    (ha : ∀ i, a i ≠ 0) : (rayPolynomial F a E).natDegree ≤ F.totalDegree := by
  classical
  rw [rayPolynomial_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  rw [(rayTerm_degree_and_leadingCoeff a E ha e _ (mem_support_iff.mp he)).1]
  exact le_totalDegree he

/-- The fixed affine shift has no effect on the leading homogeneous part. -/
theorem rayPolynomial_top_coeff (F : MvPolynomial ι ℚ) (a E : ι → ℚ)
    (ha : ∀ i, a i ≠ 0) :
    (rayPolynomial F a E).coeff F.totalDegree =
      eval a (homogeneousComponent F.totalDegree F) := by
  classical
  rw [rayPolynomial_eq_sum,Polynomial.finsetSum_coeff]
  conv_rhs => arg 2; arg 2; rw [F.as_sum]
  rw [map_sum,eval_sum]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨hdeg,hlc⟩ := rayTerm_degree_and_leadingCoeff a E ha e _ (mem_support_iff.mp he)
  rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff e F) rfl)]
  by_cases hd : e.degree = F.totalDegree
  · rw [if_pos hd.symm,← hd,← hdeg,Polynomial.coeff_natDegree,hlc,eval_monomial]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [hdeg]; exact lt_of_le_of_ne (le_totalDegree he) hd)]
    simp [Ne.symm hd]

theorem eval_top_pos (F : MvPolynomial ι ℚ) (hF : F ≠ 0)
    (hpos : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F)
    (a : ι → ℚ) (ha : ∀ i, 0 < a i) :
    0 < eval a (homogeneousComponent F.totalDegree F) := by
  classical
  rw [← rayPolynomial_top_coeff F a 0 (fun i => (ha i).ne'),
    rayPolynomial_eq_sum,Polynomial.finsetSum_coeff]
  have hterm (e : ι →₀ ℕ) (he : e ∈ F.support) :
      (rayTerm a 0 e (coeff e F)).coeff F.totalDegree =
        if e.degree = F.totalDegree then coeff e F * ∏ i, a i ^ e i else 0 := by
    obtain ⟨hdeg,hlc⟩ := rayTerm_degree_and_leadingCoeff a 0 (fun i => (ha i).ne')
      e _ (mem_support_iff.mp he)
    split_ifs with hd
    · rw [← hd,← hdeg,Polynomial.coeff_natDegree,hlc]
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [hdeg]; exact lt_of_le_of_ne (le_totalDegree he) hd)
  obtain ⟨e,he,hd⟩ := Finset.exists_mem_eq_sup F.support
    (support_nonempty.mpr hF) Finsupp.degree
  change F.totalDegree = e.degree at hd
  apply Finset.sum_pos'
  · intro b hb
    rw [hterm b hb]
    split_ifs with h
    · exact mul_nonneg (hpos b h) (Finset.prod_nonneg fun i _ => pow_nonneg (ha i).le _)
    · exact le_rfl
  · refine ⟨e,he,?_⟩
    rw [hterm e he,if_pos hd.symm]
    exact mul_pos (lt_of_le_of_ne (hpos e hd.symm) (Ne.symm (mem_support_iff.mp he)))
      (Finset.prod_pos fun i _ => pow_pos (ha i) _)

theorem rayPolynomial_degree_and_leadingCoeff (F : MvPolynomial ι ℚ) (hF : F ≠ 0)
    (hpos : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F)
    (a E : ι → ℚ) (ha : ∀ i, 0 < a i) :
    (rayPolynomial F a E).natDegree = F.totalDegree ∧
      (rayPolynomial F a E).leadingCoeff = eval a (homogeneousComponent F.totalDegree F) ∧
      0 < (rayPolynomial F a E).leadingCoeff := by
  have hcoeff := rayPolynomial_top_coeff F a E (fun i => (ha i).ne')
  have hpos' := eval_top_pos F hF hpos a ha
  have hdeg := le_antisymm (rayPolynomial_natDegree_le F a E (fun i => (ha i).ne'))
    (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact hpos'.ne'))
  refine ⟨hdeg,?_,?_⟩
  · simpa only [Polynomial.leadingCoeff,hdeg] using hcoeff
  · simpa only [Polynomial.leadingCoeff,hdeg,hcoeff] using hpos'

theorem rayPolynomial_eval (F : MvPolynomial ι ℚ) (a E : ι → ℚ) (x : ℚ) :
    (rayPolynomial F a E).eval x = eval (fun i => a i * x + E i) F := by
  change (Polynomial.evalRingHom x) (eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) F) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id ℚ := by
    ext r
    simp
  rw [hc,MvPolynomial.eval₂_id]
  have hf : (⇑(Polynomial.evalRingHom x) ∘ fun i =>
      Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) =
        fun i => a i * x + E i := by
    funext i
    simp
  rw [hf]

end PhilipponMultiplicity.Hilbert
end
end


section
-- Reused implementation: Solutions.PhilipponShiftedHilbertComparison

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert

theorem natDegree_le_of_eventual_eval_le (P Q : Polynomial ℚ)
    (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (hle : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  obtain ⟨c,C,hc,hC,hboundsP⟩ := polynomial_eventually_two_sided P hP
  obtain ⟨c',C',hc',hC',hboundsQ⟩ := polynomial_eventually_two_sided Q hQ
  apply exponent_le_of_eventual_power_bound hc (C := C')
  filter_upwards [hboundsP,hboundsQ,hle] with n hnP hnQ hn
  exact hnP.1.trans (hn.trans hnQ.2)

theorem leadingCoeff_le_of_eventual_eval_le (P Q : Polynomial ℚ)
    (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (hdeg : P.natDegree = Q.natDegree)
    (hle : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.leadingCoeff ≤ Q.leadingCoeff := by
  have hlim (R : Polynomial ℚ) (hR : 0 < R.leadingCoeff) :
      Tendsto (fun n : ℕ => R.eval (n : ℚ) / (n : ℚ) ^ R.natDegree)
        atTop (𝓝 R.leadingCoeff) := by
    have hne : R ≠ 0 := by intro h; simpa [h] using hR
    have hd : R.degree = (Polynomial.X ^ R.natDegree : Polynomial ℚ).degree := by
      rw [Polynomial.degree_X_pow,Polynomial.degree_eq_natDegree hne]
    simpa [Function.comp_def] using (R.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
      (Polynomial.X ^ R.natDegree) hd).comp (tendsto_natCast_atTop_atTop (R := ℚ))
  apply le_of_tendsto_of_tendsto (hlim P hP) (hlim Q hQ)
  filter_upwards [hle] with n hn
  rw [hdeg]
  exact div_le_div_of_nonneg_right hn (pow_nonneg (Nat.cast_nonneg _) _)

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem vanishing_hilbertPolynomial_ne_zero {S : Set M.Point} (hS : S.Nonempty) :
    hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S) ≠ 0 := by
  obtain ⟨d₀,hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension
    (M.vanishingIdeal S) (multigraded_hilbert_polynomial_exists K M _
      (vanishingIdeal_multihomogeneous K M S))
  intro hz
  have h := hd₀ d₀ (fun _ => le_rfl)
  rw [hz,map_zero] at h
  have hp : (0 : ℚ) < hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) d₀ := by exact_mod_cast M.hilbertFunction_pos hS d₀
  exact hp.ne' h.symm

theorem exists_ray_hilbertPolynomial {S : Set M.Point} (hS : S.Nonempty)
    (a E : M.FactorIndex → ℕ) (ha : ∀ i, 1 ≤ a i) :
    ∃ P : Polynomial ℚ,
      P.natDegree = (hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal S)).totalDegree ∧
      P.leadingCoeff = eval (fun i => (a i : ℚ))
        (homogeneousComponent (hilbertPolynomial K M.factorCount M.ambientDimension
          (M.vanishingIdeal S)).totalDegree
          (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S))) ∧
      0 < P.leadingCoeff ∧ ∃ N : ℕ, ∀ n ≥ N,
        P.eval (n : ℚ) = (hilbertFunction K M.factorCount M.ambientDimension
          (M.vanishingIdeal S) (fun i => a i * n + E i) : ℚ) := by
  classical
  let F := hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S)
  have hhom := vanishingIdeal_multihomogeneous K M S
  have htop : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F := by
    intro e he
    have h := (multigraded_hilbert_polynomial_top_coefficients K M _ hhom).1 e
    rwa [coeff_homogeneousComponent,if_pos he] at h
  have hap (i : M.FactorIndex) : 0 < (a i : ℚ) := by
    exact_mod_cast (show 0 < a i by have := ha i; omega)
  obtain ⟨hd,hlc,hpos⟩ := rayPolynomial_degree_and_leadingCoeff F
    (vanishing_hilbertPolynomial_ne_zero M hS) htop
    (fun i => (a i : ℚ)) (fun i => (E i : ℚ)) hap
  refine ⟨rayPolynomial F (fun i => (a i : ℚ)) (fun i => (E i : ℚ)),hd,hlc,hpos,?_⟩
  obtain ⟨d₀,hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension
    (M.vanishingIdeal S) (multigraded_hilbert_polynomial_exists K M _ hhom)
  refine ⟨Finset.univ.sup d₀,fun n hn => ?_⟩
  rw [rayPolynomial_eval]
  have h := hd₀ (fun i => a i * n + E i) (fun i =>
    (Finset.le_sup (Finset.mem_univ i)).trans (hn.trans
      ((Nat.le_mul_of_pos_left n (by have := ha i; omega)).trans (Nat.le_add_right _ _))))
  simpa only [Nat.cast_add,Nat.cast_mul] using h

/-- A fixed coordinatewise degree shift does not change the dimension
comparison inferred from Hilbert functions. -/
theorem dimension_le_of_shifted_hilbertFunction_le (S T : Set M.Point)
    (hS : S.Nonempty) (hT : T.Nonempty) (c E : M.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i)
    (hle : ∀ D : M.FactorIndex → ℕ,
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal T)
        (fun i => c i * D i + E i)) :
    (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S)).totalDegree ≤
      (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal T)).totalDegree := by
  obtain ⟨P,hPd,hPlc,hPpos,NP,hP⟩ := exists_ray_hilbertPolynomial M hS (fun _ => 1) 0
    (fun _ => le_rfl)
  obtain ⟨Q,hQd,hQlc,hQpos,NQ,hQ⟩ := exists_ray_hilbertPolynomial M hT c E hc
  rw [← hPd,← hQd]
  apply natDegree_le_of_eventual_eval_le P Q hPpos hQpos
  apply eventually_atTop.mpr
  refine ⟨max NP NQ,fun n hn => ?_⟩
  rw [hP n ((le_max_left _ _).trans hn),hQ n ((le_max_right _ _).trans hn)]
  simpa only [Pi.zero_apply,one_mul,add_zero,Nat.cast_le] using hle (fun _ => n)

/-- At equal Hilbert dimension, the same comparison yields the normalized
degree inequality with exactly the specified coordinatewise scaling. -/
theorem degreeValue_le_of_shifted_hilbertFunction_le (S T : Set M.Point)
    (hS : S.Nonempty) (hT : T.Nonempty) (c E : M.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i)
    (hle : ∀ D : M.FactorIndex → ℕ,
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal T)
        (fun i => c i * D i + E i))
    (hdim : (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S)).totalDegree =
      (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal T)).totalDegree)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    degreeValue K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      degreeValue K M.factorCount M.ambientDimension (M.vanishingIdeal T) (fun i => c i * D i) := by
  obtain ⟨P,hPd,hPlc,hPpos,NP,hP⟩ := exists_ray_hilbertPolynomial M hS D 0 hD
  obtain ⟨Q,hQd,hQlc,hQpos,NQ,hQ⟩ := exists_ray_hilbertPolynomial M hT (fun i => c i * D i) E
    (fun i => by have := hc i; have := hD i; nlinarith)
  have hlc : P.leadingCoeff ≤ Q.leadingCoeff := by
    apply leadingCoeff_le_of_eventual_eval_le P Q hPpos hQpos (by rw [hPd,hQd,hdim])
    apply eventually_atTop.mpr
    refine ⟨max NP NQ,fun n hn => ?_⟩
    rw [hP n ((le_max_left _ _).trans hn),hQ n ((le_max_right _ _).trans hn)]
    simpa only [Pi.zero_apply,add_zero,mul_assoc,Nat.cast_le] using hle (fun i => D i * n)
  rw [hPlc,hQlc] at hlc
  unfold degreeValue degreeForm
  simp only [MvPolynomial.smul_eq_C_mul,map_mul,eval_C]
  rw [hdim]
  exact mul_le_mul_of_nonneg_left (by simpa only [hdim] using hlc) (Nat.cast_nonneg _)

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponTranslatedDegree

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

/-- Translation preserves the actual Hilbert dimension and satisfies the
degree bound from Lemma 4.5. This stronger form works for every subset. -/
theorem translated_dimension_and_degree (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : Set G.Point) :
    varietyDimension G V = varietyDimension G (translate g V) ∧
    ∀ D : G.FactorIndex → ℕ, (∀ i, 1 ≤ D i) →
      hilbertDegreeForm G V D ≤
        hilbertDegreeForm G (translate g V) (fun i => c i * D i) := by
  classical
  by_cases hV : V.Nonempty
  · have hW : (translate g V).Nonempty := hV.image (fun x => g+x)
    have hS := hV.image G.embedding
    have hT := hW.image G.embedding
    have hback : translate (-g) (translate g V) = V := by
      ext x
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
        simpa only [← add_assoc,neg_add_cancel,zero_add] using hz
      · intro hx
        exact ⟨g+x,⟨x,hx,rfl⟩,by simp only [← add_assoc,neg_add_cancel,zero_add]⟩
    obtain ⟨atlas,ha⟩ := hbound g
    obtain ⟨atlas',ha'⟩ := hbound (-g)
    obtain ⟨E,hE⟩ := TranslationSupport.translated_hilbertFunction_le V g c atlas ha
    obtain ⟨E',hE'⟩ := TranslationSupport.translated_hilbertFunction_le (translate g V) (-g)
      c atlas' ha'
    rw [hback] at hE'
    have hd₁ := Hilbert.dimension_le_of_shifted_hilbertFunction_le G.ambient
      (G.embedding '' translate g V) (G.embedding '' V) hT hS c E hc hE
    have hd₂ := Hilbert.dimension_le_of_shifted_hilbertFunction_le G.ambient
      (G.embedding '' V) (G.embedding '' translate g V) hS hT c E' hc hE'
    have heq : varietyDimension G V = varietyDimension G (translate g V) :=
      le_antisymm hd₂ hd₁
    refine ⟨heq,fun D hD => ?_⟩
    have hdeg := Hilbert.degreeValue_le_of_shifted_hilbertFunction_le G.ambient
      (G.embedding '' V) (G.embedding '' translate g V) hS hT c E' hc hE' heq D hD
    change (Hilbert.degreeValue K G.ambient.factorCount G.ambient.ambientDimension
      (G.ambient.vanishingIdeal (G.embedding '' V)) D : ℝ) ≤
      (Hilbert.degreeValue K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (G.embedding '' translate g V)) (fun i => c i * D i) : ℝ)
    exact_mod_cast hdeg
  · have hV' : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hV
    subst V
    have hW : translate g (∅ : Set G.Point) = ∅ := Set.image_empty _
    have hzero : Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal ∅) = 0 := by
      change Hilbert.hilbertPolynomial K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (G.embedding '' ∅)) = 0
      rw [Set.image_empty]
      exact G.ambient.hilbertPolynomial_empty
    rw [hW]
    refine ⟨rfl,fun D hD => ?_⟩
    simp only [hilbertDegreeForm,Hilbert.degreeValue,Hilbert.degreeForm,hzero,
      map_zero,smul_zero,Rat.cast_zero,le_refl]

/-- The unchanged paper statement of Philippon's Lemma 4.5. -/
theorem lemma_4_5
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : GroupSubvariety G) :
    varietyDimension G V.carrier = varietyDimension G (translate g V.carrier) ∧
    ∀ D : G.FactorIndex → ℕ, (∀ i, 1 ≤ D i) →
      hilbertDegreeForm G V.carrier D ≤
        hilbertDegreeForm G (translate g V.carrier) (fun i => c i * D i) := by
  exact translated_dimension_and_degree G c hc hbound g V.carrier

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

/-- Polynomial substitution preserves analyticity of every coefficient. -/
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

/-- A substitution homogeneous block by block has the exact transformed degree,
including when its coefficients belong to a ring of analytic functions. -/
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
-- Reused implementation: Solutions.PhilipponPolynomialMapCharts

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

/-- A finite family of globally compatible polynomial formulas covers an
arbitrary regular map into a chosen target projective block. -/
theorem IsRegularAlong.exists_finite_polynomialMapCharts (hf : M.IsRegularAlong N e f)
    (b : N.FactorIndex) :
    ∃ charts : Finset (PolynomialMapChart M N e f b),
      ∀ x, ∃ chart ∈ charts, M.eval chart.cut (e x) ≠ 0 := by
  classical
  exact finite_polynomial_nonzero_cover (fun chart : PolynomialMapChart M N e f b => chart.cut)
    (fun x => M.coordinate (e x)) (fun x => hf.exists_polynomialMapChart x b)

end PhilipponMultiplicity.MultiProjectiveSpace

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

abbrev AdditionPolynomialChart (E : EmbeddedCommutativeGroup K) :=
  MultiProjectiveSpace.PolynomialMapChart (projectiveSquare K E.ambientDimension)
    (projectiveSpace K E.ambientDimension) E.additionSource
    (fun xy : E.Point × E.Point => fun _ => (xy.1 + xy.2).val) ⟨0,by change 0 < 1; decide⟩

/-- The algebraic addition law has a finite homogeneous polynomial cover with
one positive degree bound depending only on the embedded group. -/
theorem exists_finite_bounded_addition_charts (E : EmbeddedCommutativeGroup K) :
    ∃ c : ℕ, 1 ≤ c ∧ ∃ charts : Finset E.AdditionPolynomialChart,
      (∀ chart ∈ charts, ∀ i, chart.degree i ≤ c) ∧
      ∀ xy : E.Point × E.Point, ∃ chart ∈ charts,
        (projectiveSquare K E.ambientDimension).eval chart.cut (E.additionSource xy) ≠ 0 := by
  classical
  obtain ⟨charts,hcover⟩ := E.addition_regular.exists_finite_polynomialMapCharts
    ⟨0,by change 0 < 1; decide⟩
  let c : ℕ := 1 + ∑ chart ∈ charts, ∑ i, chart.degree i
  refine ⟨c,by dsimp [c]; omega,charts,?_,hcover⟩
  intro chart hchart i
  have hinner : chart.degree i ≤ ∑ j, chart.degree j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (chart.degree j)) (Finset.mem_univ i)
  have houter : (∑ j, chart.degree j) ≤ ∑ ch ∈ charts, ∑ j, ch.degree j :=
    Finset.single_le_sum (fun ch _ => Nat.zero_le (∑ j, ch.degree j)) hchart
  exact hinner.trans (houter.trans (Nat.le_add_left _ _))

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
-- Reused implementation: Solutions.PhilipponPolynomialChartLifts

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

def factorChartDomain (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart) :
    Set G.Point :=
  {x | G.ambient.eval (specializationAtZero A g i chart.cut) (G.embedding x) ≠ 0}

theorem factorChartDomain_isOpen (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart) :
    @IsOpen _ G.zariskiTopology (factorChartDomain A g i chart) := by
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (G.ambient.isOpen_basic _ _
    (specializationAtZero_homogeneous A g i chart.cut chart.cutDegree chart.cut_homogeneous)).preimage
      (continuous_induced_dom : @Continuous _ _ G.zariskiTopology G.ambient.zariskiTopology G.embedding)

theorem mem_factorChartDomain (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart)
    (x : G.Point)
    (hx : (factorSquare i).eval chart.cut ((G.factor i).additionSource (x i,g i)) ≠ 0) :
    x ∈ factorChartDomain A g i chart := by
  change G.ambient.eval (specializationAtZero A g i chart.cut) (G.embedding x) ≠ 0
  rw [specializationAtZero_eval]
  exact ((factorSquare i).eval_eq_zero_iff_of_lift _ (pairLift A g i x 0)
    (pairLift_represents A g i x 0 g (liftAtZero_represents A g i))
    chart.cut chart.cutDegree chart.cut_homogeneous).not.mpr hx

theorem factorChart_represents (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart)
    (x : G.Point) (hx : x ∈ factorChartDomain A g i chart) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      ∃ h : (fun j => MvPolynomial.eval (pairLift A g i x z) (chart.coordinates j)) ≠ 0,
        Projectivization.mk K (fun j => MvPolynomial.eval (pairLift A g i x z) (chart.coordinates j)) h =
          G.embedding (x+g+A.map ⟨z,hz⟩) i := by
  have hx' : MvPolynomial.eval (pairLift A g i x 0) chart.cut ≠ 0 := by
    rw [← specializationAtZero_eval]
    exact hx
  have hnear := (pairLift_evaluation_analytic A g i chart.cut x).continuousAt.eventually_ne hx'
  filter_upwards [hnear,A.lift_represents g] with z hz hrep
  obtain ⟨hzA,hL⟩ := hrep
  obtain ⟨hn,heq⟩ := chart.represents_lift (x i,(g+A.map ⟨z,hzA⟩) i)
    (pairLift A g i x z) (pairLift_represents A g i x z _ (hL i)) hz
  refine ⟨hzA,hn,?_⟩
  simpa only [EmbeddedGroupProduct.embedding,Pi.add_apply,add_assoc] using heq

theorem factorChart_compatible (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart)
    (x : G.Point) (j k : Fin (G.ambient.ambientDimension i + 1)) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      MvPolynomial.eval (pairLift A g i x z) (chart.coordinates j) * A.lift (g+x) z ⟨i,k⟩ =
        MvPolynomial.eval (pairLift A g i x z) (chart.coordinates k) * A.lift (g+x) z ⟨i,j⟩ := by
  filter_upwards [A.lift_represents g,A.lift_represents (g+x)] with z hg hgx
  obtain ⟨hz,hL⟩ := hg
  obtain ⟨hz',hL'⟩ := hgx
  have hzeq : (⟨z,hz'⟩ : A.domain) = ⟨z,hz⟩ := Subtype.ext rfl
  rw [hzeq] at hL'
  obtain ⟨hn,heq⟩ := hL' i
  apply chart.compatible_lifts (x i,(g+A.map ⟨z,hz⟩) i) (pairLift A g i x z)
    (pairLift_represents A g i x z _ (hL i)) (fun l => A.lift (g+x) z ⟨i,l⟩) hn ?_ j k
  change Projectivization.mk K (fun l : Fin (G.ambient.ambientDimension i + 1) =>
    A.lift (g+x) z ⟨i,l⟩) hn = (x i + (g i + A.map ⟨z,hz⟩ i)).val
  simpa only [EmbeddedGroupProduct.embedding,Pi.add_apply,add_assoc,add_left_comm] using heq

end PhilipponMultiplicity.AtlasSupport
end
end


section
-- Reused implementation: Solutions.PhilipponBoundedTranslationAtlas

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

/-- A choice of one algebraic addition chart in every factor gives a genuine
polynomial translation chart with analytic coefficients. -/
def assembledTranslationChart (charts : ∀ i, (G.factor i).AdditionPolynomialChart) :
    TranslationChart A g where
  domain := ⋂ i, factorChartDomain A g i (charts i)
  domain_isOpen := by
    letI : TopologicalSpace G.Point := G.zariskiTopology
    exact isOpen_iInter_of_finite (fun i => factorChartDomain_isOpen A g i (charts i))
  degree i := (charts i).degree (firstBlock i)
  coordinates v := pairSubstitution A g v.1 ((charts v.1).coordinates v.2)
  coefficient_analytic v e _ := pairSubstitution_coeff_analytic A g v.1 _ e
  coordinate_homogeneous := by
    intro v e he
    have hh := pairSubstitution_homogeneous A g v.1 ((charts v.1).coordinates v.2)
      (charts v.1).degree ((charts v.1).homogeneous v.2) (mem_support_iff.mp he)
    have hd (i : G.FactorIndex) := (G.ambient.blockWeight_apply e i).symm.trans (congrFun hh i)
    refine ⟨?_,?_⟩
    · simpa only [Pi.single_eq_same] using hd v.1
    · intro i hi
      simpa only [Pi.single_apply,if_neg hi] using hd i
  coordinate_compatible := by
    intro x i j k
    simpa only [evaluate_pairSubstitution] using factorChart_compatible A g i (charts i) x j k
  represents := by
    intro x hx
    have hh : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ i,
        ∃ hz : z ∈ A.domain,
        ∃ h : (fun j => MvPolynomial.eval (pairLift A g i x z) ((charts i).coordinates j)) ≠ 0,
          Projectivization.mk K
            (fun j => MvPolynomial.eval (pairLift A g i x z) ((charts i).coordinates j)) h =
              G.embedding (x+g+A.map ⟨z,hz⟩) i :=
      Filter.eventually_all.mpr (fun i => factorChart_represents A g i (charts i) x (Set.mem_iInter.mp hx i))
    filter_upwards [hh,A.domain_open.mem_nhds A.zero_mem] with z hrep hz
    refine ⟨hz,?_⟩
    intro i
    obtain ⟨hzi,hn,heq⟩ := hrep i
    have hzeq : (⟨z,hzi⟩ : A.domain) = ⟨z,hz⟩ := Subtype.ext rfl
    rw [hzeq] at heq
    simp only [evaluate_pairSubstitution]
    exact ⟨hn,heq⟩

/-- The finite addition-law charts are chosen once for each embedded factor;
their degree bounds are independent of the analytic subgroup and translation. -/
theorem exists_uniformly_bounded_translation_atlas :
    ∃ c : EmbeddedCommutativeGroup K → ℕ, (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point),
        ∃ atlas : TranslationAtlas A g, atlas.IsBoundedBy (fun i => c (G.factor i)) := by
  classical
  choose c hc charts hbound hcover using
    (fun E : EmbeddedCommutativeGroup K => E.exists_finite_bounded_addition_charts)
  refine ⟨c,hc,?_⟩
  intro G A g
  let Index : Type u := ∀ i : G.FactorIndex, {chart : (G.factor i).AdditionPolynomialChart // chart ∈ charts (G.factor i)}
  let atlas : TranslationAtlas A g :=
    { Index := Index
      chart := fun a => assembledTranslationChart A g (fun i => (a i).val)
      covers := by
        intro x
        choose ch hch hx using (fun i => hcover (G.factor i) (x i,g i))
        refine ⟨(fun i => ⟨ch i,hch i⟩),Set.mem_iInter.mpr ?_⟩
        intro i
        exact mem_factorChartDomain A g i (ch i) x (hx i) }
  refine ⟨atlas,?_⟩
  intro a i
  exact hbound (G.factor i) (a i).val (a i).property (firstBlock i)

end PhilipponMultiplicity.AtlasSupport
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

theorem chart_evaluation_analytic (chart : TranslationChart A g)
    (x : G.Point) (v : G.ambient.Variable) :
    AnalyticAt K (evaluateCoefficientPolynomial A (chart.coordinates v) x) 0 :=
  evaluated_coefficients_analytic _ (coordinate_coeff_analytic chart v) x

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

/-- Evaluation of the actual coefficientwise polynomial operator is the
corresponding mixed derivative of the actual evaluated chart polynomial. -/
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

theorem polynomialOperator_zero_order (chart : TranslationChart A g)
    (directions : Fin 0 → Fin A.parameterDimension) (P : G.CoordinateRing) :
    polynomialOperator chart 0 directions P =
      MvPolynomial.map (Pi.evalRingHom (fun _ : A.ParameterSpace => K) 0)
        (substitutedPolynomial chart P) := by
  ext e
  simp [polynomialOperator_coeff, coeff_map]

theorem polynomialOperator_zero_algHom (chart : TranslationChart A g)
    (directions : Fin 0 → Fin A.parameterDimension) :
    ∃ f : G.CoordinateRing →ₐ[K] G.CoordinateRing,
      ∀ P, f P = polynomialOperator chart 0 directions P := by
  let f : G.CoordinateRing →+* G.CoordinateRing :=
    (MvPolynomial.map (Pi.evalRingHom (fun _ : A.ParameterSpace => K) 0)).comp
      (MvPolynomial.eval₂Hom
        (MvPolynomial.C.comp (Pi.constRingHom A.ParameterSpace K)) chart.coordinates)
  have hf (a : K) : f (algebraMap K G.CoordinateRing a) = algebraMap K G.CoordinateRing a := by
    simp [f, MvPolynomial.algebraMap_eq]
  refine ⟨{ f with commutes' := hf }, fun P => ?_⟩
  exact (polynomialOperator_zero_order chart directions P).symm

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
-- Reused implementation: Solutions.PhilipponContactCosets
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

/-- Specialization at parameter zero gives the actual polynomial translation
chart, with the same coordinate degrees. -/
def TranslationChart.polynomialChart [CompleteSpace K] {g : G.Point}
    (chart : TranslationChart A g) : PolynomialTranslationChart G g where
  domain := chart.domain
  domain_open := chart.domain_isOpen
  degree := chart.degree
  coordinates v := polynomialOperator chart 0 Fin.elim0 (MvPolynomial.X v)
  homogeneous v := by
    have h := polynomialOperator_homogeneous chart 0 Fin.elim0 (MvPolynomial.X v)
      (fun i => if i = v.1 then 1 else 0) (G.ambient.isHomogeneous_X v)
    simpa only [mul_ite,mul_one,mul_zero] using h
  represents x hx := by
    have he (v : G.ambient.Variable) :
        G.ambient.eval (polynomialOperator chart 0 Fin.elim0 (MvPolynomial.X v))
          (G.embedding x) = evaluateCoefficientPolynomial A (chart.coordinates v) x 0 := by
      rw [polynomialOperator_eval]
      simp only [iteratedFDeriv_zero_apply,MvPolynomial.eval_X]
    simp_rw [he]
    have hh := Filter.Eventually.self_of_nhds (chart.represents x hx)
    simpa only [A.map_zero,add_zero,add_comm x g] using hh.2

def TranslationAtlas.polynomialAtlas [CompleteSpace K] {g : G.Point}
    (atlas : TranslationAtlas A g) : PolynomialTranslationAtlas G g where
  Index := atlas.Index
  chart a := (atlas.chart a).polynomialChart
  covers := atlas.covers


end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponGroupEquidimensional

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]

/-- The constant parametrization supplies analytic charts without imposing
any extra hypothesis on the algebraic group. -/
def AnalyticSubgroup.trivial (G : EmbeddedGroupProduct K) : AnalyticSubgroup G where
  parameterDimension := 1
  parameterDimension_pos := by decide
  radius := 1
  radius_pos := by norm_num
  domain := Metric.ball 0 1
  domain_eq_ball := rfl
  domain_open := Metric.isOpen_ball
  zero_mem := by simp
  map := fun _ => 0
  map_zero := rfl
  map_add := by intros; exact (zero_add 0).symm
  lift := fun g _ => G.ambient.coordinate (G.embedding g)
  lift_analytic := fun _ _ => analyticAt_const
  base_series := fun _ => ⟨_, hasFPowerSeriesOnBall_const.mono (by simp) le_top⟩
  base_represents := fun _ i => ⟨Projectivization.rep_nonzero (G.embedding 0 i),
    Projectivization.mk_rep (G.embedding 0 i)⟩
  lift_represents := by
    intro g
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0 : Fin 1 → K) ∈ Metric.ball 0 1 by simp)]
      with z hz
    refine ⟨hz, fun i => ⟨Projectivization.rep_nonzero (G.embedding g i), ?_⟩⟩
    simpa only [add_zero, MultiProjectiveSpace.coordinate] using
      Projectivization.mk_rep (G.embedding g i)

/-- A finite algebraic addition atlas gives a uniform polynomial translation
bound, independently of any specified analytic subgroup. -/
theorem exists_translationDegreeBound [CompleteSpace K] (G : EmbeddedGroupProduct K) :
    ∃ c : G.FactorIndex → ℕ, (∀ i, 1 ≤ c i) ∧ TranslationDegreeBound G c := by
  obtain ⟨c,hc,hatlas⟩ := AtlasSupport.exists_uniformly_bounded_translation_atlas (K := K)
  refine ⟨fun i => c (G.factor i), fun i => hc _, fun g => ?_⟩
  obtain ⟨atlas,hbound⟩ := hatlas G (AnalyticSubgroup.trivial G) g
  exact ⟨atlas.polynomialAtlas,hbound⟩

theorem varietyDimension_translate [CompleteSpace K] (G : EmbeddedGroupProduct K)
    (g : G.Point) (V : Set G.Point) :
    varietyDimension G (translate g V) = varietyDimension G V := by
  obtain ⟨c,hc,hbound⟩ := exists_translationDegreeBound G
  exact (translated_dimension_and_degree G c hc hbound g V).1.symm


end PhilipponMultiplicity
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
-- Reused implementation: Solutions.PhilipponMixedIntegrality

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.BinomialPolynomial

/-- Positive leading coefficients prevent cancellation at the largest cell degree. -/
theorem sum_product_degree {ι J : Type*} [Fintype ι] [Fintype J]
    (q a : J → ι → ℕ) :
    (∑ j, product (q j) (a j)).totalDegree =
      Finset.univ.sup (fun j : J => ∑ i, q j i) := by
  classical
  cases isEmpty_or_nonempty J with
  | inl h => simp
  | inr h =>
    let F := ∑ j, product (q j) (a j)
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
    exact le_antisymm hFle hFge

/-- After factorial normalization, a top coefficient counts the cells with that exponent. -/
theorem sum_product_top_normalized {ι J : Type*} [Fintype ι] [Fintype J]
    (q a : J → ι → ℕ) (α : ι → ℕ)
    (hα : ∑ i, α i = (∑ j, product (q j) (a j)).totalDegree) :
    coeff (exponent α) (∑ j, product (q j) (a j)) *
      (∏ i, ((α i).factorial : ℚ)) =
        ((Finset.univ.filter (fun j : J => q j = α)).card : ℚ) := by
  classical
  let F := ∑ j, product (q j) (a j)
  let n := F.totalDegree
  have hqn (j : J) : (∑ i, q j i) ≤ n := by
    dsimp [n, F]
    rw [sum_product_degree]
    exact Finset.le_sup (f := fun j : J => ∑ i, q j i) (Finset.mem_univ j)
  have hexp : (exponent α).sum (fun _ e => e) = n := by
    simpa [exponent, Finsupp.sum_fintype] using hα
  have htop : coeff (exponent α) F = coeff (exponent α) (homogeneousComponent n F) := by
    have hd : (exponent α).degree = n := hexp
    simp [coeff_homogeneousComponent, hd]
  change coeff (exponent α) F * _ = _
  rw [htop]
  simp only [F, map_sum, coeff_sum, Finset.sum_mul]
  have hterm (j : J) :
      coeff (exponent α) (homogeneousComponent n (product (q j) (a j))) *
        (∏ i, ((α i).factorial : ℚ)) = if q j = α then 1 else 0 := by
    by_cases he : (∑ i, q j i) = n
    · rw [← he, product_top, coeff_monomial]
      by_cases hq : q j = α
      · rw [hq, if_pos rfl, if_pos rfl]
        rw [Finset.prod_inv_distrib, inv_mul_cancel₀]
        exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero (α i))
      · have hne : exponent (q j) ≠ exponent α := by
          intro h
          apply hq
          exact Finsupp.equivFunOnFinite.symm.injective h
        simp [hne, hq]
    · have hlt : (product (q j) (a j)).totalDegree < n := by
        rw [product_degree]
        exact lt_of_le_of_ne (hqn j) he
      rw [homogeneousComponent_eq_zero n _ hlt]
      have hq : q j ≠ α := by
        intro h
        apply he
        simpa [h] using hα
      simp [hq]
  simp_rw [hterm]
  simp

end PhilipponMultiplicity.BinomialPolynomial

namespace PhilipponMultiplicity

/-- The normalized mixed degrees are actual natural-number cell counts. -/
theorem idealMixedDegree_integral
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (α : M.FactorIndex → ℕ) : ∃ n : ℕ, SectionThree.idealMixedDegree M I α = (n : ℚ) := by
  classical
  obtain ⟨s, hs⟩ := multigraded_hilbert_function_standard_monomials K M I hI
  obtain ⟨B, hB⟩ := MonomialCells.exists_bound M.factorCount M.ambientDimension s
  let J := MonomialCells.Active M.factorCount M.ambientDimension s B
  let q (b : J) (i : M.FactorIndex) := Nat.card (MonomialCells.Free B (b.val.val i)) - 1
  let a (b : J) (i : M.FactorIndex) := ∑ j, (b.val.val i j : ℕ)
  let F := ∑ b : J, BinomialPolynomial.product (q b) (a b)
  have hF : Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I F := by
    refine ⟨fun i => (M.ambientDimension i + 1) * B + 1, ?_⟩
    intro d hd
    have hd' (i : M.FactorIndex) : (M.ambientDimension i + 1) * B < d i :=
      Nat.lt_of_succ_le (hd i)
    have ha (b : J) (i : M.FactorIndex) : a b i ≤ d i :=
      (MonomialCells.pattern_sum_bound M.factorCount M.ambientDimension B b.val.val i).trans
        (hd' i).le
    change eval (fun i => (d i : ℚ)) (∑ b : J, BinomialPolynomial.product (q b) (a b)) = _
    rw [map_sum, hs d, MonomialCells.eventual_partition_count
      M.factorCount M.ambientDimension s B hB d hd', Nat.cast_sum]
    exact Finset.sum_congr rfl (fun b _ => BinomialPolynomial.product_eval (q b) (a b) d (ha b))
  have hpoly := Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
    K M.factorCount M.ambientDimension I hF
  unfold SectionThree.idealMixedDegree
  split_ifs with hα
  · refine ⟨(Finset.univ.filter (fun b : J => q b = α)).card, ?_⟩
    rw [hpoly]
    apply BinomialPolynomial.sum_product_top_normalized q a α
    simpa only [SectionThree.idealDimension, hpoly] using hα
  · exact ⟨0, rfl⟩

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzComponentCounting

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MWComponentCounting

-- The following three elementary one-variable identities are reused from
-- PhilipponCorollaryCounting, without importing its conditional assembly.
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

theorem eval_top_fin_one (P : MvPolynomial (Fin 1) ℚ) (d : Fin 1 → ℚ) :
    eval d (homogeneousComponent P.totalDegree P) =
      coeff (Finsupp.single 0 P.totalDegree) P * d 0 ^ P.totalDegree := by
  conv_lhs => rw [top_fin_one P]
  rw [eval_monomial, Finsupp.prod_single_index]
  simp

/-- The ordinary degree of a relevant homogeneous projective prime is a
positive integer, hence at least one. -/
theorem prime_degree_one_le {K : Type*} [Field K] (N : ℕ)
    (p : Ideal (projectiveSpace K N).CoordinateRing) (hp : p.IsPrime)
    (hhom : IsMultihomogeneousIdeal (projectiveSpace K N) p)
    (hrel : Hilbert.IsRelevant K 1 (fun _ => N) p) :
    1 ≤ SectionThree.idealDegreeValue (projectiveSpace K N) p (fun _ => 1) := by
  classical
  let M := projectiveSpace K N
  let F := Hilbert.hilbertPolynomial K 1 (fun _ => N) p
  let e : Fin 1 →₀ ℕ := Finsupp.single 0 F.totalDegree
  have hF : F ≠ 0 := Hilbert.relevant_prime_hilbertPolynomial_ne_zero M p hp hhom hrel
  have hce : coeff e F ≠ 0 := by
    intro hz
    have ht : homogeneousComponent F.totalDegree F = 0 := by
      rw [top_fin_one, hz, monomial_zero]
    obtain ⟨b, hb, hd⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF) Finsupp.degree
    have hd' : b.degree = F.totalDegree := hd.symm
    have hc := congrArg (coeff b) ht
    rw [coeff_homogeneousComponent, if_pos hd', coeff_zero] at hc
    exact (mem_support_iff.mp hb) hc
  have het : e.degree = F.totalDegree := by simp [e, degree_fin_one]
  have htop := multigraded_hilbert_polynomial_top_coefficients K M p hhom
  have hdegree : SectionThree.idealDegreeValue M p (fun _ => 1) =
      (F.totalDegree.factorial : ℚ) * coeff e F := by
    change eval (fun _ => (1:ℚ)) ((F.totalDegree.factorial : ℚ) •
      homogeneousComponent F.totalDegree F) = _
    rw [smul_eq_C_mul, map_mul, eval_C, eval_top_fin_one]
    simp [e]
  have hpos : 0 < SectionThree.idealDegreeValue M p (fun _ => 1) := by
    rw [hdegree]
    apply mul_pos (by exact_mod_cast Nat.factorial_pos F.totalDegree)
    have hc := htop.1 e
    change 0 ≤ coeff e (homogeneousComponent F.totalDegree F) at hc
    rw [coeff_homogeneousComponent, if_pos het] at hc
    exact lt_of_le_of_ne hc (Ne.symm hce)
  obtain ⟨n, hn⟩ := idealMixedDegree_integral M p hhom (fun _ => F.totalDegree)
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => F.totalDegree) = e := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp [e]
  have hn' : SectionThree.idealDegreeValue M p (fun _ => 1) = (n : ℚ) := by
    change (if (∑ _ : Fin 1, F.totalDegree) = F.totalDegree then
      coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => F.totalDegree)) F *
        (∏ _ : Fin 1, (F.totalDegree.factorial : ℚ)) else 0) = (n : ℚ) at hn
    simpa [he, hdegree, mul_comm] using hn
  rw [hn'] at hpos ⊢
  exact_mod_cast Nat.succ_le_of_lt (show 0 < n by exact_mod_cast hpos)

/-- Every isolated primary component has nonzero finite generic length. -/
theorem localLength_one_le {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    1 ≤ (Hilbert.localLength K M.factorCount M.ambientDimension I q).toNat := by
  let A := Localization.AtPrime q.asIdeal
  let J := I.map (algebraMap M.CoordinateRing A)
  have hle : J ≤ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal A]
    exact Ideal.map_mono hq.le
  have hne : J ≠ ⊤ := ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hle
  letI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact Nat.succ_le_of_lt (ENat.toNat_pos (Module.length_pos (R := A) (M := A ⧸ J)).ne'
    (Hilbert.localLength_ne_top K M.factorCount M.ambientDimension I q hq))

/-- An equidimensional homogeneous ideal with only relevant components has
at most its ordinary degree many minimal primes. -/
theorem component_card_le_degree {K : Type*} [Field K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (hrel : ∀ q ∈ I.minimalPrimes, Hilbert.IsRelevant K 1 (fun _ => N) q)
    (hdim : ∀ q ∈ I.minimalPrimes,
      SectionThree.idealDimension (projectiveSpace K N) q =
        SectionThree.idealDimension (projectiveSpace K N) I) :
    (Nat.card (Hilbert.MinimalComponent K 1 (fun _ => N) I) : ℚ) ≤
      SectionThree.idealDegreeValue (projectiveSpace K N) I (fun _ => 1) := by
  classical
  let T := Hilbert.MinimalComponent K 1 (fun _ => N) I
  letI := Fintype.ofFinite T
  rw [Hilbert.component_length_formula _ I hI]
  unfold SectionThree.topComponentLengthSum
  calc
    (Nat.card T : ℚ) = ∑ _ : T, (1 : ℚ) := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _
      rw [if_pos ⟨hrel q.val.asIdeal q.property, hdim q.val.asIdeal q.property⟩]
      apply one_le_mul_of_one_le_of_one_le
      · exact_mod_cast localLength_one_le (projectiveSpace K N) I q.val q.property
      · exact prime_degree_one_le N q.val.asIdeal q.val.isPrime
          (Hilbert.minimalPrime_homogeneous _ I _ hI q.property) (hrel _ q.property)

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsAlgClosed K]
  (G : EmbeddedGroupProduct K)

/-- A translate of a component that stays in an equidimensional zero set is
itself a whole minimal-prime component. -/
theorem translated_prime_minimal (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hGI : G.vanishingIdeal Set.univ ≤ I)
    (hdim : ∀ q ∈ I.minimalPrimes,
      SectionThree.idealDimension G.ambient q = SectionThree.idealDimension G.ambient I)
    (p : Ideal G.CoordinateRing) (hp : p ∈ I.minimalPrimes)
    (hmeet : ComponentMeetsGroup G p) (g : G.Point)
    (hsub : translate g (idealZeroLocusOnGroup G p) ⊆ idealZeroLocusOnGroup G I) :
    G.vanishingIdeal (translate g (idealZeroLocusOnGroup G p)) ∈ I.minimalPrimes := by
  letI := G.zariskiTopology
  have hphom := Hilbert.minimalPrime_homogeneous G.ambient I p hI hp
  have hirr := isIrreducible_group_prime_zeroLocus p hp.isPrime hphom
    (hGI.trans hp.le) hmeet
  have hirr' := hirr.image _ (G.continuous_translation g).continuousOn
  let q := G.vanishingIdeal (translate g (idealZeroLocusOnGroup G p))
  have hq : q.IsPrime := group_vanishingIdeal_prime_of_isIrreducible _ hirr'
  have hqhom : IsMultihomogeneousIdeal G.ambient q := vanishingIdeal_multihomogeneous K _ _
  have hIq : I ≤ q := homogeneousIdeal_le_group_vanishingIdeal I hI _ hsub
  have hqrel : Hilbert.IsRelevant K G.factorCount G.ambient.ambientDimension q := by
    obtain ⟨x, hx⟩ := hirr'.nonempty
    apply G.ambient.relevant_of_zeroLocus_nonempty q
    exact ⟨G.embedding x, fun P hP =>
      G.ambient.eval_eq_zero_of_mem_vanishingIdeal hP ⟨x, hx, rfl⟩⟩
  apply Hilbert.top_dimensional_prime_is_minimal G.ambient I q hI hq hqhom hIq hqrel
  calc
    SectionThree.idealDimension G.ambient q =
        varietyDimension G (idealZeroLocusOnGroup G p) := varietyDimension_translate G g _
    _ = SectionThree.idealDimension G.ambient p := by
      change SectionThree.idealDimension G.ambient (G.vanishingIdeal _) = _
      rw [vanishingIdeal_group_prime G p hp.isPrime hphom (hGI.trans hp.le) hmeet]
    _ = SectionThree.idealDimension G.ambient I := hdim p hp

/-- The degree-counting step following (1.3) on MW p.414: distinct sampled
translates inject into the actual prime components of the retained ideal. -/
theorem orbit_card_le_degree (E : EmbeddedCommutativeGroup K)
    (I : Ideal (singleGroupProduct E).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (singleGroupProduct E).ambient I)
    (hGI : (singleGroupProduct E).vanishingIdeal Set.univ ≤ I)
    (hmeet : ∀ q ∈ I.minimalPrimes, ComponentMeetsGroup (singleGroupProduct E) q)
    (hdim : ∀ q ∈ I.minimalPrimes,
      SectionThree.idealDimension (singleGroupProduct E).ambient q =
        SectionThree.idealDimension (singleGroupProduct E).ambient I)
    (p : Ideal (singleGroupProduct E).CoordinateRing) (hp : p ∈ I.minimalPrimes)
    (S : Set (singleGroupProduct E).Point)
    (hsub : ∀ g ∈ S, translate g (idealZeroLocusOnGroup (singleGroupProduct E) p) ⊆
      idealZeroLocusOnGroup (singleGroupProduct E) I) :
    ((((fun g => translate g (idealZeroLocusOnGroup (singleGroupProduct E) p)) '' S).ncard : ℚ) ≤
      SectionThree.idealDegreeValue (singleGroupProduct E).ambient I (fun _ => 1)) := by
  classical
  let G := singleGroupProduct E
  letI := G.zariskiTopology
  let T := Hilbert.MinimalComponent K 1 (fun _ => E.ambientDimension) I
  let f : T → Set G.Point := fun q => idealZeroLocusOnGroup G q.val.asIdeal
  have hincl : (fun g => translate g (idealZeroLocusOnGroup G p)) '' S ⊆ Set.range f := by
    rintro _ ⟨g, hg, rfl⟩
    have hq := translated_prime_minimal G I hI hGI hdim p hp (hmeet p hp) g (hsub g hg)
    refine ⟨⟨⟨_, hq.isPrime⟩, hq⟩, ?_⟩
    apply group_zeroLocus_vanishingIdeal_of_isClosed
    exact (G.translationHomeomorph g).isClosedMap _
      (isClosed_idealZeroLocusOnGroup G p (Hilbert.minimalPrime_homogeneous _ I p hI hp))
  have hcount : ((fun g => translate g (idealZeroLocusOnGroup G p)) '' S).ncard ≤ Nat.card T := by
    calc
      _ ≤ (Set.range f).ncard := Set.ncard_le_ncard hincl (Set.finite_range f)
      _ ≤ Nat.card T := by
        simpa only [Set.image_univ, Set.ncard_univ] using
          (Set.ncard_image_le (f := f) (s := Set.univ))
  have hrel (q) (hq : q ∈ I.minimalPrimes) :
      Hilbert.IsRelevant K 1 (fun _ => E.ambientDimension) q := by
    obtain ⟨x, hx⟩ := hmeet q hq
    exact G.ambient.relevant_of_zeroLocus_nonempty q ⟨G.embedding x, hx⟩
  exact (show (_ : ℚ) ≤ (Nat.card T : ℚ) by exact_mod_cast hcount).trans
    (component_card_le_degree E.ambientDimension I hI hrel hdim)

end PhilipponMultiplicity.MWComponentCounting

end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzComponentCountingAssembly
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u

theorem unpointed_prime_orbit_of_stationary_retained_ideal
    (horbit : ∀
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
      ∃ F : Finset G.CoordinateRing,
        (∀ Q ∈ F, ∃ d : G.FactorIndex → ℕ,
          G.ambient.IsHomogeneous Q d ∧
            ∀ i, (d i : ℝ) ≤ (a : ℝ) ^ (G.dimension - 1) * (D : ℝ)) ∧
        ∃ J : Ideal G.CoordinateRing, IsMultihomogeneousIdeal G.ambient J ∧
          (G.vanishingIdeal Set.univ ⊔ Ideal.span (F : Set G.CoordinateRing) ≤ J) ∧
          (∀ q ∈ J.minimalPrimes,
            SectionThree.idealDimension G.ambient q = SectionThree.idealDimension G.ambient J) ∧
          SectionThree.idealDimension G.ambient J = G.dimension - r ∧
          ((SectionThree.idealDegreeValue G.ambient J (fun _ => 1) : ℚ) : ℝ) ≤
            ((D : ℝ) / c) ^ r ∧
          (∀ q ∈ J.minimalPrimes, ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) ∧
          (∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (F : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) → q ∈ J.minimalPrimes) ∧
          ∃ p ∈ J.minimalPrimes, ∀ g ∈ samplingGrid γ R,
            translate g (idealZeroLocusOnGroup G p) ⊆ idealZeroLocusOnGroup G J)
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
    ∀ Γ : Submodule ℤ G.Point, Γ.FG → (∀ i, γ i ∈ Γ) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ p : Ideal G.CoordinateRing, p.IsPrime ∧ IsMultihomogeneousIdeal G.ambient p ∧
        G.vanishingIdeal Set.univ ≤ p ∧
        (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G p) ∧
        ((((fun g => translate g (idealZeroLocusOnGroup G p)) '' samplingGrid γ R).ncard : ℝ) ≤
          ((D : ℝ) / c) ^ r) ∧
        ∃ Q : Finset G.CoordinateRing,
          (∀ F ∈ Q, ∃ d : G.FactorIndex → ℕ,
            G.ambient.IsHomogeneous F d ∧
              ∀ i, (d i : ℝ) ≤ (a : ℝ) ^ (G.dimension - 1) * (D : ℝ)) ∧
          (∀ F ∈ Q, F ∈ p) ∧
          ∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (Q : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) →
            varietyDimension G (idealZeroLocusOnGroup G q) ≤ G.dimension - r := by
  letI : CompleteSpace K := hK.completeSpace
  letI : IsAlgClosed K := hK.isAlgClosed
  dsimp only
  intro hvanish hnonzero Γ hΓ hγ
  obtain ⟨r,hr,hrn,F,hF,J,hJ,hIJ,hequidim,hdim,hdegree,hmeet,hretain,p,hp,hstationary⟩ :=
    horbit K hK E hn hconnected a b ha hb htranslation hclosure m D hm hD
      γ R hR P hP hvanish hnonzero Γ hΓ hγ
  let G := singleGroupProduct E
  have hGJ : G.vanishingIdeal Set.univ ≤ J := le_sup_left.trans hIJ
  have hphom := Hilbert.minimalPrime_homogeneous G.ambient J p hJ hp
  have hmeetG : ∀ q ∈ J.minimalPrimes, ComponentMeetsGroup G q := by
    intro q hq
    obtain ⟨x,hx,hxq⟩ := hmeet q hq
    exact ⟨x,hxq⟩
  have hcount := MWComponentCounting.orbit_card_le_degree E J hJ hGJ hmeetG
    hequidim p hp (samplingGrid γ R) hstationary
  refine ⟨r,hr,hrn,p,hp.isPrime,hphom,hGJ.trans hp.le,hmeet p hp,?_,F,hF,?_,?_⟩
  · have hreal :
        ((((fun g => translate g (idealZeroLocusOnGroup G p)) '' samplingGrid γ R).ncard : ℝ) ≤
          ((SectionThree.idealDegreeValue G.ambient J (fun _ => 1) : ℚ) : ℝ)) := by
        exact_mod_cast hcount
    exact hreal.trans hdegree
  · intro Q hQ
    exact hp.le (hIJ (Ideal.mem_sup_right (Ideal.subset_span hQ)))
  · intro q hq hqmeet
    have hqJ := hretain q hq hqmeet
    obtain ⟨x,hx,hxq⟩ := hqmeet
    have heq := vanishingIdeal_group_prime G q hqJ.isPrime
      (Hilbert.minimalPrime_homogeneous G.ambient J q hJ hqJ)
      (hGJ.trans hqJ.le) ⟨x,hxq⟩
    change SectionThree.idealDimension G.ambient (G.vanishingIdeal _) ≤ G.dimension - r
    rw [heq,hequidim q hqJ,hdim]

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
    ∀ Γ : Submodule ℤ G.Point, Γ.FG → (∀ i, γ i ∈ Γ) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ p : Ideal G.CoordinateRing, p.IsPrime ∧ IsMultihomogeneousIdeal G.ambient p ∧
        G.vanishingIdeal Set.univ ≤ p ∧
        (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G p) ∧
        ((((fun g => _root_.PhilipponMultiplicity.translate g (idealZeroLocusOnGroup G p)) '' samplingGrid γ R).ncard : ℝ) ≤
          ((D : ℝ) / c) ^ r) ∧
        ∃ Q : Finset G.CoordinateRing,
          (∀ F ∈ Q, ∃ d : G.FactorIndex → ℕ,
            G.ambient.IsHomogeneous F d ∧
              ∀ i, (d i : ℝ) ≤ (a : ℝ) ^ (G.dimension - 1) * (D : ℝ)) ∧
          (∀ F ∈ Q, F ∈ p) ∧
          ∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (Q : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) →
            varietyDimension G (idealZeroLocusOnGroup G q) ≤ G.dimension - r := by
  exact unpointed_prime_orbit_of_stationary_retained_ideal
    (@masser_wustholz_stationary_retained_ideal) K hK E hn hconnected a b ha hb
    htranslation hclosure m D hm hD γ R hR P hP
