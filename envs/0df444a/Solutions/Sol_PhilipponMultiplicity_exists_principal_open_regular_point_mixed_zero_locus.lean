-- Prove2me | solution 1 for PhilipponMultiplicity.exists_principal_open_regular_point_mixed_zero_locus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T09:13:41.183444+00:00
-- url     : https://prove2.me/submissions/4a96d6dc-07c3-4aeb-9aae-4bd312afd138
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_principal_open_reduced_point_mixed_zero_locus
import Definitions.Def_P2M_Util
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_WeierstrassEllipticZeta_PhilipponModel
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.EmbeddedGroupProduct

/-- Density in the actual induced multiprojective topology is equivalent to
having no additional homogeneous relations on the proposed dense subset. -/
theorem dense_iff_homogeneous_vanishing {K : Type*} [Field K]
    (G : EmbeddedGroupProduct K) (S : Set G.Point) :
    @Dense _ G.zariskiTopology S ↔
      ∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ), G.ambient.IsHomogeneous P D →
        (∀ x ∈ S, G.ambient.eval P (G.embedding x) = 0) →
        ∀ x : G.Point, G.ambient.eval P (G.embedding x) = 0 := by
  letI := G.ambient.zariskiTopology
  letI := G.zariskiTopology
  have hcl : @closure _ G.zariskiTopology S =
      G.embedding ⁻¹' G.ambient.zeroLocus (G.vanishingIdeal S) := by
    ext x
    rw [zariskiTopology, closure_induced]
    rw [← G.ambient.zeroLocus_vanishingIdeal_eq_closure]
    rfl
  rw [dense_iff_closure_eq, hcl, Set.eq_univ_iff_forall]
  constructor
  · intro h P D hP hzero x
    apply h x P
    apply Ideal.subset_span
    refine ⟨⟨D, hP⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hzero y hy
  · intro h x P hP
    have hle : G.vanishingIdeal S ≤ RingHom.ker
        (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
      apply Ideal.span_le.mpr
      rintro Q ⟨⟨D, hQ⟩, hzero⟩
      exact h Q D hQ (fun y hy => hzero _ ⟨y, hy, rfl⟩) x
    exact hle hP

end PhilipponMultiplicity.EmbeddedGroupProduct

end

end


section

set_option autoImplicit false
noncomputable section
namespace PhilipponMultiplicity.EmbeddedGroupProduct

/-- A proper closed locus has a homogeneous equation that fails somewhere on
every Zariski-dense subset. -/
theorem exists_homogeneous_separator {K : Type*} [Field K]
    (G : EmbeddedGroupProduct K) (S C : Set G.Point)
    (hS : @Dense _ G.zariskiTopology S) (hC : @IsClosed _ G.zariskiTopology C)
    (hproper : C ≠ Set.univ) :
    ∃ P : G.CoordinateRing, ∃ D : G.FactorIndex → ℕ,
      G.ambient.IsHomogeneous P D ∧
      (∀ x ∈ C, G.ambient.eval P (G.embedding x) = 0) ∧
      ∃ x ∈ S, G.ambient.eval P (G.embedding x) ≠ 0 := by
  classical
  letI := G.zariskiTopology
  by_contra! hn
  have hCdense : Dense C := (G.dense_iff_homogeneous_vanishing C).mpr (by
    intro P D hP hzero x
    exact (G.dense_iff_homogeneous_vanishing S).mp hS P D hP (hn P D hP hzero) x)
  exact hproper (hC.closure_eq.symm.trans hCdense.closure_eq)

end PhilipponMultiplicity.EmbeddedGroupProduct
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity

namespace PhilipponMultiplicity.MultiProjectiveSpace
theorem IsHomogeneous.degree_unique {K : Type*} [Field K]
    {M : MultiProjectiveSpace K} {P : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hD : M.IsHomogeneous P D) (hE : M.IsHomogeneous P E) (hne : P ≠ 0) : D = E := by
  obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr (by simpa using hne : P.support ≠ ∅)
  funext i
  exact (hD d hd i).symm.trans (hE d hd i)
end PhilipponMultiplicity.MultiProjectiveSpace

namespace WeierstrassEllipticZeta.PhilipponApplication.Model
variable {S : Fin 5 → ℂ → ℂ} (M : Model S)

/-- The stipulated bihomogeneity forces the variable equivalence to preserve
the additive block and the extension block individually. -/
theorem variableEquiv_block (j : Fin 7) :
    (M.variableEquiv j).1 = if j.val < 2 then (0 : Fin 2) else 1 := by
  classical
  have hQ : Bihomogeneous (X j) (if j.val < 2 then 1 else 0)
      (if j.val < 2 then 0 else 1) := by
    intro d hd
    simp only [support_X, Finset.mem_singleton] at hd
    subst d
    fin_cases j <;> simp
  have hh := M.homogeneous (X j) _ _ hQ
  simp only [rename_X] at hh
  have hd := hh.degree_unique (M.group.ambient.isHomogeneous_X (M.variableEquiv j))
    (X_ne_zero (M.variableEquiv j))
  have h0 := congrFun hd (0 : Fin 2)
  by_cases hj : j.val < 2
  · simpa [hj, eq_comm] using h0.symm
  · have hne : (M.variableEquiv j).1 ≠ (0 : Fin 2) := by
      intro h
      simp [hj, h] at h0
    simp only [if_neg hj]
    have hlt := (M.variableEquiv j).1.isLt
    change (M.variableEquiv j).1.val < 2 at hlt
    apply Fin.ext
    change (M.variableEquiv j).1.val = 1
    have hv : (M.variableEquiv j).1.val ≠ 0 := fun h => hne (Fin.ext h)
    omega

theorem exponent_block_sums (d : Fin 7 →₀ ℕ) (i : Fin 2) :
    (∑ j : Fin ((M.factor i).ambientDimension + 1),
      (d.mapDomain M.variableEquiv) ⟨i, j⟩) =
      if i = 0 then d 0 + d 1 else d 2 + d 3 + d 4 + d 5 + d 6 := by
  classical
  have hall : (∑ v : M.group.ambient.Variable,
      if v.1 = i then (d.mapDomain M.variableEquiv) v else 0) =
      ∑ j : Fin 7, if (M.variableEquiv j).1 = i then d j else 0 := by
    rw [← M.variableEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finsupp.mapDomain_apply M.variableEquiv.injective]
  rw [Fintype.sum_sigma] at hall
  change (∑ k : Fin 2, ∑ j : Fin ((M.factor k).ambientDimension + 1),
    if k = i then (d.mapDomain M.variableEquiv) ⟨k, j⟩ else 0) = _ at hall
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hall
  rw [hall]
  simp only [M.variableEquiv_block]
  fin_cases i <;> simp [Fin.sum_univ_seven]

theorem homogeneous_iff (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) :
    M.group.ambient.IsHomogeneous (rename M.variableEquiv Q) ![m, n] ↔
      Bihomogeneous Q m n := by
  classical
  constructor
  · intro h d hd
    have hd' : d.mapDomain M.variableEquiv ∈ (rename M.variableEquiv Q).support := by
      rw [support_rename_of_injective M.variableEquiv.injective]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have h0 := h _ hd' (0 : Fin 2)
    have h1 := h _ hd' (1 : Fin 2)
    change (∑ j : Fin ((M.factor 0).ambientDimension + 1),
      (d.mapDomain M.variableEquiv) ⟨(0 : Fin 2), j⟩) = m at h0
    change (∑ j : Fin ((M.factor 1).ambientDimension + 1),
      (d.mapDomain M.variableEquiv) ⟨(1 : Fin 2), j⟩) = n at h1
    rw [M.exponent_block_sums] at h0 h1
    exact ⟨by simpa using h0, by simpa using h1⟩
  · exact M.homogeneous Q m n

/-- Proper closed subgroups supply the actual bihomogeneous polynomial
constraint needed by the application argument. -/
theorem exists_bihomogeneous_subgroup_separator (H : AlgebraicSubgroup M.group)
    (hproper : H.carrier ≠ Set.univ) :
    ∃ Q : MvPolynomial (Fin 7) ℂ, ∃ m n : ℕ,
      Bihomogeneous Q m n ∧
      (∀ g ∈ H.carrier, g ∈ zeroLocusOnGroup M.group (M.polynomial Q)) ∧
      ∃ v : ℂ, eval (rawCoordinates S v) Q ≠ 0 := by
  obtain ⟨P, D, hP, hzero, g, ⟨v, rfl⟩, hne⟩ :=
    M.group.exists_homogeneous_separator (Set.range M.curve) H.carrier
      M.curve_dense H.isClosed hproper
  let Q := rename M.variableEquiv.symm P
  have hrename : rename M.variableEquiv Q = P := by
    simp [Q, rename_rename]
  have hD : D = ![D 0, D 1] := by
    funext i
    change Fin 2 at i
    fin_cases i <;> rfl
  have hQ : Bihomogeneous Q (D 0) (D 1) := (M.homogeneous_iff Q _ _).mp (by
    rw [hrename]
    simpa only [← hD] using hP)
  refine ⟨Q, D 0, D 1, hQ, ?_, v, ?_⟩
  · intro g hg
    change M.group.ambient.eval (rename M.variableEquiv Q) (M.group.embedding g) = 0
    rw [hrename]
    exact hzero g hg
  · intro hz
    have hh := (M.zero_locus Q _ _ hQ v).mpr hz
    change M.group.ambient.eval (rename M.variableEquiv Q) (M.group.embedding (M.curve v)) = 0 at hh
    rw [hrename] at hh
    exact hne hh

/-- The first factor of the modeled curve detects its complex parameter. -/
theorem curve_first_factor_eq_zero_iff (v : ℂ) : M.curve v 0 = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hQ : Bihomogeneous (X (1 : Fin 7)) 1 0 := by
      intro d hd
      simp only [support_X, Finset.mem_singleton] at hd
      subst d
      simp
    have hb : (M.variableEquiv 1).1 = (0 : Fin 2) := by
      simpa using M.variableEquiv_block 1
    have hi : M.curve v (M.variableEquiv 1).1 = (0 : M.group.Point) (M.variableEquiv 1).1 := by
      have hall (i : Fin 2) (h : i = 0) : M.curve v i = (0 : M.group.Point) i := by
        subst i
        exact hv
      exact hall _ hb
    have heval : M.group.ambient.eval (rename M.variableEquiv (X (1 : Fin 7)))
        (M.group.embedding (M.curve v)) =
        M.group.ambient.eval (rename M.variableEquiv (X (1 : Fin 7)))
          (M.group.embedding 0) := by
      simp only [MultiProjectiveSpace.eval, rename_X, eval_X,
        MultiProjectiveSpace.coordinate, EmbeddedGroupProduct.embedding]
      exact congrArg (fun p => p.val.rep (M.variableEquiv 1).2) hi
    have hz := (M.zero_locus (X (1 : Fin 7)) 1 0 hQ 0).mpr (by simp [rawCoordinates])
    change M.group.ambient.eval (rename M.variableEquiv (X (1 : Fin 7)))
      (M.group.embedding (M.curve 0)) = 0 at hz
    have hz' : M.group.ambient.eval (rename M.variableEquiv (X (1 : Fin 7)))
        (M.group.embedding 0) = 0 := by simpa only [map_zero] using hz
    have hv' := (M.zero_locus (X (1 : Fin 7)) 1 0 hQ v).mp (heval.trans hz')
    simpa [rawCoordinates] using hv'
  · rintro rfl
    simp

/-- The paper's subgroups with zero additive projection meet the modeled curve
only at its identity. No classification or degree assertion is assumed here. -/
theorem pullbackSubmodule_eq_bot_of_first_factor_zero (H : AlgebraicSubgroup M.group)
    (hH : ∀ g ∈ H.carrier, g 0 = 0) : M.pullbackSubmodule H = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  exact (M.curve_first_factor_eq_zero_iff v).mp (hH (M.curve v) hv)

end WeierstrassEllipticZeta.PhilipponApplication.Model
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MvPolynomial
namespace PhilipponMultiplicity.MultiProjectiveSpace

/-- Multihomogeneous equations distinguish actual projective points. -/
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

/-- A subgroup with exactly the homogeneous equations of the identity is the
identity subgroup. This retains the arbitrary compatible Model. -/
theorem carrier_eq_singleton_of_identity_equations {S : Fin 5 → ℂ → ℂ}
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (h : M.HasParametricEquations H (fun _ : Unit => rawCoordinates S 0)) :
    H.carrier = {0} := by
  apply Set.Subset.antisymm
  · intro g hg
    have he : M.group.embedding g = M.group.embedding 0 := by
      apply M.group.ambient.point_eq_of_homogeneous_implication
      intro P degrees hP hzero
      change Fin 2 → ℕ at degrees
      let Q := rename M.variableEquiv.symm P
      have hrename : rename M.variableEquiv Q = P := by simp [Q, rename_rename]
      have hd : degrees = ![degrees 0, degrees 1] := by
        funext i
        change Fin 2 at i
        fin_cases i <;> rfl
      have hQ : Bihomogeneous Q (degrees 0) (degrees 1) := (M.homogeneous_iff Q _ _).mp (by
        rw [hrename, ← hd]
        exact hP)
      have hraw : MvPolynomial.eval (rawCoordinates S 0) Q = 0 := by
        apply (M.zero_locus Q _ _ hQ 0).mp
        change M.group.ambient.eval (rename M.variableEquiv Q)
          (M.group.embedding (M.curve 0)) = 0
        simpa only [hrename, map_zero] using hzero
      have hall := (h Q _ _ hQ).mpr (fun _ => hraw)
      simpa only [polynomial, hrename] using hall g hg
    have hg0 : g = 0 := by
      funext i
      exact Subtype.ext (congrFun he i)
    exact Set.mem_singleton_iff.mpr hg0
  · intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact H.toAddSubgroup.zero_mem

end WeierstrassEllipticZeta.PhilipponApplication.Model
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem exists_homogeneous_separator (x y : M.Point) (hne : x ≠ y) :
    ∃ P : M.CoordinateRing, ∃ D : M.FactorIndex → ℕ,
      M.IsHomogeneous P D ∧ M.eval P y = 0 ∧ M.eval P x ≠ 0 := by
  by_contra! h
  exact hne (M.point_eq_of_homogeneous_implication x y h)

/-- A homogeneous section separates one point from any finite collection of
other points. The multidegree is allowed to depend on that collection. -/
theorem exists_homogeneous_finite_separator (x : M.Point) (S : Finset M.Point)
    (hx : x ∉ S) :
    ∃ P : M.CoordinateRing, ∃ D : M.FactorIndex → ℕ,
      M.IsHomogeneous P D ∧ M.eval P x ≠ 0 ∧ ∀ y ∈ S, M.eval P y = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1,0,M.isHomogeneous_one,by simp [eval],by simp⟩
  | @insert y S hy ih =>
    have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
    have hxy : x ≠ y := fun h => hx (h ▸ Finset.mem_insert_self _ _)
    obtain ⟨P,D,hP,hPx,hPS⟩ := ih hxS
    obtain ⟨Q,E,hQ,hQy,hQx⟩ := M.exists_homogeneous_separator x y hxy
    refine ⟨P*Q,D+E,hP.mul M hQ,?_,?_⟩
    · simpa only [eval,map_mul,mul_ne_zero_iff] using And.intro hPx hQx
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa only [eval,map_mul] using mul_eq_zero_of_right (M.eval P z) hQy
      · simpa only [eval,map_mul] using mul_eq_zero_of_left (hPS z hz) (M.eval Q z)

/-- In all sufficiently large block degrees the evaluation map onto a
finite set of multiprojective points is surjective. -/
theorem finite_sectionSpace_eventually_top (S : Set M.Point) (hS : S.Finite) :
    ∃ B : M.FactorIndex → ℕ, ∀ D : M.FactorIndex → ℕ, (∀ i, B i ≤ D i) →
      M.sectionSpace (fun x : S => x.val) D = ⊤ := by
  classical
  let : Fintype S := hS.fintype
  have hsep (a : S) :
      ∃ P : M.CoordinateRing, ∃ E : M.FactorIndex → ℕ,
        M.IsHomogeneous P E ∧ M.eval P a.val ≠ 0 ∧
          ∀ b : S, b ≠ a → M.eval P b.val = 0 := by
    obtain ⟨P,E,hP,hPa,hPS⟩ := M.exists_homogeneous_finite_separator a.val
      (hS.toFinset.erase a.val) (Finset.notMem_erase _ _)
    refine ⟨P,E,hP,hPa,?_⟩
    intro b hba
    exact hPS b.val (Finset.mem_erase.mpr
      ⟨fun he => hba (Subtype.ext he),hS.mem_toFinset.mpr b.property⟩)
  choose P E hP hPa hPS using hsep
  let B : M.FactorIndex → ℕ := fun i => ∑ a : S, E a i
  refine ⟨B,?_⟩
  intro D hD
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun K S)).mpr
  intro a
  have hEa (i : M.FactorIndex) : E a i ≤ D i :=
    (Finset.single_le_sum (fun b _ => Nat.zero_le (E b i)) (Finset.mem_univ a)).trans (hD i)
  obtain ⟨Q,hQ,hQa⟩ := M.exists_form_nonzero_at a.val (fun i => D i - E a i)
  let F : M.CoordinateRing := P a * Q
  have hF : M.IsHomogeneous F D := by
    have h := (hP a).mul M hQ
    have heq : E a + (fun i => D i - E a i) = D := by
      funext i
      exact Nat.add_sub_of_le (hEa i)
    exact heq ▸ h
  have hFa : M.eval F a.val ≠ 0 := by
    simpa only [F,eval,map_mul,mul_ne_zero_iff] using And.intro (hPa a) hQa
  let R : M.CoordinateRing := C (M.eval F a.val)⁻¹ * F
  have hR : M.IsHomogeneous R D := hF.C_mul M _
  rw [Pi.basisFun_apply]
  change (Pi.single a (1 : K)) ∈
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
      (M.evaluationMap (fun x : S => x.val)).toLinearMap
  refine ⟨R,(M.degreePiece_iff _ _).mpr hR,?_⟩
  ext b
  change M.eval R b.val = Pi.single (M := fun _ : S => K) a (1 : K) b
  by_cases hba : b = a
  · subst b
    change (MvPolynomial.eval (M.coordinate a.val)) F ≠ 0 at hFa
    simp [R,eval, hFa]
  · have hzero : M.eval F b.val = 0 := by
      change M.eval (P a * Q) b.val = 0
      simpa only [eval,map_mul] using mul_eq_zero_of_left (hPS a b hba) (M.eval Q b.val)
    change (MvPolynomial.eval (M.coordinate b.val)) F = 0 at hzero
    simp [R,eval, hzero, hba]

theorem hilbertFunction_finite_eventually (S : Set M.Point) (hS : S.Finite) :
    ∃ B : M.FactorIndex → ℕ, ∀ D : M.FactorIndex → ℕ, (∀ i, B i ≤ D i) →
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D =
        S.ncard := by
  classical
  let : Fintype S := hS.fintype
  obtain ⟨B,hB⟩ := M.finite_sectionSpace_eventually_top S hS
  refine ⟨B,?_⟩
  intro D hD
  have h := M.hilbertFunction_eq_sectionSpace (fun x : S => x.val) D
  rw [Subtype.range_val,hB D hD,finrank_top] at h
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,mul_one,Set.fintypeCard_eq_ncard] using h

/-- The full eventual Hilbert polynomial of a finite set is its cardinality,
including the empty set. This is proved by homogeneous interpolation. -/
theorem hilbertPolynomial_finite (S : Set M.Point) (hS : S.Finite) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S) =
      C (S.ncard : ℚ) := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  obtain ⟨B,hB⟩ := M.hilbertFunction_finite_eventually S hS
  refine ⟨B,?_⟩
  intro D hD
  rw [hB D hD,eval_C]

theorem locusDegreeValue_finite (S : Set M.Point) (hS : S.Finite)
    (D : M.FactorIndex → ℕ) :
    SectionThree.locusDegreeValue M S D = (S.ncard : ℚ) := by
  unfold SectionThree.locusDegreeValue SectionThree.idealDegreeValue
    Hilbert.degreeValue Hilbert.degreeForm
  rw [M.hilbertPolynomial_finite S hS]
  dsimp only
  rw [MvPolynomial.totalDegree_C]
  simp
  change coeff 0 (C (S.ncard : ℚ)) = (S.ncard : ℚ)
  rw [MvPolynomial.coeff_C, if_pos rfl]

end PhilipponMultiplicity.MultiProjectiveSpace
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
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.FiniteReducedCone
variable {K : Type*} [Field K] [IsAlgClosed K] (M : MultiProjectiveSpace K)

/-- The projective Nullstellensatz at an actual nonzero-block representative. -/
theorem local_vanishing_le_radical
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (v : M.Variable → K)
    (hv : ∀ i : M.FactorIndex, (fun j => v ⟨i,j⟩) ≠ 0) :
    (M.vanishingIdeal (M.zeroLocus I)).map
        (algebraMap M.CoordinateRing (Localization.AtPrime (vanishingIdeal K {v}))) ≤
      (I.map (algebraMap M.CoordinateRing
        (Localization.AtPrime (vanishingIdeal K {v})))).radical := by
  classical
  choose j hj using fun i => Function.ne_iff.mp (hv i)
  let H : M.CoordinateRing := ∏ i, X ⟨i,j i⟩
  let R := Localization.AtPrime (vanishingIdeal K {v})
  let f : M.CoordinateRing →+* R := algebraMap _ _
  have hH : eval v H ≠ 0 := by
    simpa only [H, map_prod, eval_X, Pi.zero_apply] using Finset.prod_ne_zero_iff.mpr
      (fun i _ => hj i)
  have hunit : IsUnit (f H) := IsLocalization.map_units R
    (⟨H, by simpa [vanishingIdeal] using hH⟩ : (vanishingIdeal K {v}).primeCompl)
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  have hPH : P * H ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
    intro w hw
    change eval w (P * H) = 0
    rw [map_mul]
    by_cases hb : ∀ i : M.FactorIndex, (fun k => w ⟨i,k⟩) ≠ 0
    · apply mul_eq_zero.mpr
      left
      let x : M.Point := fun i => Projectivization.mk K (fun k => w ⟨i,k⟩) (hb i)
      have hrep : ∀ i, ∃ h : (fun k => w ⟨i,k⟩) ≠ 0,
          Projectivization.mk K (fun k => w ⟨i,k⟩) h = x i := fun i => ⟨hb i,rfl⟩
      have hx : x ∈ M.zeroLocus I := by
        apply (M.mem_zeroLocus_iff_homogeneous I hI x).mpr
        intro Q hQ E hE
        exact (M.eval_eq_zero_iff_of_lift x w hrep Q E hE).mp (hw Q hQ)
      exact (M.eval_eq_zero_iff_of_lift x w hrep P D hD).mpr (hP x hx)
    · apply mul_eq_zero.mpr
      right
      push Not at hb
      obtain ⟨i,hi⟩ := hb
      change eval w (∏ k, X ⟨k,j k⟩) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simpa only [eval_X, Pi.zero_apply] using congrFun hi (j i)
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hPH
  have hmap : f (P * H) ∈ (I.map f).radical :=
    (I.map_radical_le f) (Ideal.mem_map_of_mem f hPH)
  rw [map_mul] at hmap
  exact ((I.map f).radical.mul_unit_mem_iff_mem hunit).mp hmap

/-- Near one member of a finite projective set, its vanishing ideal agrees
with that of the single point, while all cone scaling directions remain. -/
theorem local_finite_eq_singleton
    (S : Set M.Point) (hS : S.Finite) (x : M.Point) (hx : x ∈ S)
    (v : M.Variable → K)
    (hrep : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) :
    (M.vanishingIdeal S).map
        (algebraMap M.CoordinateRing (Localization.AtPrime (vanishingIdeal K {v}))) =
      (M.vanishingIdeal {x}).map
        (algebraMap M.CoordinateRing (Localization.AtPrime (vanishingIdeal K {v}))) := by
  classical
  let R := Localization.AtPrime (vanishingIdeal K {v})
  let f : M.CoordinateRing →+* R := algebraMap _ _
  obtain ⟨H,E,hE,hHx,hHS⟩ := M.exists_homogeneous_finite_separator x
    (hS.toFinset.erase x) (Finset.notMem_erase _ _)
  have hHv : eval v H ≠ 0 := (M.eval_eq_zero_iff_of_lift x v hrep H E hE).not.mpr hHx
  have hunit : IsUnit (f H) := IsLocalization.map_units R
    (⟨H, by simpa [vanishingIdeal] using hHv⟩ : (vanishingIdeal K {v}).primeCompl)
  apply le_antisymm (Ideal.map_mono (M.vanishingIdeal_antitone (Set.singleton_subset_iff.mpr hx)))
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  have hPH : P * H ∈ M.vanishingIdeal S := by
    apply Ideal.subset_span
    refine ⟨⟨D+E,hD.mul M hE⟩,?_⟩
    intro y hy
    change eval (M.coordinate y) (P * H) = 0
    rw [map_mul]
    by_cases heq : y = x
    · exact mul_eq_zero_of_left (hP y (Set.mem_singleton_iff.mpr heq)) _
    · exact mul_eq_zero_of_right _ (hHS y (Finset.mem_erase.mpr ⟨heq,hS.mem_toFinset.mpr hy⟩))
  have hmap := Ideal.mem_map_of_mem f hPH
  rw [map_mul] at hmap
  exact ((M.vanishingIdeal S).map f).mul_unit_mem_iff_mem hunit |>.mp hmap

/-- A multihomogeneous ideal with finite projective zero set has regular
point-local quotients at each nonzero-block representative where it is radical. -/
theorem regular_of_finite_radical
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hfinite : (M.zeroLocus I).Finite) (v : M.Variable → K)
    (hv : ∀ i : M.FactorIndex, (fun j => v ⟨i,j⟩) ≠ 0)
    (hIv : ∀ P ∈ I, eval v P = 0)
    (hrad : (I.map (algebraMap M.CoordinateRing
      (Localization.AtPrime (vanishingIdeal K {v})))).IsRadical) :
    IsRegularLocalRing ((Localization.AtPrime (vanishingIdeal K {v})) ⧸
      I.map (algebraMap M.CoordinateRing
        (Localization.AtPrime (vanishingIdeal K {v})))) := by
  classical
  let x : M.Point := fun i => Projectivization.mk K (fun j => v ⟨i,j⟩) (hv i)
  have hrep : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i := fun i => ⟨hv i,rfl⟩
  have hx : x ∈ M.zeroLocus I := by
    apply (M.mem_zeroLocus_iff_homogeneous I hI x).mpr
    intro P hP D hD
    exact (M.eval_eq_zero_iff_of_lift x v hrep P D hD).mp (hIv P hP)
  let R := Localization.AtPrime (vanishingIdeal K {v})
  let f : M.CoordinateRing →+* R := algebraMap _ _
  have heq : I.map f = (M.vanishingIdeal (M.zeroLocus I)).map f := by
    apply le_antisymm (Ideal.map_mono (M.homogeneousIdeal_le_vanishingIdeal_zeroLocus I hI))
    rw [← hrad.radical]
    exact local_vanishing_le_radical M I hI v hv
  have hsingle : I.map f = (M.vanishingIdeal {x}).map f := heq.trans
    (local_finite_eq_singleton M (M.zeroLocus I) hfinite x hx v hrep)
  choose b hb using fun i => Function.ne_iff.mp (hv i)
  have hb' : ∀ i, v ⟨i,b i⟩ ≠ 0 := by simpa only [Pi.zero_apply] using hb
  rw [PointConeLinear.vanishingIdeal_singleton_eq M v b hb' x hrep] at hsingle
  letI := PointConeLinear.local_regular M v b hb'
  exact IsRegularLocalRing.of_ringEquiv
    (R := R ⧸ (PointConeLinear.ideal M v b).map f)
    (Ideal.quotientEquivAlgOfEq K hsingle.symm).toRingEquiv

end PhilipponMultiplicity.FiniteReducedCone
end

end


section

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

/-- A nonempty principal open in affine space meets the complement of any
finite union of proper linear subspaces. -/
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

/-- A finite sequence of choices can be made inside any principal open,
provided each next-row condition is dense and only depends on its prefix. -/
theorem exists_sequential_choice
    (n : ℕ) (Good : Fin n → (Fin n → σ → K) → Prop)
    (hprefix : ∀ i c d, (∀ j : Fin n, j.val ≤ i.val → c j = d j) →
      (Good i c ↔ Good i d))
    (hdense : ∀ (i : Fin n) (c : Fin n → σ → K) (F : MvPolynomial σ K),
      F ≠ 0 → ∃ a : σ → K, MvPolynomial.eval a F ≠ 0 ∧
        Good i (Function.update c i a))
    (F : MvPolynomial (Fin n × σ) K) (hF : F ≠ 0) :
    ∃ c : Fin n → σ → K, MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
      ∀ i, Good i c := by
  classical
  have haux : ∀ k : ℕ, k ≤ n →
      ∃ c : Fin n → σ → K, MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
        ∀ i : Fin n, i.val < k → Good i c := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨x,hx⟩ := exists_eval_ne_zero F hF
      exact ⟨Function.curry x, by simpa using hx, by simp⟩
    | succ k ih =>
      intro hkn
      have hk : k < n := by omega
      let i : Fin n := ⟨k,hk⟩
      obtain ⟨c,hc,hgood⟩ := ih (by omega)
      let G : MvPolynomial σ K := MvPolynomial.bind₁
        (fun w : Fin n × σ => if w.1 = i then MvPolynomial.X w.2
          else MvPolynomial.C (c w.1 w.2)) F
      have heval (a : σ → K) :
          MvPolynomial.eval a G =
            MvPolynomial.eval (Function.uncurry (Function.update c i a)) F := by
        change MvPolynomial.eval₂Hom (RingHom.id K) a
          (MvPolynomial.bind₁ _ F) = _
        rw [MvPolynomial.eval₂Hom_bind₁]
        apply congrArg (fun y : Fin n × σ → K => MvPolynomial.eval y F)
        funext w
        by_cases hw : w.1 = i
        · simp [hw, Function.uncurry]
        · simp [hw, Function.uncurry, Function.update_of_ne hw]
      have hG : G ≠ 0 := by
        intro hz
        have hh := heval (c i)
        rw [hz, map_zero, Function.update_eq_self] at hh
        exact hc hh.symm
      obtain ⟨a,ha,hnew⟩ := hdense i c G hG
      refine ⟨Function.update c i a, (heval a).symm ▸ ha, ?_⟩
      intro j hj
      by_cases hji : j = i
      · simpa [hji] using hnew
      · have hjk : j.val < k := by
          have hne : j.val ≠ k := fun h => hji (Fin.ext h)
          omega
        apply (hprefix j c (Function.update c i a) ?_).mp (hgood j hjk)
        intro t ht
        have hti : t ≠ i := by
          intro hti
          have : t.val = k := congrArg Fin.val hti
          omega
        exact (Function.update_of_ne hti _ _).symm
  obtain ⟨c,hc,hgood⟩ := haux n le_rfl
  exact ⟨c,hc,fun i => hgood i i.isLt⟩

end PhilipponMultiplicity.GenericChoice

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem rowForm_single (i : M.FactorIndex) (j : Fin (M.ambientDimension i + 1)) :
    rowForm M i (Pi.single ⟨i,j⟩ 1) = MvPolynomial.X ⟨i,j⟩ := by
  classical
  simp [rowForm, Pi.single_apply]

theorem rowForm_homogeneous (b : M.FactorIndex) (a : M.Variable → K) :
    M.IsHomogeneous (rowForm M b a) (Pi.single b 1) := by
  classical
  intro m hm i
  change m ∈ (∑ t : Fin (M.ambientDimension b + 1),
    a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)).support at hm
  have hs := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun t : Fin (M.ambientDimension b + 1) =>
      a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)) hm
  obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hs
  have hmX : m ∈ (MvPolynomial.X (⟨b,t⟩ : M.Variable) : M.CoordinateRing).support :=
    MvPolynomial.support_smul ht
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hmX
  subst m
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff, Pi.single_apply]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b,t⟩ : M.Variable) ≠ ⟨i,k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, Pi.single_apply, hi, hn]

theorem polynomial_homogeneous (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (j : Fin l.length) :
    M.IsHomogeneous (polynomial M l c j) (Pi.single l[j] 1) :=
  rowForm_homogeneous M l[j] (c j)

theorem ideal_zero (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) : ideal M I l c 0 = I := by
  simp [ideal]

theorem ideal_prefix (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c d : Fin l.length → M.Variable → K) (k : ℕ)
    (h : ∀ j : Fin l.length, j.val < k → c j = d j) :
    ideal M I l c k = ideal M I l d k := by
  classical
  unfold ideal
  congr 1
  apply iSup_congr
  intro j
  apply iSup_congr
  intro hj
  simp [polynomial, h j hj]

theorem ideal_succ (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (k : ℕ) (hk : k < l.length) :
    ideal M I l c (k+1) = ideal M I l c k ⊔
      Ideal.span {polynomial M l c ⟨k,hk⟩} := by
  unfold ideal
  apply le_antisymm
  · refine sup_le (le_sup_of_le_left le_sup_left) ?_
    refine iSup_le fun j => iSup_le fun hj => ?_
    by_cases hjk : j.val < k
    · exact le_sup_of_le_left (le_sup_of_le_right
        (le_iSup_of_le j (le_iSup_of_le hjk le_rfl)))
    · have he : j = ⟨k,hk⟩ := Fin.ext (by change j.val = k; omega)
      subst j
      exact le_sup_right
  · refine sup_le (sup_le le_sup_left ?_) ?_
    · refine iSup_le fun j => iSup_le fun hj => ?_
      exact le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le (by omega : j.val < k+1) le_rfl))
    · exact le_sup_of_le_right (le_iSup_of_le ⟨k,hk⟩ (le_iSup_of_le (by simp) le_rfl))

/-- Associated-prime avoidance in any nonempty principal open of one block's
coefficient space. No geometric hypotheses on the initial ideal are needed. -/
theorem exists_row_avoiding_associatedPrimes [Infinite K]
    (I : Ideal M.CoordinateRing) (i : M.FactorIndex)
    (F : MvPolynomial M.Variable K) (hF : F ≠ 0) :
    ∃ a : M.Variable → K, MvPolynomial.eval a F ≠ 0 ∧
      ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ I) (M.CoordinateRing ⧸ I),
        (∀ b : M.FactorIndex, ∃ j : Fin (M.ambientDimension b + 1),
          Ideal.Quotient.mk I (MvPolynomial.X ⟨b,j⟩) ∉ q) →
        Ideal.Quotient.mk I (rowForm M i a) ∉ q := by
  classical
  let Q := M.CoordinateRing ⧸ I
  let φ : (M.Variable → K) →ₗ[K] Q :=
    (Ideal.Quotient.mkₐ K I).toLinearMap.comp (rowForm M i)
  let bad (q : Ideal Q) : Submodule K (M.Variable → K) :=
    (q.restrictScalars K).comap φ
  let S := (associatedPrimes.finite Q Q).toFinset.filter
    (fun q => ∀ b : M.FactorIndex, ∃ j : Fin (M.ambientDimension b + 1),
      Ideal.Quotient.mk I (MvPolynomial.X ⟨b,j⟩) ∉ q)
  have hproper : ∀ U ∈ S.image bad, U ≠ ⊤ := by
    intro U hU
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hq).2 i
    intro he
    have hv : Pi.single (⟨i,j⟩ : M.Variable) (1 : K) ∈ bad q := by
      rw [he]
      trivial
    change Ideal.Quotient.mk I (rowForm M i (Pi.single ⟨i,j⟩ 1)) ∈ q at hv
    rw [rowForm_single] at hv
    exact hj hv
  obtain ⟨a,ha,havoid⟩ := GenericChoice.exists_eval_ne_zero_avoiding_subspaces
    (S.image bad) hproper F hF
  refine ⟨a,ha,?_⟩
  intro q hq hblocks
  exact havoid (bad q) (Finset.mem_image.mpr ⟨q,
    Finset.mem_filter.mpr ⟨by simpa using hq, hblocks⟩,rfl⟩)

/-- Filter-regular flags meet every nonempty principal open of coefficient matrices. -/
theorem exists_flag_avoiding_associatedPrimes [Infinite K]
    (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (F : MvPolynomial (Fin l.length × M.Variable) K) (hF : F ≠ 0) :
    ∃ c : Fin l.length → M.Variable → K,
      MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
      ∀ j : Fin l.length,
        ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ ideal M I l c j.val)
          (M.CoordinateRing ⧸ ideal M I l c j.val),
          (∀ b : M.FactorIndex, ∃ t : Fin (M.ambientDimension b + 1),
            Ideal.Quotient.mk (ideal M I l c j.val) (MvPolynomial.X ⟨b,t⟩) ∉ q) →
          Ideal.Quotient.mk (ideal M I l c j.val) (polynomial M l c j) ∉ q := by
  classical
  let Good (j : Fin l.length) (c : Fin l.length → M.Variable → K) : Prop :=
    ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ ideal M I l c j.val)
      (M.CoordinateRing ⧸ ideal M I l c j.val),
      (∀ b : M.FactorIndex, ∃ t : Fin (M.ambientDimension b + 1),
        Ideal.Quotient.mk (ideal M I l c j.val) (MvPolynomial.X ⟨b,t⟩) ∉ q) →
      Ideal.Quotient.mk (ideal M I l c j.val) (polynomial M l c j) ∉ q
  apply GenericChoice.exists_sequential_choice l.length Good ?_ ?_ F hF
  · intro j c d hp
    have hI := ideal_prefix M I l c d j.val (fun t ht => hp t (by omega))
    have hP : polynomial M l c j = polynomial M l d j := by
      simp [polynomial, hp j le_rfl]
    dsimp [Good]
    rw [hI,hP]
  · intro j c G hG
    obtain ⟨a,ha,havoid⟩ := exists_row_avoiding_associatedPrimes M
      (ideal M I l c j.val) l[j] G hG
    refine ⟨a,ha,?_⟩
    have hI : ideal M I l (Function.update c j a) j.val = ideal M I l c j.val := by
      apply ideal_prefix
      intro t ht
      exact Function.update_of_ne (fun he => by subst t; omega) _ _
    dsimp [Good]
    rw [hI]
    simpa [polynomial] using havoid

end PhilipponMultiplicity.MixedFlag

end

end


section

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

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem ideal_multihomogeneous (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) :
    ∀ k ≤ l.length, IsMultihomogeneousIdeal M (ideal M I l c k) := by
  intro k
  induction k with
  | zero => intro _; simpa only [ideal_zero] using hI
  | succ k ih =>
    intro hk
    rw [ideal_succ M I l c k (by omega)]
    exact Hilbert.homogeneous_sup_span M _ (ih (by omega)) _ _
      (polynomial_homogeneous M l c ⟨k,by omega⟩)

theorem zeroLocus_ideal (W : Set M.Point) (hW : @IsClosed _ M.zariskiTopology W)
    (l : List M.FactorIndex) (c : Fin l.length → M.Variable → K) :
    M.zeroLocus (ideal M (M.vanishingIdeal W) l c l.length) =
      {x : M.Point | x ∈ W ∧ ∀ j : Fin l.length, M.eval (polynomial M l c j) x = 0} := by
  let := M.zariskiTopology
  have hW' : M.zeroLocus (M.vanishingIdeal W) = W :=
    (M.zeroLocus_vanishingIdeal_eq_closure W).trans hW.closure_eq
  ext x
  constructor
  · intro hx
    have hbase : M.vanishingIdeal W ≤ ideal M (M.vanishingIdeal W) l c l.length := le_sup_left
    have hxW : x ∈ M.zeroLocus (M.vanishingIdeal W) :=
      fun P hP => hx P (hbase hP)
    refine ⟨hW' ▸ hxW, ?_⟩
    intro j
    have hj : Ideal.span {polynomial M l c j} ≤
        ideal M (M.vanishingIdeal W) l c l.length :=
      le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le j.isLt le_rfl))
    exact hx _ (hj (Ideal.subset_span (Set.mem_singleton _)))
  · rintro ⟨hxW,hx⟩
    have hle : ideal M (M.vanishingIdeal W) l c l.length ≤
        RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
      refine sup_le (fun P hP => M.eval_eq_zero_of_mem_vanishingIdeal hP hxW) ?_
      refine iSup_le fun j => iSup_le fun _ => Ideal.span_le.mpr ?_
      rintro P rfl
      exact hx j
    exact hle

end PhilipponMultiplicity.MixedFlag
end

end


section

set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem regular_mixed_sections_of_reduced
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                ((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                  (algebraMap M.CoordinateRing
                    (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical)) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                IsRegularLocalRing
                  ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) := by
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
  intro M W hW hirr α hα hdim B hB hBW hne l hl
  obtain ⟨F,hF,hgood⟩ := hgeometry M W hW hirr α hα hdim B hB hBW hne l hl
  refine ⟨F,hF,?_⟩
  intro c hc
  obtain ⟨hfinite,hdisjoint,hrad⟩ := hgood c hc
  refine ⟨hfinite,hdisjoint,?_⟩
  intro v hv hIv
  apply FiniteReducedCone.regular_of_finite_radical M
    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length)
    (MixedFlag.ideal_multihomogeneous M _ (vanishingIdeal_multihomogeneous K M W) l c
      l.length le_rfl) _ v hv hIv (hrad v hv hIv)
  rw [MixedFlag.zeroLocus_ideal M W hW l c]
  exact hfinite

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
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                IsRegularLocalRing
                  ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) := by
  exact regular_mixed_sections_of_reduced K hK
    (exists_principal_open_reduced_point_mixed_zero_locus K hK)
