-- Prove2me | solution 1 for PhilipponMultiplicity.proposition_4_7
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T15:41:29.816039+00:00
-- url     : https://prove2.me/submissions/b9d97f07-0b33-428f-b16b-076f0d6f9360

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Differential
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Hilbert
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus
import Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_homogeneous
import Mathlib

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
-- Implementation: Solutions/PhilipponFiniteBasicCover.lean

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
-- Implementation: Solutions/PhilipponAnalyticUnitOrder.lean

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
-- Implementation: Solutions/PhilipponAnalyticContainment.lean

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
-- Implementation: Solutions/PhilipponTranslationGeometry.lean

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
-- Implementation: Solutions/PhilipponHomogeneousPrimary.lean

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
-- Implementation: Solutions/PhilipponOperatorEvaluation.lean

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
-- Implementation: Solutions/PhilipponOperatorAlgebra.lean

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
-- Implementation: Solutions/PhilipponOperatorIdeals.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem retainOnGroup_mono {I J : Ideal G.CoordinateRing} (h : I ≤ J) :
    retainOnGroup G I ≤ retainOnGroup G J := by
  apply iInf_mono
  intro x
  exact Ideal.comap_mono (Ideal.map_mono h)

/-- Retention preserves the localized ideal at every genuine group representative. -/
theorem retainOnGroup_localization (I : Ideal G.CoordinateRing)
    (x : GroupHomogeneousRepresentative G) :
    (retainOnGroup G I).map (algebraMap G.CoordinateRing
      (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) =
    I.map (algebraMap G.CoordinateRing
      (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) := by
  apply le_antisymm
  · have h : retainOnGroup G I ≤ retainAtRepresentative G I x :=
      iInf_le (fun y : GroupHomogeneousRepresentative G => retainAtRepresentative G I y) x
    exact (Ideal.map_mono h).trans (le_of_eq (Ideal.map_comap_map _ I))
  · exact Ideal.map_mono (le_retainOnGroup G I)

theorem retainOnGroup_idempotent (I : Ideal G.CoordinateRing) :
    retainOnGroup G (retainOnGroup G I) = retainOnGroup G I := by
  unfold retainOnGroup retainAtRepresentative
  congr 1
  funext x
  change ((retainOnGroup G I).map _).under G.CoordinateRing = _
  rw [retainOnGroup_localization]

theorem retainOnGroup_sup (I J : Ideal G.CoordinateRing) :
    retainOnGroup G (retainOnGroup G I ⊔ retainOnGroup G J) =
      retainOnGroup G (I ⊔ J) := by
  apply le_antisymm
  · apply le_trans (retainOnGroup_mono G (sup_le
      (retainOnGroup_mono G le_sup_left) (retainOnGroup_mono G le_sup_right)))
    exact (retainOnGroup_idempotent G (I ⊔ J)).le
  · exact retainOnGroup_mono G (sup_le_sup (le_retainOnGroup G I) (le_retainOnGroup G J))

variable {G} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperatorIdeal_mono (atlas : TranslationAtlas A g) (T : ℕ)
    {I J : Ideal G.CoordinateRing} (h : I ≤ J) :
    polynomialOperatorIdeal atlas T I ≤ polynomialOperatorIdeal atlas T J := by
  apply sup_le_sup_left
  apply Ideal.span_mono
  rintro Q ⟨P, hP, hhom, a, n, hn, dirs, rfl⟩
  exact ⟨P, h hP, hhom, a, n, hn, dirs, rfl⟩

theorem retainedPolynomialOperatorIdeal_mono (atlas : TranslationAtlas A g) (T : ℕ)
    {I J : Ideal G.CoordinateRing} (h : I ≤ J) :
    retainedPolynomialOperatorIdeal atlas T I ≤ retainedPolynomialOperatorIdeal atlas T J :=
  retainOnGroup_mono G (polynomialOperatorIdeal_mono atlas T h)

variable [CompleteSpace K]

theorem polynomialOperatorIdeal_sup (atlas : TranslationAtlas A g) (T : ℕ)
    (I J : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hJ : IsMultihomogeneousIdeal G.ambient J) :
    polynomialOperatorIdeal atlas T (I ⊔ J) =
      polynomialOperatorIdeal atlas T I ⊔ polynomialOperatorIdeal atlas T J := by
  classical
  apply le_antisymm
  · apply sup_le
    · exact le_sup_of_le_left le_sup_left
    · apply Ideal.span_le.mpr
      rintro Q ⟨P, hP, ⟨D, hD⟩, a, n, hn, dirs, rfl⟩
      obtain ⟨P₁, h₁, P₂, h₂, heq⟩ := Submodule.mem_sup.mp hP
      let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
      let Q₁ := weightedHomogeneousComponent w D P₁
      let Q₂ := weightedHomogeneousComponent w D P₂
      have hQ₁ : Q₁ ∈ I := hI P₁ h₁ D
      have hQ₂ : Q₂ ∈ J := hJ P₂ h₂ D
      have hD₁ : G.ambient.IsHomogeneous Q₁ D :=
        (G.ambient.degreePiece_iff Q₁ D).mp (weightedHomogeneousComponent_mem w P₁ D)
      have hD₂ : G.ambient.IsHomogeneous Q₂ D :=
        (G.ambient.degreePiece_iff Q₂ D).mp (weightedHomogeneousComponent_mem w P₂ D)
      have hsum : P = Q₁ + Q₂ := by
        have hp : weightedHomogeneousComponent w D P = P :=
          weightedHomogeneousComponent_eq_self ((G.ambient.degreePiece_iff P D).mpr hD)
        rw [← hp, ← heq, map_add]
      rw [hsum, polynomialOperator_add]
      apply Ideal.add_mem
      · apply Ideal.mem_sup_left
        apply Ideal.mem_sup_right
        exact Ideal.subset_span ⟨Q₁, hQ₁, ⟨D, hD₁⟩, a, n, hn, dirs, rfl⟩
      · apply Ideal.mem_sup_right
        apply Ideal.mem_sup_right
        exact Ideal.subset_span ⟨Q₂, hQ₂, ⟨D, hD₂⟩, a, n, hn, dirs, rfl⟩
  · exact sup_le (polynomialOperatorIdeal_mono atlas T le_sup_left)
      (polynomialOperatorIdeal_mono atlas T le_sup_right)

theorem retainedPolynomialOperatorIdeal_sup (atlas : TranslationAtlas A g) (T : ℕ)
    (I J : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hJ : IsMultihomogeneousIdeal G.ambient J) :
    retainedPolynomialOperatorIdeal atlas T (I ⊔ J) =
      retainOnGroup G (retainedPolynomialOperatorIdeal atlas T I ⊔
        retainedPolynomialOperatorIdeal atlas T J) := by
  rw [retainedPolynomialOperatorIdeal, polynomialOperatorIdeal_sup atlas T I J hI hJ]
  exact (retainOnGroup_sup G _ _).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRetentionPrimary.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open SectionThreeSupport
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem retainAtRepresentative_iInf {ι : Type*} [Finite ι]
    (J : ι → Ideal G.CoordinateRing) (x : GroupHomogeneousRepresentative G) :
    retainAtRepresentative G (⨅ i, J i) x = ⨅ i, retainAtRepresentative G (J i) x := by
  classical
  letI := Fintype.ofFinite ι
  let S := (representativeMaximalIdeal G x).asIdeal.primeCompl
  let B := Localization.AtPrime (representativeMaximalIdeal G x).asIdeal
  have hm : (⨅ i, J i).map (algebraMap G.CoordinateRing B) =
      ⨅ i, (J i).map (algebraMap G.CoordinateRing B) := by
    simpa only [Finset.inf_univ_eq_iInf, Function.comp_def, IsLocalization.mapFrameHom_apply]
      using map_finset_inf (IsLocalization.mapFrameHom S B) Finset.univ J
  unfold retainAtRepresentative
  rw [hm]
  exact Ideal.comap_iInf _ _

theorem retainAtRepresentative_primary (J : Ideal G.CoordinateRing) (hJ : J.IsPrimary)
    (x : GroupHomogeneousRepresentative G) :
    retainAtRepresentative G J x = (by
      classical
      exact if J ≤ (representativeMaximalIdeal G x).asIdeal then J else ⊤) := by
  classical
  split_ifs with hx
  · exact IsLocalization.under_map_of_isPrimary_disjoint
      (representativeMaximalIdeal G x).asIdeal.primeCompl
      (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal) hJ
      (Set.disjoint_left.mpr fun s hs hsi => hs (hx hsi))
  · unfold retainAtRepresentative
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime (representativeMaximalIdeal G x).asIdeal) hx]
    exact Ideal.comap_top

/-- Definition 4.2: retention keeps exactly the actual primary components
whose support contains a genuine homogeneous representative of a group point. -/
theorem retainOnGroup_eq_primaryDecomposition (I : Ideal G.CoordinateRing)
    (D : PrimaryDecomposition G.ambient I) :
    retainOnGroup G I =
      ⨅ i : {i : Fin D.count // ∃ x : GroupHomogeneousRepresentative G,
        D.component i ≤ (representativeMaximalIdeal G x).asIdeal}, D.component i.1 := by
  classical
  conv_lhs => rw [D.intersection_eq]
  unfold retainOnGroup
  simp_rw [retainAtRepresentative_iInf]
  rw [iInf_comm]
  apply le_antisymm
  · apply le_iInf
    rintro ⟨i, x, hx⟩
    apply le_trans (iInf_le (fun j => ⨅ x, retainAtRepresentative G (D.component j) x) i)
    apply le_trans (iInf_le (fun y => retainAtRepresentative G (D.component i) y) x)
    rw [retainAtRepresentative_primary G _ (D.primary i) x, if_pos hx]
  · apply le_iInf
    intro i
    apply le_iInf
    intro x
    rw [retainAtRepresentative_primary G _ (D.primary i) x]
    split_ifs with hx
    · exact iInf_le (fun j : {j : Fin D.count // ∃ x : GroupHomogeneousRepresentative G,
        D.component j ≤ (representativeMaximalIdeal G x).asIdeal} => D.component j.1) ⟨i,x,hx⟩
    · exact le_top

theorem retainOnGroup_homogeneous (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) :
    IsMultihomogeneousIdeal G.ambient (retainOnGroup G I) := by
  obtain ⟨D⟩ := exists_primaryDecomposition G.ambient I hI
  rw [retainOnGroup_eq_primaryDecomposition G I D]
  intro P hP d
  simp only [Submodule.mem_iInf] at hP ⊢
  intro i
  exact D.homogeneous i.1 P (hP i) d

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponColonHilbert.lean

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

theorem homogeneous_colon (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I.colon {P}) := by
  intro Q hQ d
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hQ ⊢
  have h := hI (P * Q) (by simpa [mul_comm] using hQ) (D + d)
  rw [component_mul_homogeneous M hP Q d, mul_comm] at h
  exact h


end PhilipponMultiplicity.Hilbert
end
end


section
-- Implementation: Solutions/PhilipponDifferentialVanishing.lean

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

theorem locallyGeneratedIdeal_of_zero_sections (S : Set (LocalSection G))
    (hS : ∀ f ∈ S, ∀ x ∈ f.domain, f.value x = 0) :
    locallyGeneratedIdeal G S = G.vanishingIdeal Set.univ := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨⟨D, hD⟩, hP⟩
    apply Ideal.subset_span
    refine ⟨⟨D, hD⟩, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    obtain ⟨b, U, hU, hx, hsub, n, f, r, hfr, heq⟩ := hP x
    have hz : chartValue G b P x = 0 := by
      rw [heq x hx]
      apply Finset.sum_eq_zero
      intro i _
      rw [hS _ (f i).property x (hfr i x hx).1, mul_zero]
    rw [chartValue_homogeneous b P D hD x] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (inv_ne_zero (hsub hx i))))
  · apply Ideal.span_le.mpr
    rintro P ⟨⟨D, hD⟩, hP⟩
    apply Ideal.subset_span
    refine ⟨⟨D, hD⟩, ?_⟩
    intro x
    obtain ⟨b, hb⟩ := exists_chartDomain x
    refine ⟨b, chartDomain G b, chartDomain_isOpen b, hb, Set.Subset.rfl,
      0, Fin.elim0, Fin.elim0, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro y hy
      rw [chartValue_homogeneous b P D hD y, hP _ ⟨y, Set.mem_univ y, rfl⟩, mul_zero]
      simp

theorem normalizedJet_vanishingIdeal (A : AnalyticSubgroup G) (g : G.Point)
    (P : G.CoordinateRing) (hP : P ∈ G.vanishingIdeal Set.univ)
    (D : G.FactorIndex → ℕ) (hD : G.ambient.IsHomogeneous P D)
    (b : CoordinateChart G) {T : ℕ} (j : JetIndex A.parameterDimension T) (x : G.Point) :
    normalizedJet A g b P j x = 0 := by
  have hz : normalizedPullback A g b P x =ᶠ[𝓝 0] (fun _ => (0 : K)) := by
    filter_upwards [A.lift_represents (g + x)] with z hz
    obtain ⟨hz, hlift⟩ := hz
    have hzero : MvPolynomial.eval (A.lift (g + x) z) P = 0 :=
      G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding (Set.mem_univ _)) _ hlift hP
    unfold normalizedPullback
    calc
      _ = MvPolynomial.eval
          (fun v : G.ambient.Variable =>
            (A.lift (g + x) z ⟨v.1, b v.1⟩)⁻¹ * A.lift (g + x) z v) P := by
        apply congrArg (fun v : G.ambient.Variable → K => MvPolynomial.eval v P)
        funext v
        exact div_eq_inv_mul _ _
      _ = _ := (G.ambient.eval_block_scale P D hD (A.lift (g + x) z)
        (fun i => (A.lift (g + x) z ⟨i, b i⟩)⁻¹)).trans (by rw [hzero, mul_zero])
  unfold normalizedJet
  rw [(hz.iteratedFDeriv K j.order).eq_of_nhds]
  simp

/-- Every intrinsic differential ideal of the group's defining ideal is itself. -/
theorem differentialIdeal_vanishingIdeal (A : AnalyticSubgroup G) (g : G.Point) (T : ℕ) :
    differentialIdeal A g T (G.vanishingIdeal Set.univ) = G.vanishingIdeal Set.univ := by
  apply locallyGeneratedIdeal_of_zero_sections
  rintro f ⟨P, hP, ⟨D, hD⟩, b, j, rfl⟩ x hx
  exact normalizedJet_vanishingIdeal A g P hP D hD b j x

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalDenominators.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem exists_homogeneous_nonzero_evaluation (J : Ideal G.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal G.ambient J) (v : G.ambient.Variable → K)
    (P : G.CoordinateRing) (hP : P ∈ J) (hn : MvPolynomial.eval v P ≠ 0) :
    ∃ Q ∈ J, ∃ D : G.FactorIndex → ℕ,
      G.ambient.IsHomogeneous Q D ∧ MvPolynomial.eval v Q ≠ 0 := by
  classical
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  rw [← sum_weightedHomogeneousComponent w P,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) P), map_sum] at hn
  obtain ⟨D, _, hD⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact ⟨weightedHomogeneousComponent w D P, hJ P hP D, D,
    (G.ambient.degreePiece_iff _ D).mp (weightedHomogeneousComponent_mem w P D), hD⟩

/-- A homogeneous equation belongs to a point localization precisely when
one homogeneous denominator, nonzero at that representative, clears it. -/
theorem mem_retainAtRepresentative_iff_homogeneous_denominator
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : GroupHomogeneousRepresentative G) :
    P ∈ retainAtRepresentative G I x ↔
      ∃ s : G.CoordinateRing, ∃ E : G.FactorIndex → ℕ, G.ambient.IsHomogeneous s E ∧
        representativeEvaluation G x s ≠ 0 ∧ s * P ∈ I := by
  let m := representativeMaximalIdeal G x
  change algebraMap G.CoordinateRing (Localization.AtPrime m.asIdeal) P ∈
      I.map (algebraMap G.CoordinateRing (Localization.AtPrime m.asIdeal)) ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff m.asIdeal.primeCompl]
  constructor
  · rintro ⟨s, hs, hsp⟩
    have hsI : s ∈ I.colon {P} := by
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hsp
    obtain ⟨t, ht, E, htE, htx⟩ := exists_homogeneous_nonzero_evaluation
      (I.colon {P}) (Hilbert.homogeneous_colon G.ambient I hI P D hP) x.coordinates s hsI hs
    exact ⟨t, E, htE, htx, by simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ht⟩
  · rintro ⟨s, E, hsE, hs, hsp⟩
    exact ⟨s, hs, hsp⟩

theorem mem_retainOnGroup_iff_homogeneous_denominators
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    P ∈ retainOnGroup G I ↔
      ∀ x : GroupHomogeneousRepresentative G,
        ∃ s : G.CoordinateRing, ∃ E : G.FactorIndex → ℕ, G.ambient.IsHomogeneous s E ∧
          representativeEvaluation G x s ≠ 0 ∧ s * P ∈ I := by
  simp only [retainOnGroup, Submodule.mem_iInf,
    mem_retainAtRepresentative_iff_homogeneous_denominator I hI P D hP]

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRelevantHilbert.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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


end PhilipponMultiplicity.Hilbert
end
end


section
-- Implementation: Solutions/PhilipponLocalPolynomialSections.lean

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

theorem pivotPolynomial_eval_ne_zero (b : CoordinateChart G) (D : G.FactorIndex → ℕ)
    (x : G.Point) (hx : x ∈ chartDomain G b) :
    G.ambient.eval (pivotPolynomial b D) (G.embedding x) ≠ 0 := by
  classical
  simp only [pivotPolynomial, MultiProjectiveSpace.eval, map_prod, map_pow, eval_X]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hx i))

theorem chartValue_eq_div_pivot (b : CoordinateChart G) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) (x : G.Point) :
    chartValue G b P x = G.ambient.eval P (G.embedding x) /
      G.ambient.eval (pivotPolynomial b D) (G.embedding x) := by
  rw [chartValue_homogeneous b P D hP x]
  simp only [pivotPolynomial, MultiProjectiveSpace.eval, map_prod, map_pow, eval_X,
    MultiProjectiveSpace.coordinate, div_eq_mul_inv, Finset.prod_inv_distrib, inv_pow]
  exact mul_comm _ _

theorem locallyGenerated_translationSections_of_mem_retained
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (hmem : P ∈ retainOnGroup G I) : LocallyGenerated G (translationSections G 0 I) P := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  intro x
  obtain ⟨b, hb⟩ := exists_chartDomain x
  obtain ⟨s, E, hsE, hsx, hsp⟩ :=
    (mem_retainOnGroup_iff_homogeneous_denominators I hI P D hP).mp hmem (representativeOfPoint G x)
  have hsopen : IsOpen {y : G.Point | G.ambient.eval s (G.embedding y) ≠ 0} :=
    (G.ambient.isOpen_basic s E hsE).preimage continuous_induced_dom
  let U := chartDomain G b ∩ {y : G.Point | G.ambient.eval s (G.embedding y) ≠ 0}
  let f : (translationSections G 0 I) := ⟨
    ⟨chartDomain G b, chartValue G b (s * P)⟩,
    s * P, hsp, ⟨E + D, hsE.mul G.ambient hP⟩, b, by simp⟩
  let r : RationalCoefficient G :=
    ⟨pivotPolynomial b E, s, E, pivotPolynomial_homogeneous b E, hsE⟩
  refine ⟨b, U, (chartDomain_isOpen b).inter hsopen, ⟨hb, hsx⟩,
    Set.inter_subset_left, 1, (fun _ => f), (fun _ => r), ?_, ?_⟩
  · intro i y hy
    exact ⟨hy.1, hy.2⟩
  · intro y hy
    simp only [Fintype.sum_unique, f, r, RationalCoefficient.value]
    have hmul : chartValue G b (s * P) y = chartValue G b s y * chartValue G b P y := map_mul _ _ _
    rw [hmul, chartValue_eq_div_pivot b s E hsE y]
    have hpivot := pivotPolynomial_eval_ne_zero b E y hy.1
    have hsy : G.ambient.eval s (G.embedding y) ≠ 0 := hy.2
    field_simp

theorem retainOnGroup_le_translatedIdeal_zero
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I) :
    retainOnGroup G I ≤ translatedIdeal G 0 I := by
  classical
  intro P hP
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  rw [← sum_weightedHomogeneousComponent w P,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) P)]
  apply Ideal.sum_mem
  intro D _
  have hD := (G.ambient.degreePiece_iff _ D).mp (weightedHomogeneousComponent_mem w P D)
  apply Ideal.subset_span
  exact ⟨⟨D,hD⟩,locallyGenerated_translationSections_of_mem_retained I hI _ D hD
    (retainOnGroup_homogeneous G I hI P hP D)⟩

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalRational.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem representativeEvaluation_zero_iff (x : GroupHomogeneousRepresentative G)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    representativeEvaluation G x P = 0 ↔ G.ambient.eval P (G.embedding x.point) = 0 := by
  classical
  have ha (i : G.FactorIndex) : ∃ a : Kˣ,
      ∀ j, x.coordinates ⟨i,j⟩ = (a : K) * (G.embedding x.point i).rep j := by
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ (x.nonzero i)
      (G.embedding x.point i).rep_nonzero).mp
      ((x.represents i).trans (G.embedding x.point i).mk_rep.symm)
    exact ⟨a,fun j => by simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm⟩
  choose a ha using ha
  have hcoords : x.coordinates = fun v => (a v.1 : K) * G.ambient.coordinate (G.embedding x.point) v := by
    funext v
    exact ha v.1 v.2
  have heval : representativeEvaluation G x P =
      (∏ i, (a i : K) ^ D i) * G.ambient.eval P (G.embedding x.point) := by
    unfold representativeEvaluation
    rw [hcoords]
    exact G.ambient.eval_block_scale P D hP (G.ambient.coordinate (G.embedding x.point))
      (fun i => (a i : K))
  rw [heval]
  exact mul_eq_zero_iff_left (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero))

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

def rationalZero : RationalCoefficient G :=
  ⟨0, 1, 0, by simp [MultiProjectiveSpace.IsHomogeneous], G.ambient.isHomogeneous_one⟩

def rationalAdd (r s : RationalCoefficient G) : RationalCoefficient G :=
  ⟨r.numerator * s.denominator + s.numerator * r.denominator,
    r.denominator * s.denominator, r.degree + s.degree,
    (r.numerator_homogeneous.mul G.ambient s.denominator_homogeneous).add G.ambient
      (by simpa only [add_comm] using s.numerator_homogeneous.mul G.ambient r.denominator_homogeneous),
    r.denominator_homogeneous.mul G.ambient s.denominator_homogeneous⟩

theorem rationalAdd_value (r s : RationalCoefficient G) (x : G.Point)
    (hr : G.ambient.eval r.denominator (G.embedding x) ≠ 0)
    (hs : G.ambient.eval s.denominator (G.embedding x) ≠ 0) :
    (rationalAdd r s).value x = r.value x + s.value x := by
  simp only [RationalCoefficient.value, rationalAdd, MultiProjectiveSpace.eval, map_add, map_mul]
  change (G.ambient.eval r.numerator (G.embedding x) * G.ambient.eval s.denominator (G.embedding x) +
    G.ambient.eval s.numerator (G.embedding x) * G.ambient.eval r.denominator (G.embedding x)) /
    (G.ambient.eval r.denominator (G.embedding x) * G.ambient.eval s.denominator (G.embedding x)) =
    G.ambient.eval r.numerator (G.embedding x) / G.ambient.eval r.denominator (G.embedding x) +
      G.ambient.eval s.numerator (G.embedding x) / G.ambient.eval s.denominator (G.embedding x)
  field_simp

theorem exists_rational_sum {n : ℕ} (r : Fin n → RationalCoefficient G)
    (I : Ideal G.CoordinateRing) (hrI : ∀ i, (r i).numerator ∈ I) :
    ∃ s : RationalCoefficient G, s.numerator ∈ I ∧
      ∀ x : G.Point, (∀ i, G.ambient.eval (r i).denominator (G.embedding x) ≠ 0) →
        G.ambient.eval s.denominator (G.embedding x) ≠ 0 ∧ s.value x = ∑ i, (r i).value x := by
  induction n with
  | zero =>
    refine ⟨rationalZero, I.zero_mem, ?_⟩
    intro x hx
    simp [rationalZero, RationalCoefficient.value, MultiProjectiveSpace.eval]
  | succ n ih =>
    obtain ⟨s,hsI,hs⟩ := ih (fun i => r i.succ) (fun i => hrI i.succ)
    refine ⟨rationalAdd (r 0) s, ?_, ?_⟩
    · exact I.add_mem (I.mul_mem_right _ (hrI 0)) (I.mul_mem_right _ hsI)
    · intro x hx
      obtain ⟨hsx,hseq⟩ := hs x (fun i => hx i.succ)
      refine ⟨?_, ?_⟩
      · change G.ambient.eval ((r 0).denominator * s.denominator) (G.embedding x) ≠ 0
        simp only [MultiProjectiveSpace.eval, map_mul]
        exact mul_ne_zero (hx 0) hsx
      · rw [rationalAdd_value _ _ x (hx 0) hsx, hseq, Fin.sum_univ_succ]

/-- Clear an identity on a Zariski neighborhood using one homogeneous basic
open equation, preserving actual ideal membership modulo the group ideal. -/
theorem local_fraction_identity_mem_retained
    (I : Ideal G.CoordinateRing) (hG : G.vanishingIdeal Set.univ ≤ I)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : GroupHomogeneousRepresentative G) (b : CoordinateChart G)
    (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U) (hx : x.point ∈ U)
    (hUb : U ⊆ chartDomain G b) (r : RationalCoefficient G) (hrI : r.numerator ∈ I)
    (hr : ∀ y ∈ U, G.ambient.eval r.denominator (G.embedding y) ≠ 0)
    (heq : ∀ y ∈ U, chartValue G b P y = r.value y) :
    P ∈ retainAtRepresentative G I x := by
  classical
  obtain ⟨s,E,hsE,hsx,hsU⟩ := exists_basic_subset U hU x.point hx
  let B := pivotPolynomial b D
  let L := P * r.denominator - r.numerator * B
  have hL : G.ambient.IsHomogeneous L (D + r.degree) :=
    (hP.mul G.ambient r.denominator_homogeneous).sub G.ambient (by
      simpa only [add_comm] using r.numerator_homogeneous.mul G.ambient (pivotPolynomial_homogeneous b D))
  have hzero : ∀ y ∈ U, G.ambient.eval L (G.embedding y) = 0 := by
    intro y hy
    have h := heq y hy
    rw [chartValue_eq_div_pivot b P D hP y] at h
    have hb := pivotPolynomial_eval_ne_zero b D y (hUb hy)
    change _ / _ = _ / _ at h
    have hc := (div_eq_div_iff hb (hr y hy)).mp h
    change G.ambient.eval (P * r.denominator - r.numerator * B) (G.embedding y) = 0
    simpa only [MultiProjectiveSpace.eval, map_sub, map_mul, sub_eq_zero, B] using hc
  have hsL : s * L ∈ I := by
    apply hG
    apply Ideal.subset_span
    refine ⟨⟨E + (D + r.degree), hsE.mul G.ambient hL⟩, ?_⟩
    rintro _ ⟨y,_,rfl⟩
    change MvPolynomial.eval (G.ambient.coordinate (G.embedding y)) (s * L) = 0
    rw [map_mul]
    change G.ambient.eval s (G.embedding y) * G.ambient.eval L (G.embedding y) = 0
    by_cases hsy : G.ambient.eval s (G.embedding y) = 0
    · rw [hsy, zero_mul]
    · rw [hzero y (hsU hsy), mul_zero]
  have hclear : (s * r.denominator) * P ∈ I := by
    have h := I.add_mem hsL (I.mul_mem_left (s * B) hrI)
    convert h using 1 <;> dsimp [L] <;> ring
  have hsx' : representativeEvaluation G x s ≠ 0 := by
    exact fun h => hsx ((representativeEvaluation_zero_iff x s E hsE).mp h)
  have hdx' : representativeEvaluation G x r.denominator ≠ 0 := by
    exact fun h => hr x.point hx ((representativeEvaluation_zero_iff x _ _ r.denominator_homogeneous).mp h)
  change algebraMap G.CoordinateRing (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal) P ∈
    I.map (algebraMap G.CoordinateRing (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal))
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (representativeMaximalIdeal G x).asIdeal.primeCompl _ I P).mpr
  refine ⟨s * r.denominator, ?_, hclear⟩
  change representativeEvaluation G x (s * r.denominator) ≠ 0
  rw [map_mul]
  exact mul_ne_zero hsx' hdx'

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRationalOperations.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

def rationalMul (r s : RationalCoefficient G) : RationalCoefficient G :=
  ⟨r.numerator * s.numerator,r.denominator * s.denominator,r.degree + s.degree,
    r.numerator_homogeneous.mul G.ambient s.numerator_homogeneous,
    r.denominator_homogeneous.mul G.ambient s.denominator_homogeneous⟩

def rationalNeg (r : RationalCoefficient G) : RationalCoefficient G :=
  ⟨-r.numerator,r.denominator,r.degree,r.numerator_homogeneous.neg G.ambient,r.denominator_homogeneous⟩

theorem rationalMul_value (r s : RationalCoefficient G) (x : G.Point) :
    (rationalMul r s).value x = r.value x * s.value x := by
  simp only [rationalMul,RationalCoefficient.value,MultiProjectiveSpace.eval,map_mul]
  exact (div_mul_div_comm _ _ _ _).symm

theorem rationalNeg_value (r : RationalCoefficient G) (x : G.Point) :
    (rationalNeg r).value x = -r.value x := by
  simp only [rationalNeg,RationalCoefficient.value,MultiProjectiveSpace.eval,map_neg,neg_div]

theorem rationalMul_denominator_ne_zero (r s : RationalCoefficient G) (x : G.Point)
    (hr : G.ambient.eval r.denominator (G.embedding x) ≠ 0)
    (hs : G.ambient.eval s.denominator (G.embedding x) ≠ 0) :
    G.ambient.eval (rationalMul r s).denominator (G.embedding x) ≠ 0 := by
  simp only [rationalMul,MultiProjectiveSpace.eval,map_mul]
  exact mul_ne_zero hr hs

theorem rationalAdd_denominator_ne_zero (r s : RationalCoefficient G) (x : G.Point)
    (hr : G.ambient.eval r.denominator (G.embedding x) ≠ 0)
    (hs : G.ambient.eval s.denominator (G.embedding x) ≠ 0) :
    G.ambient.eval (rationalAdd r s).denominator (G.embedding x) ≠ 0 := by
  simp only [rationalAdd,MultiProjectiveSpace.eval,map_mul]
  exact mul_ne_zero hr hs

theorem rationalAdd_numerator_mem (I : Ideal G.CoordinateRing) (r s : RationalCoefficient G)
    (hr : r.numerator ∈ I) (hs : s.numerator ∈ I) : (rationalAdd r s).numerator ∈ I :=
  I.add_mem (I.mul_mem_right _ hr) (I.mul_mem_right _ hs)

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponChartRational.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

/-- Even a nonhomogeneous polynomial, evaluated in normalized coordinates,
is a balanced homogeneous rational function regular on that coordinate chart. -/
theorem chartValue_rational (b : CoordinateChart G) (P : G.CoordinateRing) :
    ∃ r : RationalCoefficient G, ∀ x ∈ chartDomain G b,
      G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧ r.value x = chartValue G b P x := by
  classical
  have hX (v : G.ambient.Variable) : G.ambient.IsHomogeneous (X v) (Pi.single v.1 1) := by
    apply (G.ambient.degreePiece_iff _ _).mp
    exact isWeightedHomogeneous_X K _ v
  have hv (v : G.ambient.Variable) : ∃ r : RationalCoefficient G,
      ∀ x ∈ chartDomain G b, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧
        r.value x = chartValue G b (X v) x := by
    let r : RationalCoefficient G := ⟨X v,X ⟨v.1,b v.1⟩,Pi.single v.1 1,hX v,hX _⟩
    refine ⟨r,?_⟩
    intro x hx
    refine ⟨?_,?_⟩
    · simpa only [r,MultiProjectiveSpace.eval,eval_X,MultiProjectiveSpace.coordinate] using hx v.1
    · simp only [r,RationalCoefficient.value,MultiProjectiveSpace.eval,chartValue,eval_X]
      rfl
  induction P using MvPolynomial.induction_on with
  | C a =>
    have ha : G.ambient.IsHomogeneous (C a) 0 := by
      simpa using G.ambient.isHomogeneous_one.C_mul G.ambient a
    refine ⟨⟨C a,1,0,ha,G.ambient.isHomogeneous_one⟩,?_⟩
    intro x hx
    simp [RationalCoefficient.value,MultiProjectiveSpace.eval,chartValue]
  | add P Q hP hQ =>
    obtain ⟨r,hr⟩ := hP
    obtain ⟨s,hs⟩ := hQ
    refine ⟨rationalAdd r s,?_⟩
    intro x hx
    refine ⟨rationalAdd_denominator_ne_zero r s x (hr x hx).1 (hs x hx).1,?_⟩
    rw [rationalAdd_value r s x (hr x hx).1 (hs x hx).1,(hr x hx).2,(hs x hx).2]
    exact (map_add _ P Q).symm
  | mul_X P v hP =>
    obtain ⟨r,hr⟩ := hP
    obtain ⟨s,hs⟩ := hv v
    refine ⟨rationalMul r s,?_⟩
    intro x hx
    refine ⟨rationalMul_denominator_ne_zero r s x (hr x hx).1 (hs x hx).1,?_⟩
    rw [rationalMul_value,(hr x hx).2,(hs x hx).2]
    exact (map_mul _ P (X v)).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalJetSpan.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

/-- A finite regular rational expression in sections on a neighborhood of a point. -/
def LocalSpanAt (S : Set (LocalSection G)) (h : G.Point → K) (x : G.Point) : Prop :=
  ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
    ∃ n : ℕ, ∃ f : Fin n → S, ∃ r : Fin n → RationalCoefficient G,
      (∀ i, ∀ y ∈ U, y ∈ (f i).val.domain ∧ G.ambient.eval (r i).denominator (G.embedding y) ≠ 0) ∧
      ∀ y ∈ U, h y = ∑ i, (r i).value y * (f i).val.value y

theorem localSpanAt_zero (S : Set (LocalSection G)) (x : G.Point) :
    LocalSpanAt S (fun _ => 0) x := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ x,0,Fin.elim0,Fin.elim0,?_,?_⟩
  · intro i
    exact Fin.elim0 i
  · intro y hy
    simp

theorem LocalSpanAt.congr_on {S : Set (LocalSection G)} {f h : G.Point → K} {x : G.Point}
    (hf : LocalSpanAt S f x) (V : Set G.Point) (hV : @IsOpen _ G.zariskiTopology V)
    (hxV : x ∈ V) (heq : ∀ y ∈ V, f y = h y) : LocalSpanAt S h x := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨U,hU,hx,n,s,r,hr,hf⟩ := hf
  refine ⟨U ∩ V,hU.inter hV,⟨hx,hxV⟩,n,s,r,?_,?_⟩
  · intro i y hy
    exact hr i y hy.1
  · intro y hy
    exact (heq y hy.2).symm.trans (hf y hy.1)

theorem LocalSpanAt.add {S : Set (LocalSection G)} {f h : G.Point → K} {x : G.Point}
    (hf : LocalSpanAt S f x) (hh : LocalSpanAt S h x) :
    LocalSpanAt S (fun y => f y + h y) x := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨U,hU,hxU,n,s,r,hs,hf⟩ := hf
  obtain ⟨V,hV,hxV,m,t,q,ht,hh⟩ := hh
  refine ⟨U ∩ V,hU.inter hV,⟨hxU,hxV⟩,n+m,Fin.addCases s t,Fin.addCases r q,?_,?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j y hy
      simpa only [Fin.addCases_left] using hs j y hy.1
    · intro j y hy
      simpa only [Fin.addCases_right] using ht j y hy.2
  · intro y hy
    change f y + h y = _
    rw [hf y hy.1,hh y hy.2,Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right]

theorem LocalSpanAt.rational_mul {S : Set (LocalSection G)} {f : G.Point → K} {x : G.Point}
    (hf : LocalSpanAt S f x) (q : RationalCoefficient G)
    (V : Set G.Point) (hV : @IsOpen _ G.zariskiTopology V) (hxV : x ∈ V)
    (hq : ∀ y ∈ V, G.ambient.eval q.denominator (G.embedding y) ≠ 0) :
    LocalSpanAt S (fun y => q.value y * f y) x := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨U,hU,hxU,n,s,r,hs,heq⟩ := hf
  refine ⟨U ∩ V,hU.inter hV,⟨hxU,hxV⟩,n,s,(fun i => rationalMul q (r i)),?_,?_⟩
  · intro i y hy
    exact ⟨(hs i y hy.1).1,
      rationalMul_denominator_ne_zero _ _ y (hq y hy.2) (hs i y hy.1).2⟩
  · intro y hy
    change q.value y * f y = _
    rw [heq y hy.1,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [rationalMul_value,mul_assoc]

theorem LocalSpanAt.fin_sum {S : Set (LocalSection G)} {n : ℕ}
    (f : Fin n → G.Point → K) (x : G.Point) (hf : ∀ i, LocalSpanAt S (f i) x) :
    LocalSpanAt S (fun y => ∑ i, f i y) x := by
  induction n with
  | zero => simpa using localSpanAt_zero S x
  | succ n ih =>
    have hh := (hf 0).add (ih (fun i => f i.succ) (fun i => hf i.succ))
    simpa only [Fin.sum_univ_succ] using hh

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalSectionIdeal.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem localSpanAt_section (S : Set (LocalSection G)) (f : S) (x : G.Point)
    (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U) (hx : x ∈ U)
    (hUf : U ⊆ f.val.domain) : LocalSpanAt S f.val.value x := by
  let r : RationalCoefficient G :=
    ⟨1,1,0,G.ambient.isHomogeneous_one,G.ambient.isHomogeneous_one⟩
  refine ⟨U,hU,hx,1,(fun _ => f),(fun _ => r),?_,?_⟩
  · intro i y hy
    refine ⟨hUf hy,?_⟩
    simp only [r,MultiProjectiveSpace.eval,map_one,ne_eq,one_ne_zero,not_false_eq_true]
  · intro y hy
    simp [r,RationalCoefficient.value,MultiProjectiveSpace.eval]

theorem LocalSpanAt.list_sum {ι : Type*} {S : Set (LocalSection G)} (s : List ι)
    (f : ι → G.Point → K) (x : G.Point) (hf : ∀ i ∈ s, LocalSpanAt S (f i) x) :
    LocalSpanAt S (fun y => (s.map (fun i => f i y)).sum) x := by
  induction s with
  | nil => simpa using localSpanAt_zero S x
  | cons i s ih =>
    exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

theorem locallyGenerated_iff_localSpan (S : Set (LocalSection G)) (P : G.CoordinateRing) :
    LocallyGenerated G S P ↔
      ∀ x : G.Point, ∃ b : CoordinateChart G, x ∈ chartDomain G b ∧
        LocalSpanAt S (chartValue G b P) x := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  constructor
  · intro h x
    obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := h x
    exact ⟨b,hUb hx,U,hU,hx,n,f,r,hfr,heq⟩
  · intro h x
    obtain ⟨b,hb,U,hU,hx,n,f,r,hfr,heq⟩ := h x
    refine ⟨b,U ∩ chartDomain G b,hU.inter (chartDomain_isOpen b),⟨hx,hb⟩,
      Set.inter_subset_right,n,f,r,?_,?_⟩
    · intro i y hy
      exact hfr i y hy.1
    · intro y hy
      exact heq y hy.1

/-- At a fixed source chart and point, membership in the local section span
pulls back to an actual polynomial ideal. -/
def localSectionIdeal (S : Set (LocalSection G)) (b : CoordinateChart G)
    (x : G.Point) (hx : x ∈ chartDomain G b) : Ideal G.CoordinateRing where
  carrier := {P | LocalSpanAt S (chartValue G b P) x}
  zero_mem' := by
    change LocalSpanAt S (chartValue G b 0) x
    have heq : chartValue G b 0 = fun _ => 0 := by
      funext y
      exact map_zero _
    rw [heq]
    exact localSpanAt_zero S x
  add_mem' := by
    intro P Q hP hQ
    change LocalSpanAt S (chartValue G b (P + Q)) x
    have heq : chartValue G b (P + Q) = fun y => chartValue G b P y + chartValue G b Q y := by
      funext y
      exact map_add _ P Q
    rw [heq]
    exact hP.add hQ
  smul_mem' := by
    intro a P hP
    obtain ⟨r,hr⟩ := chartValue_rational b a
    have h := hP.rational_mul r (chartDomain G b) (chartDomain_isOpen b) hx
      (fun y hy => (hr y hy).1)
    apply h.congr_on (chartDomain G b) (chartDomain_isOpen b) hx
    intro y hy
    rw [(hr y hy).2]
    exact (map_mul _ a P).symm

theorem mem_localSectionIdeal (S : Set (LocalSection G)) (b : CoordinateChart G)
    (x : G.Point) (hx : x ∈ chartDomain G b) (P : G.CoordinateRing) :
    P ∈ localSectionIdeal S b x hx ↔ LocalSpanAt S (chartValue G b P) x := Iff.rfl

theorem groupIdeal_le_localSectionIdeal (S : Set (LocalSection G)) (b : CoordinateChart G)
    (x : G.Point) (hx : x ∈ chartDomain G b) :
    G.vanishingIdeal Set.univ ≤ localSectionIdeal S b x hx := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  apply (localSpanAt_zero S x).congr_on Set.univ isOpen_univ (Set.mem_univ x)
  intro y hy
  rw [chartValue_homogeneous b P D hD y,hP _ ⟨y,Set.mem_univ y,rfl⟩,mul_zero]

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalGenerationCharts.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem translation_preimage_isOpen (g : G.Point) (U : Set G.Point)
    (hU : @IsOpen _ G.zariskiTopology U) :
    @IsOpen _ G.zariskiTopology {x | g+x ∈ U} := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have hc : Continuous (fun x : G.Point => x+g) :=
    continuous_induced_rng.mpr (G.translation_regular g).continuous
  have hc' : Continuous (fun x : G.Point => g+x) := by simpa only [add_comm] using hc
  exact hU.preimage hc'

/-- Homogeneous local expressions may be read in any chart through the point.
The chart-change factor is an actual balanced rational function. -/
theorem LocalSpanAt.change_chart {S : Set (LocalSection G)}
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (b c : CoordinateChart G) (x : G.Point)
    (hb : x ∈ chartDomain G b) (hc : x ∈ chartDomain G c)
    (h : LocalSpanAt S (chartValue G b P) x) :
    LocalSpanAt S (chartValue G c P) x := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  let r : RationalCoefficient G :=
    ⟨pivotPolynomial b D,pivotPolynomial c D,D,
      pivotPolynomial_homogeneous b D,pivotPolynomial_homogeneous c D⟩
  have hh := h.rational_mul r (chartDomain G c) (chartDomain_isOpen c) hc
    (fun y hy => pivotPolynomial_eval_ne_zero c D y hy)
  apply hh.congr_on (chartDomain G b ∩ chartDomain G c)
    ((chartDomain_isOpen b).inter (chartDomain_isOpen c)) ⟨hb,hc⟩
  intro y hy
  rw [chartValue_eq_div_pivot b P D hP,chartValue_eq_div_pivot c P D hP]
  change (_ / _) * (_ / _) = _ / _
  dsimp only [r]
  have hn := pivotPolynomial_eval_ne_zero b D y hy.1
  field_simp

/-- The ideal span in the global definition does not lose the local expression:
every polynomial in it has a finite expression in every chart through x. -/
theorem locallyGeneratedIdeal_le_localSectionIdeal (S : Set (LocalSection G))
    (b : CoordinateChart G) (x : G.Point) (hx : x ∈ chartDomain G b) :
    locallyGeneratedIdeal G S ≤ localSectionIdeal S b x hx := by
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  obtain ⟨c,hc,hh⟩ := (locallyGenerated_iff_localSpan S P).mp hP x
  exact hh.change_chart P D hD c b x hc hx

theorem LocalSpanAt.trans {S R : Set (LocalSection G)} {f : G.Point → K}
    {x : G.Point} (h : LocalSpanAt S f x)
    (hS : ∀ s : S, x ∈ s.val.domain → LocalSpanAt R s.val.value x) :
    LocalSpanAt R f x := by
  obtain ⟨U,hU,hx,n,s,r,hs,heq⟩ := h
  have ht (i : Fin n) := (hS (s i) (hs i x hx).1).rational_mul (r i) U hU hx
    (fun y hy => (hs i y hy).2)
  exact (LocalSpanAt.fin_sum (fun i y => (r i).value y * (s i).val.value y) x ht).congr_on
    U hU hx (fun y hy => (heq y hy).symm)

theorem locallyGeneratedIdeal_le_of_localSpan (S R : Set (LocalSection G))
    (hS : ∀ s : S, ∀ x ∈ s.val.domain, LocalSpanAt R s.val.value x) :
    locallyGeneratedIdeal G S ≤ locallyGeneratedIdeal G R := by
  apply Ideal.span_le.mpr
  rintro P ⟨hP,h⟩
  apply Ideal.subset_span
  refine ⟨hP,(locallyGenerated_iff_localSpan R P).mpr ?_⟩
  intro x
  obtain ⟨b,hb,hh⟩ := (locallyGenerated_iff_localSpan S P).mp h x
  exact ⟨b,hb,hh.trans (fun s hs => hS s x hs)⟩

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponTranslationSeparation.lean

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
-- Implementation: Solutions/PhilipponProjectiveHilbertExistence.lean

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
    rw [M.blockWeight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d


end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponPrimeFiltration.lean

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
-- Implementation: Solutions/PhilipponConnectedGroupIrreducible.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity

/-- A connected Noetherian space on which homeomorphisms act transitively
is irreducible. This uses only individual homeomorphisms, not a topological
group structure on the Zariski topology. -/
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

def AlgebraicSubgroup.translationHomeomorph (H : AlgebraicSubgroup G)
    (a : H.toAddSubgroup) :
    @Homeomorph H.carrier H.carrier
      (TopologicalSpace.induced Subtype.val G.zariskiTopology)
      (TopologicalSpace.induced Subtype.val G.zariskiTopology) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (G.translationHomeomorph a.val).subtype (by
    intro x
    change x ∈ H.toAddSubgroup ↔ a.val+x ∈ H.toAddSubgroup
    exact ⟨fun hx => H.toAddSubgroup.add_mem a.property hx,fun hx => by
      have h := H.toAddSubgroup.add_mem (H.toAddSubgroup.neg_mem a.property) hx
      simpa only [← add_assoc,neg_add_cancel,zero_add] using h⟩)

/-- The actual connected algebraic subgroup is irreducible for the specified
polynomial Zariski topology, as used before Philippon's Lemma 4.6. -/
theorem AlgebraicSubgroup.isIrreducible_of_isConnected (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) : @IsIrreducible _ G.zariskiTopology H.carrier := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : NoetherianSpace G.Point := G.ambient.noetherian_induced G.embedding
  letI : ConnectedSpace H.carrier := isConnected_iff_connectedSpace.mp hH
  apply isIrreducible_iff_irreducibleSpace.mpr
  apply irreducible_of_transitive_homeomorphisms
  intro x y
  let a : H.toAddSubgroup := ⟨y.val-x.val,H.toAddSubgroup.sub_mem y.property x.property⟩
  refine ⟨H.translationHomeomorph a,?_⟩
  apply Subtype.ext
  change y.val-x.val+x.val = y.val
  exact sub_add_cancel _ _

theorem AlgebraicSubgroup.isIrreducible_translate (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) (g : G.Point) :
    @IsIrreducible _ G.zariskiTopology (translate g H.carrier) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (H.isIrreducible_of_isConnected hH).image _ (G.continuous_translation g).continuousOn

/-- Irreducibility implies ordinary primality of the actual homogeneous
vanishing ideal, by the proved multigraded homogeneous-product criterion. -/
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

/-- The coset prime used in the opening paragraph of Section 4.2 is the
mission's actual vanishing ideal. -/
theorem AlgebraicSubgroup.translated_vanishingIdeal_isPrime (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) (g : G.Point) :
    (G.vanishingIdeal (translate g H.carrier)).IsPrime := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  exact G.ambient.vanishingIdeal_isPrime_of_isIrreducible _
    ((H.isIrreducible_translate hH g).image G.embedding
      (show Continuous G.embedding from continuous_induced_dom).continuousOn)

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponNormalizedChartGerms.lean

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

/-- The source coordinate-ratio identity, including charts whose own domain
does not contain x. Only the intrinsic target pivots must be nonzero. -/
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

theorem normalizedPullback_eq_chart_quotient (chart : TranslationChart A g)
    (b : CoordinateChart G) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (x : G.Point) (hchart : x ∈ chart.domain)
    (hx : g+x ∈ chartDomain G b) :
    normalizedPullback A g b P x =ᶠ[𝓝 0]
      (fun z => evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x z /
        ∏ i, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z ^ D i) := by
  classical
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ i : G.FactorIndex, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (chart_evaluation_analytic chart x _).continuousAt.eventually_ne
      (chart_pivot_ne_zero chart x hchart b hx i)
  filter_upwards [chart_normalized_factorization chart b P D hP x hx,hnear] with z heq hz
  rw [heq]
  exact (mul_div_cancel_left₀ _ (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hz i))).symm

theorem evaluate_pivot_substitution (chart : TranslationChart A g)
    (b : CoordinateChart G) (D : G.FactorIndex → ℕ) (x : G.Point) (z : A.ParameterSpace) :
    evaluateCoefficientPolynomial A (substitutedPolynomial chart (pivotPolynomial b D)) x z =
      ∏ i, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z ^ D i := by
  rw [evaluate_substituted]
  simp only [pivotPolynomial,map_prod,map_pow,eval_X]
  rfl

/-- A genuine Zariski neighborhood with simultaneous nonvanishing target pivots. -/
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
-- Implementation: Solutions/PhilipponMixedLeibniz.lean

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

/-- Ordered directional differentiation; the head direction is applied last. -/
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

/-- All product-rule terms except the term with no derivative on the first factor. -/
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

/-- A triangular finite Leibniz formula: every term in the remainder uses a
strictly lower derivative of the second factor. -/
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
-- Implementation: Solutions/PhilipponRationalJetRecursion.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem exists_rational_list_sum {ι : Type*} (s : List ι) (f : ι → G.Point → K)
    (I : Ideal G.CoordinateRing) (U : Set G.Point)
    (hf : ∀ i ∈ s, ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
      ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧ r.value x = f i x) :
    ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
      ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧
        r.value x = (s.map (fun i => f i x)).sum := by
  induction s with
  | nil =>
    refine ⟨rationalZero,I.zero_mem,?_⟩
    intro x hx
    simp [rationalZero,RationalCoefficient.value,MultiProjectiveSpace.eval]
  | cons i s ih =>
    obtain ⟨r,hrI,hr⟩ := hf i (by simp)
    obtain ⟨t,htI,ht⟩ := ih (fun j hj => hf j (by simp [hj]))
    refine ⟨rationalAdd r t,rationalAdd_numerator_mem I r t hrI htI,?_⟩
    intro x hx
    obtain ⟨hrx,heqr⟩ := hr x hx
    obtain ⟨htx,heqt⟩ := ht x hx
    exact ⟨rationalAdd_denominator_ne_zero r t x hrx htx,by
      rw [rationalAdd_value r t x hrx htx,heqr,heqt,List.map_cons,List.sum_cons]⟩

/-- A triangular jet identity yields honest homogeneous fractions. The
numerators remain in the given ideal, without taking radicals. -/
theorem rational_jet_recursion {ι : Type*}
    (F Q : List ι → G.CoordinateRing) (H : List ι → G.Point → K)
    (E : G.FactorIndex → ℕ) (I : Ideal G.CoordinateRing) (U : Set G.Point) (T : ℕ)
    (hF : ∀ w, G.ambient.IsHomogeneous (F w) E)
    (hQ : ∀ w, G.ambient.IsHomogeneous (Q w) E)
    (hFI : ∀ w, w.length ≤ T → F w ∈ I)
    (hQ0 : ∀ x ∈ U, G.ambient.eval (Q []) (G.embedding x) ≠ 0)
    (heq : ∀ w, w.length ≤ T → ∀ x ∈ U,
      G.ambient.eval (F w) (G.embedding x) =
        G.ambient.eval (Q []) (G.embedding x) * H w x +
          ((properSplits w).map (fun p =>
            G.ambient.eval (Q p.1) (G.embedding x) * H p.2 x)).sum)
    (w : List ι) (hw : w.length ≤ T) :
    ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
      ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧ r.value x = H w x := by
  classical
  suffices hall : ∀ n, ∀ w : List ι, w.length = n → w.length ≤ T →
      ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
        ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧ r.value x = H w x from
    hall w.length w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn hw
    let a : RationalCoefficient G := ⟨F w,Q [],E,hF w,hQ []⟩
    let q : List ι → RationalCoefficient G := fun v => ⟨Q v,Q [],E,hQ v,hQ []⟩
    have hterms : ∀ p ∈ properSplits w, ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
        ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧
          r.value x = G.ambient.eval (Q p.1) (G.embedding x) /
            G.ambient.eval (Q []) (G.embedding x) * H p.2 x := by
      intro p hp
      have hlen := (properSplits_lengths w p hp).2.2
      obtain ⟨r,hrI,hr⟩ := ih p.2.length (by omega) p.2 rfl (by omega)
      refine ⟨rationalMul (q p.1) r,I.mul_mem_left _ hrI,?_⟩
      intro x hx
      obtain ⟨hrx,heqr⟩ := hr x hx
      exact ⟨rationalMul_denominator_ne_zero _ _ x (hQ0 x hx) hrx,by
        rw [rationalMul_value,heqr]; rfl⟩
    obtain ⟨s,hsI,hs⟩ := exists_rational_list_sum (properSplits w)
      (fun p x => G.ambient.eval (Q p.1) (G.embedding x) /
        G.ambient.eval (Q []) (G.embedding x) * H p.2 x) I U hterms
    refine ⟨rationalAdd a (rationalNeg s),
      rationalAdd_numerator_mem I _ _ (hFI w hw) (I.neg_mem hsI),?_⟩
    intro x hx
    obtain ⟨hsx,heqs⟩ := hs x hx
    have hax : G.ambient.eval a.denominator (G.embedding x) ≠ 0 := hQ0 x hx
    refine ⟨rationalAdd_denominator_ne_zero _ _ x hax hsx,?_⟩
    rw [rationalAdd_value a (rationalNeg s) x hax hsx,rationalNeg_value,heqs]
    change G.ambient.eval (F w) (G.embedding x) / G.ambient.eval (Q []) (G.embedding x) + -_ = _
    rw [heq w hw x hx,add_div,mul_div_cancel_left₀ _ (hQ0 x hx)]
    have hsum : ((properSplits w).map (fun p =>
        G.ambient.eval (Q p.1) (G.embedding x) / G.ambient.eval (Q []) (G.embedding x) * H p.2 x)).sum =
        ((properSplits w).map (fun p => G.ambient.eval (Q p.1) (G.embedding x) * H p.2 x)).sum /
          G.ambient.eval (Q []) (G.embedding x) := by
      induction properSplits w with
      | nil => simp
      | cons p ps ih => simp only [List.map_cons,List.sum_cons,add_div,ih]; ring
    rw [hsum]
    ring

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponNormalizedJetFractions.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperator_eval_mixed (chart : TranslationChart A g) (P : G.CoordinateRing)
    (x : G.Point) (w : List (Fin A.parameterDimension)) :
    G.ambient.eval (polynomialOperator chart w.length w.get P) (G.embedding x) =
      mixedDeriv (w.map (fun i => Pi.single i (1 : K)))
        (evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x) 0 := by
  rw [mixedDeriv_map_eq_iteratedFDeriv _
    (evaluated_coefficients_analytic _ (substituted_coeff_analytic chart P) x)]
  rw [polynomialOperator_eval]
  congr 2
  funext z
  exact (evaluate_substituted chart P x z).symm

/-- Every intrinsic normalized jet has, on a genuine neighborhood, a balanced
homogeneous fraction whose numerator belongs to the polynomial-operator ideal. -/
theorem normalizedJet_rational_fraction (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (P : G.CoordinateRing) (hPI : P ∈ I)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (b : CoordinateChart G) (j : JetIndex A.parameterDimension T)
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
      ∃ r : RationalCoefficient G, r.numerator ∈ polynomialOperatorIdeal atlas T I ∧
        ∀ y ∈ U, G.ambient.eval r.denominator (G.embedding y) ≠ 0 ∧
          r.value y = normalizedJet A g b P j y := by
  classical
  obtain ⟨a,ha⟩ := atlas.covers x
  let chart := atlas.chart a
  obtain ⟨U,hU,hxU,hUc,hUb⟩ := exists_translation_pivot_neighborhood chart b x ha hx
  let B := pivotPolynomial b D
  let F := fun w : List (Fin A.parameterDimension) => polynomialOperator chart w.length w.get P
  let Q := fun w : List (Fin A.parameterDimension) => polynomialOperator chart w.length w.get B
  let H := fun (w : List (Fin A.parameterDimension)) (y : G.Point) =>
    mixedDeriv (w.map (fun i => Pi.single i (1 : K))) (normalizedPullback A g b P y) 0
  have hF (w) : G.ambient.IsHomogeneous (F w) (fun i => chart.degree i * D i) :=
    polynomialOperator_homogeneous chart _ _ P D hP
  have hQ (w) : G.ambient.IsHomogeneous (Q w) (fun i => chart.degree i * D i) :=
    polynomialOperator_homogeneous chart _ _ B D (pivotPolynomial_homogeneous b D)
  have hFI (w : List (Fin A.parameterDimension)) (hw : w.length ≤ T) :
      F w ∈ polynomialOperatorIdeal atlas T I :=
    Ideal.mem_sup_right (Ideal.subset_span ⟨P,hPI,⟨D,hP⟩,a,w.length,hw,w.get,rfl⟩)
  have hQ0 (y : G.Point) (hy : y ∈ U) : G.ambient.eval (Q []) (G.embedding y) ≠ 0 := by
    rw [polynomialOperator_eval_mixed]
    simp only [List.map_nil,mixedDeriv]
    rw [evaluate_pivot_substitution]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ ((hUb y hy).2 i))
  have heq (w : List (Fin A.parameterDimension)) (_hw : w.length ≤ T)
      (y : G.Point) (hy : y ∈ U) :
      G.ambient.eval (F w) (G.embedding y) = G.ambient.eval (Q []) (G.embedding y) * H w y +
        ((properSplits w).map (fun p => G.ambient.eval (Q p.1) (G.embedding y) * H p.2 y)).sum := by
    have hfactor : evaluateCoefficientPolynomial A (substitutedPolynomial chart P) y =ᶠ[𝓝 0]
        (fun z => evaluateCoefficientPolynomial A (substitutedPolynomial chart B) y z *
          normalizedPullback A g b P y z) := by
      simpa only [B,evaluate_pivot_substitution] using
        chart_normalized_factorization chart b P D hP y (hUb y hy).1
    have hderiv := (mixedDeriv_congr hfactor (w.map (fun i => Pi.single i (1 : K)))).self_of_nhds
    rw [mixedDeriv_map_mul _
      (evaluated_coefficients_analytic _ (substituted_coeff_analytic chart B) y)
      (normalizedPullback_analytic A g b P y (hUb y hy).1)] at hderiv
    simpa only [F,Q,H,polynomialOperator_eval_mixed,List.map_nil,mixedDeriv] using hderiv
  obtain ⟨r,hrI,hr⟩ := rational_jet_recursion F Q H _ (polynomialOperatorIdeal atlas T I) U T
    hF hQ hFI hQ0 heq (List.ofFn j.directions) (by simpa using j.order_le)
  refine ⟨U,hU,hxU,r,hrI,?_⟩
  intro y hy
  refine ⟨(hr y hy).1,(hr y hy).2.trans ?_⟩
  dsimp only [H,normalizedJet]
  rw [mixedDeriv_map_eq_iteratedFDeriv _ (normalizedPullback_analytic A g b P y (hUb y hy).1)]
  apply iteratedFDeriv_apply_congr (List.length_ofFn ..)
  intro i
  simp only [List.get_ofFn]

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponPolynomialJetLeibniz.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

/-- The opposite Leibniz expansion holds for every polynomial chart, whether
or not its chart domain contains the point. -/
theorem polynomialOperator_normalized_jet_expansion (chart : TranslationChart A g)
    (b : CoordinateChart G) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (w : List (Fin A.parameterDimension))
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    G.ambient.eval (polynomialOperator chart w.length w.get P) (G.embedding x) =
      G.ambient.eval (polynomialOperator chart 0 Fin.elim0 (pivotPolynomial b D)) (G.embedding x) *
        normalizedJet A g b P (⟨w.length,le_rfl,w.get⟩ : JetIndex A.parameterDimension w.length) x +
      ((properSplits w).map (fun p =>
        G.ambient.eval (polynomialOperator chart p.1.length p.1.get (pivotPolynomial b D)) (G.embedding x) *
          normalizedJet A g b P (⟨p.2.length,le_rfl,p.2.get⟩ : JetIndex A.parameterDimension p.2.length) x)).sum := by
  have hfactor : evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x =ᶠ[𝓝 0]
      (fun z => evaluateCoefficientPolynomial A (substitutedPolynomial chart (pivotPolynomial b D)) x z *
        normalizedPullback A g b P x z) := by
    simpa only [evaluate_pivot_substitution] using chart_normalized_factorization chart b P D hP x hx
  have hderiv := (mixedDeriv_congr hfactor (w.map (fun i => Pi.single i (1 : K)))).self_of_nhds
  rw [mixedDeriv_map_mul _
    (evaluated_coefficients_analytic _ (substituted_coeff_analytic chart (pivotPolynomial b D)) x)
    (normalizedPullback_analytic A g b P x hx)] at hderiv
  have hj (v : List (Fin A.parameterDimension)) :
      mixedDeriv (v.map (fun i => Pi.single i (1 : K))) (normalizedPullback A g b P x) 0 =
        normalizedJet A g b P (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length) x :=
    mixedDeriv_map_eq_iteratedFDeriv _ (normalizedPullback_analytic A g b P x hx) v
  have hzero : polynomialOperator chart 0 Fin.elim0 (pivotPolynomial b D) =
      polynomialOperator chart ([] : List (Fin A.parameterDimension)).length [].get (pivotPolynomial b D) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [hzero]
  simpa only [polynomialOperator_eval_mixed,List.map_nil,mixedDeriv,hj] using hderiv

/-- The coefficients in the reverse generator expansion are balanced
homogeneous fractions on any source coordinate chart. -/
def polynomialJetCoefficient (chart : TranslationChart A g) (b c : CoordinateChart G)
    (D : G.FactorIndex → ℕ) (w : List (Fin A.parameterDimension)) : RationalCoefficient G :=
  ⟨polynomialOperator chart w.length w.get (pivotPolynomial b D),
    pivotPolynomial c (fun i => chart.degree i * D i),fun i => chart.degree i * D i,
    polynomialOperator_homogeneous chart _ _ _ D (pivotPolynomial_homogeneous b D),
    pivotPolynomial_homogeneous c _⟩

theorem polynomialJetCoefficient_regular (chart : TranslationChart A g) (b c : CoordinateChart G)
    (D : G.FactorIndex → ℕ) (w : List (Fin A.parameterDimension)) (x : G.Point)
    (hx : x ∈ chartDomain G c) :
    G.ambient.eval (polynomialJetCoefficient chart b c D w).denominator (G.embedding x) ≠ 0 :=
  pivotPolynomial_eval_ne_zero c _ x hx

theorem chartValue_polynomialOperator_jet_expansion (chart : TranslationChart A g)
    (b c : CoordinateChart G) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (w : List (Fin A.parameterDimension))
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    chartValue G c (polynomialOperator chart w.length w.get P) x =
      (polynomialJetCoefficient chart b c D []).value x *
        normalizedJet A g b P (⟨w.length,le_rfl,w.get⟩ : JetIndex A.parameterDimension w.length) x +
      ((properSplits w).map (fun p =>
        (polynomialJetCoefficient chart b c D p.1).value x *
          normalizedJet A g b P (⟨p.2.length,le_rfl,p.2.get⟩ : JetIndex A.parameterDimension p.2.length) x)).sum := by
  rw [chartValue_eq_div_pivot c _ _ (polynomialOperator_homogeneous chart _ _ P D hP),
    polynomialOperator_normalized_jet_expansion chart b P D hP w x hx,add_div]
  have hzero : polynomialOperator chart 0 Fin.elim0 (pivotPolynomial b D) =
      polynomialOperator chart ([] : List (Fin A.parameterDimension)).length [].get (pivotPolynomial b D) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [hzero]
  dsimp only [polynomialJetCoefficient,RationalCoefficient.value]
  congr 1
  · exact mul_div_right_comm _ _ _
  · induction properSplits w with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons,List.sum_cons,add_div,ih,mul_div_right_comm]
      rfl

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponReverseJetGenerators.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperator_order_congr (chart : TranslationChart A g) (P : G.CoordinateRing)
    {n m : ℕ} (h : n = m) (u : Fin n → Fin A.parameterDimension)
    (v : Fin m → Fin A.parameterDimension) (huv : ∀ i, u i = v (Fin.cast h i)) :
    polynomialOperator chart n u P = polynomialOperator chart m v P := by
  subst m
  have heq : u = v := by funext i; exact huv i
  rw [heq]

theorem polynomialOperator_ofFn (chart : TranslationChart A g) (P : G.CoordinateRing)
    (n : ℕ) (directions : Fin n → Fin A.parameterDimension) :
    polynomialOperator chart (List.ofFn directions).length (List.ofFn directions).get P =
      polynomialOperator chart n directions P := by
  apply polynomialOperator_order_congr chart P (List.length_ofFn ..)
  intro i
  simp only [List.get_ofFn]

theorem normalized_word_jet_localSpan (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (P : G.CoordinateRing) (hPI : P ∈ I)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (b : CoordinateChart G) (w : List (Fin A.parameterDimension)) (hw : w.length ≤ T)
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    LocalSpanAt (differentialSections A g T I)
      (normalizedJet A g b P (⟨w.length,le_rfl,w.get⟩ : JetIndex A.parameterDimension w.length)) x := by
  obtain ⟨a,ha⟩ := atlas.covers x
  obtain ⟨U,hU,hxU,hUa,hUb⟩ := exists_translation_pivot_neighborhood (atlas.chart a) b x ha hx
  let j : JetIndex A.parameterDimension T := ⟨w.length,hw,w.get⟩
  let f : differentialSections A g T I :=
    ⟨⟨{y | g+y ∈ chartDomain G b},normalizedJet A g b P j⟩,P,hPI,⟨D,hP⟩,b,j,rfl⟩
  exact localSpanAt_section _ f x U hU hxU (fun y hy => (hUb y hy).1)

theorem polynomialOperator_localSpan (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (chart : TranslationChart A g)
    (P : G.CoordinateRing) (hPI : P ∈ I) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (w : List (Fin A.parameterDimension)) (hw : w.length ≤ T)
    (c : CoordinateChart G) (x : G.Point) (hx : x ∈ chartDomain G c) :
    LocalSpanAt (differentialSections A g T I)
      (chartValue G c (polynomialOperator chart w.length w.get P)) x := by
  classical
  obtain ⟨b,hb⟩ := exists_chartDomain (g+x)
  have hterm (u v : List (Fin A.parameterDimension)) (hv : v.length ≤ T) :
      LocalSpanAt (differentialSections A g T I)
        (fun y => (polynomialJetCoefficient chart b c D u).value y *
          normalizedJet A g b P (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length) y) x :=
    (normalized_word_jet_localSpan atlas T I P hPI D hP b v hv x hb).rational_mul
      (polynomialJetCoefficient chart b c D u) (chartDomain G c) (chartDomain_isOpen c) hx
      (fun y hy => polynomialJetCoefficient_regular chart b c D u y hy)
  have hrest := LocalSpanAt.list_sum (properSplits w)
    (fun p y => (polynomialJetCoefficient chart b c D p.1).value y *
      normalizedJet A g b P (⟨p.2.length,le_rfl,p.2.get⟩ : JetIndex A.parameterDimension p.2.length) y) x
    (fun p hp => hterm p.1 p.2 (by have hh := (properSplits_lengths w p hp).2.2; omega))
  have hsum := (hterm [] w hw).add hrest
  obtain ⟨a,ha⟩ := atlas.covers x
  obtain ⟨U,hU,hxU,hUa,hUb⟩ := exists_translation_pivot_neighborhood (atlas.chart a) b x ha hb
  apply hsum.congr_on U hU hxU
  intro y hy
  exact (chartValue_polynomialOperator_jet_expansion chart b c P D hP w y (hUb y hy).1).symm

theorem polynomialOperatorIdeal_le_localSectionIdeal (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (b : CoordinateChart G) (x : G.Point)
    (hx : x ∈ chartDomain G b) :
    polynomialOperatorIdeal atlas T I ≤ localSectionIdeal (differentialSections A g T I) b x hx := by
  apply sup_le (groupIdeal_le_localSectionIdeal _ b x hx)
  apply Ideal.span_le.mpr
  rintro Q ⟨P,hPI,⟨D,hP⟩,a,n,hn,dirs,rfl⟩
  change LocalSpanAt _ (chartValue G b (polynomialOperator (atlas.chart a) n dirs P)) x
  rw [← polynomialOperator_ofFn]
  exact polynomialOperator_localSpan atlas T I (atlas.chart a) P hPI D hP
    (List.ofFn dirs) (by simpa using hn) b x hx

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponReverseJetComparison.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

/-- Local sections of the polynomial operator ideal are locally generated by
the actual normalized analytic jets, preserving the full ideal structure. -/
theorem local_polynomial_jet_ideal_le_differentialIdeal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    translatedIdeal G 0 (polynomialOperatorIdeal atlas T I) ≤ differentialIdeal A g T I := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  apply Ideal.subset_span
  refine ⟨⟨D,hD⟩,(locallyGenerated_iff_localSpan _ P).mpr ?_⟩
  intro x
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hP x
  have hsec (i : Fin n) :
      LocalSpanAt (differentialSections A g T I) (f i).val.value x := by
    obtain ⟨Q,hQ,⟨E,hE⟩,c,hfeq⟩ := (f i).property
    have hc : x ∈ chartDomain G c := by
      simpa only [hfeq,zero_add,Set.mem_setOf_eq] using (hfr i x hx).1
    have hh := polynomialOperatorIdeal_le_localSectionIdeal atlas T I c x hc hQ
    change LocalSpanAt (differentialSections A g T I) (chartValue G c Q) x at hh
    simpa only [hfeq,zero_add] using hh
  have hterms (i : Fin n) :=
    (hsec i).rational_mul (r i) U hU hx (fun y hy => (hfr i y hy).2)
  have hsum := LocalSpanAt.fin_sum
    (fun i y => (r i).value y * (f i).val.value y) x hterms
  refine ⟨b,hUb hx,hsum.congr_on U hU hx ?_⟩
  intro y hy
  exact (heq y hy).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalIdealComparison.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem translatedIdeal_zero_le_retainOnGroup
    (I : Ideal G.CoordinateRing) (hG : G.vanishingIdeal Set.univ ≤ I) :
    translatedIdeal G 0 I ≤ retainOnGroup G I := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  apply (Submodule.mem_iInf _).mpr
  intro x
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hP x.point
  have hf (i : Fin n) : ∃ Q ∈ I, ∃ E : G.FactorIndex → ℕ,
      G.ambient.IsHomogeneous Q E ∧ ∃ c : CoordinateChart G,
        (f i).val = ⟨{y | 0 + y ∈ chartDomain G c}, fun y => chartValue G c Q (0 + y)⟩ := by
    obtain ⟨Q,hQI,⟨E,hQE⟩,c,hc⟩ := (f i).property
    exact ⟨Q,hQI,E,hQE,c,hc⟩
  choose Q hQI E hQE c hfeq using hf
  let R : Fin n → RationalCoefficient G := fun i =>
    ⟨(r i).numerator * Q i, (r i).denominator * pivotPolynomial (c i) (E i),
      (r i).degree + E i, (r i).numerator_homogeneous.mul G.ambient (hQE i),
      (r i).denominator_homogeneous.mul G.ambient (pivotPolynomial_homogeneous (c i) (E i))⟩
  have hRden (i : Fin n) (y : G.Point) (hy : y ∈ U) :
      G.ambient.eval (R i).denominator (G.embedding y) ≠ 0 := by
    have hdom : y ∈ chartDomain G (c i) := by
      simpa only [hfeq i, zero_add, Set.mem_setOf_eq] using (hfr i y hy).1
    change G.ambient.eval ((r i).denominator * pivotPolynomial (c i) (E i)) (G.embedding y) ≠ 0
    simp only [MultiProjectiveSpace.eval, map_mul]
    exact mul_ne_zero (hfr i y hy).2 (pivotPolynomial_eval_ne_zero (c i) (E i) y hdom)
  have hRval (i : Fin n) (y : G.Point) :
      (R i).value y = (r i).value y * (f i).val.value y := by
    simp only [hfeq i, zero_add]
    rw [chartValue_eq_div_pivot (c i) (Q i) (E i) (hQE i) y]
    simp only [R, RationalCoefficient.value, MultiProjectiveSpace.eval, map_mul]
    exact (div_mul_div_comm _ _ _ _).symm
  obtain ⟨s,hsI,hs⟩ := exists_rational_sum R I (fun i => I.mul_mem_left _ (hQI i))
  apply local_fraction_identity_mem_retained I hG P D hD x b U hU hx hUb s hsI
  · intro y hy
    exact (hs y (fun i => hRden i y hy)).1
  · intro y hy
    rw [(hs y (fun i => hRden i y hy)).2,heq y hy]
    apply Finset.sum_congr rfl
    intro i _
    exact (hRval i y).symm

/-- Local polynomial-section generation equals primary-component retention,
as actual ideals including nilpotent multiplicities. -/
theorem retainOnGroup_eq_translatedIdeal_zero
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (hG : G.vanishingIdeal Set.univ ≤ I) :
    retainOnGroup G I = translatedIdeal G 0 I :=
  le_antisymm (retainOnGroup_le_translatedIdeal_zero I hI)
    (translatedIdeal_zero_le_retainOnGroup I hG)

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponPolynomialIdealHomogeneous.lean

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

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperatorIdeal_homogeneous (atlas : TranslationAtlas A g) (T : ℕ)
    (I : Ideal G.CoordinateRing) : IsMultihomogeneousIdeal G.ambient (polynomialOperatorIdeal atlas T I) := by
  unfold polynomialOperatorIdeal EmbeddedGroupProduct.vanishingIdeal MultiProjectiveSpace.vanishingIdeal
  rw [← Ideal.span_union]
  apply homogeneous_span
  rintro Q (hQ | ⟨P,hPI,⟨D,hD⟩,a,n,hn,dirs,rfl⟩)
  · exact hQ.1
  · exact ⟨fun i => (atlas.chart a).degree i * D i,
      polynomialOperator_homogeneous (atlas.chart a) n dirs P D hD⟩

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponJetIdealInclusion.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem locallyGeneratedIdeal_le_retention_of_fractions
    (I : Ideal G.CoordinateRing) (hG : G.vanishingIdeal Set.univ ≤ I)
    (S : Set (LocalSection G))
    (hS : ∀ f ∈ S, ∀ x ∈ f.domain,
      ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
        ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
          ∀ y ∈ U, G.ambient.eval r.denominator (G.embedding y) ≠ 0 ∧ r.value y = f.value y) :
    locallyGeneratedIdeal G S ≤ retainOnGroup G I := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  apply (Submodule.mem_iInf _).mpr
  intro x
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hP x.point
  have hf (i : Fin n) := hS (f i).val (f i).property x.point (hfr i x.point hx).1
  choose V hVo hxV s hsI hs using hf
  let W := U ∩ ⋂ i, V i
  have hWo : @IsOpen _ G.zariskiTopology W := hU.inter (isOpen_iInter_of_finite hVo)
  have hxW : x.point ∈ W := ⟨hx,Set.mem_iInter.mpr hxV⟩
  have hWV (y : G.Point) (hy : y ∈ W) (i : Fin n) : y ∈ V i := Set.mem_iInter.mp hy.2 i
  let R := fun i => rationalMul (r i) (s i)
  have hRI (i : Fin n) : (R i).numerator ∈ I := I.mul_mem_left _ (hsI i)
  have hRden (i : Fin n) (y : G.Point) (hy : y ∈ W) :
      G.ambient.eval (R i).denominator (G.embedding y) ≠ 0 :=
    rationalMul_denominator_ne_zero _ _ y (hfr i y hy.1).2 (hs i y (hWV y hy i)).1
  have hRval (i : Fin n) (y : G.Point) (hy : y ∈ W) :
      (R i).value y = (r i).value y * (f i).val.value y := by
    rw [rationalMul_value,(hs i y (hWV y hy i)).2]
  obtain ⟨t,htI,ht⟩ := exists_rational_sum R I hRI
  apply local_fraction_identity_mem_retained I hG P D hD x b W hWo hxW
    (fun _ hy => hUb hy.1) t htI
  · intro y hy
    exact (ht y (fun i => hRden i y hy)).1
  · intro y hy
    rw [(ht y (fun i => hRden i y hy)).2,heq y hy.1]
    exact Finset.sum_congr rfl (fun i _ => (hRval i y hy).symm)

variable [CompleteSpace K] {A : AnalyticSubgroup G} {g : G.Point}

theorem differentialIdeal_le_retainedPolynomialOperatorIdeal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T I ≤ retainedPolynomialOperatorIdeal atlas T I := by
  apply locallyGeneratedIdeal_le_retention_of_fractions _ le_sup_left
  rintro f ⟨P,hPI,⟨D,hP⟩,b,j,rfl⟩ x hx
  exact normalizedJet_rational_fraction atlas T I P hPI D hP b j x hx

theorem differentialIdeal_le_local_polynomial_jet_ideal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T I ≤ translatedIdeal G 0 (polynomialOperatorIdeal atlas T I) := by
  have h := differentialIdeal_le_retainedPolynomialOperatorIdeal atlas T I
  unfold retainedPolynomialOperatorIdeal at h
  rwa [retainOnGroup_eq_translatedIdeal_zero _ (polynomialOperatorIdeal_homogeneous atlas T I)
    le_sup_left] at h

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponJetComparisonCompleted.lean

set_option autoImplicit false
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem differentialIdeal_eq_local_polynomial_jet_ideal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T I = translatedIdeal G 0 (polynomialOperatorIdeal atlas T I) :=
  le_antisymm (differentialIdeal_le_local_polynomial_jet_ideal atlas T I)
    (local_polynomial_jet_ideal_le_differentialIdeal atlas T I)

theorem retainedPolynomialOperatorIdeal_eq_differentialIdeal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    retainedPolynomialOperatorIdeal atlas T I = differentialIdeal A g T I :=
  (retainOnGroup_eq_translatedIdeal_zero _ (polynomialOperatorIdeal_homogeneous atlas T I)
    le_sup_left).trans (differentialIdeal_eq_local_polynomial_jet_ideal atlas T I).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponCosetMultiplicitySetup.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [Field K] {G : EmbeddedGroupProduct K}

theorem AlgebraicSubgroup.componentMeetsGroup_coset (H : AlgebraicSubgroup G) (g : G.Point) :
    ComponentMeetsGroup G (G.vanishingIdeal (translate g H.carrier)) := by
  refine ⟨g,fun P hP => ?_⟩
  exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal hP
    ⟨g,⟨0,H.toAddSubgroup.zero_mem,add_zero g⟩,rfl⟩

theorem incomplete_coset_minimalPrime (H : AlgebraicSubgroup G) (hH : H.IsConnected)
    (g : G.Point) (I : Ideal G.CoordinateRing)
    (hI : IncompletelyDefines G I (translate g H.carrier)) :
    G.vanishingIdeal (translate g H.carrier) ∈ (G.vanishingIdeal Set.univ ⊔ I).minimalPrimes := by
  letI := H.translated_vanishingIdeal_isPrime hH g
  exact hI.2 _ (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _)
    (H.componentMeetsGroup_coset g)

theorem incomplete_coset_le (H : AlgebraicSubgroup G) (hH : H.IsConnected)
    (g : G.Point) (I : Ideal G.CoordinateRing)
    (hI : IncompletelyDefines G I (translate g H.carrier)) :
    I ≤ G.vanishingIdeal (translate g H.carrier) :=
  le_sup_right.trans (incomplete_coset_minimalPrime H hH g I hI).1.2

/-- For a connected coset the multiplicity target is exactly one actual
localized quotient length, since its vanishing ideal is prime. -/
theorem coset_multiplicity_iff_localLength (H : AlgebraicSubgroup G) (hH : H.IsConnected)
    (g : G.Point) (I : Ideal G.CoordinateRing)
    (hI : IncompletelyDefines G I (translate g H.carrier)) (ell : ℕ) :
    IncompletelyDefinesWithMultiplicityAtLeast G I (translate g H.carrier) ell ↔
      (ell : ℕ∞) ≤ Hilbert.localLength K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ ⊔ I)
        ⟨G.vanishingIdeal (translate g H.carrier),H.translated_vanishingIdeal_isPrime hH g⟩ := by
  letI := H.translated_vanishingIdeal_isPrime hH g
  constructor
  · intro h
    exact h.2 _ (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _)
      (H.componentMeetsGroup_coset g)
  · intro h
    refine ⟨hI,?_⟩
    intro q hq _
    rw [Ideal.minimalPrimes_eq_subsingleton_self,Set.mem_singleton_iff] at hq
    have heq : q = ⟨G.vanishingIdeal (translate g H.carrier),
        H.translated_vanishingIdeal_isPrime hH g⟩ := PrimeSpectrum.ext hq
    simpa only [heq] using h

end PhilipponMultiplicity

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

/-- The prolongation hypothesis of Proposition 4.7 implies membership in
the actual coset prime for every polynomial chart derivative up to order T. -/
theorem polynomialOperator_mem_coset_of_incomplete_differential
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (I : Ideal G.CoordinateRing) (T : ℕ)
    (hprolongation : IncompletelyDefines G (differentialIdeal A 0 T I)
      (translate g H.carrier)) (atlas : TranslationAtlas A 0)
    (P : G.CoordinateRing) (hPI : P ∈ I)
    (hP : ∃ D, G.ambient.IsHomogeneous P D)
    (a : atlas.Index) (n : ℕ) (hn : n ≤ T) (directions : Fin n → Fin A.parameterDimension) :
    polynomialOperator (atlas.chart a) n directions P ∈
      G.vanishingIdeal (translate g H.carrier) := by
  apply incomplete_coset_le H hH g _ hprolongation
  rw [← retainedPolynomialOperatorIdeal_eq_differentialIdeal atlas T I]
  apply le_retainOnGroup G _
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨P,hPI,hP,a,n,hn,directions,rfl⟩)

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponOrbitLocality.lean

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

/-- A sufficiently short orbit stays in any prescribed Zariski neighborhood
of its initial point. This justifies pulling back local ideal expressions. -/
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

theorem rationalCoefficient_value_of_lift (r : RationalCoefficient G) (g : G.Point)
    (v : G.ambient.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = G.embedding g i) :
    MvPolynomial.eval v r.numerator / MvPolynomial.eval v r.denominator = r.value g := by
  classical
  have ha (i : G.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i,j⟩ = (a : K) * (G.embedding g i).rep j := by
    obtain ⟨h,heq⟩ := hv i
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (G.embedding g i).rep_nonzero).mp (heq.trans (G.embedding g i).mk_rep.symm)
    exact ⟨a,fun j => by
      simpa only [Pi.smul_apply,Units.smul_def,smul_eq_mul] using (congrFun ha j).symm⟩
  choose a ha using ha
  have hcoords : v = fun q => (a q.1 : K) * G.ambient.coordinate (G.embedding g) q := by
    funext q
    exact ha q.1 q.2
  rw [hcoords,G.ambient.eval_block_scale r.numerator r.degree r.numerator_homogeneous
      (G.ambient.coordinate (G.embedding g)) (fun i => (a i : K)),
    G.ambient.eval_block_scale r.denominator r.degree r.denominator_homogeneous
      (G.ambient.coordinate (G.embedding g)) (fun i => (a i : K))]
  exact mul_div_mul_left _ _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero))

theorem rational_orbit_pullback_germ (A : AnalyticSubgroup G) (g : G.Point)
    (r : RationalCoefficient G) :
    (fun z : A.ParameterSpace => if hz : z ∈ A.domain then r.value (g+A.map ⟨z,hz⟩) else 0)
      =ᶠ[𝓝 0] (fun z => A.pullback r.numerator g z / A.pullback r.denominator g z) := by
  filter_upwards [A.lift_represents g] with z hrep
  obtain ⟨hz,hrep⟩ := hrep
  rw [dif_pos hz]
  exact (rationalCoefficient_value_of_lift r _ _ hrep).symm

/-- Regular rational coefficients become analytic coefficients along the
orbit germ, provided their actual denominator is nonzero at the initial point. -/
theorem rational_orbit_pullback_analytic (A : AnalyticSubgroup G) (g : G.Point)
    (r : RationalCoefficient G) (hr : G.ambient.eval r.denominator (G.embedding g) ≠ 0) :
    AnalyticAt K
      (fun z : A.ParameterSpace => if hz : z ∈ A.domain then r.value (g+A.map ⟨z,hz⟩) else 0) 0 := by
  have h0 : A.pullback r.denominator g 0 ≠ 0 :=
    (not_congr (G.ambient.eval_eq_zero_iff_of_lift (G.embedding g) (A.lift g 0)
      (lift_zero_represents A g) r.denominator r.degree r.denominator_homogeneous)).mpr hr
  exact ((polynomialPullback_analytic A g r.numerator).div
    (polynomialPullback_analytic A g r.denominator) h0).congr
      (rational_orbit_pullback_germ A g r).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponPolynomialMapCharts.lean

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
-- Implementation: Solutions/PhilipponPolynomialChartLifts.lean

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
-- Implementation: Solutions/PhilipponTangentTransport.lean

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

/-- Pulling an equation back by the regular translation by `-x`, then
multiplying by the chart cuts, gives a global equation of `x + V`. Near
`x` the cuts are units, so its derivative detects the original direction. -/
theorem AnalyticSubgroup.mem_tangentKernel_of_translated_equations
    (A : AnalyticSubgroup G) (V : Set G.Point) (hV : (0 : G.Point) ∈ V)
    (x : G.Point) (v : A.ParameterSpace)
    (hd : ∀ Q ∈ G.vanishingIdeal (translate x V),
      fderiv K (A.pullback Q x) 0 v = 0) :
    v ∈ A.tangentKernel V := by
  classical
  apply (Submodule.mem_iInf _).mpr
  intro P
  change fderiv K (A.pullback P.val 0) 0 v = 0
  apply A.fderiv_zero_of_homogeneous_equations V 0 hV v _ P.val P.property
  rintro P ⟨D,hP⟩ hPV
  have hPI : P ∈ G.vanishingIdeal V :=
    Ideal.subset_span ⟨⟨D,hP⟩,by rintro _ ⟨y,hy,rfl⟩; exact hPV y hy⟩
  have hP0 : A.pullback P 0 0 = 0 :=
    G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
      (Set.mem_image_of_mem G.embedding hV) _ (lift_zero_represents A 0) hPI
  choose chart hchart using
    (fun i => (G.translation_regular (-x)).exists_polynomialMapChart x i)
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
    dsimp only [R,MultiProjectiveSpace.eval]
    rw [← eval_assoc]
    rfl
  have hsR : s*R ∈ G.vanishingIdeal (translate x V) := by
    apply Ideal.subset_span
    refine ⟨⟨E+F,hs.mul G.ambient hR⟩,?_⟩
    rintro _ ⟨y,hy,rfl⟩
    change G.ambient.eval (s*R) (G.embedding y) = 0
    rw [show G.ambient.eval (s*R) (G.embedding y) =
      G.ambient.eval s (G.embedding y) * G.ambient.eval R (G.embedding y) from map_mul _ _ _]
    by_cases hsy : G.ambient.eval s (G.embedding y) = 0
    · rw [hsy,zero_mul]
    · have hcuts : ∀ i, G.ambient.eval (chart i).cut (G.embedding y) ≠ 0 := by
        have hp : (∏ i, G.ambient.eval (chart i).cut (G.embedding y)) ≠ 0 :=
          (hseval y) ▸ hsy
        exact fun i => (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
      have hyV : y+(-x) ∈ V := by
        obtain ⟨z,hz,rfl⟩ := hy
        simpa only [add_comm x z,add_neg_cancel_right] using hz
      have hz : G.ambient.eval R (G.embedding y) = 0 := by
        rw [hReval]
        apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
          (Set.mem_image_of_mem G.embedding hyV) _ _ hPI
        exact fun i => (chart i).represents y (hcuts i)
      rw [hz,mul_zero]
  let f (z : A.ParameterSpace) (q : G.ambient.Variable) :=
    MvPolynomial.eval (A.lift x z) (coords q)
  have hf (q) : AnalyticAt K (fun z => f z q) 0 :=
    polynomialPullback_analytic A x (coords q)
  have hcut0 (i : G.FactorIndex) : A.pullback (chart i).cut x 0 ≠ 0 :=
    (G.ambient.eval_eq_zero_iff_of_lift (G.embedding x) (A.lift x 0)
      (lift_zero_represents A x) _ _ (chart i).cut_homogeneous).not.mpr (hchart i)
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ i,
      A.pullback (chart i).cut x z ≠ 0 := by
    rw [Filter.eventually_all]
    exact fun i => (polynomialPullback_analytic A x _).continuousAt.eventually_ne (hcut0 i)
  have hrep : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ i : G.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i,j⟩) ≠ 0,
      ∃ hgi : (fun j => A.lift 0 z ⟨i,j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i,j⟩) hfi =
          Projectivization.mk K (fun j => A.lift 0 z ⟨i,j⟩) hgi := by
    filter_upwards [hnear,A.lift_represents x,A.lift_represents 0] with z hz hzx hz0
    obtain ⟨hzx,hxlift⟩ := hzx
    obtain ⟨hz0,h0lift⟩ := hz0
    have hsame : (⟨z,hzx⟩ : A.domain) = ⟨z,hz0⟩ := Subtype.ext rfl
    intro i
    obtain ⟨hn,heq⟩ := (chart i).represents_lift (x+A.map ⟨z,hzx⟩)
      (A.lift x z) hxlift (hz i)
    obtain ⟨hn0,heq0⟩ := h0lift i
    refine ⟨hn,hn0,heq.trans ?_⟩
    rw [heq0,hsame]
    exact congrArg (fun y => G.embedding y i) (by abel)
  have hRpull : A.pullback R x = fun z => MvPolynomial.eval (f z) P := by
    funext z
    dsimp only [AnalyticSubgroup.pullback,R,f]
    rw [← eval_assoc]
    rfl
  have hR0 : A.pullback R x 0 = 0 := by
    rw [hRpull]
    apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
      (Set.mem_image_of_mem G.embedding hV) _ _ hPI
    intro i
    obtain ⟨hn,hn0,heq⟩ := hrep.self_of_nhds i
    obtain ⟨hn',heq'⟩ := lift_zero_represents A 0 i
    exact ⟨hn,heq.trans heq'⟩
  have hs0 : A.pullback s x 0 ≠ 0 := by
    change MvPolynomial.eval (A.lift x 0) (∏ i, (chart i).cut) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hcut0 i)
  have hsd := hd (s*R) hsR
  have hmul : A.pullback (s*R) x = fun z => A.pullback s x z * A.pullback R x z := by
    funext z; exact map_mul _ _ _
  rw [hmul,fderiv_fun_mul (polynomialPullback_analytic A x s).differentiableAt
    (polynomialPullback_analytic A x R).differentiableAt] at hsd
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    hR0,smul_eq_mul,zero_mul,add_zero] at hsd
  have hRd : fderiv K (A.pullback R x) 0 v = 0 := (mul_eq_zero.mp hsd).resolve_left hs0
  rw [hRpull] at hRd
  exact (G.ambient.fderiv_eval_zero_iff_of_projective_lifts P D hP f (A.lift 0)
    0 v hf (A.lift_analytic 0) hrep hP0).mp hRd

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponTangentCoordinates.lean

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [NontriviallyNormedField K]
variable {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)

theorem AnalyticSubgroup.tangentKernel_mono {V W : Set G.Point} (h : V ⊆ W) :
    A.tangentKernel V ≤ A.tangentKernel W := by
  have hi : G.vanishingIdeal W ≤ G.vanishingIdeal V :=
    G.ambient.vanishingIdeal_antitone (Set.image_mono h)
  apply le_iInf
  intro P
  exact iInf_le_of_le ⟨P.val, hi P.property⟩ le_rfl

theorem analyticCodimension_le_dimension (H : AlgebraicSubgroup G) :
    analyticCodimension A H.carrier ≤ A.dimension := by
  have hk : A.tangentKernel {0} ≤ A.tangentKernel H.carrier :=
    A.tangentKernel_mono (Set.singleton_subset_iff.mpr H.toAddSubgroup.zero_mem)
  exact Nat.sub_le_sub_left (Submodule.finrank_mono hk) A.parameterDimension

theorem analyticCodimension_eq_finrank_quotient (V : Set G.Point) :
    analyticCodimension A V = Module.finrank K
      (A.ParameterSpace ⧸ A.tangentKernel V) := by
  have h := (A.tangentKernel V).finrank_quotient_add_finrank
  have hp : Module.finrank K A.ParameterSpace = A.parameterDimension := by
    simp [AnalyticSubgroup.ParameterSpace]
  rw [hp] at h
  unfold analyticCodimension
  omega

/-- Select a basis of the tangent quotient from the original parameter axes.
This is the coordinate reindexing used on Philippon, p. 377. -/
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
-- Implementation: Solutions/PhilipponTransverseRank.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem AlgebraicSubgroup.translate_eq_of_mem (H : AlgebraicSubgroup G)
    (g x : G.Point) (hx : x ∈ translate g H.carrier) :
    translate x H.carrier = translate g H.carrier := by
  obtain ⟨h,hh,rfl⟩ := hx
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨h+z,H.toAddSubgroup.add_mem hh hz,by ext i; simp [add_assoc]⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨-h+z,H.toAddSubgroup.add_mem (H.toAddSubgroup.neg_mem hh) hz,
      by ext i; simp [add_assoc]⟩

/-- The geometric implication in Philippon's rank argument: if all coset
equations annihilate a direction at `x`, it is in the identity tangent kernel. -/
theorem AnalyticSubgroup.mem_tangentKernel_of_coset_equations
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g x : G.Point)
    (hx : x ∈ translate g H.carrier) (v : A.ParameterSpace)
    (hd : ∀ Q ∈ G.vanishingIdeal (translate g H.carrier),
      fderiv K (A.pullback Q x) 0 v = 0) :
    v ∈ A.tangentKernel H.carrier := by
  apply A.mem_tangentKernel_of_translated_equations H.carrier H.toAddSubgroup.zero_mem x v
  simpa only [H.translate_eq_of_mem g x hx] using hd

/-- Actual homogeneous equations of the coset have independent directional
derivatives on the specified transverse axes. No rank assumption is added. -/
theorem transverse_equation_derivatives_linearIndependent
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g x : G.Point)
    (hx : x ∈ translate g H.carrier)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions) :
    LinearIndependent K (fun i => fun Q :
      {Q : G.CoordinateRing // Q ∈ G.vanishingIdeal (translate g H.carrier) ∧
        ∃ D, G.ambient.IsHomogeneous Q D} =>
      fderiv K (A.pullback Q.val x) 0 (Pi.single (directions i) 1)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let v : A.ParameterSpace := ∑ i, c i • Pi.single (directions i) 1
  have hd : ∀ Q ∈ G.vanishingIdeal (translate g H.carrier),
      fderiv K (A.pullback Q x) 0 v = 0 := by
    intro Q hQ
    apply A.fderiv_zero_of_homogeneous_equations _ x hx v _ Q hQ
    intro P hP hzero
    have hPI : P ∈ G.vanishingIdeal (translate g H.carrier) :=
      Ideal.subset_span ⟨hP,by rintro _ ⟨y,hy,rfl⟩; exact hzero y hy⟩
    have he := congrFun hc ⟨P,hPI,hP⟩
    simpa only [v,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,Pi.zero_apply] using he
  have hv := A.mem_tangentKernel_of_coset_equations H g x hx v hd
  have hquot : ∑ i, c i • (A.tangentKernel H.carrier).mkQ (Pi.single (directions i) 1) = 0 := by
    simp_rw [← map_smul]
    rw [← map_sum]
    change (A.tangentKernel H.carrier).mkQ v = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hv
  exact Fintype.linearIndependent_iff.mp htransverse.1 c hquot

/-- A finite square minor witnessing full rank at a specified coset point,
chosen from genuine homogeneous equations. -/
theorem exists_transverse_derivative_minor
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g x : G.Point)
    (hx : x ∈ translate g H.carrier)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions) :
    ∃ Q : Fin (analyticCodimension A H.carrier) → G.CoordinateRing,
      (∀ j, Q j ∈ G.vanishingIdeal (translate g H.carrier)) ∧
      (∀ j, ∃ D, G.ambient.IsHomogeneous (Q j) D) ∧
      (Matrix.of (fun i j => fderiv K (A.pullback (Q j) x) 0
        (Pi.single (directions i) 1))).det ≠ 0 := by
  classical
  let T := {Q : G.CoordinateRing // Q ∈ G.vanishingIdeal (translate g H.carrier) ∧
    ∃ D, G.ambient.IsHomogeneous Q D}
  let col (Q : T) (i : Fin (analyticCodimension A H.carrier)) :=
    fderiv K (A.pullback Q.val x) 0 (Pi.single (directions i) 1)
  have hspan : Submodule.span K (Set.range col) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr
      (transverse_equation_derivatives_linearIndependent A H g x hx directions htransverse)
  obtain ⟨κ,a,ha,hsp,hli⟩ := exists_linearIndependent' K col
  rw [hspan] at hsp
  let b : Module.Basis κ K (Fin (analyticCodimension A H.carrier) → K) :=
    Module.Basis.mk hli hsp.ge
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : Fintype.card κ = analyticCodimension A H.carrier := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let e : κ ≃ Fin (analyticCodimension A H.carrier) :=
    (Fintype.equivFin κ).trans (finCongr hc)
  refine ⟨fun j => (a (e.symm j)).val,fun j => (a (e.symm j)).property.1,
    fun j => (a (e.symm j)).property.2,?_⟩
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  exact hli.comp e.symm e.symm.injective

/-- Equalize the equation degrees with pivot monomials nonzero at `x`.
This preserves the nonzero derivative minor. -/
theorem exists_uniform_transverse_derivative_minor
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g x : G.Point)
    (hx : x ∈ translate g H.carrier)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions) :
    ∃ D : G.FactorIndex → ℕ,
    ∃ Q : Fin (analyticCodimension A H.carrier) → G.CoordinateRing,
      (∀ j, Q j ∈ G.vanishingIdeal (translate g H.carrier)) ∧
      (∀ j, G.ambient.IsHomogeneous (Q j) D) ∧
      (Matrix.of (fun i j => fderiv K (A.pullback (Q j) x) 0
        (Pi.single (directions i) 1))).det ≠ 0 := by
  classical
  obtain ⟨Q,hQI,hQ,hdet⟩ := exists_transverse_derivative_minor A H g x hx directions htransverse
  choose d hd using hQ
  obtain ⟨b,hb⟩ := exists_chartDomain x
  let D : G.ambient.FactorIndex → ℕ := ∑ j, d j
  let B (j : Fin (analyticCodimension A H.carrier)) := pivotPolynomial b (D-d j)
  have hdD (j : Fin (analyticCodimension A H.carrier)) : d j ≤ D := by
    intro i
    simpa only [D,Finset.sum_apply] using
      Finset.single_le_sum (fun k _ => Nat.zero_le (d k i)) (Finset.mem_univ j)
  have hB (j) : G.ambient.IsHomogeneous (B j) (D-d j) := pivotPolynomial_homogeneous _ _
  have hB0 (j) : A.pullback (B j) x 0 ≠ 0 :=
    (G.ambient.eval_eq_zero_iff_of_lift (G.embedding x) (A.lift x 0)
      (lift_zero_represents A x) _ _ (hB j)).not.mpr (pivotPolynomial_eval_ne_zero b _ x hb)
  have hQ0 (j) : A.pullback (Q j) x 0 = 0 :=
    G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal (Set.mem_image_of_mem G.embedding hx)
      _ (lift_zero_represents A x) (hQI j)
  refine ⟨D,fun j => B j * Q j,
    fun j => (G.vanishingIdeal _).mul_mem_left _ (hQI j),?_,?_⟩
  · intro j
    have hh := (hB j).mul G.ambient (hd j)
    have hdeg : (D-d j)+d j = D := by
      funext i
      exact Nat.sub_add_cancel (hdD j i)
    exact hdeg ▸ hh
  · have he (i j) : fderiv K (A.pullback (B j * Q j) x) 0 (Pi.single (directions i) 1) =
        A.pullback (B j) x 0 * fderiv K (A.pullback (Q j) x) 0 (Pi.single (directions i) 1) := by
      have hmul : A.pullback (B j * Q j) x =
          fun z => A.pullback (B j) x z * A.pullback (Q j) x z := by
        funext z; exact map_mul _ _ _
      rw [hmul,fderiv_fun_mul (polynomialPullback_analytic A x _).differentiableAt
        (polynomialPullback_analytic A x _).differentiableAt]
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
        hQ0 j,smul_eq_mul,zero_mul,add_zero]
    simp_rw [he]
    rw [Matrix.det_mul_row]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => hB0 j)) hdet

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponTransverseOperators.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

def chartPullback (chart : TranslationChart A 0) (P : G.CoordinateRing) (x : G.Point) :=
  evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x

theorem chartPullback_analytic (chart : TranslationChart A 0)
    (P : G.CoordinateRing) (x : G.Point) : AnalyticAt K (chartPullback chart P x) 0 :=
  evaluated_coefficients_analytic _ (substituted_coeff_analytic chart P) x

theorem chartPullback_mul (chart : TranslationChart A 0)
    (P Q : G.CoordinateRing) (x : G.Point) :
    chartPullback chart (P*Q) x = fun z => chartPullback chart P x z * chartPullback chart Q x z := by
  funext z
  simp only [chartPullback,evaluate_substituted,map_mul]

theorem first_operator_eval (chart : TranslationChart A 0)
    (P : G.CoordinateRing) (x : G.Point) (i : Fin A.parameterDimension) :
    G.ambient.eval (polynomialOperator chart 1 (fun _ => i) P) (G.embedding x) =
      fderiv K (chartPullback chart P x) 0 (Pi.single i 1) := by
  rw [polynomialOperator_eval,iteratedFDeriv_one_apply]
  congr 2
  funext z
  exact (evaluate_substituted chart P x z).symm

theorem chart_zero_represents (chart : TranslationChart A 0)
    (x : G.Point) (hx : x ∈ chart.domain) :
    ∀ i : G.FactorIndex,
      ∃ hn : (fun j => evaluateCoefficientPolynomial A (chart.coordinates ⟨i,j⟩) x 0) ≠ 0,
        Projectivization.mk K (fun j => evaluateCoefficientPolynomial A
          (chart.coordinates ⟨i,j⟩) x 0) hn = G.embedding x i := by
  obtain ⟨hz,hrep⟩ := (chart.represents x hx).self_of_nhds
  have he : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  simpa only [he,A.map_zero,add_zero] using hrep

theorem chartPullback_zero_of_mem (chart : TranslationChart A 0)
    (V : Set G.Point) (P : G.CoordinateRing) (hP : P ∈ G.vanishingIdeal V)
    (x : G.Point) (hx : x ∈ chart.domain) (hxV : x ∈ V) :
    chartPullback chart P x 0 = 0 := by
  rw [chartPullback,evaluate_substituted]
  exact G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
    (Set.mem_image_of_mem G.embedding hxV)
    (fun q => evaluateCoefficientPolynomial A (chart.coordinates q) x 0)
    (chart_zero_represents chart x hx) hP

/-- At a chart point the degree-dependent scale is shared by every
homogeneous polynomial of that degree. -/
theorem chartPullback_zero_scales (chart : TranslationChart A 0)
    (x : G.Point) (hx : x ∈ chart.domain) :
    ∃ a : G.ambient.FactorIndex → Kˣ, ∀ P : G.CoordinateRing, ∀ D : G.ambient.FactorIndex → ℕ,
      G.ambient.IsHomogeneous P D →
      chartPullback chart P x 0 = (∏ i, (a i : K) ^ D i) * G.ambient.eval P (G.embedding x) := by
  classical
  have hh (i : G.ambient.FactorIndex) : ∃ a : Kˣ, ∀ j,
      evaluateCoefficientPolynomial A (chart.coordinates ⟨i,j⟩) x 0 =
        (a : K) * (G.embedding x i).rep j := by
    obtain ⟨hn,heq⟩ := chart_zero_represents chart x hx i
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ hn (G.embedding x i).rep_nonzero).mp
      (heq.trans (G.embedding x i).mk_rep.symm)
    exact ⟨a,fun j => by
      simpa only [Pi.smul_apply,Units.smul_def,smul_eq_mul] using (congrFun ha j).symm⟩
  choose a ha using hh
  refine ⟨a,?_⟩
  intro P D hP
  rw [chartPullback,evaluate_substituted]
  have he : (fun q => evaluateCoefficientPolynomial A (chart.coordinates q) x 0) =
      fun q => (a q.1 : K) * G.ambient.coordinate (G.embedding x) q := by
    funext q; exact ha q.1 q.2
  rw [he]
  exact G.ambient.eval_block_scale P D hP
    (G.ambient.coordinate (G.embedding x)) (fun i => (a i : K))

theorem first_operator_mul_eval (chart : TranslationChart A 0)
    (P Q : G.CoordinateRing) (x : G.Point) (i : Fin A.parameterDimension)
    (hQ : chartPullback chart Q x 0 = 0) :
    G.ambient.eval (polynomialOperator chart 1 (fun _ => i) (P*Q)) (G.embedding x) =
      chartPullback chart P x 0 *
        G.ambient.eval (polynomialOperator chart 1 (fun _ => i) Q) (G.embedding x) := by
  rw [first_operator_eval,first_operator_eval,chartPullback_mul,
    fderiv_fun_mul (chartPullback_analytic chart P x).differentiableAt
      (chartPullback_analytic chart Q x).differentiableAt]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    hQ,smul_eq_mul,zero_mul,add_zero]

theorem polynomialOperator_sum (chart : TranslationChart A 0)
    (n : ℕ) (directions : Fin n → Fin A.parameterDimension) {ι : Type*}
    (t : Finset ι) (P : ι → G.CoordinateRing) :
    polynomialOperator chart n directions (∑ i ∈ t, P i) =
      ∑ i ∈ t, polynomialOperator chart n directions (P i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    ext e
    simp [polynomialOperator_coeff,substitutedPolynomial]
  | @insert i t hi ih =>
    simp only [Finset.sum_insert,hi,not_false_eq_true,polynomialOperator_add,ih]

/-- The nonzero intrinsic derivative minor remains nonzero for every
polynomial translation chart that contains the chosen point. -/
theorem operator_derivative_minor_ne_zero
    (chart : TranslationChart A 0) {n : ℕ} (directions : Fin n → Fin A.parameterDimension)
    (V : Set G.Point) (x : G.Point) (hx : x ∈ V) (hchart : x ∈ chart.domain)
    (Q : Fin n → G.CoordinateRing)
    (hQI : ∀ j, Q j ∈ G.vanishingIdeal V)
    (hQ : ∀ j, ∃ D, G.ambient.IsHomogeneous (Q j) D)
    (hdet : (Matrix.of (fun i j => fderiv K (A.pullback (Q j) x) 0
      (Pi.single (directions i) 1))).det ≠ 0) :
    (Matrix.of (fun i j => G.ambient.eval
      (polynomialOperator chart 1 (fun _ => directions i) (Q j)) (G.embedding x))).det ≠ 0 := by
  classical
  intro hz
  obtain ⟨c,hc,hcB⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz
  let v : A.ParameterSpace := ∑ i, c i • Pi.single (directions i) 1
  have hzero (j) : A.pullback (Q j) x 0 = 0 :=
    G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal (Set.mem_image_of_mem G.embedding hx)
      _ (lift_zero_represents A x) (hQI j)
  have hder (j) : fderiv K (A.pullback (Q j) x) 0 v = 0 := by
    obtain ⟨D,hD⟩ := hQ j
    have hsum := congrFun hcB j
    simp only [Matrix.vecMul,Matrix.of_apply,dotProduct,Pi.zero_apply,first_operator_eval] at hsum
    have hchartd : fderiv K (chartPullback chart (Q j) x) 0 v = 0 := by
      simpa only [v,map_sum,map_smul,smul_eq_mul] using hsum
    have hlift : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ b : G.FactorIndex,
        ∃ hf : (fun k => evaluateCoefficientPolynomial A (chart.coordinates ⟨b,k⟩) x z) ≠ 0,
        ∃ hg : (fun k => A.lift x z ⟨b,k⟩) ≠ 0,
          Projectivization.mk K (fun k => evaluateCoefficientPolynomial A
            (chart.coordinates ⟨b,k⟩) x z) hf =
          Projectivization.mk K (fun k => A.lift x z ⟨b,k⟩) hg := by
      filter_upwards [chart.represents x hchart,A.lift_represents x] with z hz hz'
      obtain ⟨hd,hr⟩ := hz
      obtain ⟨hd',hr'⟩ := hz'
      intro b
      obtain ⟨hf,hfr⟩ := hr b
      obtain ⟨hg,hgr⟩ := hr' b
      exact ⟨hf,hg,hfr.trans (by simpa only [add_zero] using hgr.symm)⟩
    apply (G.ambient.fderiv_eval_zero_iff_of_projective_lifts (Q j) D hD
      (fun z q => evaluateCoefficientPolynomial A (chart.coordinates q) x z)
      (A.lift x) 0 v (chart_evaluation_analytic chart x) (A.lift_analytic x) hlift (hzero j)).mp
    have heval : chartPullback chart (Q j) x = fun z =>
        MvPolynomial.eval (fun q => evaluateCoefficientPolynomial A (chart.coordinates q) x z) (Q j) :=
      funext fun z => evaluate_substituted chart (Q j) x z
    rw [← heval]
    exact hchartd
  apply hdet
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨c,hc,?_⟩
  funext j
  simpa only [v,map_sum,map_smul,smul_eq_mul,Matrix.vecMul,Matrix.of_apply,
    dotProduct,Pi.zero_apply] using hder j

end PhilipponMultiplicity.OperatorSupport

end
end


section
-- Implementation: Solutions/PhilipponHomogeneousMatrices.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_det {n : ℕ} (B : Matrix (Fin n) (Fin n) M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hB : ∀ i j, M.IsHomogeneous (B i j) D) :
    M.IsHomogeneous B.det (n • D) := by
  classical
  rw [Matrix.det_apply]
  apply M.isHomogeneous_sum
  intro σ _
  have hp : M.IsHomogeneous (∏ i, B (σ i) i) (n • D) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin] using
      M.isHomogeneous_prod Finset.univ (fun i => B (σ i) i) (fun _ => D)
        (fun i _ => hB (σ i) i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa only [h,one_smul] using hp
  · simpa only [h,Units.neg_smul,one_smul] using hp.neg M

theorem isHomogeneous_adjugate {n : ℕ} (B : Matrix (Fin n) (Fin n) M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hB : ∀ i j, M.IsHomogeneous (B i j) D)
    (i j : Fin n) : M.IsHomogeneous (B.adjugate i j) ((n-1) • D) := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hd := M.isHomogeneous_det (B.submatrix j.succAbove i.succAbove) D
      (fun a b => hB (j.succAbove a) (i.succAbove b))
    simpa only [Nat.add_sub_cancel,map_pow,map_neg,map_one] using
      hd.C_mul M ((-1 : K) ^ (j.val+i.val))

end PhilipponMultiplicity.MultiProjectiveSpace

end
end


section
-- Implementation: Solutions/PhilipponTransverseEquations.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem homogeneous_mem_vanishingIdeal_of_open
    (V U : Set G.Point) (hV : @IsIrreducible _ G.zariskiTopology V)
    (hU : @IsOpen _ G.zariskiTopology U) (hmeets : (V ∩ U).Nonempty)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (hz : ∀ x ∈ V ∩ U, G.ambient.eval P (G.embedding x) = 0) :
    P ∈ G.vanishingIdeal V := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have hclosed : IsClosed {x : G.Point | G.ambient.eval P (G.embedding x) = 0} :=
    (G.ambient.isClosed_zero P D hP).preimage continuous_induced_dom
  have hsub : V ⊆ {x : G.Point | G.ambient.eval P (G.embedding x) = 0} :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hV.2 hU hmeets).trans
      (closure_minimal hz hclosed)
  exact Ideal.subset_span ⟨⟨D,hP⟩,by rintro _ ⟨x,hx,rfl⟩; exact hsub hx⟩

/-- The adjugate identity, with all degree and chart factors retained.
Its input equations and its output equations lie in the same actual ideal. -/
theorem first_operator_adjugate_eval
    (chart : TranslationChart A 0) {n : ℕ}
    (directions : Fin n → Fin A.parameterDimension)
    (V : Set G.Point) (D : G.FactorIndex → ℕ)
    (Q : Fin n → G.CoordinateRing)
    (hQI : ∀ j, Q j ∈ G.vanishingIdeal V)
    (hQ : ∀ j, G.ambient.IsHomogeneous (Q j) D)
    (x : G.Point) (hx : x ∈ V) (hxchart : x ∈ chart.domain) :
    let B : Matrix (Fin n) (Fin n) G.CoordinateRing :=
      fun i j => polynomialOperator chart 1 (fun _ => directions i) (Q j)
    let E : G.FactorIndex → ℕ := (n-1) • (fun i => chart.degree i * D i)
    ∃ a : G.FactorIndex → Kˣ, ∀ i j,
      G.ambient.eval (polynomialOperator chart 1 (fun _ => directions i)
        (∑ k, B.adjugate k j * Q k)) (G.embedding x) =
      (∏ b, (a b : K) ^ E b) *
        (if i=j then G.ambient.eval B.det (G.embedding x) else 0) := by
  classical
  dsimp only
  let B : Matrix (Fin n) (Fin n) G.CoordinateRing :=
    fun i j => polynomialOperator chart 1 (fun _ => directions i) (Q j)
  let F : G.FactorIndex → ℕ := fun i => chart.degree i * D i
  have hB (i j) : G.ambient.IsHomogeneous (B i j) F :=
    polynomialOperator_homogeneous chart _ _ _ D (hQ j)
  have hC (k j) : G.ambient.IsHomogeneous (B.adjugate k j) ((n-1) • F) :=
    G.ambient.isHomogeneous_adjugate B F hB k j
  obtain ⟨a,ha⟩ := chartPullback_zero_scales chart x hxchart
  refine ⟨a,?_⟩
  intro i j
  have hprod (k) : G.ambient.eval
      (polynomialOperator chart 1 (fun _ => directions i) (B.adjugate k j * Q k)) (G.embedding x) =
      (∏ b, (a b : K) ^ ((n-1) • F) b) *
        (G.ambient.eval (B.adjugate k j) (G.embedding x) *
          G.ambient.eval (B i k) (G.embedding x)) := by
    rw [first_operator_mul_eval chart _ _ x _
      (chartPullback_zero_of_mem chart V (Q k) (hQI k) x hxchart hx),ha _ _ (hC k j)]
    exact mul_assoc _ _ _
  have hsum : ∑ k, G.ambient.eval (B.adjugate k j) (G.embedding x) *
      G.ambient.eval (B i k) (G.embedding x) =
      if i=j then G.ambient.eval B.det (G.embedding x) else 0 := by
    have hh := congrArg (fun P : G.CoordinateRing => G.ambient.eval P (G.embedding x))
      (congrFun (congrFun (Matrix.mul_adjugate B) i) j)
    simpa only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
      MultiProjectiveSpace.eval,map_sum,map_mul,apply_ite,map_one,map_zero,mul_one,mul_zero,
      mul_comm,one_mul,zero_mul] using hh
  change G.ambient.eval (polynomialOperator chart 1 (fun _ => directions i)
    (∑ k, B.adjugate k j * Q k)) (G.embedding x) = _
  rw [polynomialOperator_sum]
  change MvPolynomial.eval _ (∑ k, _) = _
  rw [map_sum]
  change (∑ k, G.ambient.eval
    (polynomialOperator chart 1 (fun _ => directions i) (B.adjugate k j * Q k))
      (G.embedding x)) = _
  simp_rw [hprod]
  rw [← Finset.mul_sum,hsum]
  rfl

/-- Philippon, Lemma 4.6, using a nonzero homogeneous derivative minor and
its adjugate. Irreducibility extends the off-diagonal identities from the
chosen chart to the full coset. -/
theorem lemma_4_6
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions)
    (chart : TranslationChart A (0 : G.Point))
    (hmeets : (translate g H.carrier ∩ chart.domain).Nonempty) :
    ∃ Q : Fin (analyticCodimension A H.carrier) → G.CoordinateRing,
      (∀ j, Q j ∈ G.vanishingIdeal (translate g H.carrier)) ∧
      (∀ i j,
        polynomialOperator chart 1 (fun _ => directions i) (Q j) ∉
          G.vanishingIdeal (translate g H.carrier) ↔ i = j) := by
  classical
  letI : CompleteSpace K := hK.completeSpace
  obtain ⟨x,hx,hxchart⟩ := hmeets
  obtain ⟨D,Q,hQI,hQ,hdet⟩ :=
    exists_uniform_transverse_derivative_minor A H g x hx directions htransverse
  let n := analyticCodimension A H.carrier
  let B : Matrix (Fin n) (Fin n) G.CoordinateRing :=
    fun i j => polynomialOperator chart 1 (fun _ => directions i) (Q j)
  let F : G.FactorIndex → ℕ := fun i => chart.degree i * D i
  let E : G.FactorIndex → ℕ := (n-1) • F
  let R : Fin n → G.CoordinateRing := fun j => ∑ k, B.adjugate k j * Q k
  have hB (i j) : G.ambient.IsHomogeneous (B i j) F :=
    polynomialOperator_homogeneous chart _ _ _ D (hQ j)
  have hC (k j) : G.ambient.IsHomogeneous (B.adjugate k j) E :=
    G.ambient.isHomogeneous_adjugate B F hB k j
  have hR (j) : G.ambient.IsHomogeneous (R j) (E+D) :=
    G.ambient.isHomogeneous_sum Finset.univ _ _ (fun k _ => (hC k j).mul G.ambient (hQ k))
  have hdetx : G.ambient.eval B.det (G.embedding x) ≠ 0 := by
    have hh := operator_derivative_minor_ne_zero chart directions _ x hx hxchart Q hQI
      (fun j => ⟨D,hQ j⟩) hdet
    rw [MultiProjectiveSpace.eval,RingHom.map_det]
    exact hh
  refine ⟨R,?_,?_⟩
  · intro j
    exact (G.vanishingIdeal _).sum_mem (fun k _ =>
      (G.vanishingIdeal _).mul_mem_left _ (hQI k))
  · intro i j
    constructor
    · intro hnot
      by_contra hij
      apply hnot
      apply homogeneous_mem_vanishingIdeal_of_open _ chart.domain
        (H.isIrreducible_translate hH g) chart.domain_isOpen ⟨x,hx,hxchart⟩
        _ _ (polynomialOperator_homogeneous chart _ _ (R j) (E+D) (hR j))
      rintro y ⟨hy,hyc⟩
      obtain ⟨a,ha⟩ := first_operator_adjugate_eval chart directions _ D Q hQI hQ y hy hyc
      have hh := ha i j
      simpa only [if_neg hij,mul_zero] using hh
    · rintro rfl hmem
      have hz := G.ambient.eval_eq_zero_of_mem_vanishingIdeal hmem
        (Set.mem_image_of_mem G.embedding hx)
      obtain ⟨a,ha⟩ := first_operator_adjugate_eval chart directions _ D Q hQI hQ x hx hxchart
      have he := ha i i
      simp only [ite_true] at he
      rw [he] at hz
      exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun b _ => pow_ne_zero _ (a b).ne_zero))
        hdetx) hz

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponPrimaryComponentDegree.lean

end


section
-- Implementation: Solutions/PhilipponJetIdeal.lean

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

theorem derivative_eq_zero_iff_basis {d n : ℕ}
    (L : ContinuousMultilinearMap K (fun _ : Fin n => Fin d → K) K) :
    L = 0 ↔ ∀ directions : Fin n → Fin d, L (fun i => Pi.single (directions i) 1) = 0 := by
  constructor
  · intro h
    simp [h]
  · intro h
    have heq : L.toMultilinearMap = (0 : MultilinearMap K (fun _ : Fin n => Fin d → K) K) := by
      apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun K (Fin d))
      intro directions
      simpa using h directions
    ext x
    exact congrArg (fun f : MultilinearMap K (fun _ : Fin n => Fin d → K) K => f x) heq

theorem pullback_analytic (A : AnalyticSubgroup G) (P : G.CoordinateRing) (g : G.Point) :
    AnalyticAt K (A.pullback P g) 0 := by
  exact AnalyticAt.aeval_mvPolynomial (A.lift_analytic g) P

/-- Polynomials whose full finite jets vanish at the specified translate. -/
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

/-- Closure under homogeneous projections reduces ideal containment to
homogeneous polynomials, without adding any hypothesis on the ideal. -/
theorem homogeneousIdeal_le_of_homogeneous (M : MultiProjectiveSpace K)
    (I J : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (h : ∀ P ∈ I, (∃ D, M.IsHomogeneous P D) → P ∈ J) : I ≤ J := by
  classical
  intro P hP
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  rw [← sum_weightedHomogeneousComponent w P,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) P)]
  apply J.sum_mem
  intro D _
  apply h _ (hI P hP D)
  exact ⟨D,(M.degreePiece_iff _ D).mp (weightedHomogeneousComponent_mem w P D)⟩

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRetentionZeros.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

/-- Retention preserves the vanishing test at each genuine homogeneous
representative. This follows from the literal localization definition. -/
theorem retainOnGroup_le_point_iff (J : Ideal G.CoordinateRing)
    (x : GroupHomogeneousRepresentative G) :
    retainOnGroup G J ≤ (representativeMaximalIdeal G x).asIdeal ↔
      J ≤ (representativeMaximalIdeal G x).asIdeal := by
  constructor
  · exact fun h => (le_retainOnGroup G J).trans h
  · intro hJ P hP
    let m := representativeMaximalIdeal G x
    have hle : retainOnGroup G J ≤ retainAtRepresentative G J x :=
      iInf_le (fun y : GroupHomogeneousRepresentative G => retainAtRepresentative G J y) x
    have hx : P ∈ retainAtRepresentative G J x := hle hP
    change algebraMap G.CoordinateRing (Localization.AtPrime m.asIdeal) P ∈
      J.map (algebraMap G.CoordinateRing (Localization.AtPrime m.asIdeal)) at hx
    obtain ⟨s,hs,hsp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal) J P).mp hx
    exact (m.isMaximal.isPrime.mem_or_mem (hJ hsp)).resolve_left hs

theorem retainOnGroup_zero_iff (J : Ideal G.CoordinateRing) (x : G.Point) :
    (∀ P ∈ retainOnGroup G J, G.ambient.eval P (G.embedding x) = 0) ↔
      ∀ P ∈ J, G.ambient.eval P (G.embedding x) = 0 := by
  change (retainOnGroup G J ≤ (representativeMaximalIdeal G (representativeOfPoint G x)).asIdeal) ↔
    J ≤ (representativeMaximalIdeal G (representativeOfPoint G x)).asIdeal
  exact retainOnGroup_le_point_iff G J (representativeOfPoint G x)

theorem retainedOperator_zero_iff {A : AnalyticSubgroup G} {g : G.Point}
    (atlas : TranslationAtlas A g) (k : ℕ) (I : Ideal G.CoordinateRing) (x : G.Point) :
    (∀ Q ∈ retainedPolynomialOperatorIdeal atlas k I, G.ambient.eval Q (G.embedding x) = 0) ↔
    ∀ P ∈ I, (∃ D, G.ambient.IsHomogeneous P D) → ∀ a : atlas.Index,
      ∀ n ≤ k, ∀ directions : Fin n → Fin A.parameterDimension,
        G.ambient.eval (polynomialOperator (atlas.chart a) n directions P) (G.embedding x) = 0 := by
  rw [retainedPolynomialOperatorIdeal, retainOnGroup_zero_iff]
  change polynomialOperatorIdeal atlas k I ≤ RingHom.ker
    (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) ↔ _
  rw [polynomialOperatorIdeal, sup_le_iff, Ideal.span_le]
  have hG : G.vanishingIdeal Set.univ ≤ RingHom.ker
      (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
    apply Ideal.span_le.mpr
    rintro P ⟨_,hP⟩
    exact hP (G.embedding x) ⟨x,Set.mem_univ _,rfl⟩
  constructor
  · rintro ⟨_,h⟩ P hPI hPh a n hn directions
    exact h ⟨P,hPI,hPh,a,n,hn,directions,rfl⟩
  · intro h
    refine ⟨hG,?_⟩
    rintro Q ⟨P,hPI,hPh,a,n,hn,directions,rfl⟩
    exact h P hPI hPh a n hn directions

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponOperatorContact.lean

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

/-- Even off its own domain, a chart gives an analytic scalar multiple of
the intrinsic pullback. The scalar need not be a unit off the chart. -/
theorem chart_pullback_analytic_multiple (chart : TranslationChart A g)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) :
    ∃ u : A.ParameterSpace → K, AnalyticAt K u 0 ∧
      (fun z => MvPolynomial.eval
        (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) P) =ᶠ[𝓝 0]
        (fun z => u z * A.pullback P (g + x) z) := by
  classical
  have hpivot (i : G.FactorIndex) : ∃ j, A.lift (g + x) 0 ⟨i,j⟩ ≠ 0 := by
    obtain ⟨_,hi⟩ := (A.lift_represents (g + x)).self_of_nhds
    obtain ⟨hne,_⟩ := hi i
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hne
  choose b hb using hpivot
  let a (z : A.ParameterSpace) (i : G.FactorIndex) :=
    evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z / A.lift (g + x) z ⟨i,b i⟩
  let u (z : A.ParameterSpace) := ∏ i, a z i ^ D i
  have ha (i : G.FactorIndex) : AnalyticAt K (fun z => a z i) 0 :=
    (chart_evaluation_analytic chart x _).div (A.lift_analytic (g + x) _) (hb i)
  refine ⟨u,Finset.analyticAt_fun_prod _ (fun i _ => (ha i).pow _),?_⟩
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ i : G.FactorIndex, A.lift (g + x) z ⟨i,b i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (A.lift_analytic (g + x) _).continuousAt.eventually_ne (hb i)
  have hcompat : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ v : G.ambient.Variable,
      evaluateCoefficientPolynomial A (chart.coordinates v) x z * A.lift (g + x) z ⟨v.1,b v.1⟩ =
        evaluateCoefficientPolynomial A (chart.coordinates ⟨v.1,b v.1⟩) x z * A.lift (g + x) z v := by
    rw [Filter.eventually_all]
    intro v
    exact chart.coordinate_compatible x v.1 v.2 (b v.1)
  filter_upwards [hnear,hcompat] with z hz hc
  have hcoords : (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) =
      fun v => a z v.1 * A.lift (g + x) z v := by
    funext v
    dsimp [a]
    apply (mul_right_cancel₀ (hz v.1))
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (hz v.1)]
    exact hc v
  rw [hcoords,G.ambient.eval_block_scale P D hP]
  rfl

theorem operator_zero_of_contact (chart : TranslationChart A g)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) (k : ℕ) (hcontact : (k : WithTop ℕ) < vanishingOrder A P (g + x))
    (n : ℕ) (hn : n ≤ k) (directions : Fin n → Fin A.parameterDimension) :
    G.ambient.eval (polynomialOperator chart n directions P) (G.embedding x) = 0 := by
  obtain ⟨u,hu,heq⟩ := chart_pullback_analytic_multiple chart P D hP x
  have hj := (natCast_lt_jetOrder_iff (A.pullback P (g + x)) 0 k).mp hcontact
  rw [polynomialOperator_eval, (heq.iteratedFDeriv K n).eq_of_nhds,
    iteratedFDeriv_mul_eq_zero_of_vanishing_jet (pullback_analytic A P (g + x)).contDiffAt
      hu.contDiffAt (fun i hi => hj i (hi.trans hn))]
  rfl

end PhilipponMultiplicity.OperatorSupport

namespace PhilipponMultiplicity
open OperatorSupport

/-- Proposition 4.4: zeros of the actual retained polynomial operator ideal
are exactly the points where every original equation has the required contact. -/
theorem proposition_4_4
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g h : G.Point) (k : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (atlas : TranslationAtlas A g) :
    (∀ Q ∈ retainedPolynomialOperatorIdeal atlas k I,
      G.ambient.eval Q (G.embedding h) = 0) ↔
    (∀ Q ∈ I, (k : WithTop ℕ) < vanishingOrder A Q (g + h)) := by
  letI : CompleteSpace K := hK.completeSpace
  rw [retainedOperator_zero_iff]
  constructor
  · intro hop
    have hle : I ≤ jetIdeal A (g + h) k := by
      apply homogeneousIdeal_le_of_homogeneous G.ambient I _ hI
      rintro P hPI ⟨D,hP⟩
      apply (mem_jetIdeal_iff A (g + h) k P).mpr
      obtain ⟨a,ha⟩ := atlas.covers h
      rw [projective_lift_contact_invariance K hK G A (g + h) P D hP
        (fun z v => evaluateCoefficientPolynomial A ((atlas.chart a).coordinates v) h z)
        (chart_evaluation_analytic (atlas.chart a) h)
        (by simpa only [add_comm h g] using (atlas.chart a).represents h ha)]
      apply (natCast_lt_jetOrder_iff _ 0 k).mpr
      intro n hn
      apply (derivative_eq_zero_iff_basis _).mpr
      intro directions
      rw [← polynomialOperator_eval]
      exact hop P hPI ⟨D,hP⟩ a n hn directions
    exact fun Q hQ => (mem_jetIdeal_iff A (g + h) k Q).mp (hle hQ)
  · intro hcontact P hPI hPh a n hn directions
    obtain ⟨D,hP⟩ := hPh
    exact operator_zero_of_contact (atlas.chart a) P D hP h k (hcontact P hPI) n hn directions

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponAnalyticPolynomialSubstitution.lean

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
-- Implementation: Solutions/PhilipponBoundedAdditionCharts.lean

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
-- Implementation: Solutions/PhilipponAdditionSubstitution.lean

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
-- Implementation: Solutions/PhilipponAdditionChartGerms.lean

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
-- Implementation: Solutions/PhilipponBoundedTranslationAtlas.lean

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
-- Implementation: Solutions/PhilipponPrimaryContact.lean

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
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

/-- A homogeneous ideal not contained in another ideal has a homogeneous
element outside it. -/
theorem exists_homogeneous_not_mem (I p : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hnot : ¬ I ≤ p) :
    ∃ Q ∈ I, ∃ D, G.ambient.IsHomogeneous Q D ∧ Q ∉ p := by
  by_contra! h
  apply hnot
  exact homogeneousIdeal_le_of_homogeneous G.ambient I p hI
    (by rintro Q hQ ⟨D,hD⟩; exact h Q hQ D hD)

/-- Denominators at a homogeneous prime can be chosen homogeneous when
clearing one homogeneous element of an ideal's localization. -/
theorem primaryComponent_homogeneous_denominator
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (q : PrimeSpectrum G.CoordinateRing) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (hPJ : P ∈ Hilbert.primaryComponent K G.factorCount G.ambient.ambientDimension I q) :
    ∃ Q : G.CoordinateRing, ∃ E, G.ambient.IsHomogeneous Q E ∧
      Q ∉ q.asIdeal ∧ Q * P ∈ I := by
  obtain ⟨s,hs,hsp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) I P).mp hPJ
  have hscolon : s ∈ I.colon {P} := by
    simpa only [Submodule.mem_colon_singleton,smul_eq_mul] using hsp
  obtain ⟨Q,hQ,E,hQE,hQp⟩ := exists_homogeneous_not_mem (I.colon {P}) q.asIdeal
    (Hilbert.homogeneous_colon G.ambient I hI P D hP) (fun h => hs (h hscolon))
  exact ⟨Q,E,hQE,hQp,by simpa only [Submodule.mem_colon_singleton,smul_eq_mul] using hQ⟩

/-- Every equation of the ambient group vanishes to all orders along every
analytic orbit; this is proved using the actual projective lifts. -/
theorem groupIdeal_le_jetIdeal (A : AnalyticSubgroup G) (x : G.Point) (T : ℕ) :
    G.vanishingIdeal Set.univ ≤ jetIdeal A x T := by
  intro P hP n hn
  have hz : A.pullback P x =ᶠ[𝓝 0] (fun _ => (0 : K)) := by
    filter_upwards [A.lift_represents x] with z hz
    obtain ⟨hz,hlift⟩ := hz
    exact G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
      (Set.mem_image_of_mem G.embedding (Set.mem_univ _)) _ hlift hP
  rw [(hz.iteratedFDeriv K n).eq_of_nhds]
  simp

/-- Finite contact descends through a polynomial factor whose value in the
chosen lift is nonzero. This is the analytic-unit version of Leibniz induction. -/
theorem mem_jetIdeal_of_mul (x : G.Point) (T : ℕ) (P Q : G.CoordinateRing)
    (hQ : A.pullback Q x 0 ≠ 0) (hQP : Q * P ∈ jetIdeal A x T) :
    P ∈ jetIdeal A x T := by
  apply (mem_jetIdeal_iff A x T P).mpr
  have heq : vanishingOrder A (Q*P) x = vanishingOrder A P x := by
    change jetOrder (A.pullback (Q*P) x) 0 = jetOrder (A.pullback P x) 0
    have hfun : A.pullback (Q*P) x = fun z => A.pullback Q x z * A.pullback P x z := by
      funext z; exact map_mul _ _ _
    rw [hfun]
    exact jetOrder_mul_unit (pullback_analytic A P x) (pullback_analytic A Q x) hQ
  rw [← heq]
  exact (mem_jetIdeal_iff A x T (Q*P)).mp hQP

/-- Contact survives contraction from the coset-prime localization. The
homogeneous separator is nonzero on a dense open part of the irreducible coset;
analytic-unit cancellation there and density give every polynomial jet globally. -/
theorem primaryComponent_polynomialOperator_mem_coset
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (T : ℕ) (hcontact : ∀ x ∈ translate g H.carrier, I ≤ jetIdeal A x T)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (hPJ : P ∈ Hilbert.primaryComponent K G.factorCount G.ambient.ambientDimension I
      ⟨G.vanishingIdeal (translate g H.carrier), H.translated_vanishingIdeal_isPrime hH g⟩)
    (chart : TranslationChart A 0) (n : ℕ) (hn : n ≤ T)
    (directions : Fin n → Fin A.parameterDimension) :
    polynomialOperator chart n directions P ∈ G.vanishingIdeal (translate g H.carrier) := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  obtain ⟨Q,E,hQE,hQp,hQP⟩ := primaryComponent_homogeneous_denominator I hI _ P D hP hPJ
  let U : Set G.Point := {x | G.ambient.eval Q (G.embedding x) ≠ 0}
  have hU : IsOpen U := (G.ambient.isOpen_basic Q E hQE).preimage continuous_induced_dom
  have hmeets : (translate g H.carrier ∩ U).Nonempty := by
    by_contra hz
    apply hQp
    exact Ideal.subset_span ⟨⟨E,hQE⟩,by
      rintro _ ⟨x,hx,rfl⟩
      by_contra hxQ
      exact hz ⟨x,hx,hxQ⟩⟩
  apply homogeneous_mem_vanishingIdeal_of_open _ U (H.isIrreducible_translate hH g) hU hmeets
    _ _ (polynomialOperator_homogeneous chart n directions P D hP)
  intro x hx
  have hQ0 : A.pullback Q x 0 ≠ 0 :=
    (not_congr (G.ambient.eval_eq_zero_iff_of_lift (G.embedding x) (A.lift x 0)
      (lift_zero_represents A x) Q E hQE)).mpr hx.2
  have hPx : P ∈ jetIdeal A x T := mem_jetIdeal_of_mul x T P Q hQ0 (hcontact x hx.1 hQP)
  apply operator_zero_of_contact chart P D hP x T _ n hn directions
  simpa only [zero_add] using (mem_jetIdeal_iff A x T P).mp hPx

/-- The first reduction in the proof of Proposition 4.7: the canonical
isolated primary component retains all contact orders up to T. -/
theorem primaryComponent_contact_of_incomplete_differential
    (hK : IsPhilipponBaseField K)
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (T : ℕ) (hcomponent : IncompletelyDefines G I (translate g H.carrier))
    (hprolongation : IncompletelyDefines G (differentialIdeal A 0 T I)
      (translate g H.carrier)) :
    ∀ x ∈ translate g H.carrier,
      Hilbert.primaryComponent K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ ⊔ I)
        ⟨G.vanishingIdeal (translate g H.carrier),H.translated_vanishingIdeal_isPrime hH g⟩ ≤
      jetIdeal A x T := by
  obtain ⟨c,hc,hatlas⟩ := AtlasSupport.exists_uniformly_bounded_translation_atlas (K := K)
  obtain ⟨atlas,_⟩ := hatlas G A 0
  let q : PrimeSpectrum G.CoordinateRing :=
    ⟨G.vanishingIdeal (translate g H.carrier),H.translated_vanishingIdeal_isPrime hH g⟩
  let I₀ := G.vanishingIdeal Set.univ ⊔ I
  let J := Hilbert.primaryComponent K G.factorCount G.ambient.ambientDimension I₀ q
  have hI₀ : IsMultihomogeneousIdeal G.ambient I₀ := by
    intro P hP D
    obtain ⟨P₁,h₁,P₂,h₂,rfl⟩ := Submodule.mem_sup.mp hP
    rw [map_add]
    exact I₀.add_mem (Ideal.mem_sup_left
      (vanishingIdeal_multihomogeneous K G.ambient _ P₁ h₁ D))
      (Ideal.mem_sup_right (hI P₂ h₂ D))
  have hJ : IsMultihomogeneousIdeal G.ambient J :=
    Hilbert.primaryComponent_homogeneous G.ambient I₀ hI₀ q
      (incomplete_coset_minimalPrime H hH g I hcomponent)
  have horiginal (x : G.Point) (hx : x ∈ translate g H.carrier) : I ≤ jetIdeal A x T := by
    have hz : ∀ Q ∈ retainedPolynomialOperatorIdeal atlas T I,
        G.ambient.eval Q (G.embedding x) = 0 := by
      intro Q hQ
      rw [retainedPolynomialOperatorIdeal_eq_differentialIdeal] at hQ
      exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal
        (incomplete_coset_le H hH g _ hprolongation hQ) ⟨x,hx,rfl⟩
    intro P hP
    apply (mem_jetIdeal_iff A x T P).mpr
    simpa only [zero_add] using
      ((proposition_4_4 K hK G A 0 x T I hI atlas).mp hz) P hP
  have hcontact (x : G.Point) (hx : x ∈ translate g H.carrier) : I₀ ≤ jetIdeal A x T :=
    sup_le (groupIdeal_le_jetIdeal A x T) (horiginal x hx)
  intro x hx
  apply homogeneousIdeal_le_of_homogeneous G.ambient J _ hJ
  rintro P hPJ ⟨D,hP⟩
  apply (mem_jetIdeal_iff A x T P).mpr
  obtain ⟨a,ha⟩ := atlas.covers x
  rw [projective_lift_contact_invariance K hK G A x P D hP
    (fun z v => evaluateCoefficientPolynomial A ((atlas.chart a).coordinates v) x z)
    (chart_evaluation_analytic (atlas.chart a) x)
    (by simpa only [add_zero] using (atlas.chart a).represents x ha)]
  apply (natCast_lt_jetOrder_iff _ 0 T).mpr
  intro n hn
  apply (derivative_eq_zero_iff_basis _).mpr
  intro directions
  rw [← polynomialOperator_eval]
  exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal
    (primaryComponent_polynomialOperator_mem_coset H hH g I₀ hI₀ T hcontact
      P D hP hPJ (atlas.chart a) n hn directions) ⟨x,hx,rfl⟩

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponHigherContact.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity
variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- The elementary finite-jet product estimate, retaining both vanishing orders. -/
theorem iteratedFDeriv_mul_zero_of_orders {f g : E → K} {x : E} {n a b : ℕ}
    (hf : ContDiffAt K n f x) (hg : ContDiffAt K n g x) (hab : n < a+b)
    (hfz : ∀ i < a, iteratedFDeriv K i f x = 0)
    (hgz : ∀ i < b, iteratedFDeriv K i g x = 0) :
    iteratedFDeriv K n (fun y => f y*g y) x = 0 := by
  obtain ⟨s,hs,hopen,hxs⟩ := eventually_nhds_iff.mp
    ((hf.eventually (by simp)).and (hg.eventually (by simp)))
  have hfs : ContDiffOn K n f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have hgs : ContDiffOn K n g s := fun y hy => (hs y hy).2.contDiffWithinAt
  have hbound := norm_iteratedFDerivWithin_mul_le hfs hgs hopen.uniqueDiffOn hxs
    (le_refl (n : ℕ∞ω))
  simp only [iteratedFDerivWithin_of_isOpen _ hopen hxs] at hbound
  have hz : (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
      ‖iteratedFDeriv K i f x‖ * ‖iteratedFDeriv K (n-i) g x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hia : i < a
    · simp [hfz i hia]
    · simp [hgz (n-i) (by have := Finset.mem_range.mp hi; omega)]
  rw [hz] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

variable [CompleteSpace K] {G : EmbeddedGroupProduct K}
open OperatorSupport

/-- The product of two ideals of finite contact has the sum of their orders. -/
theorem jetIdeal_mul_le (A : AnalyticSubgroup G) (x : G.Point) (a b : ℕ) :
    jetIdeal A x a * jetIdeal A x b ≤ jetIdeal A x (a+b+1) := by
  apply Ideal.mul_le.mpr
  intro P hP Q hQ n hn
  have heq : A.pullback (P*Q) x = fun z => A.pullback P x z * A.pullback Q x z := by
    funext z; exact map_mul _ _ _
  rw [heq]
  exact iteratedFDeriv_mul_zero_of_orders (a := a+1) (b := b+1)
    (pullback_analytic A P x).contDiffAt (pullback_analytic A Q x).contDiffAt
    (by omega) (fun i hi => hP i (by omega)) (fun i hi => hQ i (by omega))

/-- A product of n+1 equations of a locus has vanishing n-jet at its points. -/
theorem vanishingIdeal_pow_le_jetIdeal (A : AnalyticSubgroup G) (V : Set G.Point)
    (x : G.Point) (hx : x ∈ V) (n : ℕ) :
    (G.vanishingIdeal V)^(n+1) ≤ jetIdeal A x n := by
  have hzero : G.vanishingIdeal V ≤ jetIdeal A x 0 := by
    intro P hP k hk
    have hk0 : k = 0 := by omega
    subst k
    ext m
    simpa only [iteratedFDeriv_zero_apply,ContinuousMultilinearMap.zero_apply,
      AnalyticSubgroup.pullback] using
      G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding hx) (A.lift x 0) (lift_zero_represents A x) hP
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    rw [pow_succ]
    exact (mul_le_mul' ih hzero).trans (by simpa using jetIdeal_mul_le A x n 0)

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/AnalyticMonomialJets.lean

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

theorem mixedDeriv_comp_linear (L : F →L[K] E) {f : E → K} {x : F}
    (hf : AnalyticAt K f (L x)) (w : List F) :
    mixedDeriv w (f ∘ L) x = mixedDeriv (w.map L) f (L x) := by
  induction w generalizing x with
  | nil => rfl
  | cons v w ih =>
    have heq : mixedDeriv w (f ∘ L) =ᶠ[𝓝 x] (mixedDeriv (w.map L) f ∘ L) := by
      have he := L.continuous.continuousAt.preimage_mem_nhds hf.eventually_analyticAt
      filter_upwards [he] with y hy
      exact ih hy
    change fderiv K (mixedDeriv w (f ∘ L)) x v = _
    rw [heq.fderiv_eq,fderiv_comp x (mixedDeriv_analytic hf _).differentiableAt
      L.differentiableAt,L.fderiv]
    rfl

theorem mixedDeriv_ofFn {f : E → K} {x : E} (hf : AnalyticAt K f x)
    {n : ℕ} (v : Fin n → E) :
    mixedDeriv (List.ofFn v) f x = iteratedFDeriv K n f x v := by
  rw [mixedDeriv_eq_iteratedFDeriv hf]
  apply iteratedFDeriv_apply_congr (List.length_ofFn ..)
  intro i
  exact List.get_ofFn v i

theorem iteratedDeriv_comp_line {f : E → K} (hf : AnalyticAt K f 0) (v : E) (n : ℕ) :
    iteratedDeriv n (fun t : K => f (t • v)) 0 =
      iteratedFDeriv K n f 0 (fun _ => v) := by
  let L : K →L[K] E := (ContinuousLinearMap.id K K).smulRight v
  have hfl : AnalyticAt K f (L 0) := by simpa only [map_zero] using hf
  have hfcomp := hfl.comp (L.analyticAt 0)
  have h := mixedDeriv_comp_linear L hfl (List.ofFn (fun _ : Fin n => (1 : K)))
  rw [List.map_ofFn,mixedDeriv_ofFn hfcomp,mixedDeriv_ofFn hfl] at h
  simpa [L,iteratedDeriv,List.map_ofFn,Function.comp_def] using h

theorem analyticAt_multiset_prod {ι : Type*} (m : Multiset ι) (f : ι → E → K) (x : E)
    (hf : ∀ i, AnalyticAt K (f i) x) :
    AnalyticAt K (fun y => (m.map (fun i => f i y)).prod) x := by
  induction m using Multiset.induction_on with
  | empty => simpa using (analyticAt_const : AnalyticAt K (fun _ : E => (1 : K)) x)
  | cons i m ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons]
    exact (hf i).mul ih

/-- The degree-n part of a vanishing n-jet is obtained by replacing each
vanishing factor by its first derivative and each coefficient by its value. -/
theorem leading_monomial_relation [CharZero K] {s n : ℕ}
    (q : Fin s → E → K) (hq : ∀ i, AnalyticAt K (q i) 0) (hq0 : ∀ i, q i 0 = 0)
    (c : Sym (Fin s) n → E → K) (hc : ∀ a, AnalyticAt K (c a) 0)
    (hjet : ∀ k ≤ n, iteratedFDeriv K k
      (fun z => ∑ a, c a z * ((a : Multiset (Fin s)).map (fun i => q i z)).prod) 0 = 0)
    (v : E) :
    (∑ a, c a 0 * ((a : Multiset (Fin s)).map (fun i => fderiv K (q i) 0 v)).prod) = 0 := by
  classical
  let L : K →L[K] E := (ContinuousLinearMap.id K K).smulRight v
  let f (i : Fin s) (t : K) := q i (t • v)
  have hf (i : Fin s) : AnalyticAt K (f i) 0 := by
    exact (show AnalyticAt K (q i) (L 0) by simpa only [map_zero] using hq i).comp (L.analyticAt 0)
  let r (i : Fin s) := dslope (f i) 0
  have hr (i : Fin s) : AnalyticAt K (r i) 0 :=
    (hf i).hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt
  have hfr (i : Fin s) (t : K) : f i t = t * r i t := by
    simpa only [sub_zero,smul_eq_mul] using
      (sub_smul_dslope_of_zero (f := f i) (a := 0) (by simpa [f] using hq0 i) t).symm
  let F₀ (z : E) := ∑ a, c a z * ((a : Multiset (Fin s)).map (fun i => q i z)).prod
  have hF : AnalyticAt K F₀ 0 :=
    Finset.analyticAt_fun_sum _ (fun a _ => (hc a).mul (analyticAt_multiset_prod a q 0 hq))
  let w (t : K) := ∑ a, c a (t • v) * ((a : Multiset (Fin s)).map (fun i => r i t)).prod
  have hw : AnalyticAt K w 0 := by
    apply Finset.analyticAt_fun_sum
    intro a _
    apply AnalyticAt.mul
    · exact (show AnalyticAt K (c a) (L 0) by simpa only [map_zero] using hc a).comp (L.analyticAt 0)
    · exact analyticAt_multiset_prod a r 0 hr
  have heq (t : K) : F₀ (t • v) = t^n * w t := by
    dsimp only [F₀,w]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    have he (i : Fin s) : q i (t • v) = t*r i t := hfr i t
    simp_rw [he]
    rw [Multiset.prod_map_mul]
    rw [Multiset.map_const',Multiset.prod_replicate,Sym.card_coe]
    ring
  have hfl : AnalyticAt K (fun t : K => F₀ (t • v)) 0 :=
    (show AnalyticAt K F₀ (L 0) by simpa only [map_zero] using hF).comp (L.analyticAt 0)
  have horder : (n+1 : ℕ) ≤ analyticOrderAt (fun t : K => F₀ (t • v)) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfl]
    intro k hk
    rw [iteratedDeriv_comp_line hF,hjet k (by omega)]
    rfl
  have hw0 : w 0 = 0 := by
    by_contra hn
    have ho : analyticOrderAt (fun t : K => F₀ (t • v)) 0 = n :=
      hfl.analyticOrderAt_eq_natCast.mpr ⟨w,hw,hn,Filter.Eventually.of_forall (by
        intro t; simpa only [sub_zero,smul_eq_mul] using heq t)⟩
    rw [ho] at horder
    exact (Nat.not_succ_le_self n) (by exact_mod_cast horder)
  have hr0 (i : Fin s) : r i 0 = fderiv K (q i) 0 v := by
    dsimp only [r]
    rw [dslope_same]
    change fderiv K (q i ∘ L) 0 1 = _
    rw [fderiv_comp 0 (by simpa only [map_zero] using (hq i).differentiableAt)
      L.differentiableAt,L.fderiv]
    simp [L]
  simpa only [w,zero_smul,hr0] using hw0

theorem multiset_prod_X {ι : Type*} [DecidableEq ι] (m : Multiset ι) :
    (m.map (MvPolynomial.X : ι → MvPolynomial ι K)).prod =
      MvPolynomial.monomial m.toFinsupp 1 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons i m ih =>
    rw [Multiset.map_cons,Multiset.prod_cons,ih]
    have he : (i ::ₘ m).toFinsupp = Finsupp.single i 1 + m.toFinsupp := by
      ext j
      simp [Multiset.toFinsupp_apply,Multiset.count_cons,Finsupp.single_apply,eq_comm,add_comm]
    rw [he,MvPolynomial.X,MvPolynomial.monomial_mul,one_mul]

theorem sym_monomial_coefficients_zero [Infinite K] {s n : ℕ}
    (c : Sym (Fin s) n → K)
    (hz : ∀ y : Fin s → K,
      (∑ a, c a * ((a : Multiset (Fin s)).map y).prod) = 0) : ∀ a, c a = 0 := by
  classical
  let P : MvPolynomial (Fin s) K := ∑ a : Sym (Fin s) n, MvPolynomial.monomial
    (a : Multiset (Fin s)).toFinsupp (c a)
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro y
    simp only [P,map_sum,map_zero]
    convert hz y using 1
    apply Finset.sum_congr rfl
    intro a _
    have hm : MvPolynomial.monomial (a : Multiset (Fin s)).toFinsupp (c a) =
        MvPolynomial.C (c a) * MvPolynomial.monomial (a : Multiset (Fin s)).toFinsupp (1 : K) := by
      rw [MvPolynomial.C_mul_monomial,mul_one]
    rw [hm,← multiset_prod_X,map_mul,MvPolynomial.eval_C]
    congr 1
    rw [map_multiset_prod,Multiset.map_map]
    simp only [Function.comp_def,MvPolynomial.eval_X]
  intro a
  have h := congrArg (MvPolynomial.coeff (a : Multiset (Fin s)).toFinsupp) hP
  have he (b : Sym (Fin s) n) :
      (b : Multiset (Fin s)).toFinsupp = (a : Multiset (Fin s)).toFinsupp ↔ b = a := by
    rw [Multiset.toFinsupp.injective.eq_iff,Sym.coe_inj]
  simpa only [P,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,he,
    Finset.sum_ite_eq',if_pos (Finset.mem_univ a),MvPolynomial.coeff_zero] using h

/-- Full first-derivative rank makes degree-n monomials independent in the
n-th jet: every coefficient of a vanishing relation has zero value. -/
theorem monomial_jet_coefficients_zero [CharZero K] {s n : ℕ}
    (q : Fin s → E → K) (hq : ∀ i, AnalyticAt K (q i) 0) (hq0 : ∀ i, q i 0 = 0)
    (hrank : Function.Surjective (fun v : E => fun i => fderiv K (q i) 0 v))
    (c : Sym (Fin s) n → E → K) (hc : ∀ a, AnalyticAt K (c a) 0)
    (hjet : ∀ k ≤ n, iteratedFDeriv K k
      (fun z => ∑ a, c a z * ((a : Multiset (Fin s)).map (fun i => q i z)).prod) 0 = 0) :
    ∀ a, c a 0 = 0 := by
  apply sym_monomial_coefficients_zero
  intro y
  obtain ⟨v,rfl⟩ := hrank y
  exact leading_monomial_relation q hq hq0 c hc hjet v

end PhilipponMultiplicity.JetSupport

end
end


section
-- Implementation: Solutions/PhilipponMonomialSeparation.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem homogeneousIdeal_sup (I J : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hJ : IsMultihomogeneousIdeal G.ambient J) :
    IsMultihomogeneousIdeal G.ambient (I ⊔ J) := by
  intro P hP D
  obtain ⟨P₁,h₁,P₂,h₂,rfl⟩ := Submodule.mem_sup.mp hP
  rw [map_add]
  exact (I ⊔ J).add_mem (Ideal.mem_sup_left (hI P₁ h₁ D)) (Ideal.mem_sup_right (hJ P₂ h₂ D))

theorem homogeneousIdeal_mul (I J : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hJ : IsMultihomogeneousIdeal G.ambient J) :
    IsMultihomogeneousIdeal G.ambient (I*J) := by
  classical
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  letI := weightedGradedAlgebra K w
  have hi : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro D P hP
    change ((MvPolynomial.decompose' K w P) D : G.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply]
    exact hI P hP D
  have hj : J.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro D P hP
    change ((MvPolynomial.decompose' K w P) D : G.CoordinateRing) ∈ J
    rw [MvPolynomial.decompose'_apply]
    exact hJ P hP D
  intro P hP D
  exact weightedHomogeneousComponent_mem_of_mem K w (hi.mul hj) hP D

theorem homogeneousIdeal_pow (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (n : ℕ) :
    IsMultihomogeneousIdeal G.ambient (I ^ n) := by
  induction n with
  | zero => simp only [pow_zero,Ideal.one_eq_top]; intro P hP D; trivial
  | succ n ih => rw [pow_succ]; exact homogeneousIdeal_mul _ _ ih hI

theorem homogeneous_sym_monomial {s n : ℕ} (Q : Fin s → G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hQ : ∀ i, G.ambient.IsHomogeneous (Q i) D)
    (a : Sym (Fin s) n) :
    G.ambient.IsHomogeneous ((a : Multiset (Fin s)).map Q).prod (n • D) := by
  have h (m : Multiset (Fin s)) :
      G.ambient.IsHomogeneous (m.map Q).prod (m.card • D) := by
    induction m using Multiset.induction_on with
    | empty => simpa using G.ambient.isHomogeneous_one
    | cons i m ih =>
      simpa only [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons,
        add_nsmul,one_nsmul,add_comm] using (hQ i).mul G.ambient ih
  simpa using h a

/-- The reverse direction of the chart/intrinsic rank comparison. -/
theorem intrinsic_derivative_minor_ne_zero
    (chart : TranslationChart A 0) {s : ℕ} (directions : Fin s → Fin A.parameterDimension)
    (V : Set G.Point) (x : G.Point) (hx : x ∈ V) (hchart : x ∈ chart.domain)
    (Q : Fin s → G.CoordinateRing)
    (hQI : ∀ j, Q j ∈ G.vanishingIdeal V)
    (hQ : ∀ j, ∃ D, G.ambient.IsHomogeneous (Q j) D)
    (hdet : (Matrix.of (fun i j => G.ambient.eval
      (polynomialOperator chart 1 (fun _ => directions i) (Q j)) (G.embedding x))).det ≠ 0) :
    (Matrix.of (fun i j => fderiv K (A.pullback (Q j) x) 0
      (Pi.single (directions i) 1))).det ≠ 0 := by
  classical
  intro hz
  obtain ⟨c,hc,hcB⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz
  let v : A.ParameterSpace := ∑ i, c i • Pi.single (directions i) 1
  have hzero (j) : A.pullback (Q j) x 0 = 0 :=
    G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal (Set.mem_image_of_mem G.embedding hx)
      _ (lift_zero_represents A x) (hQI j)
  have hder (j) : fderiv K (chartPullback chart (Q j) x) 0 v = 0 := by
    obtain ⟨D,hD⟩ := hQ j
    have hsum := congrFun hcB j
    have hintrinsic : fderiv K (A.pullback (Q j) x) 0 v = 0 := by
      simpa only [v,map_sum,map_smul,smul_eq_mul,Matrix.vecMul,Matrix.of_apply,dotProduct,
        Pi.zero_apply] using hsum
    have hlift : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ b : G.FactorIndex,
        ∃ hf : (fun k => evaluateCoefficientPolynomial A (chart.coordinates ⟨b,k⟩) x z) ≠ 0,
        ∃ hg : (fun k => A.lift x z ⟨b,k⟩) ≠ 0,
          Projectivization.mk K (fun k => evaluateCoefficientPolynomial A
            (chart.coordinates ⟨b,k⟩) x z) hf =
          Projectivization.mk K (fun k => A.lift x z ⟨b,k⟩) hg := by
      filter_upwards [chart.represents x hchart,A.lift_represents x] with z hz hz'
      obtain ⟨hd,hr⟩ := hz
      obtain ⟨hd',hr'⟩ := hz'
      intro b
      obtain ⟨hf,hfr⟩ := hr b
      obtain ⟨hg,hgr⟩ := hr' b
      exact ⟨hf,hg,hfr.trans (by simpa only [add_zero] using hgr.symm)⟩
    have h := (G.ambient.fderiv_eval_zero_iff_of_projective_lifts (Q j) D hD
      (fun z q => evaluateCoefficientPolynomial A (chart.coordinates q) x z)
      (A.lift x) 0 v (chart_evaluation_analytic chart x) (A.lift_analytic x) hlift (hzero j)).mpr hintrinsic
    have heval : chartPullback chart (Q j) x = fun z =>
        MvPolynomial.eval (fun q => evaluateCoefficientPolynomial A (chart.coordinates q) x z) (Q j) :=
      funext fun z => evaluate_substituted chart (Q j) x z
    rw [heval]
    exact h
  apply hdet
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨c,hc,?_⟩
  funext j
  simpa only [v,map_sum,map_smul,smul_eq_mul,Matrix.vecMul,Matrix.of_apply,
    dotProduct,Pi.zero_apply,first_operator_eval] using hder j

theorem derivative_surjective_of_minor {s : ℕ} (directions : Fin s → Fin A.parameterDimension)
    (x : G.Point) (Q : Fin s → G.CoordinateRing)
    (hdet : (Matrix.of (fun i j => fderiv K (A.pullback (Q j) x) 0
      (Pi.single (directions i) 1))).det ≠ 0) :
    Function.Surjective (fun v : A.ParameterSpace => fun j => fderiv K (A.pullback (Q j) x) 0 v) := by
  classical
  let B : Matrix (Fin s) (Fin s) K := fun i j =>
    fderiv K (A.pullback (Q j) x) 0 (Pi.single (directions i) 1)
  have hu : IsUnit B.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (by rw [Matrix.det_transpose]; exact hdet))
  intro y
  obtain ⟨c,hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu y
  refine ⟨∑ i, c i • Pi.single (directions i) 1,?_⟩
  funext j
  simpa only [map_sum,map_smul,smul_eq_mul,Matrix.mulVec,Matrix.transpose_apply,
    dotProduct,B,mul_comm] using congrFun hc j

/-- The independent monomials in the proof of Proposition 4.7. Coefficients
are arbitrary polynomials; homogeneous projection handles every graded piece
before the pointwise jet calculation is extended from a dense open subset. -/
theorem homogeneous_monomials_independent_of_contact [CharZero K]
    (V : Set G.Point) (hV : @IsIrreducible _ G.zariskiTopology V)
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (T : ℕ) (hcontact : ∀ x ∈ V, I ≤ jetIdeal A x T)
    {s : ℕ} (Q : Fin s → G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hQ : ∀ i, G.ambient.IsHomogeneous (Q i) D)
    (hQI : ∀ i, Q i ∈ G.vanishingIdeal V)
    (directions : Fin s → Fin A.parameterDimension) (x₀ : G.Point) (hx₀ : x₀ ∈ V)
    (hdet : (Matrix.of (fun i j => fderiv K (A.pullback (Q j) x₀) 0
      (Pi.single (directions i) 1))).det ≠ 0) :
    ∀ n ≤ T, ∀ c : Sym (Fin s) n → G.CoordinateRing,
      (∑ a, c a * ((a : Multiset (Fin s)).map Q).prod) ∈
        I ⊔ (G.vanishingIdeal V)^(n+1) → ∀ a, c a ∈ G.vanishingIdeal V := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  obtain ⟨_,_,hatlas⟩ := AtlasSupport.exists_uniformly_bounded_translation_atlas (K := K)
  obtain ⟨atlas,_⟩ := hatlas G A 0
  obtain ⟨a₀,ha₀⟩ := atlas.covers x₀
  let chart := atlas.chart a₀
  let B : Matrix (Fin s) (Fin s) G.CoordinateRing := fun i j =>
    polynomialOperator chart 1 (fun _ => directions i) (Q j)
  let R := B.det
  let F : G.FactorIndex → ℕ := fun i => chart.degree i * D i
  have hB (i j) : G.ambient.IsHomogeneous (B i j) F :=
    polynomialOperator_homogeneous chart _ _ _ D (hQ j)
  have hR : G.ambient.IsHomogeneous R (s • F) := G.ambient.isHomogeneous_det B F hB
  have heval (x : G.Point) : G.ambient.eval R (G.embedding x) =
      (Matrix.of (fun i j => G.ambient.eval (B i j) (G.embedding x))).det := by
    exact RingHom.map_det (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) B
  let U : Set G.Point := chart.domain ∩ {x | G.ambient.eval R (G.embedding x) ≠ 0}
  have hU : IsOpen U := chart.domain_isOpen.inter
    ((G.ambient.isOpen_basic R (s • F) hR).preimage continuous_induced_dom)
  have hU₀ : (V ∩ U).Nonempty := by
    refine ⟨x₀,hx₀,ha₀,?_⟩
    change G.ambient.eval R (G.embedding x₀) ≠ 0
    rw [heval]
    exact operator_derivative_minor_ne_zero chart directions V x₀ hx₀ ha₀ Q hQI
      (fun j => ⟨D,hQ j⟩) hdet
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  intro n hn c hrelation
  let J := I ⊔ (G.vanishingIdeal V)^(n+1)
  have hJ : IsMultihomogeneousIdeal G.ambient J := homogeneousIdeal_sup _ _ hI
    (homogeneousIdeal_pow _ (vanishingIdeal_multihomogeneous K G.ambient _) _)
  have hJcontact (x : G.Point) (hx : x ∈ V) : J ≤ jetIdeal A x n := by
    refine sup_le ?_ (vanishingIdeal_pow_le_jetIdeal A V x hx n)
    intro P hP k hk
    exact hcontact x hx hP k (hk.trans hn)
  have hcomponents (E : G.FactorIndex → ℕ) (a : Sym (Fin s) n) :
      weightedHomogeneousComponent w E (c a) ∈ G.vanishingIdeal V := by
    let cE := fun a => weightedHomogeneousComponent w E (c a)
    have hcE (b : Sym (Fin s) n) : G.ambient.IsHomogeneous (cE b) E :=
      (G.ambient.degreePiece_iff _ E).mp (weightedHomogeneousComponent_mem w (c b) E)
    have hm (b : Sym (Fin s) n) :
        G.ambient.IsHomogeneous ((b : Multiset (Fin s)).map Q).prod (n • D) :=
      homogeneous_sym_monomial Q D hQ b
    have hprojected : (∑ b, cE b * ((b : Multiset (Fin s)).map Q).prod) ∈ J := by
      have hh := hJ _ hrelation (n • D + E)
      have heq : weightedHomogeneousComponent w (n • D + E)
          (∑ b, c b * ((b : Multiset (Fin s)).map Q).prod) =
          ∑ b, cE b * ((b : Multiset (Fin s)).map Q).prod := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [mul_comm (c b),Hilbert.component_mul_homogeneous G.ambient (hm b) (c b) E,mul_comm]
      rwa [heq] at hh
    apply homogeneous_mem_vanishingIdeal_of_open V U hV hU hU₀ _ E (hcE a)
    intro x hx
    have hop : (Matrix.of (fun i j => G.ambient.eval (B i j) (G.embedding x))).det ≠ 0 := by
      rw [← heval]
      exact hx.2.2
    have hintr := intrinsic_derivative_minor_ne_zero chart directions V x hx.1 hx.2.1 Q hQI
      (fun j => ⟨D,hQ j⟩) hop
    have hqzero (j) : A.pullback (Q j) x 0 = 0 :=
      G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal (Set.mem_image_of_mem G.embedding hx.1)
        _ (lift_zero_represents A x) (hQI j)
    have hjet : ∀ k ≤ n, iteratedFDeriv K k
        (fun z => ∑ b, A.pullback (cE b) x z *
          ((b : Multiset (Fin s)).map (fun j => A.pullback (Q j) x z)).prod) 0 = 0 := by
      have heq : A.pullback (∑ b, cE b * ((b : Multiset (Fin s)).map Q).prod) x =
          fun z => ∑ b, A.pullback (cE b) x z *
            ((b : Multiset (Fin s)).map (fun j => A.pullback (Q j) x z)).prod := by
        funext z
        simp only [AnalyticSubgroup.pullback,map_sum,map_mul,map_multiset_prod,
          Multiset.map_map,Function.comp_def]
      rw [← heq]
      exact hJcontact x hx.1 hprojected
    have hczero := monomial_jet_coefficients_zero (fun j => A.pullback (Q j) x)
      (fun j => pullback_analytic A (Q j) x) hqzero
      (derivative_surjective_of_minor directions x Q hintr)
      (fun b => A.pullback (cE b) x) (fun b => pullback_analytic A (cE b) x) hjet a
    exact (G.ambient.eval_eq_zero_iff_of_lift (G.embedding x) (A.lift x 0)
      (lift_zero_represents A x) _ E (hcE a)).mp hczero
  intro a
  rw [← sum_weightedHomogeneousComponent w (c a),
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) (c a))]
  exact (G.vanishingIdeal V).sum_mem (fun E _ => hcomponents E a)

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/IndependentMonomialLocalLength.lean

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace TranscendenceTheory
variable {R : Type*} [CommRing R]

/-- Independence modulo an ideal and a prime forces every new generator
to enlarge the ideal after localization at that prime. -/
theorem localized_span_strict_of_independent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J p : Ideal R) [p.IsPrime] (v : ι → R)
    (hind : ∀ c : ι → R, (∑ i, c i * v i) ∈ J → ∀ i, c i ∈ p)
    (S : Finset ι) (i : ι) (hi : i ∉ S) :
    (J ⊔ Ideal.span (v '' (S : Set ι))).map (algebraMap R (Localization.AtPrime p)) <
      (J ⊔ Ideal.span (v '' (↑(insert i S) : Set ι))).map
        (algebraMap R (Localization.AtPrime p)) := by
  classical
  let f := algebraMap R (Localization.AtPrime p)
  apply lt_iff_le_not_ge.mpr
  refine ⟨Ideal.map_mono (sup_le_sup_left (Ideal.span_mono
    (Set.image_mono (by intro j hj; exact Finset.mem_insert_of_mem hj))) _),?_⟩
  intro hle
  have hv : v i ∈ J ⊔ Ideal.span (v '' (↑(insert i S) : Set ι)) :=
    Ideal.mem_sup_right (Ideal.subset_span ⟨i,Finset.mem_insert_self i S,rfl⟩)
  have hloc := hle (Ideal.mem_map_of_mem f hv)
  obtain ⟨s,hs,hsv⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    p.primeCompl (Localization.AtPrime p) _ (v i)).mp hloc
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hsv
  obtain ⟨c,hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' R).mp hy
  let d : ι → R := fun j => (if j = i then s else 0) - (if j ∈ S then c j else 0)
  have hd : (∑ j, d j * v j) ∈ J := by
    have heq : (∑ j, d j * v j) = s * v i - y := by
      simp only [d,sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul]
      rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ i)]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
      simpa only [smul_eq_mul] using congrArg (fun z => s*v i-z) hc
    rw [heq,← hxy,add_sub_cancel_right]
    exact hx
  have hsi := hind d hd i
  exact hs (by simpa [d,hi] using hsi)

/-- A finite independent family between two ideals contributes its cardinality
to the actual localized quotient length. -/
theorem local_coheight_add_card_le {ι : Type*} [Fintype ι]
    (J N p : Ideal R) [p.IsPrime] (hJN : J ≤ N) (v : ι → R)
    (hv : ∀ i, v i ∈ N)
    (hind : ∀ c : ι → R, (∑ i, c i * v i) ∈ J → ∀ i, c i ∈ p) :
    Order.coheight (N.map (algebraMap R (Localization.AtPrime p))) + Fintype.card ι ≤
      Order.coheight (J.map (algebraMap R (Localization.AtPrime p))) := by
  classical
  let f := algebraMap R (Localization.AtPrime p)
  have h (S : Finset ι) :
      Order.coheight ((J ⊔ Ideal.span (v '' (S : Set ι))).map f) + S.card ≤
        Order.coheight (J.map f) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      have hstep := Order.coheight_add_one_le
        (localized_span_strict_of_independent J p v hind S i hi)
      rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]
      calc
        _ = (Order.coheight ((J ⊔ Ideal.span (v '' (↑(insert i S) : Set ι))).map f) + 1)
            + S.card := by ac_rfl
        _ ≤ Order.coheight ((J ⊔ Ideal.span (v '' (S : Set ι))).map f) + S.card :=
          add_le_add hstep le_rfl
        _ ≤ _ := ih
  have hsub : J ⊔ Ideal.span (v '' (↑(Finset.univ : Finset ι) : Set ι)) ≤ N := by
    refine sup_le hJN (Ideal.span_le.mpr ?_)
    rintro _ ⟨i,_,rfl⟩
    exact hv i
  exact (add_le_add (Order.coheight_anti (Ideal.map_mono hsub)) le_rfl).trans
    (by simpa only [Finset.card_univ] using h Finset.univ)

/-- The powers of a prime filter the quotient. Independent families in its
first T+1 graded layers give an additive lower bound for its local length. -/
theorem local_length_ge_independent_layers (I p : Ideal R) [p.IsPrime]
    (T : ℕ) (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (v : ∀ n, ι n → R)
    (hv : ∀ n ≤ T, ∀ i, v n i ∈ p ^ n)
    (hind : ∀ n ≤ T, ∀ c : ι n → R,
      (∑ i, c i * v n i) ∈ I ⊔ p ^ (n+1) → ∀ i, c i ∈ p) :
    (∑ n ∈ Finset.range (T+1), (Fintype.card (ι n) : ℕ∞)) ≤
      Module.length (Localization.AtPrime p)
        ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  let f := algebraMap R (Localization.AtPrime p)
  have hbound (n : ℕ) (hn : n ≤ T+1) :
      (∑ j ∈ Finset.range n, (Fintype.card (ι j) : ℕ∞)) ≤
        Order.coheight ((I ⊔ p^n).map f) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      apply (add_le_add (ih (by omega)) le_rfl).trans
      apply local_coheight_add_card_le _ _ p
        (sup_le_sup_left (Ideal.pow_le_pow_right (by omega : n ≤ n+1)) I)
        (v n) (fun i => Ideal.mem_sup_right (hv n (by omega) i)) (hind n (by omega))
  rw [Module.length_quotient]
  exact (hbound (T+1) le_rfl).trans (Order.coheight_anti (Ideal.map_mono le_sup_left))

theorem sym_monomial_mem_pow {s n : ℕ} (p : Ideal R) (Q : Fin s → R)
    (hQ : ∀ i, Q i ∈ p) (a : Sym (Fin s) n) :
    ((a : Multiset (Fin s)).map Q).prod ∈ p^n := by
  have h (m : Multiset (Fin s)) : (m.map Q).prod ∈ p^m.card := by
    induction m using Multiset.induction_on with
    | empty => simp
    | cons i m ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons]
      rw [pow_succ']
      exact Ideal.mul_mem_mul (hQ i) ih
  simpa using h a

/-- The algebraic counting step in Philippon's Proposition 4.7, including
degree zero and the case of zero transverse directions. -/
theorem local_length_ge_binomial_of_monomial_independent
    (I p : Ideal R) [p.IsPrime] (s T : ℕ) (Q : Fin s → R) (hQ : ∀ i, Q i ∈ p)
    (hind : ∀ n ≤ T, ∀ c : Sym (Fin s) n → R,
      (∑ a, c a * ((a : Multiset (Fin s)).map Q).prod) ∈ I ⊔ p^(n+1) →
      ∀ a, c a ∈ p) :
    (Nat.choose (T+s) s : ℕ∞) ≤ Module.length (Localization.AtPrime p)
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  have h := local_length_ge_independent_layers I p T (fun n => Sym (Fin s) n)
    (fun _ a => ((a : Multiset (Fin s)).map Q).prod)
    (fun n _ a => sym_monomial_mem_pow p Q hQ a) hind
  simpa only [Sym.card_sym_eq_multichoose,Fintype.card_fin,← Nat.cast_sum,
    Nat.sum_range_multichoose] using h

end TranscendenceTheory

end
end


section
-- Implementation: Solutions/PhilipponCosetMultiplicity.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport

theorem IsPhilipponBaseField.charZero {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CharZero K := by
  rcases hK with ⟨e,_⟩ | ⟨p,hp,h⟩
  · exact e.toRingHom.charZero
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e,_⟩ := h
    exact e.toRingHom.charZero

/-- Philippon's corrected binomial multiplicity bound, Proposition 4.7. -/
theorem proposition_4_7
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (T : ℕ)
    (hcomponent : IncompletelyDefines G I (translate g H.carrier))
    (hprolongation : IncompletelyDefines G (differentialIdeal A 0 T I)
      (translate g H.carrier)) :
    IncompletelyDefinesWithMultiplicityAtLeast G I (translate g H.carrier)
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier)) := by
  letI : CompleteSpace K := hK.completeSpace
  letI : CharZero K := hK.charZero
  let q : PrimeSpectrum G.CoordinateRing :=
    ⟨G.vanishingIdeal (translate g H.carrier),H.translated_vanishingIdeal_isPrime hH g⟩
  let I₀ := G.vanishingIdeal Set.univ ⊔ I
  let J := Hilbert.primaryComponent K G.factorCount G.ambient.ambientDimension I₀ q
  have hI₀ : IsMultihomogeneousIdeal G.ambient I₀ := homogeneousIdeal_sup _ _
    (vanishingIdeal_multihomogeneous K G.ambient _) hI
  have hJ : IsMultihomogeneousIdeal G.ambient J := Hilbert.primaryComponent_homogeneous
    G.ambient I₀ hI₀ q (incomplete_coset_minimalPrime H hH g I hcomponent)
  have hJcontact : ∀ x ∈ translate g H.carrier, J ≤ jetIdeal A x T :=
    primaryComponent_contact_of_incomplete_differential hK H hH g I hI T hcomponent hprolongation
  obtain ⟨directions,htransverse⟩ := exists_transverseCoordinateFamily A H
  have hg : g ∈ translate g H.carrier := ⟨0,H.toAddSubgroup.zero_mem,add_zero g⟩
  obtain ⟨D,Q,hQI,hQ,hdet⟩ := exists_uniform_transverse_derivative_minor A H g g hg
    directions htransverse
  have hind := homogeneous_monomials_independent_of_contact (translate g H.carrier)
    (H.isIrreducible_translate hH g) J hJ T hJcontact Q D hQ hQI directions g hg hdet
  letI : q.asIdeal.IsPrime := q.isPrime
  have hlength := TranscendenceTheory.local_length_ge_binomial_of_monomial_independent
    J q.asIdeal (analyticCodimension A H.carrier) T Q hQI hind
  apply (coset_multiplicity_iff_localLength H hH g I hcomponent _).mpr
  change (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℕ∞) ≤
    Module.length (Localization.AtPrime q.asIdeal)
      ((Localization.AtPrime q.asIdeal) ⧸ I₀.map (algebraMap G.CoordinateRing (Localization.AtPrime q.asIdeal)))
  have hmap : J.map (algebraMap G.CoordinateRing (Localization.AtPrime q.asIdeal)) =
      I₀.map (algebraMap G.CoordinateRing (Localization.AtPrime q.asIdeal)) :=
    IsLocalization.map_under q.asIdeal.primeCompl _ _
  change (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℕ∞) ≤
    Module.length (Localization.AtPrime q.asIdeal)
      ((Localization.AtPrime q.asIdeal) ⧸ J.map (algebraMap G.CoordinateRing (Localization.AtPrime q.asIdeal))) at hlength
  rwa [hmap] at hlength

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (T : ℕ)
    (hcomponent : IncompletelyDefines G I (PhilipponMultiplicity.translate g H.carrier))
    (hprolongation : IncompletelyDefines G (differentialIdeal A 0 T I)
      (PhilipponMultiplicity.translate g H.carrier)) :
    IncompletelyDefinesWithMultiplicityAtLeast G I (PhilipponMultiplicity.translate g H.carrier)
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier)) := by
  exact PhilipponMultiplicity.proposition_4_7 K hK G A H hH g I hI T hcomponent hprolongation
