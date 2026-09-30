-- Prove2me | solution 1 for WeierstrassEllipticZeta.subgroup_degree_profile_of_paper_type
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T01:21:56.194603+00:00
-- url     : https://prove2.me/submissions/00dc5c89-7d31-4b65-9cf6-8eeb10ea4874

import Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_hilbert_polynomial
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_group_with_regular_negation
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_group_geometry
import Theorems.Thm_WeierstrassEllipticZeta_additive_line_hilbert_degree
import Theorems.Thm_WeierstrassEllipticZeta_additive_plane_hilbert_degree

-- Source: Solutions/PhilipponProjectiveGeometry.lean

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
-- Source: Solutions/PhilipponPointHilbert.lean

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
-- Source: Solutions/PhilipponProjectiveContact.lean

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
-- Source: Solutions/PhilipponAdditiveSubgroups.lean

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
-- Source: Solutions/PhilipponHomogeneousOperations.lean

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
-- Source: Solutions/PhilipponParametrizedHilbert.lean

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

end PhilipponMultiplicity.MultiProjectiveSpace

end
-- Source: Solutions/PhilipponFixedFactorHilbert.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

variable {K : Type*} [Field K] (N : ℕ)

abbrev fixedFactorAmbient : MultiProjectiveSpace K := ⟨2, by decide, ![1, N]⟩

def fixedFactorVariables (t : K) :
    (fixedFactorAmbient N (K := K)).Variable → (projectiveSpace K N).CoordinateRing :=
  fun x => (Fin.cons (α := fun i : Fin 2 =>
      Fin (![1, N] i + 1) → (projectiveSpace K N).CoordinateRing)
    (fun j : Fin 2 => C (![1, t] j))
    (Fin.cons (α := fun i : Fin 1 =>
      Fin (![1, N] i.succ + 1) → (projectiveSpace K N).CoordinateRing)
      (fun j : Fin (N + 1) => X ⟨(0 : Fin 1), j⟩) (fun i => Fin.elim0 i))) x.1 x.2

def fixedFactorRestriction (t : K) :
    (fixedFactorAmbient N (K := K)).CoordinateRing →ₐ[K]
      (projectiveSpace K N).CoordinateRing := aeval (fixedFactorVariables N t)

def fixedFactorInjection (v : (projectiveSpace K N).Variable) :
    (fixedFactorAmbient N (K := K)).Variable := ⟨1, v.2⟩

theorem projective_homogeneous_iff (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) :
    (projectiveSpace K N).IsHomogeneous P (fun _ => n) ↔ P.IsHomogeneous n := by
  classical
  change (∀ d ∈ P.support, ∀ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ = n) ↔ _
  constructor
  · intro h d hd
    rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
    change (∑ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ • (1 : ℕ)) = n
    simpa [Fin.sum_univ_one] using h d (mem_support_iff.mpr hd) (0 : Fin 1)
  · intro h d hd i
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have hh := h (mem_support_iff.mp hd)
    rw [Finsupp.weight_eq_sum, Fintype.sum_sigma] at hh
    change (∑ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ • (1 : ℕ)) = n at hh
    simpa [Fin.sum_univ_one] using hh

theorem fixedFactorRestriction_homogeneous (t : K)
    (P : (fixedFactorAmbient N (K := K)).CoordinateRing) (D : Fin 2 → ℕ)
    (hP : (fixedFactorAmbient N).IsHomogeneous P D) :
    (projectiveSpace K N).IsHomogeneous (fixedFactorRestriction N t P) (fun _ => D 1) := by
  classical
  rw [projective_homogeneous_iff]
  change (aeval (fixedFactorVariables N t) P).IsHomogeneous _
  rw [aeval_def, eval₂_eq]
  apply IsHomogeneous.sum
  intro d hd
  change (C (coeff d P) * d.prod (fun j n => fixedFactorVariables N t j ^ n)).IsHomogeneous _
  apply MvPolynomial.IsHomogeneous.C_mul
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hprod := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun j : (fixedFactorAmbient N (K := K)).Variable => fixedFactorVariables N t j ^ d j)
    (fun j => if j.1 = 0 then 0 else d j) (fun j _ => ?_)
  · convert hprod using 1
    rw [Fintype.sum_sigma]
    change D 1 = ∑ i : Fin 2, ∑ j : Fin (![1, N] i + 1),
      if i = 0 then 0 else d ⟨i, j⟩
    simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, Finset.sum_const_zero, zero_add]
    exact (hP d hd 1).symm
  · rcases j with ⟨i, j⟩
    fin_cases i
    · simpa [fixedFactorVariables] using
        (MvPolynomial.isHomogeneous_C ((projectiveSpace K N).Variable) (![1, t] j)).pow (d ⟨0, j⟩)
    · simpa [fixedFactorVariables] using
        (MvPolynomial.isHomogeneous_X K (⟨(0 : Fin 1), j⟩ : (projectiveSpace K N).Variable)).pow (d ⟨1, j⟩)

theorem fixedFactorInjection_injective :
    Function.Injective (fixedFactorInjection N (K := K)) := by
  rintro ⟨a, j⟩ ⟨b, k⟩ h
  have hj : j = k := by simpa [fixedFactorInjection] using h
  subst k
  have hab : a = b := Subsingleton.elim (α := Fin 1) _ _
  subst b
  rfl

theorem fixedFactor_rename_homogeneous (P : (projectiveSpace K N).CoordinateRing)
    (n : ℕ) (hP : (projectiveSpace K N).IsHomogeneous P (fun _ => n)) :
    (fixedFactorAmbient N).IsHomogeneous (rename (fixedFactorInjection N) P) ![0, n] := by
  classical
  intro d hd i
  rw [support_rename_of_injective (fixedFactorInjection_injective N)] at hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  fin_cases i
  · apply Finset.sum_eq_zero
    intro j _
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨b, k⟩, h⟩
    have hh := congrArg Sigma.fst h
    norm_num [fixedFactorInjection] at hh
  · change (∑ j : Fin (N + 1), (a.mapDomain (fixedFactorInjection N)) ⟨1, j⟩) = n
    have he (j : Fin (N + 1)) :
        (a.mapDomain (fixedFactorInjection N)) ⟨1, j⟩ = a ⟨(0 : Fin 1), j⟩ :=
      Finsupp.mapDomain_apply (fixedFactorInjection_injective N) a ⟨(0 : Fin 1), j⟩
    simp_rw [he]
    exact hP a ha (0 : Fin 1)

theorem fixedFactorRestriction_rename (t : K)
    (P : (projectiveSpace K N).CoordinateRing) :
    fixedFactorRestriction N t (rename (fixedFactorInjection N) P) = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [fixedFactorRestriction]
  | add P Q ihP ihQ => simp only [map_add, ihP, ihQ]
  | mul_X P j ih =>
      rw [map_mul, map_mul, ih, rename_X]
      rcases j with ⟨b, j⟩
      have hb : b = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst b
      simp [fixedFactorRestriction, fixedFactorInjection, fixedFactorVariables]

theorem fixedFactorRestriction_degreePiece (t : K) (D : Fin 2 → ℕ) :
    (Hilbert.degreePiece K 2 ![1, N] D).map
      (fixedFactorRestriction N t).toLinearMap =
        Hilbert.degreePiece K 1 (fun _ => N) (fun _ => D 1) := by
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    exact ((projectiveSpace K N).degreePiece_iff _ _).mpr
      (fixedFactorRestriction_homogeneous N t P D
        (((fixedFactorAmbient N).degreePiece_iff _ _).mp hP))
  · intro P hP
    let Q := X (⟨0, 0⟩ : (fixedFactorAmbient N (K := K)).Variable) ^ D 0 *
      rename (fixedFactorInjection N) P
    refine ⟨Q, ?_, ?_⟩
    · apply ((fixedFactorAmbient N).degreePiece_iff _ _).mpr
      have hh := (((fixedFactorAmbient N).isHomogeneous_X ⟨0, 0⟩).pow
        (fixedFactorAmbient N) (D 0)).mul (fixedFactorAmbient N)
        (fixedFactor_rename_homogeneous N P (D 1)
          (((projectiveSpace K N).degreePiece_iff _ _).mp hP))
      convert hh using 1
      funext i
      fin_cases i <;> simp
    · change fixedFactorRestriction N t Q = P
      dsimp [Q]
      rw [map_mul, map_pow, fixedFactorRestriction_rename]
      simp [fixedFactorRestriction, fixedFactorVariables]

def fixedFactorPoint (t : K) (q : (projectiveSpace K N).Point) :
    (fixedFactorAmbient N (K := K)).Point :=
  Fin.cons (Projectivization.mk K ![1, t]
    (by intro h; exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h 0)))
    (Fin.cons (q (0 : Fin 1)) (fun i => Fin.elim0 i))

theorem fixedFactorRestriction_eval (t : K)
    (P : (fixedFactorAmbient N (K := K)).CoordinateRing)
    (q : (projectiveSpace K N).Point) :
    (projectiveSpace K N).eval (fixedFactorRestriction N t P) q =
      MvPolynomial.eval (fun j => (projectiveSpace K N).eval (fixedFactorVariables N t j) q) P := by
  change (aeval ((projectiveSpace K N).coordinate q))
    (aeval (fixedFactorVariables N t) P) = _
  rw [comp_aeval_apply]
  rfl

theorem fixedFactor_eval_zero_iff (t : K)
    (P : (fixedFactorAmbient N (K := K)).CoordinateRing)
    (D : Fin 2 → ℕ) (hP : (fixedFactorAmbient N).IsHomogeneous P D)
    (q : (projectiveSpace K N).Point) :
    (projectiveSpace K N).eval (fixedFactorRestriction N t P) q = 0 ↔
      (fixedFactorAmbient N).eval P (fixedFactorPoint N t q) = 0 := by
  rw [fixedFactorRestriction_eval]
  apply (fixedFactorAmbient N).eval_eq_zero_iff_of_lift _ _ _ P D hP
  intro i
  change Fin 2 at i
  fin_cases i
  · have he : (fun j : Fin 2 => (projectiveSpace K N).eval
        (fixedFactorVariables N t ⟨0, j⟩) q) = ![1, t] := by
      funext j
      simp [fixedFactorVariables, MultiProjectiveSpace.eval]
    change ∃ h : (fun j : Fin 2 => (projectiveSpace K N).eval
      (fixedFactorVariables N t ⟨0, j⟩) q) ≠ 0,
      Projectivization.mk K (fun j : Fin 2 => (projectiveSpace K N).eval
        (fixedFactorVariables N t ⟨0, j⟩) q) h = fixedFactorPoint N t q (0 : Fin 2)
    rw [he]
    refine ⟨?_, rfl⟩
    intro h
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h 0)
  · have he : (fun j : Fin (N + 1) => (projectiveSpace K N).eval
        (fixedFactorVariables N t ⟨1, j⟩) q) = (q (0 : Fin 1)).rep := by
      funext j
      simp [fixedFactorVariables, MultiProjectiveSpace.eval, coordinate]
    change ∃ h : (fun j : Fin (N + 1) => (projectiveSpace K N).eval
      (fixedFactorVariables N t ⟨1, j⟩) q) ≠ 0,
      Projectivization.mk K (fun j : Fin (N + 1) => (projectiveSpace K N).eval
        (fixedFactorVariables N t ⟨1, j⟩) q) h = fixedFactorPoint N t q (1 : Fin 2)
    rw [he]
    exact ⟨Projectivization.rep_nonzero _, Projectivization.mk_rep _⟩

/-- Adding a fixed first projective coordinate does not change any homogeneous
quotient dimension in the other factor. This identifies the actual vanishing
ideals on each degree piece, without assuming Hilbert polynomials exist. -/
theorem hilbertFunction_fixedFactor {T : Type*} (t : K)
    (q : T → (projectiveSpace K N).Point) (D : Fin 2 → ℕ) :
    Hilbert.hilbertFunction K 2 ![1, N]
      ((fixedFactorAmbient N).vanishingIdeal (Set.range (fun s => fixedFactorPoint N t (q s)))) D =
    Hilbert.hilbertFunction K 1 (fun _ => N)
      ((projectiveSpace K N).vanishingIdeal (Set.range q)) (fun _ => D 1) := by
  let I := (projectiveSpace K N).vanishingIdeal (Set.range q)
  let φ := (Ideal.Quotient.mkₐ K I).comp (fixedFactorRestriction N t)
  rw [(fixedFactorAmbient N).hilbertFunction_eq_finrank_image _ φ D]
  · change Module.finrank K ((Hilbert.degreePiece K 2 ![1, N] D).map
        ((Ideal.Quotient.mkₐ K I).toLinearMap.comp (fixedFactorRestriction N t).toLinearMap)) = _
    rw [Submodule.map_comp, fixedFactorRestriction_degreePiece]
    rfl
  · intro P hP
    change Ideal.Quotient.mk I (fixedFactorRestriction N t P) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h s
      apply (fixedFactor_eval_zero_iff N t P D hP (q s)).mp
      exact (projectiveSpace K N).eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_range_self s)
    · intro h
      apply Ideal.subset_span
      refine ⟨⟨fun _ => D 1, fixedFactorRestriction_homogeneous N t P D hP⟩, ?_⟩
      rintro x ⟨s, rfl⟩
      exact (fixedFactor_eval_zero_iff N t P D hP (q s)).mpr (h s)

/-- Transport an established Hilbert polynomial through a fixed first factor. -/
theorem hilbertPolynomial_fixedFactor {T : Type*} (t : K)
    (q : T → (projectiveSpace K N).Point) (P : MvPolynomial (Fin 1) ℚ)
    (hP : Hilbert.IsHilbertPolynomial K 1 (fun _ => N)
      ((projectiveSpace K N).vanishingIdeal (Set.range q)) P) :
    Hilbert.hilbertPolynomial K 2 ![1, N]
      ((fixedFactorAmbient N).vanishingIdeal (Set.range (fun s => fixedFactorPoint N t (q s)))) =
        rename (fun _ : Fin 1 => (1 : Fin 2)) P := by
  obtain ⟨d₀, hd₀⟩ := hP
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => d₀ 0, ?_⟩
  intro D hD
  rw [hilbertFunction_fixedFactor, eval_rename]
  apply hd₀
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact hD 1

end PhilipponMultiplicity.MultiProjectiveSpace

end
-- Source: Solutions/PhilipponHilbertTransport.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M N : MultiProjectiveSpace K)

/-- Exact transport of quotient Hilbert functions through homogeneous coordinates.
Only equivalence of homogeneous vanishing is needed; no isomorphism of groups
or a priori equality of their carriers is assumed. -/
theorem hilbertFunction_transport {T U : Type*}
    (p : T → M.Point) (q : U → N.Point)
    (e : M.CoordinateRing ≃ₐ[K] N.CoordinateRing)
    (D : M.FactorIndex → ℕ) (E : N.FactorIndex → ℕ)
    (hhom : ∀ P, M.IsHomogeneous P D ↔ N.IsHomogeneous (e P) E)
    (hzero : ∀ P, M.IsHomogeneous P D →
      ((∀ t, M.eval P (p t) = 0) ↔ ∀ u, N.eval (e P) (q u) = 0)) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D =
    Hilbert.hilbertFunction K N.factorCount N.ambientDimension
      (N.vanishingIdeal (Set.range q)) E := by
  let I := N.vanishingIdeal (Set.range q)
  let φ := (Ideal.Quotient.mkₐ K I).comp e.toAlgHom
  have himage : (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
      e.toLinearEquiv.toLinearMap =
        Hilbert.degreePiece K N.factorCount N.ambientDimension E := by
    apply le_antisymm
    · rintro _ ⟨P, hP, rfl⟩
      exact (N.degreePiece_iff _ _).mpr ((hhom P).mp ((M.degreePiece_iff _ _).mp hP))
    · intro Q hQ
      refine ⟨e.symm Q, ?_, e.apply_symm_apply Q⟩
      apply (M.degreePiece_iff _ _).mpr
      apply (hhom _).mpr
      simpa only [e.apply_symm_apply] using (N.degreePiece_iff _ _).mp hQ
  rw [M.hilbertFunction_eq_finrank_image p φ D]
  · change Module.finrank K ((Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
      ((Ideal.Quotient.mkₐ K I).toLinearMap.comp e.toLinearEquiv.toLinearMap)) = _
    rw [Submodule.map_comp, himage]
    rfl
  · intro P hP
    change Ideal.Quotient.mk I (e P) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, hzero P hP]
    constructor
    · intro h u
      exact N.eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_range_self u)
    · intro h
      exact Ideal.subset_span ⟨⟨E, (hhom P).mp hP⟩, by
        rintro _ ⟨u, rfl⟩; exact h u⟩

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] {p : ℕ} {N₁ N₂ : Fin p → ℕ}

theorem hilbertPolynomial_eq_of_hilbertFunction_eq
    (I : Ideal (CoordinateRing K p N₁)) (J : Ideal (CoordinateRing K p N₂))
    (h : ∀ D, hilbertFunction K p N₁ I D = hilbertFunction K p N₂ J D) :
    hilbertPolynomial K p N₁ I = hilbertPolynomial K p N₂ J := by
  have hh (P) : IsHilbertPolynomial K p N₁ I P ↔ IsHilbertPolynomial K p N₂ J P := by
    simp only [IsHilbertPolynomial, h]
  by_cases hi : ∃ P, IsHilbertPolynomial K p N₁ I P
  · exact hilbertPolynomial_eq_of_isHilbertPolynomial K p N₁ I
      ((hh _).mpr (hilbertPolynomial_spec K p N₂ J (by simpa only [← hh] using hi)))
  · rw [hilbertPolynomial_eq_zero_of_not_exists K p N₁ I hi,
      hilbertPolynomial_eq_zero_of_not_exists K p N₂ J (by simpa only [← hh] using hi)]

end PhilipponMultiplicity.Hilbert

end
-- Source: Solutions/WeierstrassModelHomogeneous.lean

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

end WeierstrassEllipticZeta.PhilipponApplication.Model

end

noncomputable section
namespace PhilipponMultiplicity
def additivePoint (K : Type*) [Field K] (z : K) : Projectivization K (Fin 2 → K) :=
  Projectivization.mk K ![1, z] (by intro h; have := congrFun h 0; simpa using this)
end PhilipponMultiplicity
end
-- Source: Solutions/WeierstrassProductCoordinates.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators
open MvPolynomial TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta

abbrev extensionProductAmbient : MultiProjectiveSpace ℂ := ⟨2, by decide, ![1, 4]⟩

abbrev ExtensionProductVariable := Sigma fun i : Fin 2 => Fin (![1, 4] i + 1)

def extensionProductVariableEquiv : Fin 7 ≃ ExtensionProductVariable where
  toFun := ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 3⟩, ⟨1, 4⟩]
  invFun := fun s => if h : s.1 = 0 then
      ⟨s.2.val, by have := s.2.isLt; simp only [h] at this; norm_num at this; omega⟩
    else ⟨s.2.val + 2, by
      have hs : s.1 = 1 := by omega
      have hh := s.2.isLt
      simp only [hs] at hh
      norm_num at hh
      omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv s := by
    rcases s with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> rfl

def extensionProductEmbedding {g₂ g₃ : ℂ}
    (p : ℂ × ProjectiveExtensionChartLocus g₂ g₃) : extensionProductAmbient.Point :=
  Fin.cons (additivePoint ℂ p.1) (Fin.cons p.2.val.val (fun i => Fin.elim0 i))

private theorem product_exponent_sums (d : Fin 7 →₀ ℕ) :
    (∑ j : Fin 2, (d.mapDomain extensionProductVariableEquiv) ⟨(0 : Fin 2), j⟩) =
        d 0 + d 1 ∧
    (∑ j : Fin 5, (d.mapDomain extensionProductVariableEquiv) ⟨(1 : Fin 2), j⟩) =
        d 2 + d 3 + d 4 + d 5 + d 6 := by
  have h0 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 0
  have h1 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 1
  have h2 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 2
  have h3 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 3
  have h4 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 4
  have h5 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 5
  have h6 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 6
  change (d.mapDomain extensionProductVariableEquiv) ⟨0, 0⟩ = d 0 at h0
  change (d.mapDomain extensionProductVariableEquiv) ⟨0, 1⟩ = d 1 at h1
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 0⟩ = d 2 at h2
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 1⟩ = d 3 at h3
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 2⟩ = d 4 at h4
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 3⟩ = d 5 at h5
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 4⟩ = d 6 at h6
  simp only [Fin.sum_univ_two, Fin.sum_univ_five, h0, h1, h2, h3, h4, h5, h6, and_self]

theorem extensionProduct_homogeneous_iff (Q : MvPolynomial (Fin 7) ℂ)
    (D : Fin 2 → ℕ) :
    extensionProductAmbient.IsHomogeneous (rename extensionProductVariableEquiv Q) D ↔
      ∀ d ∈ Q.support, d 0 + d 1 = D 0 ∧ d 2 + d 3 + d 4 + d 5 + d 6 = D 1 := by
  classical
  unfold MultiProjectiveSpace.IsHomogeneous
  rw [support_rename_of_injective extensionProductVariableEquiv.injective]
  constructor
  · intro h d hd
    have hh := h _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
    exact ⟨(product_exponent_sums d).1.symm.trans (hh 0),
      (product_exponent_sums d).2.symm.trans (hh 1)⟩
  · intro h d hd i
    obtain ⟨c, hc, hcd⟩ := Finset.mem_image.mp hd
    subst d
    change Fin 2 at i
    fin_cases i
    · exact (product_exponent_sums c).1.trans (h c hc).1
    · exact (product_exponent_sums c).2.trans (h c hc).2

private theorem product_block_scale (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (v : Fin 7 → ℂ) (a b : ℂ) :
    eval ![a * v 0, a * v 1, b * v 2, b * v 3, b * v 4, b * v 5, b * v 6] Q =
      a ^ m * b ^ n * eval v Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← (hQ d hd).1, ← (hQ d hd).2]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

theorem extensionProduct_eval_zero_iff (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n)
    {g₂ g₃ : ℂ} (p : ℂ × ProjectiveExtensionChartLocus g₂ g₃) :
    extensionProductAmbient.eval (rename extensionProductVariableEquiv Q)
      (extensionProductEmbedding p) = 0 ↔
    eval ![1, p.1, p.2.val.val.rep 0, p.2.val.val.rep 1, p.2.val.val.rep 2,
      p.2.val.val.rep 3, p.2.val.val.rep 4] Q = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ ![1, p.1]
    (by intro h; have := congrFun h 0; simpa using this)
  change eval (extensionProductAmbient.coordinate (extensionProductEmbedding p))
    (rename extensionProductVariableEquiv Q) = 0 ↔ _
  rw [eval_rename]
  have hv : (fun i => extensionProductAmbient.coordinate (extensionProductEmbedding p)
      (extensionProductVariableEquiv i)) =
      ![a.val, a.val * p.1, p.2.val.val.rep 0, p.2.val.val.rep 1,
        p.2.val.val.rep 2, p.2.val.val.rep 3, p.2.val.val.rep 4] := by
    funext i
    fin_cases i <;>
      simp [extensionProductAmbient, MultiProjectiveSpace.coordinate, extensionProductEmbedding,
        extensionProductVariableEquiv, additivePoint, ← ha, Units.smul_def]
  have heval : eval (extensionProductAmbient.coordinate (extensionProductEmbedding p) ∘
      extensionProductVariableEquiv) Q =
      eval ![a.val, a.val * p.1, p.2.val.val.rep 0, p.2.val.val.rep 1,
        p.2.val.val.rep 2, p.2.val.val.rep 3, p.2.val.val.rep 4] Q :=
    congrArg (fun f : Fin 7 → ℂ => eval f Q) hv
  rw [heval]
  have hscale := product_block_scale Q m n hQ
    ![1, p.1, p.2.val.val.rep 0, p.2.val.val.rep 1, p.2.val.val.rep 2,
      p.2.val.val.rep 3, p.2.val.val.rep 4] a.val 1
  simp at hscale
  rw [hscale]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ a.ne_zero))

theorem extensionProduct_raw_eval_zero_iff (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n)
    {g₂ g₃ : ℂ} (p : ℂ × ProjectiveExtensionChartLocus g₂ g₃)
    (v : Fin 5 → ℂ) (hv : v ≠ 0) (hp : p.2.val.val = Projectivization.mk ℂ v hv) :
    extensionProductAmbient.eval (rename extensionProductVariableEquiv Q)
      (extensionProductEmbedding p) = 0 ↔
    eval ![1, p.1, v 0, v 1, v 2, v 3, v 4] Q = 0 := by
  rw [extensionProduct_eval_zero_iff Q m n hQ p]
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [hp, ← hb]
  simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul]
  have hscale := product_block_scale Q m n hQ ![1, p.1, v 0, v 1, v 2, v 3, v 4] 1 b.val
  simp at hscale
  rw [hscale]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ b.ne_zero))

end WeierstrassEllipticZeta

end
-- Source: Solutions/WeierstrassExtensionFactorDegree.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
open MvPolynomial TranscendenceTheory PhilipponMultiplicity

namespace WeierstrassEllipticZeta

variable (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

include D S hS hS_value hS_ne η e he in
/-- Fixing the additive factor leaves the extension's Hilbert polynomial unchanged. -/
theorem extension_factor_hilbertPolynomial (t : ℂ) :
    Hilbert.hilbertPolynomial ℂ 2 ![1, 4]
      (extensionProductAmbient.vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          extensionProductEmbedding (t, p)))) = C 3 * X 1 ^ 2 + C 2 := by
  let q := fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ : Fin 1 => p.val.val
  let I := (projectiveSpace ℂ 4).vanishingIdeal (Set.range q)
  have hpoly : Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4) I = C 3 * X 0 ^ 2 + C 2 :=
    projective_extension_hilbert_polynomial L D S hS hS_value hS_ne η e he
  have hne : (C 3 * X 0 ^ 2 + C 2 : MvPolynomial (Fin 1) ℚ) ≠ 0 := by
    intro h
    have hh := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) h
    norm_num at hh
  have hex : ∃ P, Hilbert.IsHilbertPolynomial ℂ 1 (fun _ => 4) I P := by
    by_contra h
    rw [Hilbert.hilbertPolynomial_eq_zero_of_not_exists ℂ 1 (fun _ => 4) I h] at hpoly
    exact hne hpoly.symm
  have hspec := Hilbert.hilbertPolynomial_spec ℂ 1 (fun _ => 4) I hex
  rw [hpoly] at hspec
  have hh := MultiProjectiveSpace.hilbertPolynomial_fixedFactor 4 t q
    (C 3 * X 0 ^ 2 + C 2) hspec
  simpa only [map_add, map_mul, map_pow, rename_C, rename_X, q,
    MultiProjectiveSpace.fixedFactorPoint, MultiProjectiveSpace.fixedFactorAmbient,
    extensionProductAmbient, extensionProductEmbedding, additivePoint] using hh

include D S hS hS_value hS_ne η e he in
/-- The actual factorial-normalized degree of {t} × G₂ is 6n². -/
theorem extension_factor_degreeValue (t : ℂ) (d : Fin 2 → ℕ) :
    Hilbert.degreeValue ℂ 2 ![1, 4]
      (extensionProductAmbient.vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          extensionProductEmbedding (t, p)))) d = 6 * (d 1 : ℚ) ^ 2 := by
  let R : MvPolynomial (Fin 2) ℚ := C 3 * X 1 ^ 2
  have hR : R.IsHomogeneous 2 := (isHomogeneous_X_pow (1 : Fin 2) 2).C_mul 3
  have hRne : R ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ (X_ne_zero _))
  have hd : (R + C 2).totalDegree = 2 := by
    rw [totalDegree_add_eq_left_of_totalDegree_lt]
    · exact hR.totalDegree hRne
    · rw [hR.totalDegree hRne]
      simp
  rw [Hilbert.degreeValue, Hilbert.degreeForm,
    extension_factor_hilbertPolynomial L D S hS hS_value hS_ne η e he]
  change MvPolynomial.eval _ (((R + C 2).totalDegree.factorial : ℚ) •
    homogeneousComponent (R + C 2).totalDegree (R + C 2)) = _
  rw [hd, map_add, homogeneousComponent_eq_self hR,
    homogeneousComponent_eq_zero 2 (C 2) (by simp), add_zero]
  norm_num [R, smul_eq_C_mul]
  ring
end WeierstrassEllipticZeta

end
-- Source: Solutions/WeierstrassModelHilbertTransport.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial PhilipponMultiplicity

namespace WeierstrassEllipticZeta.PhilipponApplication.Model
variable {S : Fin 5 → ℂ → ℂ} (M : Model S)

/-- The genuine Hilbert function of an arbitrary compatible model is determined
by its bihomogeneous equations in the original seven coordinates. -/
theorem hilbertFunction_eq_of_equations {T : Type*}
    (H : AlgebraicSubgroup M.group) (p : T → extensionProductAmbient.Point)
    (hzero : ∀ (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ), Bihomogeneous Q m n →
      ((∀ g ∈ H.carrier, M.group.ambient.eval (M.polynomial Q) (M.group.embedding g) = 0) ↔
        ∀ t, extensionProductAmbient.eval (rename extensionProductVariableEquiv Q) (p t) = 0))
    (d : Fin 2 → ℕ) :
    Hilbert.hilbertFunction ℂ 2 M.group.ambient.ambientDimension (M.group.vanishingIdeal H.carrier) d =
    Hilbert.hilbertFunction ℂ 2 ![1, 4]
      (extensionProductAmbient.vanishingIdeal (Set.range p)) d := by
  let e := (renameEquiv ℂ M.variableEquiv).symm.trans
    (renameEquiv ℂ extensionProductVariableEquiv)
  have hback (P : M.group.CoordinateRing) :
      rename M.variableEquiv (rename M.variableEquiv.symm P) = P := by
    simp [rename_rename]
  have hhom (P : M.group.CoordinateRing) :
      M.group.ambient.IsHomogeneous P d ↔ extensionProductAmbient.IsHomogeneous (e P) d := by
    have hd : d = ![d 0, d 1] := by ext i; fin_cases i <;> rfl
    calc
      M.group.ambient.IsHomogeneous P d ↔ M.group.ambient.IsHomogeneous
          (rename M.variableEquiv (rename M.variableEquiv.symm P)) ![d 0, d 1] := by
        rw [hback, ← hd]
      _ ↔ Bihomogeneous (rename M.variableEquiv.symm P) (d 0) (d 1) :=
        M.homogeneous_iff _ _ _
      _ ↔ extensionProductAmbient.IsHomogeneous
          (rename extensionProductVariableEquiv (rename M.variableEquiv.symm P)) d := by
        rw [hd]
        exact (extensionProduct_homogeneous_iff _ _).symm
      _ ↔ extensionProductAmbient.IsHomogeneous (e P) d := Iff.rfl
  have h := M.group.ambient.hilbertFunction_transport extensionProductAmbient
    (fun g : H.carrier => M.group.embedding g.val) p e d d hhom ?_
  · have hr : Set.range (fun g : H.carrier => M.group.embedding g.val) =
        M.group.embedding '' H.carrier := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩; exact ⟨g.val, g.property, rfl⟩
      · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩
    rw [hr] at h
    exact h
  · intro P hP
    let Q := rename M.variableEquiv.symm P
    have hQ : Bihomogeneous Q (d 0) (d 1) := (M.homogeneous_iff Q _ _).mp (by
      rw [hback]
      convert hP using 1
      funext i; change Fin 2 at i; fin_cases i <;> rfl)
    have hh := hzero Q (d 0) (d 1) hQ
    change ((∀ g ∈ H.carrier, M.group.ambient.eval
      (rename M.variableEquiv (rename M.variableEquiv.symm P)) (M.group.embedding g) = 0) ↔ _) at hh
    rw [hback] at hh
    change ((∀ g ∈ H.carrier, M.group.ambient.eval P (M.group.embedding g) = 0) ↔
      ∀ t, extensionProductAmbient.eval (e P) (p t) = 0) at hh
    exact (by simpa only [Subtype.forall] using hh)

theorem hilbertDegreeForm_eq_of_equations {T : Type*}
    (H : AlgebraicSubgroup M.group) (p : T → extensionProductAmbient.Point)
    (hzero : ∀ (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ), Bihomogeneous Q m n →
      ((∀ g ∈ H.carrier, M.group.ambient.eval (M.polynomial Q) (M.group.embedding g) = 0) ↔
        ∀ t, extensionProductAmbient.eval (rename extensionProductVariableEquiv Q) (p t) = 0))
    (d : Fin 2 → ℕ) :
    hilbertDegreeForm M.group H.carrier d =
      (Hilbert.degreeValue ℂ 2 ![1, 4]
        (extensionProductAmbient.vanishingIdeal (Set.range p)) d : ℝ) := by
  have hp := Hilbert.hilbertPolynomial_eq_of_hilbertFunction_eq (p := 2)
    (N₁ := M.group.ambient.ambientDimension) (N₂ := ![1, 4])
    (M.group.vanishingIdeal H.carrier)
    (extensionProductAmbient.vanishingIdeal (Set.range p))
    (M.hilbertFunction_eq_of_equations H p hzero)
  change (Hilbert.degreeValue ℂ 2 M.group.ambient.ambientDimension
    (M.group.vanishingIdeal H.carrier) d : ℝ) = _
  unfold Hilbert.degreeValue Hilbert.degreeForm
  rw [hp]

end WeierstrassEllipticZeta.PhilipponApplication.Model

end
-- Source: Solutions/WeierstrassTrivialSubgroupProfile.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open PhilipponMultiplicity

namespace WeierstrassEllipticZeta.PhilipponApplication.Model

/-- The trivial-subgroup case of the application profile, with the degree
computed from the actual multiprojective quotient Hilbert polynomial. -/
theorem subgroup_degree_profile_of_singleton {S : Fin 5 → ℂ → ℂ}
    (M : Model S) (H : AlgebraicSubgroup M.group) (hH : H.carrier = {0}) :
    M.pullbackSubmodule H = ⊥ ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        1 ≤ hilbertDegreeForm M.group H.carrier ![m, n] := by
  constructor
  · apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    change M.curve v ∈ H.carrier at hv
    rw [hH, Set.mem_singleton_iff] at hv
    apply M.curve_injective
    exact hv.trans (map_zero M.curve).symm
  · intro m n _ _
    rw [hH, hilbertDegreeForm_singleton]

end WeierstrassEllipticZeta.PhilipponApplication.Model
end

open PhilipponMultiplicity MvPolynomial
theorem WeierstrassEllipticZeta.boundary_line_degreeValue (a b ρ : ℂ) (hne : a ≠ 0 ∨ b ≠ 0)
    (p : ℂ → (@MultiProjectiveSpace.mk ℂ 2 (by decide) ![1, 4]).Point)
    (hp : ∀ t, (∃ h : ![1, a * t] ≠ (0 : Fin 2 → ℂ),
        Projectivization.mk ℂ ![1, a * t] h = p t (0 : Fin 2)) ∧
      (∃ h : ![0, 0, 1, 0, ρ + b * t] ≠ (0 : Fin 5 → ℂ),
        Projectivization.mk ℂ ![0, 0, 1, 0, ρ + b * t] h = p t (1 : Fin 2))) (D : Fin 2 → ℕ) :
    Hilbert.degreeValue ℂ 2 ![1, 4]
      ((@MultiProjectiveSpace.mk ℂ 2 (by decide) ![1, 4]).vanishingIdeal (Set.range p)) D =
        (if a = 0 then 0 else (D 0 : ℚ)) + (if b = 0 then 0 else (D 1 : ℚ)) := by
  exact WeierstrassEllipticZeta.additive_line_hilbert_degree a b ρ hne p hp D

open PhilipponMultiplicity MvPolynomial
theorem WeierstrassEllipticZeta.boundary_plane_degreeValue (ρ : ℂ)
    (p : (Fin 2 → ℂ) → (@MultiProjectiveSpace.mk ℂ 2 (by decide) ![1, 4]).Point)
    (hp : ∀ t, (∃ h : ![1, t 0] ≠ (0 : Fin 2 → ℂ),
        Projectivization.mk ℂ ![1, t 0] h = p t (0 : Fin 2)) ∧
      (∃ h : ![0, 0, 1, 0, ρ + t 1] ≠ (0 : Fin 5 → ℂ),
        Projectivization.mk ℂ ![0, 0, 1, 0, ρ + t 1] h = p t (1 : Fin 2))) (D : Fin 2 → ℕ) :
    Hilbert.degreeValue ℂ 2 ![1, 4]
      ((@MultiProjectiveSpace.mk ℂ 2 (by decide) ![1, 4]).vanishingIdeal (Set.range p)) D = 2 * (D 0 : ℚ) * (D 1 : ℚ) := by
  exact WeierstrassEllipticZeta.additive_plane_hilbert_degree ρ p hp D
-- Source: Solutions/WeierstrassSubgroupCoordinateProfile.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial PhilipponMultiplicity TranscendenceTheory

namespace WeierstrassEllipticZeta
open PhilipponApplication

private def boundaryProductPoint (t u : ℂ) : extensionProductAmbient.Point :=
  Fin.cons (additivePoint ℂ t)
    (Fin.cons (Projectivization.mk ℂ ![0, 0, 1, 0, u]
      (by intro h; exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun h 2)))
      (fun i => Fin.elim0 i))

private theorem boundaryProductPoint_eval (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : Bihomogeneous Q m n) (t u : ℂ) :
    extensionProductAmbient.eval (rename extensionProductVariableEquiv Q) (boundaryProductPoint t u) = 0 ↔
      eval ![1, t, 0, 0, 1, 0, u] Q = 0 := by
  let v : extensionProductAmbient.Variable → ℂ :=
    fun j => ![1, t, 0, 0, 1, 0, u] (extensionProductVariableEquiv.symm j)
  have hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j => v ⟨i, j⟩) h = boundaryProductPoint t u i := by
    intro i
    change Fin 2 at i
    fin_cases i
    · have he : (fun j : Fin 2 => v ⟨(0 : Fin 2), j⟩) = ![1, t] := by
        funext j; fin_cases j <;> rfl
      change ∃ h : (fun j : Fin 2 => v ⟨(0 : Fin 2), j⟩) ≠ 0,
        Projectivization.mk ℂ (fun j : Fin 2 => v ⟨(0 : Fin 2), j⟩) h = additivePoint ℂ t
      rw [he]
      exact ⟨by intro h; exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun h 0), rfl⟩
    · have he : (fun j : Fin 5 => v ⟨(1 : Fin 2), j⟩) = ![0, 0, 1, 0, u] := by
        funext j; fin_cases j <;> rfl
      change ∃ h : (fun j : Fin 5 => v ⟨(1 : Fin 2), j⟩) ≠ 0,
        Projectivization.mk ℂ (fun j : Fin 5 => v ⟨(1 : Fin 2), j⟩) h = boundaryProductPoint t u 1
      rw [he]
      exact ⟨by intro h; exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun h 2), rfl⟩
  have hh := (extensionProductAmbient.eval_eq_zero_iff_of_lift _ v hv
    (rename extensionProductVariableEquiv Q) ![m, n]
    ((extensionProduct_homogeneous_iff Q _).mpr hQ)).symm
  rw [eval_rename] at hh
  simpa only [v, Function.comp_def, Equiv.symm_apply_apply] using hh

namespace PhilipponApplication.Model
variable {S : Fin 5 → ℂ → ℂ} (M : Model S)

private theorem homogeneous_X1 : Bihomogeneous (X (1 : Fin 7) : MvPolynomial (Fin 7) ℂ) 1 0 := by
  intro d hd
  simp only [support_X, Finset.mem_singleton] at hd
  subst d
  simp

private theorem homogeneous_X2 : Bihomogeneous (X (2 : Fin 7) : MvPolynomial (Fin 7) ℂ) 0 1 := by
  intro d hd
  simp only [support_X, Finset.mem_singleton] at hd
  subst d
  simp

private theorem pullback_eq_bot_of_X1 (H : AlgebraicSubgroup M.group)
    (hH : ∀ g ∈ H.carrier,
      M.group.ambient.eval (M.polynomial (X (1 : Fin 7))) (M.group.embedding g) = 0) :
    M.pullbackSubmodule H = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  have h := (M.zero_locus (X (1 : Fin 7)) 1 0 homogeneous_X1 z).mp (hH _ hz)
  simpa [rawCoordinates] using h

private theorem pullback_le_lattice_of_X2
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (H : AlgebraicSubgroup M.group)
    (hH : ∀ g ∈ H.carrier,
      M.group.ambient.eval (M.polynomial (X (2 : Fin 7))) (M.group.embedding g) = 0) :
    M.pullbackSubmodule H ≤ L.lattice := by
  intro z hz
  by_contra hzl
  have h := (M.zero_locus (X (2 : Fin 7)) 0 1 homogeneous_X2 z).mp (hH _ hz)
  have h0 : S 0 z = 0 := by simpa [rawCoordinates] using h
  have hs : D.sigma z = 0 := by
    have hp : D.sigma z ^ 3 = 0 := by simpa [hS_value z hzl] using h0
    exact (pow_eq_zero_iff (by decide)).mp hp
  obtain ⟨j, hj⟩ := hS_ne z
  exact hj (by simp [hS_value z hzl, hs])

end PhilipponApplication.Model

/-- The complete application profile, for every compatible Model, follows from
the paper's geometric classification alone. All degree and curve-pullback claims
are derived, and no model is replaced by a specially chosen realization. -/
theorem subgroup_degree_profile_of_paper_type
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hclass : M.HasPaperSubgroupType L H) :
    (M.pullbackSubmodule H = ⊥ ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → 1 ≤ hilbertDegreeForm M.group H.carrier ![m, n]) ∨
    (M.pullbackSubmodule H ≤ L.lattice ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → (m : ℝ) ≤ hilbertDegreeForm M.group H.carrier ![m, n]) := by
  rcases hclass with hpoint | hfactor | ⟨ρ, hplane⟩ | ⟨a, b, ρ, hab, hline⟩
  · exact Or.inl (M.subgroup_degree_profile_of_singleton H hpoint)
  · left
    constructor
    · apply M.pullback_eq_bot_of_X1 H
      exact (hfactor (X 1) 1 0 Model.homogeneous_X1).mpr (by intro p; simp)
    · obtain ⟨η, hη, _⟩ := elliptic_extension_group_geometry L
      obtain ⟨group, e, he, _⟩ := projective_extension_group_with_regular_negation
        L D S hS hS_value hS_ne η hη
      letI := group
      have hz := M.hilbertDegreeForm_eq_of_equations H
        (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ => extensionProductEmbedding (0, p)) ?_
      · intro m n _ hn
        rw [hz, extension_factor_degreeValue L D S hS hS_value hS_ne η e he]
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        push_cast
        nlinarith
      · intro Q m n hQ
        exact (hfactor Q m n hQ).trans (forall_congr' (fun p =>
          (extensionProduct_eval_zero_iff Q m n hQ (0, p)).symm))
  · right
    constructor
    · apply M.pullback_le_lattice_of_X2 L D hS_value hS_ne H
      exact (hplane (X 2) 0 1 Model.homogeneous_X2).mpr (by intro p; simp)
    · let p : (Fin 2 → ℂ) → extensionProductAmbient.Point :=
        fun t => boundaryProductPoint (t 0) (ρ + t 1)
      have hz := M.hilbertDegreeForm_eq_of_equations H p (by
        intro Q m n hQ
        exact (hplane Q m n hQ).trans (forall_congr' (fun t =>
          (boundaryProductPoint_eval Q m n hQ (t 0) (ρ + t 1)).symm)))
      have hp (t : Fin 2 → ℂ) :
          (∃ h : ![1, t 0] ≠ (0 : Fin 2 → ℂ), Projectivization.mk ℂ ![1, t 0] h = p t 0) ∧
          (∃ h : ![0, 0, 1, 0, ρ + t 1] ≠ (0 : Fin 5 → ℂ),
            Projectivization.mk ℂ ![0, 0, 1, 0, ρ + t 1] h = p t 1) := by
        constructor
        · exact ⟨by intro h; exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun h 0), rfl⟩
        · exact ⟨by intro h; exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun h 2), rfl⟩
      intro m n _ hn
      rw [hz, boundary_plane_degreeValue ρ p hp]
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      push_cast
      nlinarith
  · let p : ℂ → extensionProductAmbient.Point := fun t => boundaryProductPoint (a * t) (ρ + b * t)
    have hz := M.hilbertDegreeForm_eq_of_equations H p (by
      intro Q m n hQ
      exact (hline Q m n hQ).trans (forall_congr' (fun t =>
        (boundaryProductPoint_eval Q m n hQ (a * t) (ρ + b * t)).symm)))
    have hp (t : ℂ) :
        (∃ h : ![1, a * t] ≠ (0 : Fin 2 → ℂ), Projectivization.mk ℂ ![1, a * t] h = p t 0) ∧
        (∃ h : ![0, 0, 1, 0, ρ + b * t] ≠ (0 : Fin 5 → ℂ),
          Projectivization.mk ℂ ![0, 0, 1, 0, ρ + b * t] h = p t 1) := by
      constructor
      · exact ⟨by intro h; exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun h 0), rfl⟩
      · exact ⟨by intro h; exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun h 2), rfl⟩
    by_cases ha : a = 0
    · left
      constructor
      · apply M.pullback_eq_bot_of_X1 H
        exact (hline (X 1) 1 0 Model.homogeneous_X1).mpr (by intro t; simp [ha])
      · intro m n _ hn
        have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
        rw [hz, boundary_line_degreeValue a b ρ hab p hp]
        simpa [ha, hb] using (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    · right
      constructor
      · apply M.pullback_le_lattice_of_X2 L D hS_value hS_ne H
        exact (hline (X 2) 0 1 Model.homogeneous_X2).mpr (by intro t; simp)
      · intro m n _ _
        rw [hz, boundary_line_degreeValue a b ρ hab p hp]
        by_cases hb : b = 0 <;> simp [ha, hb]

end WeierstrassEllipticZeta

end

set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity
theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hclass : M.HasPaperSubgroupType L H) :
    (M.pullbackSubmodule H = ⊥ ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → 1 ≤ hilbertDegreeForm M.group H.carrier ![m, n]) ∨
    (M.pullbackSubmodule H ≤ L.lattice ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → (m : ℝ) ≤ hilbertDegreeForm M.group H.carrier ![m, n]) := by
  exact WeierstrassEllipticZeta.subgroup_degree_profile_of_paper_type L D S hS hS_value hS_ne M H hclass
#print axioms solution
