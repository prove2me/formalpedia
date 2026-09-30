-- Prove2me | solution 1 for WeierstrassEllipticZeta.subgroup_exponential_preimage_additive
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T04:23:34.230237+00:00
-- url     : https://prove2.me/submissions/6d86d5d1-512a-4635-a34b-c996ad4bfd3f

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_group_geometry
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_group_with_regular_negation
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_addition_regular
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_curve_zariski_dense
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_hilbert_polynomial
import Theorems.Thm_PhilipponMultiplicity_additive_projective_hilbert_polynomial
import Definitions.Def_WeierstrassEllipticZeta_ExponentialPreimage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity



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

-- Source: Solutions/PhilipponRegularMapTopology.lean

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

-- Source: Solutions/PhilipponProjectiveTranslations.lean

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

-- Source: Solutions/PhilipponRegularMapComposition.lean

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

-- Source: Solutions/PhilipponCoordinateReindex.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

def projectiveReindex {ι κ : Type*} (c : κ ≃ ι) :
    Projectivization K (ι → K) ≃ Projectivization K (κ → K) where
  toFun := Projectivization.map (LinearEquiv.funCongrLeft K K c).toLinearMap
    (LinearEquiv.funCongrLeft K K c).injective
  invFun := Projectivization.map (LinearEquiv.funCongrLeft K K c.symm).toLinearMap
    (LinearEquiv.funCongrLeft K K c.symm).injective
  left_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    exact ⟨1, by ext j; simp⟩
  right_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    exact ⟨1, by ext j; simp⟩

theorem projectiveReindex_mk {ι κ : Type*} (c : κ ≃ ι) (v : ι → K) (hv : v ≠ 0) :
    projectiveReindex c (Projectivization.mk K v hv) =
      Projectivization.mk K (fun j => v (c j)) (by
        intro h
        apply hv
        ext i
        simpa using congrFun h (c.symm i)) := rfl

namespace MultiProjectiveSpace
variable {r : ℕ} (hr : 0 < r) {d e : Fin r → ℕ}

def coordinateReindex (c : ∀ i, Fin (e i + 1) ≃ Fin (d i + 1)) :
    (mk (K := K) r hr d).Point ≃ (mk (K := K) r hr e).Point :=
  Equiv.piCongrRight (fun i => projectiveReindex (c i))

theorem coordinateReindex_regular (c : ∀ i, Fin (e i + 1) ≃ Fin (d i + 1)) :
    (mk (K := K) r hr d).IsRegularAlong (mk (K := K) r hr e) id (coordinateReindex hr c) := by
  classical
  let := (mk (K := K) r hr d).zariskiTopology
  intro x b
  refine ⟨univ, isOpen_univ, mem_univ _, (fun i => if i = b then 1 else 0),
    (fun j => X ⟨b, c b j⟩), ?_, ?_⟩
  · intro j
    exact (mk (K := K) r hr d).isHomogeneous_X ⟨b, c b j⟩
  · intro y _
    simp only [eval, eval_X, coordinate, id_eq]
    have hn : (fun j => (y b).rep (c b j)) ≠ 0 := by
      intro h
      apply Projectivization.rep_nonzero (y b)
      ext j
      simpa using congrFun h ((c b).symm j)
    refine ⟨hn, ?_⟩
    change Projectivization.mk K (fun j => (y b).rep (c b j)) hn =
      projectiveReindex (c b) (y b)
    exact congrArg (projectiveReindex (c b)) (Projectivization.mk_rep (y b))

def coordinateHomeomorph (c : ∀ i, Fin (e i + 1) ≃ Fin (d i + 1)) :
    @Homeomorph (mk (K := K) r hr d).Point (mk (K := K) r hr e).Point
      (mk (K := K) r hr d).zariskiTopology (mk (K := K) r hr e).zariskiTopology := by
  let := (mk (K := K) r hr d).zariskiTopology
  let := (mk (K := K) r hr e).zariskiTopology
  exact
    { toEquiv := coordinateReindex hr c
      continuous_toFun := by
        have h := (coordinateReindex_regular (K := K) hr c).continuous
        rw [induced_id] at h
        exact h
      continuous_invFun := by
        have h := (coordinateReindex_regular (K := K) hr (fun i => (c i).symm)).continuous
        rw [induced_id] at h
        exact h }

/-- A change of homogeneous coordinate order preserves regularity on both
the embedded domain and the target. -/
theorem IsRegularAlong.reindex_coordinates {X : Type u}
    (c : ∀ i, Fin (e i + 1) ≃ Fin (d i + 1))
    {a f : X → (mk (K := K) r hr d).Point}
    (hf : (mk (K := K) r hr d).IsRegularAlong (mk (K := K) r hr d) a f) :
    (mk (K := K) r hr e).IsRegularAlong (mk (K := K) r hr e)
      (coordinateReindex hr c ∘ a) (coordinateReindex hr c ∘ f) := by
  have hi := (coordinateReindex_regular (K := K) hr (fun i => (c i).symm)).comp_domain
    (coordinateReindex hr c ∘ a)
  have hia : (coordinateReindex hr (fun i => (c i).symm) ∘
      (coordinateReindex hr c ∘ a)) = a := by
    funext x
    exact (coordinateReindex hr c).symm_apply_apply (a x)
  rw [hia] at hi
  exact (hi.comp hf).comp ((coordinateReindex_regular (K := K) hr c).comp_domain f)

end MultiProjectiveSpace
end PhilipponMultiplicity
end

-- Source: Solutions/PhilipponProductRegularity.lean

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

-- Source: Solutions/PhilipponDenseGroupComparison.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set
open scoped Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

/-- A regular embedding with a dense additive parametrization determines both
the carrier and group law, among locally closed regular group embeddings. -/
theorem dense_group_comparison
    (M : MultiProjectiveSpace K) {A B C : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (e : A → M.Point) (f : B → M.Point)
    (he : Function.Injective e) (hf : Function.Injective f)
    (heLoc : @IsLocallyClosed _ M.zariskiTopology (range e))
    (hfLoc : @IsLocallyClosed _ M.zariskiTopology (range f))
    (heAdd : ∀ a, M.IsRegularAlong M e (fun x => e (x + a)))
    (hfAdd : ∀ b, M.IsRegularAlong M f (fun x => f (x + b)))
    (heNeg : M.IsRegularAlong M e (fun x => e (-x)))
    (hfNeg : M.IsRegularAlong M f (fun x => f (-x)))
    (c : C →+ A) (d : C →+ B)
    (hc : @Dense _ (TopologicalSpace.induced e M.zariskiTopology) (range c))
    (hd : @Dense _ (TopologicalSpace.induced f M.zariskiTopology) (range d))
    (hcd : ∀ z, e (c z) = f (d z)) :
    ∃ E : A ≃+ B, ∀ a, f (E a) = e a := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  let := TopologicalSpace.induced f M.zariskiTopology
  let P := {p : A × B // e p.1 = f p.2}
  let j : P → M.Point := fun p => e p.val.1
  let k : C → P := fun z => ⟨(c z, d z), hcd z⟩
  have hjf : (fun p : P => f p.val.2) = j := by
    funext p
    exact p.property.symm
  have hk : j '' range k = e '' range c := by
    rw [← range_comp, ← range_comp]
    rfl
  have hkDense : @Dense _ (TopologicalSpace.induced j M.zariskiTopology) (range k) := by
    let := TopologicalSpace.induced j M.zariskiTopology
    apply (Topology.IsInducing.dense_iff (f := j) ⟨rfl⟩).mpr
    intro p
    rw [hk]
    exact (Topology.IsInducing.dense_iff (f := e) ⟨rfl⟩).mp hc p.val.1
  have hcurveAdd (z : C) (p : P) :
      e (p.val.1 + c z) = f (p.val.2 + d z) := by
    have h₁ := (heAdd (c z)).comp_domain (fun p : P => p.val.1)
    have h₂ := (hfAdd (d z)).comp_domain (fun p : P => p.val.2)
    change M.IsRegularAlong M (fun p : P => f p.val.2) _ at h₂
    rw [hjf] at h₂
    have heq := h₁.eq_of_dense M M h₂ (range k) hkDense (by
      rintro _ ⟨t, rfl⟩
      change e (c t + c z) = f (d t + d z)
      simpa only [← map_add] using hcd (t + z))
    exact congrFun heq p
  have hAdd (p q : P) : e (p.val.1 + q.val.1) = f (p.val.2 + q.val.2) := by
    have h₁ := (heAdd q.val.1).comp_domain (fun p : P => p.val.1)
    have h₂ := (hfAdd q.val.2).comp_domain (fun p : P => p.val.2)
    change M.IsRegularAlong M (fun p : P => f p.val.2) _ at h₂
    rw [hjf] at h₂
    have heq := h₁.eq_of_dense M M h₂ (range k) hkDense (by
      rintro _ ⟨z, rfl⟩
      change e (c z + q.val.1) = f (d z + q.val.2)
      simpa only [add_comm] using hcurveAdd z q)
    exact congrFun heq p
  have hNeg (p : P) : e (-p.val.1) = f (-p.val.2) := by
    have h₁ := heNeg.comp_domain (fun p : P => p.val.1)
    have h₂ := hfNeg.comp_domain (fun p : P => p.val.2)
    change M.IsRegularAlong M (fun p : P => f p.val.2) _ at h₂
    rw [hjf] at h₂
    have heq := h₁.eq_of_dense M M h₂ (range k) hkDense (by
      rintro _ ⟨z, rfl⟩
      change e (-c z) = f (-d z)
      simpa only [map_neg] using hcd (-z))
    exact congrFun heq p
  let H : AddSubgroup (A × B) :=
    { carrier := {p | e p.1 = f p.2}
      zero_mem' := by change e 0 = f 0; simpa only [map_zero] using hcd 0
      add_mem' := fun hp hq => hAdd ⟨_, hp⟩ ⟨_, hq⟩
      neg_mem' := fun hp => hNeg ⟨_, hp⟩ }
  have heIn : range e ⊆ closure (range f) := by
    rintro _ ⟨a, rfl⟩
    apply closure_mono (s := e '' range c) ?_
      ((Topology.IsInducing.dense_iff (f := e) ⟨rfl⟩).mp hc a)
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨d z, (hcd z).symm⟩
  have hfIn : range f ⊆ closure (range e) := by
    rintro _ ⟨b, rfl⟩
    apply closure_mono (s := f '' range d) ?_
      ((Topology.IsInducing.dense_iff (f := f) ⟨rfl⟩).mp hd b)
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨c z, hcd z⟩
  have hcontA (a : A) : Continuous (fun x : A => x + a) :=
    continuous_induced_rng.mpr (heAdd a).continuous
  have hcontB (b : B) : Continuous (fun x : B => x + b) :=
    continuous_induced_rng.mpr (hfAdd b).continuous
  let : SeparatelyContinuousAdd A :=
    { continuous_add_const := hcontA _
      continuous_const_add := by intro a; simpa only [add_comm a] using hcontA a }
  let : SeparatelyContinuousAdd B :=
    { continuous_add_const := hcontB _
      continuous_const_add := by intro b; simpa only [add_comm b] using hcontB b }
  let IA : AddSubgroup A := H.map (AddMonoidHom.fst A B)
  let IB : AddSubgroup B := H.map (AddMonoidHom.snd A B)
  have hIA : (IA : Set A) = e ⁻¹' range f := by
    ext a
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, hp.symm⟩
    · rintro ⟨b, hb⟩
      exact ⟨(a, b), hb.symm, rfl⟩
  have hIB : (IB : Set B) = f ⁻¹' range e := by
    ext b
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, hp⟩
    · rintro ⟨a, ha⟩
      exact ⟨(a, b), ha, rfl⟩
  have hIAopen : IsOpen (IA : Set A) := by
    obtain ⟨U, Z, hU, hZ, hUZ⟩ := hfLoc
    have hZ' : closure (range f) ⊆ Z :=
      closure_minimal (by rw [hUZ]; exact inter_subset_right) hZ
    have heq : (IA : Set A) = e ⁻¹' U := by
      rw [hIA, hUZ]
      ext a
      exact and_iff_left (hZ' (heIn (mem_range_self a)))
    rw [heq]
    exact hU.preimage continuous_induced_dom
  have hIBopen : IsOpen (IB : Set B) := by
    obtain ⟨U, Z, hU, hZ, hUZ⟩ := heLoc
    have hZ' : closure (range e) ⊆ Z :=
      closure_minimal (by rw [hUZ]; exact inter_subset_right) hZ
    have heq : (IB : Set B) = f ⁻¹' U := by
      rw [hIB, hUZ]
      ext b
      exact and_iff_left (hZ' (hfIn (mem_range_self b)))
    rw [heq]
    exact hU.preimage continuous_induced_dom
  have hAall (a : A) : a ∈ IA := by
    apply closure_minimal (s := range c) ?_ (IA.isClosed_of_isOpen hIAopen) (hc a)
    rintro _ ⟨z, rfl⟩
    rw [hIA]
    exact ⟨d z, (hcd z).symm⟩
  have hBall (b : B) : b ∈ IB := by
    apply closure_minimal (s := range d) ?_ (IB.isClosed_of_isOpen hIBopen) (hd b)
    rintro _ ⟨z, rfl⟩
    rw [hIB]
    exact ⟨c z, hcd z⟩
  have hChoose (a : A) : ∃ b, f b = e a := by
    have ha := hAall a
    change a ∈ (IA : Set A) at ha
    rw [hIA] at ha
    exact ha
  choose F hF using hChoose
  let Fhom : A →+ B :=
    { toFun := F
      map_zero' := hf ((hF 0).trans (by simpa only [map_zero] using hcd 0))
      map_add' := by
        intro a a'
        apply hf
        rw [hF]
        exact hAdd ⟨(a, F a), (hF a).symm⟩ ⟨(a', F a'), (hF a').symm⟩ }
  refine ⟨AddEquiv.ofBijective Fhom ⟨?_, ?_⟩, hF⟩
  · intro a a' h
    apply he
    exact (hF a).symm.trans ((congrArg f h).trans (hF a'))
  · intro b
    have hb := hBall b
    change b ∈ (IB : Set B) at hb
    rw [hIB] at hb
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, hf ((hF a).trans ha)⟩

end PhilipponMultiplicity.MultiProjectiveSpace

end

-- Source: Solutions/PhilipponDensityCriterion.lean

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

-- Source: Solutions/PhilipponClosedLocusSeparation.lean

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

-- Source: Solutions/WeierstrassModelCoordinates.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators Topology
open MvPolynomial PhilipponMultiplicity
namespace WeierstrassEllipticZeta.PhilipponApplication.Model
variable {S : Fin 5 → ℂ → ℂ} (M : Model S)

/-- Compatibility forces precisely the ambient P¹ × P⁴ coordinate sizes;
it is not an extra assumption on the arbitrary model in the bridge. -/
theorem factor_ambientDimension (i : Fin 2) : (M.factor i).ambientDimension = ![1, 4] i := by
  classical
  let d : Fin 7 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)
  have hm : d.mapDomain M.variableEquiv =
      Finsupp.equivFunOnFinite.symm (fun _ : M.group.ambient.Variable => 1) := by
    ext v
    obtain ⟨j, rfl⟩ := M.variableEquiv.surjective v
    rw [Finsupp.mapDomain_apply M.variableEquiv.injective]
    rfl
  have h := M.exponent_block_sums d i
  rw [hm] at h
  fin_cases i <;> simp [d] at h ⊢ <;> omega

/-- The analytic pullback axiom determines actual homogeneous lifts of every
curve point, in any compatible model, not just its zero loci. -/
theorem curve_projective_lifts (z : ℂ) :
    ∀ i : Fin 2, ∃ h :
      (fun j : Fin ((M.factor i).ambientDimension + 1) =>
        rawCoordinates S z (M.variableEquiv.symm ⟨i, j⟩)) ≠ 0,
      Projectivization.mk ℂ
        (fun j => rawCoordinates S z (M.variableEquiv.symm ⟨i, j⟩)) h =
          M.group.embedding (M.curve z) i := by
  have hv (v : M.group.ambient.Variable) :
      M.A.lift (M.curve z) 0 v = rawCoordinates S z (M.variableEquiv.symm v) := by
    have h := M.pullback (X (M.variableEquiv.symm v)) z 0
    simpa [AnalyticSubgroup.pullback] using h
  obtain ⟨hz, hp⟩ := (M.A.lift_represents (M.curve z)).self_of_nhds
  intro i
  have hfun : (fun j => M.A.lift (M.curve z) 0 ⟨i, j⟩) =
      (fun j => rawCoordinates S z (M.variableEquiv.symm ⟨i, j⟩)) := by
    funext j
    exact hv ⟨i, j⟩
  obtain ⟨h, heq⟩ := hp i
  have hraw : (fun j => rawCoordinates S z (M.variableEquiv.symm ⟨i, j⟩)) ≠ 0 := by
    rwa [← hfun]
  refine ⟨hraw, ?_⟩
  calc
    Projectivization.mk ℂ _ hraw = Projectivization.mk ℂ _ h := by
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      exact ⟨1, by simpa only [one_smul] using hfun⟩
    _ = M.group.embedding (M.curve z) i := by
      simpa only [M.A.map_zero, add_zero] using heq

end WeierstrassEllipticZeta.PhilipponApplication.Model
end

-- Source: Solutions/WeierstrassModelComparison.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set PhilipponMultiplicity
open scoped Topology

namespace WeierstrassEllipticZeta.PhilipponApplication.Model

private def sigmaFiberAtEquiv {ι : Type*} (α : ι → Type*) (i : ι) :
    α i ≃ {v : Sigma α // v.1 = i} where
  toFun x := ⟨⟨i, x⟩, rfl⟩
  invFun x := x.property ▸ x.val.2
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨j, x⟩, h⟩; cases h; rfl

private theorem sigma_mk_fiberAt_symm {ι : Type*} (α : ι → Type*) (i : ι)
    (v : {v : Sigma α // v.1 = i}) :
    Sigma.mk i ((sigmaFiberAtEquiv α i).symm v) = v.val := by
  rcases v with ⟨⟨j, x⟩, h⟩
  cases h
  rfl

private def sigmaBlockEquiv {ι : Type*} {α β : ι → Type*}
    (E : Sigma α ≃ Sigma β) (hE : ∀ v, (E v).1 = v.1) (i : ι) : α i ≃ β i :=
  ((sigmaFiberAtEquiv α i).trans
    (E.subtypeEquiv (fun v => by change v.1 = i ↔ (E v).1 = i; rw [hE v]))).trans
      (sigmaFiberAtEquiv β i).symm

private theorem sigma_mk_blockEquiv {ι : Type*} {α β : ι → Type*}
    (E : Sigma α ≃ Sigma β) (hE : ∀ v, (E v).1 = v.1) (i : ι) (j : α i) :
    Sigma.mk i (sigmaBlockEquiv E hE i j) = E ⟨i, j⟩ :=
  sigma_mk_fiberAt_symm β i _

variable {S : Fin 5 → ℂ → ℂ} (M N : Model S)

private theorem variableComparison_block (v : N.group.ambient.Variable) :
    (M.variableEquiv (N.variableEquiv.symm v)).1 = v.1 := by
  rw [M.variableEquiv_block, ← N.variableEquiv_block, N.variableEquiv.apply_symm_apply]

/-- The coordinate permutation forced by two models' published variable equivalences. -/
def coordinatePermutation (i : Fin 2) :
    Fin ((N.factor i).ambientDimension + 1) ≃ Fin ((M.factor i).ambientDimension + 1) :=
  sigmaBlockEquiv (N.variableEquiv.symm.trans M.variableEquiv)
    (variableComparison_block M N) i

theorem coordinatePermutation_variable (i : Fin 2)
    (j : Fin ((N.factor i).ambientDimension + 1)) :
    (⟨i, coordinatePermutation M N i j⟩ : M.group.ambient.Variable) =
      M.variableEquiv (N.variableEquiv.symm ⟨i, j⟩) :=
  sigma_mk_blockEquiv (N.variableEquiv.symm.trans M.variableEquiv)
    (variableComparison_block M N) i j

def ambientComparison : M.group.ambient.Point ≃ N.group.ambient.Point :=
  MultiProjectiveSpace.coordinateReindex (by decide : 0 < 2) (coordinatePermutation M N)

def ambientHomeomorph :
    @Homeomorph M.group.ambient.Point N.group.ambient.Point
      M.group.ambient.zariskiTopology N.group.ambient.zariskiTopology :=
  MultiProjectiveSpace.coordinateHomeomorph (by decide : 0 < 2) (coordinatePermutation M N)

theorem ambientComparison_curve (z : ℂ) :
    ambientComparison M N (M.group.embedding (M.curve z)) = N.group.embedding (N.curve z) := by
  funext i
  obtain ⟨hm, hM⟩ := M.curve_projective_lifts z i
  obtain ⟨hn, hN⟩ := N.curve_projective_lifts z i
  change projectiveReindex (coordinatePermutation M N i) (M.group.embedding (M.curve z) i) = _
  rw [← hM, projectiveReindex_mk, ← hN]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  funext j
  simp only [one_smul]
  rw [coordinatePermutation_variable, M.variableEquiv.symm_apply_apply]

/-- Every compatible Model realizes the same embedded additive group. The
result is derived from regularity, local closedness and the dense curve. -/
theorem exists_group_comparison :
    ∃ E : M.group.Point ≃+ N.group.Point,
      ∀ g, N.group.embedding (E g) = ambientComparison M N (M.group.embedding g) := by
  let := M.group.ambient.zariskiTopology
  let := N.group.ambient.zariskiTopology
  let := M.group.zariskiTopology
  let := N.group.zariskiTopology
  let e := ambientComparison M N ∘ M.group.embedding
  let h := ambientHomeomorph M N
  have hloc : IsLocallyClosed (range e) := by
    have heq : range e = h.symm ⁻¹' range M.group.embedding := by
      ext p
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, ((ambientComparison M N).symm_apply_apply _).symm⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, (congrArg h hx).trans (h.apply_symm_apply p)⟩
    rw [heq]
    exact M.group.embedding_locallyClosed.preimage h.symm.continuous
  have htop : TopologicalSpace.induced e N.group.ambient.zariskiTopology =
      M.group.zariskiTopology := by
    change TopologicalSpace.induced (h ∘ M.group.embedding) _ =
      TopologicalSpace.induced M.group.embedding _
    rw [← induced_compose, ← h.isInducing.eq_induced]
  have hreg (g : M.group.Point) :
      N.group.ambient.IsRegularAlong N.group.ambient e (fun x => e (x + g)) :=
    (M.group.translation_regular g).reindex_coordinates (by decide : 0 < 2)
      (coordinatePermutation M N)
  have hneg : N.group.ambient.IsRegularAlong N.group.ambient e (fun x => e (-x)) :=
    M.group.negation_regular.reindex_coordinates (by decide : 0 < 2)
      (coordinatePermutation M N)
  apply N.group.ambient.dense_group_comparison e N.group.embedding
    ((ambientComparison M N).injective.comp M.group.embedding_injective)
    N.group.embedding_injective hloc N.group.embedding_locallyClosed hreg
    N.group.translation_regular hneg N.group.negation_regular M.curve N.curve
  · rw [htop]
    exact M.curve_dense
  · exact N.curve_dense
  · exact ambientComparison_curve M N

theorem polynomial_zero_iff_comparison (p : M.group.ambient.Point)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (hQ : Bihomogeneous Q m n) :
    M.group.ambient.eval (M.polynomial Q) p = 0 ↔
      N.group.ambient.eval (N.polynomial Q) (ambientComparison M N p) = 0 := by
  let v : N.group.ambient.Variable → ℂ :=
    fun t => M.group.ambient.coordinate p ⟨t.1, coordinatePermutation M N t.1 t.2⟩
  have hv (i : Fin 2) : ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j => v ⟨i, j⟩) h = ambientComparison M N p i := by
    have hn : (fun j => (p i).rep (coordinatePermutation M N i j)) ≠ 0 := by
      intro h
      apply Projectivization.rep_nonzero (p i)
      ext j
      simpa using congrFun h ((coordinatePermutation M N i).symm j)
    exact ⟨hn, congrArg (projectiveReindex (coordinatePermutation M N i))
      (Projectivization.mk_rep (p i))⟩
  have heval : MvPolynomial.eval v (N.polynomial Q) = M.group.ambient.eval (M.polynomial Q) p := by
    simp only [Model.polynomial, MultiProjectiveSpace.eval, MvPolynomial.eval_rename]
    apply congrArg (fun w => MvPolynomial.eval w Q)
    funext j
    change M.group.ambient.coordinate p
      ⟨(N.variableEquiv j).1, coordinatePermutation M N (N.variableEquiv j).1 (N.variableEquiv j).2⟩ = _
    rw [coordinatePermutation_variable, N.variableEquiv.symm_apply_apply]
    rfl
  rw [← heval]
  exact N.group.ambient.eval_eq_zero_iff_of_lift _ v hv _ ![m, n] (N.homogeneous Q m n hQ)

end WeierstrassEllipticZeta.PhilipponApplication.Model
end

-- Source: Solutions/PhilipponAdditiveGroup.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity
universe u

variable (K : Type u) [Field K]

private theorem homogeneous_X (M : MultiProjectiveSpace K) (v : M.Variable) :
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

private theorem homogeneous_add (M : MultiProjectiveSpace K)
    {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

def additiveCarrier : Set (Projectivization K (Fin 2 → K)) := {p | p.rep 0 ≠ 0}

def additivePoint (z : K) : Projectivization K (Fin 2 → K) :=
  Projectivization.mk K ![1, z] (by intro h; have := congrFun h 0; simpa using this)

theorem additivePoint_mem (z : K) : additivePoint K z ∈ additiveCarrier K := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K ![1, z]
    (by intro h; have := congrFun h 0; simpa using this)
  change (Projectivization.mk K ![1, z] _).rep 0 ≠ 0
  rw [← hc]
  simpa [Units.smul_def] using c.ne_zero

def additiveCoordinateEquiv : additiveCarrier K ≃ K where
  toFun p := p.val.rep 1 / p.val.rep 0
  invFun z := ⟨additivePoint K z, additivePoint_mem K z⟩
  left_inv p := by
    apply Subtype.ext
    apply Eq.trans ?_ p.val.mk_rep
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(p.val.rep 0)⁻¹, ?_⟩
    have hp0 : p.val.rep 0 ≠ 0 := p.property
    ext j
    fin_cases j
    · simp [hp0]
    · simp [div_eq_mul_inv, mul_comm]
  right_inv z := by
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K ![1, z]
      (by intro h; have := congrFun h 0; simpa using this)
    change (Projectivization.mk K ![1, z] _).rep 1 /
      (Projectivization.mk K ![1, z] _).rep 0 = z
    rw [← hc]
    simp [Units.smul_def, c.ne_zero]

def additiveCarrierGroup : AddCommGroup (additiveCarrier K) :=
  (additiveCoordinateEquiv K).addCommGroup

private theorem additivePoint_eq_mk {v : Fin 2 → K} (hv : v 0 ≠ 0) :
    additivePoint K (v 1 / v 0) =
      Projectivization.mk K v (by intro h; exact hv (congrFun h 0)) := by
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨(v 0)⁻¹, ?_⟩
  ext j
  fin_cases j <;> simp [hv, div_eq_mul_inv, mul_comm]

theorem additiveCarrier_negation_regular :
    letI := additiveCarrierGroup K
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K 1) (projectiveSpace K 1)
      (fun x : additiveCarrier K => fun _ => x.val)
      (fun x : additiveCarrier K => fun _ => (-x).val) := by
  letI := additiveCarrierGroup K
  let P : Fin 2 → MvPolynomial (Fin 2) K := ![MvPolynomial.X 0, -MvPolynomial.X 1]
  apply projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X K 0
    · exact (MvPolynomial.isHomogeneous_X K 1).neg
  · intro x
    have hx : x.val.rep 0 ≠ 0 := x.property
    have hn : ![x.val.rep 0, -x.val.rep 1] ≠ 0 := by
      intro h
      exact hx (by simpa using congrFun h 0)
    have he : (fun j => MvPolynomial.eval x.val.rep (P j)) =
        ![x.val.rep 0, -x.val.rep 1] := by
      ext j
      fin_cases j <;> simp [P]
    refine ⟨by simpa only [he] using hn, ?_⟩
    change Projectivization.mk K _ _ = additivePoint K (-(x.val.rep 1 / x.val.rep 0))
    have hpoint := additivePoint_eq_mk K (v := ![x.val.rep 0, -x.val.rep 1]) hx
    simpa only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      neg_div] using hpoint.symm


theorem additiveCarrier_locallyClosed :
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p : Projectivization K (Fin 2 → K) =>
          (fun _ => p : (projectiveSpace K 1).Point))
        (projectiveSpace K 1).zariskiTopology) (additiveCarrier K) := by
  letI := TopologicalSpace.induced
    (fun p : Projectivization K (Fin 2 → K) => (fun _ => p : (projectiveSpace K 1).Point))
      (projectiveSpace K 1).zariskiTopology
  exact (projective_isOpen_coordinate (K := K) (0 : Fin 2)).isLocallyClosed

private theorem homogeneous_bilinear (a b : Fin 2) :
    (projectiveSquare K 1).IsHomogeneous
      (MvPolynomial.X ⟨(0 : Fin 2), a⟩ * MvPolynomial.X ⟨(1 : Fin 2), b⟩) (fun _ => 1) := by
  have h := (homogeneous_X K (projectiveSquare K 1) ⟨(0 : Fin 2), a⟩).mul (projectiveSquare K 1)
    (homogeneous_X K (projectiveSquare K 1) ⟨(1 : Fin 2), b⟩)
  convert h using 1
  funext i
  fin_cases i <;> rfl

theorem additiveCarrier_addition_regular :
    letI := additiveCarrierGroup K
    MultiProjectiveSpace.IsRegularAlong (projectiveSquare K 1) (projectiveSpace K 1)
      (fun xy : additiveCarrier K × additiveCarrier K =>
        fun i => if i.val = 0 then xy.1.val else xy.2.val)
      (fun xy : additiveCarrier K × additiveCarrier K => fun _ => (xy.1 + xy.2).val) := by
  letI := additiveCarrierGroup K
  letI := (projectiveSquare K 1).zariskiTopology
  let P : Fin 2 → (projectiveSquare K 1).CoordinateRing :=
    ![MvPolynomial.X ⟨(0 : Fin 2), 0⟩ * MvPolynomial.X ⟨(1 : Fin 2), 0⟩,
      MvPolynomial.X ⟨(0 : Fin 2), 1⟩ * MvPolynomial.X ⟨(1 : Fin 2), 0⟩ +
        MvPolynomial.X ⟨(0 : Fin 2), 0⟩ * MvPolynomial.X ⟨(1 : Fin 2), 1⟩]
  intro x b
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 1, P, ?_, ?_⟩
  · intro j
    change (projectiveSquare K 1).IsHomogeneous (P j) (fun _ => 1)
    fin_cases j
    · exact homogeneous_bilinear K 0 0
    · exact homogeneous_add K _ (homogeneous_bilinear K 1 0) (homogeneous_bilinear K 0 1)
  · intro y _
    let v : Fin 2 → K :=
      ![y.1.val.rep 0 * y.2.val.rep 0,
        y.1.val.rep 1 * y.2.val.rep 0 + y.1.val.rep 0 * y.2.val.rep 1]
    have hv : v 0 ≠ 0 := mul_ne_zero y.1.property y.2.property
    have he : (fun j : Fin 2 => (projectiveSquare K 1).eval (P j)
        (fun i => if i.val = 0 then y.1.val else y.2.val)) = v := by
      ext j
      fin_cases j <;>
        simp [P, v, MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate, projectiveSquare]
    change ∃ h : (fun j : Fin 2 => (projectiveSquare K 1).eval (P j)
        (fun i => if i.val = 0 then y.1.val else y.2.val)) ≠ 0,
      Projectivization.mk K _ h = (y.1 + y.2).val
    refine ⟨by rw [he]; intro h; exact hv (congrFun h 0), ?_⟩
    change Projectivization.mk K _ _ =
      additivePoint K (y.1.val.rep 1 / y.1.val.rep 0 + y.2.val.rep 1 / y.2.val.rep 0)
    have hs : v 1 / v 0 =
        y.1.val.rep 1 / y.1.val.rep 0 + y.2.val.rep 1 / y.2.val.rep 0 := by
      dsimp [v]
      exact (div_add_div _ _ y.1.property y.2.property).symm
    simpa only [he, hs] using (additivePoint_eq_mk K hv).symm

/-- The additive group in its standard open projective-line chart, with
regular addition and negation proved by homogeneous coordinate formulae. -/
def additiveEmbeddedGroup : EmbeddedCommutativeGroup K where
  ambientDimension := 1
  carrier := additiveCarrier K
  group := additiveCarrierGroup K
  locallyClosed := additiveCarrier_locallyClosed K
  addition_regular := additiveCarrier_addition_regular K
  negation_regular := additiveCarrier_negation_regular K

def additiveEmbeddedGroupEquiv : (additiveEmbeddedGroup K).Point ≃+ K :=
  letI := additiveCarrierGroup K
  (additiveCoordinateEquiv K).addEquiv

/-- Existence of the standard additive group law, with both operations regular
in the projective embedding and with the ordinary affine coordinate. -/
theorem additive_projective_realization :
    let U : Set (Projectivization K (Fin 2 → K)) := {p | p.rep 0 ≠ 0}
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p : Projectivization K (Fin 2 → K) =>
        (fun _ => p : (projectiveSpace K 1).Point)) (projectiveSpace K 1).zariskiTopology) U ∧
    ∃ group : AddCommGroup U,
      letI := group
      MultiProjectiveSpace.IsRegularAlong (projectiveSquare K 1) (projectiveSpace K 1)
        (fun xy : U × U => fun i => if i.val = 0 then xy.1.val else xy.2.val)
        (fun xy : U × U => fun _ => (xy.1 + xy.2).val) ∧
      MultiProjectiveSpace.IsRegularAlong (projectiveSpace K 1) (projectiveSpace K 1)
        (fun x : U => fun _ => x.val) (fun x : U => fun _ => (-x).val) ∧
      ∃ e : U ≃+ K, ∀ p : U, e p = p.val.rep 1 / p.val.rep 0 := by
  refine ⟨additiveCarrier_locallyClosed K, additiveCarrierGroup K, ?_⟩
  letI := additiveCarrierGroup K
  exact ⟨additiveCarrier_addition_regular K, additiveCarrier_negation_regular K,
    additiveEmbeddedGroupEquiv K, fun _ => rfl⟩

end PhilipponMultiplicity

end

noncomputable section
namespace PhilipponMultiplicity
theorem additiveEmbeddedGroup_dimension (K : Type*) [Field K] [Infinite K] :
    (additiveEmbeddedGroup K).dimension = 1 := by
  change (Hilbert.hilbertPolynomial K 1 (fun _ => 1)
    ((projectiveSpace K 1).vanishingIdeal
      ((fun p => fun _ => p) '' additiveCarrier K))).totalDegree = 1
  have hp := congrArg MvPolynomial.totalDegree (additive_projective_hilbert_polynomial K)
  apply hp.trans
  rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt (by simp)]
  simp
end PhilipponMultiplicity
end

-- Source: Solutions/WeierstrassRegularGroup.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TranscendenceTheory
namespace WeierstrassEllipticZeta

/-- The concrete extension has a compatible commutative group structure and
both of its group operations are regular. -/
theorem projective_extension_group_with_regular_operations
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ) (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
    ∃ group : AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃),
      letI := group
      ∃ e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃,
        (∀ z u : ℂ, ∃ hv :
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
          (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) ∧
        PhilipponMultiplicity.MultiProjectiveSpace.IsRegularAlong
          (PhilipponMultiplicity.projectiveSquare ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun xy : ProjectiveExtensionChartLocus L.g₂ L.g₃ × ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
            fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
          (fun xy => fun _ => (xy.1 + xy.2).val.val) ∧
        PhilipponMultiplicity.MultiProjectiveSpace.IsRegularAlong
          (PhilipponMultiplicity.projectiveSpace ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => (-x).val.val) := by
  obtain ⟨group, e, he, hneg⟩ :=
    projective_extension_group_with_regular_negation L D S hS hS_value hS_ne η hη
  letI := group
  exact ⟨group, e, he,
    projective_extension_addition_regular L D S hS hS_value hS_ne η e he, hneg⟩

end WeierstrassEllipticZeta
end

-- Source: Solutions/WeierstrassEmbeddedGroup.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta

/-- The same surface as the two nested subtypes, expressed as a carrier set
for Philippon's embedded-group structure. -/
def extensionEmbeddedCarrier (g₂ g₃ : ℂ) : Set (Projectivization ℂ (Fin 5 → ℂ)) :=
  {p | MvPolynomial.eval p.rep extensionQuadric = 0 ∧
    MvPolynomial.eval p.rep (extensionCubic g₂ g₃) = 0 ∧
    (p.rep 0 ≠ 0 ∨ p.rep 2 ≠ 0)}

def extensionCarrierEquiv (g₂ g₃ : ℂ) :
    extensionEmbeddedCarrier g₂ g₃ ≃ ProjectiveExtensionChartLocus g₂ g₃ where
  toFun p := ⟨⟨p.val, p.property.1, p.property.2.1⟩, p.property.2.2⟩
  invFun p := ⟨p.val.val, p.val.property.1, p.val.property.2, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Once the two regular-operation theorems have been proved, this constructs
an actual `EmbeddedCommutativeGroup`; no geometric field is postulated. -/
def extensionEmbeddedGroup (g₂ g₃ : ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus g₂ g₃)]
    (hadd : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun xy : ProjectiveExtensionChartLocus g₂ g₃ × ProjectiveExtensionChartLocus g₂ g₃ =>
        fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
      (fun xy => fun _ => (xy.1 + xy.2).val.val))
    (hneg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => x.val.val)
      (fun x => fun _ => (-x).val.val)) : EmbeddedCommutativeGroup ℂ where
  ambientDimension := 4
  carrier := extensionEmbeddedCarrier g₂ g₃
  group := (extensionCarrierEquiv g₂ g₃).addCommGroup
  locallyClosed := projective_extension_locallyClosed g₂ g₃
  addition_regular := by
    letI := (extensionCarrierEquiv g₂ g₃).addCommGroup
    let f := (extensionCarrierEquiv g₂ g₃).addEquiv
    intro xy b
    obtain ⟨U, hU, hx, d, P, hP, hcorrect⟩ := hadd (f xy.1, f xy.2) b
    refine ⟨U, hU, hx, d, P, hP, ?_⟩
    intro pq hpq
    obtain ⟨hn, hh⟩ := hcorrect (f pq.1, f pq.2) hpq
    refine ⟨hn, ?_⟩
    change Projectivization.mk ℂ _ _ = (f (pq.1 + pq.2)).val.val
    rw [map_add]
    exact hh
  negation_regular := by
    letI := (extensionCarrierEquiv g₂ g₃).addCommGroup
    let f := (extensionCarrierEquiv g₂ g₃).addEquiv
    intro x b
    obtain ⟨U, hU, hx, d, P, hP, hcorrect⟩ := hneg (f x) b
    refine ⟨U, hU, hx, d, P, hP, ?_⟩
    intro p hp
    obtain ⟨hn, hh⟩ := hcorrect (f p) hp
    refine ⟨hn, ?_⟩
    change Projectivization.mk ℂ _ _ = (f (-p)).val.val
    rw [map_neg]
    exact hh

end WeierstrassEllipticZeta
end

-- Source: Solutions/WeierstrassExtensionDimension.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
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
/-- Hilbert dimension of the actual projective extension carrier. -/
theorem projective_extension_hilbert_dimension :
    (Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4)
      ((projectiveSpace ℂ 4).vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          fun _ : Fin 1 => p.val.val)))).totalDegree = 2 := by
  rw [projective_extension_hilbert_polynomial L D S hS hS_value hS_ne η e he]
  have hp : (C (3 : ℚ) * (X (0 : Fin 1) ^ 2)).totalDegree = 2 := by
    rw [totalDegree_mul_of_isDomain (by norm_num) (by simp), totalDegree_C, zero_add,
      totalDegree_X_pow]
  rw [totalDegree_add_eq_left_of_totalDegree_lt (by simp [hp]), hp]

end WeierstrassEllipticZeta
end

-- Source: Solutions/WeierstrassEmbeddedDimension.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
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
    (hadd : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun xy : ProjectiveExtensionChartLocus L.g₂ L.g₃ × ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
      (fun xy => fun _ => (xy.1 + xy.2).val.val))
    (hneg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
      (fun x => fun _ => (-x).val.val))

include D S hS hS_value hS_ne η e he in
/-- The regular embedded-group object has the dimension computed on its carrier. -/
theorem extensionEmbeddedGroup_dimension :
    (extensionEmbeddedGroup L.g₂ L.g₃ hadd hneg).dimension = 2 := by
  have hcarrier :
      ((fun p : Projectivization ℂ (Fin 5 → ℂ) => fun _ : Fin 1 => p) ''
        extensionEmbeddedCarrier L.g₂ L.g₃) =
      Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        fun _ : Fin 1 => p.val.val) := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨extensionCarrierEquiv L.g₂ L.g₃ ⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.val.val, ((extensionCarrierEquiv L.g₂ L.g₃).symm x).property, rfl⟩
  change (Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4)
    ((projectiveSpace ℂ 4).vanishingIdeal
      ((fun p : Projectivization ℂ (Fin 5 → ℂ) => fun _ : Fin 1 => p) ''
        extensionEmbeddedCarrier L.g₂ L.g₃))).totalDegree = 2
  rw [hcarrier]
  exact projective_extension_hilbert_dimension L D S hS hS_value hS_ne η e he

end WeierstrassEllipticZeta
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

-- Source: Solutions/WeierstrassProductDensity.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
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
theorem extensionProduct_curve_dense :
    @Dense (ℂ × ProjectiveExtensionChartLocus L.g₂ L.g₃)
      (TopologicalSpace.induced extensionProductEmbedding extensionProductAmbient.zariskiTopology)
      (Set.range (fun z : ℂ => (z, e ((extensionPeriodGraph L.lattice η).mkQ (z, 0))))) := by
  exact projective_extension_curve_zariski_dense L D S hS hS_value hS_ne η e he
end WeierstrassEllipticZeta
end

-- Source: Solutions/WeierstrassApplicationProduct.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open MvPolynomial TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta

variable (g₂ g₃ : ℂ) [AddCommGroup (ProjectiveExtensionChartLocus g₂ g₃)]
    (hadd : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun xy : ProjectiveExtensionChartLocus g₂ g₃ × ProjectiveExtensionChartLocus g₂ g₃ =>
        fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
      (fun xy => fun _ => (xy.1 + xy.2).val.val))
    (hneg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => x.val.val)
      (fun x => fun _ => (-x).val.val))

/-- Use fixed ambient dimensions so the product's coordinate types coincide
with the two-block coordinates of the density calculation. -/
def applicationFactor (i : Fin 2) : EmbeddedCommutativeGroup ℂ where
  ambientDimension := ![1, 4] i
  carrier := Fin.cases (additiveEmbeddedGroup ℂ).carrier
    (Fin.cases (extensionEmbeddedGroup g₂ g₃ hadd hneg).carrier (fun j => Fin.elim0 j)) i
  group := Fin.cases (additiveEmbeddedGroup ℂ).group
    (Fin.cases (extensionEmbeddedGroup g₂ g₃ hadd hneg).group (fun j => Fin.elim0 j)) i
  locallyClosed := by
    fin_cases i
    · exact (additiveEmbeddedGroup ℂ).locallyClosed
    · exact (extensionEmbeddedGroup g₂ g₃ hadd hneg).locallyClosed
  addition_regular := by
    fin_cases i
    · exact (additiveEmbeddedGroup ℂ).addition_regular
    · exact (extensionEmbeddedGroup g₂ g₃ hadd hneg).addition_regular
  negation_regular := by
    fin_cases i
    · exact (additiveEmbeddedGroup ℂ).negation_regular
    · exact (extensionEmbeddedGroup g₂ g₃ hadd hneg).negation_regular

abbrev applicationGroup : EmbeddedGroupProduct ℂ :=
  ⟨2, by decide, applicationFactor g₂ g₃ hadd hneg⟩

def applicationExtensionEquiv :
    (extensionEmbeddedGroup g₂ g₃ hadd hneg).Point ≃+
      ProjectiveExtensionChartLocus g₂ g₃ :=
  (extensionCarrierEquiv g₂ g₃).addEquiv

def applicationPointEquiv :
    (applicationGroup g₂ g₃ hadd hneg).Point ≃+
      (ℂ × ProjectiveExtensionChartLocus g₂ g₃) where
  toFun x := (additiveEmbeddedGroupEquiv ℂ (x 0), applicationExtensionEquiv g₂ g₃ hadd hneg (x 1))
  invFun p := Fin.cons ((additiveEmbeddedGroupEquiv ℂ).symm p.1)
    (Fin.cons ((applicationExtensionEquiv g₂ g₃ hadd hneg).symm p.2) (fun i => Fin.elim0 i))
  left_inv x := by
    funext i
    fin_cases i
    · exact (additiveEmbeddedGroupEquiv ℂ).symm_apply_apply (x 0)
    · exact (applicationExtensionEquiv g₂ g₃ hadd hneg).symm_apply_apply (x 1)
  right_inv p := Prod.ext ((additiveEmbeddedGroupEquiv ℂ).apply_symm_apply p.1)
    ((applicationExtensionEquiv g₂ g₃ hadd hneg).apply_symm_apply p.2)
  map_add' x y := Prod.ext ((additiveEmbeddedGroupEquiv ℂ).map_add (x 0) (y 0))
    ((applicationExtensionEquiv g₂ g₃ hadd hneg).map_add (x 1) (y 1))

theorem applicationGroup_embedding (x : (applicationGroup g₂ g₃ hadd hneg).Point) :
    (applicationGroup g₂ g₃ hadd hneg).embedding x =
      extensionProductEmbedding (applicationPointEquiv g₂ g₃ hadd hneg x) := by
  funext i
  change Fin 2 at i
  fin_cases i
  · change (x 0).val = additivePoint ℂ (additiveEmbeddedGroupEquiv ℂ (x 0))
    exact (congrArg Subtype.val ((additiveEmbeddedGroupEquiv ℂ).symm_apply_apply (x 0))).symm
  · rfl

theorem applicationFactor_dimension
    (hE : (extensionEmbeddedGroup g₂ g₃ hadd hneg).dimension = 2) :
    ∀ i, (applicationFactor g₂ g₃ hadd hneg i).dimension = ![1, 2] i := by
  intro i
  fin_cases i
  · exact additiveEmbeddedGroup_dimension ℂ
  · exact hE

theorem applicationGroup_homogeneous (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    IsMultihomogeneousOfDegree (applicationGroup g₂ g₃ hadd hneg)
      (rename extensionProductVariableEquiv Q) ![m, n] :=
  (extensionProduct_homogeneous_iff Q ![m, n]).mpr hQ

variable (Γ : Submodule ℤ ℂ) (η : Γ →ₗ[ℤ] ℂ)
    (e : GraphQuotientExtension Γ η ≃+ ProjectiveExtensionChartLocus g₂ g₃)

def applicationCurve : ℂ →+ (applicationGroup g₂ g₃ hadd hneg).Point where
  toFun z := (applicationPointEquiv g₂ g₃ hadd hneg).symm
    (z, e ((extensionPeriodGraph Γ η).mkQ (z, 0)))
  map_zero' := by
    change (applicationPointEquiv g₂ g₃ hadd hneg).symm
      (0, e ((extensionPeriodGraph Γ η).mkQ (0, 0))) = 0
    have hz : e ((extensionPeriodGraph Γ η).mkQ (0, 0)) = 0 := by
      change e ((extensionPeriodGraph Γ η).mkQ 0) = 0
      simp
    rw [hz]
    exact (applicationPointEquiv g₂ g₃ hadd hneg).symm.map_zero
  map_add' z w := by
    rw [← map_add]
    congr 1
    apply Prod.ext
    · rfl
    · change e ((extensionPeriodGraph Γ η).mkQ (z + w, 0)) =
        e ((extensionPeriodGraph Γ η).mkQ (z, 0)) + e ((extensionPeriodGraph Γ η).mkQ (w, 0))
      rw [← map_add, ← map_add]
      simp only [Prod.mk_add_mk, add_zero]

theorem applicationPointEquiv_curve (z : ℂ) :
    applicationPointEquiv g₂ g₃ hadd hneg (applicationCurve g₂ g₃ hadd hneg Γ η e z) =
      (z, e ((extensionPeriodGraph Γ η).mkQ (z, 0))) :=
  (applicationPointEquiv g₂ g₃ hadd hneg).apply_symm_apply _

theorem applicationCurve_injective :
    Function.Injective (applicationCurve g₂ g₃ hadd hneg Γ η e) := by
  intro z w h
  have hh := congrArg (fun p => (applicationPointEquiv g₂ g₃ hadd hneg p).1) h
  simpa only [applicationPointEquiv_curve] using hh

theorem applicationCurve_dense
    (hDense : @Dense (ℂ × ProjectiveExtensionChartLocus g₂ g₃)
      (TopologicalSpace.induced extensionProductEmbedding extensionProductAmbient.zariskiTopology)
      (Set.range (fun z : ℂ => (z, e ((extensionPeriodGraph Γ η).mkQ (z, 0)))))) :
    @Dense _ (applicationGroup g₂ g₃ hadd hneg).zariskiTopology
      (Set.range (applicationCurve g₂ g₃ hadd hneg Γ η e)) := by
  letI := (applicationGroup g₂ g₃ hadd hneg).zariskiTopology
  letI := TopologicalSpace.induced (extensionProductEmbedding (g₂ := g₂) (g₃ := g₃))
    extensionProductAmbient.zariskiTopology
  have hi : Topology.IsInducing (applicationPointEquiv g₂ g₃ hadd hneg) := by
    constructor
    change TopologicalSpace.induced _ _ = TopologicalSpace.induced _
      (TopologicalSpace.induced _ _)
    rw [induced_compose]
    congr 1
    funext x
    exact applicationGroup_embedding g₂ g₃ hadd hneg x
  apply hi.dense_iff.mpr
  intro x
  have hr : (applicationPointEquiv g₂ g₃ hadd hneg) ''
      Set.range (applicationCurve g₂ g₃ hadd hneg Γ η e) =
      Set.range (fun z : ℂ => (z, e ((extensionPeriodGraph Γ η).mkQ (z, 0)))) := by
    rw [← Set.range_comp]
    congr 1
    funext z
    exact applicationPointEquiv_curve g₂ g₃ hadd hneg Γ η e z
  rw [hr]
  exact hDense _

theorem applicationCurve_zero_locus (S : Fin 5 → ℂ → ℂ)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph Γ η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (v : ℂ) :
    applicationCurve g₂ g₃ hadd hneg Γ η e v ∈
      zeroLocusOnGroup (applicationGroup g₂ g₃ hadd hneg)
        (rename extensionProductVariableEquiv Q) ↔
      eval ![1, v, S 0 v, S 1 v, S 2 v, S 3 v, S 4 v] Q = 0 := by
  change extensionProductAmbient.eval (rename extensionProductVariableEquiv Q)
    ((applicationGroup g₂ g₃ hadd hneg).embedding (applicationCurve g₂ g₃ hadd hneg Γ η e v)) = 0 ↔ _
  rw [applicationGroup_embedding, applicationPointEquiv_curve]
  obtain ⟨hv, hp⟩ := he v 0
  simpa using extensionProduct_raw_eval_zero_iff Q m n hQ
    (v, e ((extensionPeriodGraph Γ η).mkQ (v, 0))) _ hv hp

end WeierstrassEllipticZeta
end

-- Source: Solutions/PhilipponLocalCurveCarrier.lean

set_option autoImplicit false
noncomputable section
open scoped Topology
namespace PhilipponMultiplicity

/-- Every neighborhood ball generates a connected normed additive group.
Here closure means algebraic subgroup generation, not topological closure. -/
theorem additive_closure_ball_eq_top {E : Type*} [SeminormedAddCommGroup E]
    [PreconnectedSpace E] (r : ℝ) (hr : 0 < r) :
    AddSubgroup.closure (Metric.ball (0 : E) r) = ⊤ := by
  let H := AddSubgroup.closure (Metric.ball (0 : E) r)
  have hopen : IsOpen (H : Set E) := H.isOpen_of_mem_nhds
    (Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) hr) AddSubgroup.subset_closure)
  have huniv : (H : Set E) = Set.univ :=
    IsClopen.eq_univ ⟨H.isClosed_of_isOpen hopen, hopen⟩ ⟨0, H.zero_mem⟩
  exact SetLike.coe_injective huniv

/-- If an analytic subgroup's local map restricts a global additive curve,
its generated carrier is exactly the range of that global curve. -/
theorem AnalyticSubgroup.carrier_eq_range_of_global_curve
    {G : EmbeddedGroupProduct ℂ} (A : AnalyticSubgroup G)
    (f : A.ParameterSpace →+ G.Point) (hf : ∀ z : A.domain, A.map z = f z.val) :
    A.carrier = Set.range f := by
  have hlocal : Set.range A.map = f '' A.domain := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, (hf z).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, hf ⟨z, hz⟩⟩
  unfold AnalyticSubgroup.carrier
  rw [hlocal, A.domain_eq_ball, ← AddMonoidHom.map_closure,
    additive_closure_ball_eq_top A.radius A.radius_pos]
  simp

end PhilipponMultiplicity

end

-- Source: Solutions/PhilipponAnalyticGlobalCurve.lean

set_option autoImplicit false
noncomputable section
open scoped Topology
namespace PhilipponMultiplicity

/-- An injective differential of one equation through the identity forces the
analytic tangent kernel to be zero. -/
theorem AnalyticSubgroup.tangentKernel_eq_bot_of_linear_pullback
    {G : EmbeddedGroupProduct ℂ} (A : AnalyticSubgroup G)
    (ev : A.ParameterSpace ≃L[ℂ] ℂ) (P : G.CoordinateRing)
    (hP : P ∈ G.vanishingIdeal {0}) (hf : A.pullback P 0 = ev) :
    A.tangentKernel {0} = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro t ht
  change t = 0
  change t ∈ ⨅ Q : {Q : G.CoordinateRing // Q ∈ G.vanishingIdeal {0}},
    LinearMap.ker (fderiv ℂ (A.pullback Q.val 0) 0).toLinearMap at ht
  have hp := ((Submodule.mem_iInf _).mp ht) ⟨P, hP⟩
  change (fderiv ℂ (A.pullback P 0) 0) t = 0 at hp
  rw [hf] at hp
  have hd : fderiv ℂ ev 0 = ev.toContinuousLinearMap := ev.hasFDerivAt.fderiv
  rw [hd] at hp
  exact ev.injective (hp.trans ev.map_zero.symm)

/-- A finite family of analytic germs has a common positive real power-series ball. -/
theorem finite_analytic_common_ball {ι : Type*} [Fintype ι]
    (f : ι → (Fin 1 → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, ∃ p : FormalMultilinearSeries ℂ (Fin 1 → ℂ) ℂ,
      HasFPowerSeriesOnBall (f i) p 0 (ENNReal.ofReal r) := by
  choose p hp using hf
  obtain ⟨r, hr⟩ := HasFPowerSeriesAt.pi hp
  obtain ⟨s, hs, hsr⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := 1) (b := r) (by simp) hr.r_pos.ne'
  have hsr' : (s : ENNReal) ≤ r := by simpa using hsr.le
  refine ⟨s, hs, fun i => ⟨p i, ?_⟩⟩
  exact (hasFPowerSeriesOnBall_pi_iff (by simpa using hs)).mp
    (hr.mono (by simpa using hs) (by simpa using hsr')) i

variable {G : EmbeddedGroupProduct ℂ}
    (curve : ℂ →+ G.Point)
    (lift : G.Point → (Fin 1 → ℂ) → G.ambient.Variable → ℂ)
    (ha : ∀ g v, AnalyticAt ℂ (fun z => lift g z v) 0)
    (hr : ∀ g t i, ∃ h : (fun j => lift g t ⟨i, j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j => lift g t ⟨i, j⟩) h =
        G.embedding (g + curve (t 0)) i)

/-- Restrict a global additive curve with analytic translated lifts to a genuine
common power-series ball. -/
def AnalyticSubgroup.ofGlobalCurve : AnalyticSubgroup G :=
  let hb := finite_analytic_common_ball (fun v t => lift 0 t v) (ha 0)
  let r := Classical.choose hb
  let h := Classical.choose_spec hb
  { parameterDimension := 1
    parameterDimension_pos := by decide
    radius := r
    radius_pos := h.1
    domain := Metric.ball 0 r
    domain_eq_ball := rfl
    domain_open := Metric.isOpen_ball
    zero_mem := Metric.mem_ball_self h.1
    map := fun t => curve (t.val 0)
    map_zero := curve.map_zero
    map_add := fun x y _ => curve.map_add (x.val 0) (y.val 0)
    lift := lift
    lift_analytic := ha
    base_series := h.2
    base_represents := fun t i => by simpa using hr 0 t.val i
    lift_represents := fun g => by
      filter_upwards [Metric.ball_mem_nhds (0 : Fin 1 → ℂ) h.1] with t ht
      exact ⟨ht, hr g t⟩ }

theorem AnalyticSubgroup.ofGlobalCurve_carrier :
    (AnalyticSubgroup.ofGlobalCurve curve lift ha hr).carrier = Set.range curve := by
  let ev : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)
  rw [AnalyticSubgroup.carrier_eq_range_of_global_curve _
    (curve.comp ev.toLinearEquiv.toAddEquiv.toAddMonoidHom) (fun _ => rfl)]
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨ev t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨ev.symm t, congrArg curve (ev.apply_symm_apply t)⟩

end PhilipponMultiplicity
end

-- Source: Solutions/WeierstrassAnalyticLifts.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Topology
open MvPolynomial TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta

variable (g₂ g₃ : ℂ) [AddCommGroup (ProjectiveExtensionChartLocus g₂ g₃)]
    (hadd : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun xy : ProjectiveExtensionChartLocus g₂ g₃ × ProjectiveExtensionChartLocus g₂ g₃ =>
        fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
      (fun xy => fun _ => (xy.1 + xy.2).val.val))
    (hneg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => x.val.val)
      (fun x => fun _ => (-x).val.val))
    (Γ : Submodule ℤ ℂ) (η : Γ →ₗ[ℤ] ℂ)
    (e : GraphQuotientExtension Γ η ≃+ ProjectiveExtensionChartLocus g₂ g₃)

/-- A representative of the extension coordinate, normalized on the global curve.
This normalization is what makes polynomial pullbacks exactly the paper's formulas. -/
def applicationRepresentative (g : (applicationGroup g₂ g₃ hadd hneg).Point) : ℂ × ℂ :=
  let p := applicationPointEquiv g₂ g₃ hadd hneg g
  if p.2 = e ((extensionPeriodGraph Γ η).mkQ (p.1, 0)) then (p.1, 0)
  else Classical.choose ((extensionPeriodGraph Γ η).mkQ_surjective (e.symm p.2))

theorem applicationRepresentative_spec (g : (applicationGroup g₂ g₃ hadd hneg).Point) :
    e ((extensionPeriodGraph Γ η).mkQ (applicationRepresentative g₂ g₃ hadd hneg Γ η e g)) =
      (applicationPointEquiv g₂ g₃ hadd hneg g).2 := by
  classical
  unfold applicationRepresentative
  dsimp only
  split_ifs with h
  · exact h.symm
  · rw [Classical.choose_spec ((extensionPeriodGraph Γ η).mkQ_surjective _)]
    exact e.apply_symm_apply _

theorem applicationRepresentative_curve (v : ℂ) :
    applicationRepresentative g₂ g₃ hadd hneg Γ η e
      (applicationCurve g₂ g₃ hadd hneg Γ η e v) = (v, 0) := by
  simp [applicationRepresentative, applicationPointEquiv_curve]

def applicationRawLift (S : Fin 5 → ℂ → ℂ)
    (g : (applicationGroup g₂ g₃ hadd hneg).Point) (t : Fin 1 → ℂ) : Fin 7 → ℂ :=
  let p := applicationPointEquiv g₂ g₃ hadd hneg g
  let r := applicationRepresentative g₂ g₃ hadd hneg Γ η e g
  ![1, p.1 + t 0, S 0 (r.1 + t 0), S 1 (r.1 + t 0), S 2 (r.1 + t 0),
    S 3 (r.1 + t 0) + r.2 * S 0 (r.1 + t 0),
    S 4 (r.1 + t 0) + r.2 * S 2 (r.1 + t 0)]

def applicationLift (S : Fin 5 → ℂ → ℂ)
    (g : (applicationGroup g₂ g₃ hadd hneg).Point) (t : Fin 1 → ℂ) :
    ExtensionProductVariable → ℂ :=
  applicationRawLift g₂ g₃ hadd hneg Γ η e S g t ∘ extensionProductVariableEquiv.symm

theorem applicationRawLift_curve (S : Fin 5 → ℂ → ℂ) (v : ℂ) (t : Fin 1 → ℂ) :
    applicationRawLift g₂ g₃ hadd hneg Γ η e S
      (applicationCurve g₂ g₃ hadd hneg Γ η e v) t =
      PhilipponApplication.rawCoordinates S (v + t 0) := by
  simp [applicationRawLift, applicationRepresentative_curve, applicationPointEquiv_curve,
    PhilipponApplication.rawCoordinates]

theorem applicationLift_pullback (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (v : ℂ) (t : Fin 1 → ℂ) :
    eval (applicationLift g₂ g₃ hadd hneg Γ η e S
      (applicationCurve g₂ g₃ hadd hneg Γ η e v) t)
      (rename extensionProductVariableEquiv Q) =
      eval (PhilipponApplication.rawCoordinates S (v + t 0)) Q := by
  rw [eval_rename]
  have hh : applicationLift g₂ g₃ hadd hneg Γ η e S
      (applicationCurve g₂ g₃ hadd hneg Γ η e v) t ∘ extensionProductVariableEquiv =
      PhilipponApplication.rawCoordinates S (v + t 0) := by
    funext j
    simpa [applicationLift] using congrFun
      (applicationRawLift_curve g₂ g₃ hadd hneg Γ η e S v t) j
  rw [hh]

theorem applicationLift_analytic (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (g : (applicationGroup g₂ g₃ hadd hneg).Point)
    (v : ExtensionProductVariable) :
    AnalyticAt ℂ (fun t => applicationLift g₂ g₃ hadd hneg Γ η e S g t v) 0 := by
  have ht : AnalyticAt ℂ (fun t : Fin 1 → ℂ => t 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _
  have hs (j : Fin 5) (a : ℂ) :
      AnalyticAt ℂ (fun t : Fin 1 → ℂ => S j (a + t 0)) 0 := by
    exact (hS j _ (Set.mem_univ _)).comp (analyticAt_const.add ht)
  change AnalyticAt ℂ (fun t => applicationRawLift g₂ g₃ hadd hneg Γ η e S g t
    (extensionProductVariableEquiv.symm v)) 0
  generalize extensionProductVariableEquiv.symm v = j
  fin_cases j
  · exact analyticAt_const
  · exact analyticAt_const.add ht
  · exact hs _ _
  · exact hs _ _
  · exact hs _ _
  · exact (hs _ _).add (analyticAt_const.mul (hs _ _))
  · exact (hs _ _).add (analyticAt_const.mul (hs _ _))

theorem applicationLift_represents (S : Fin 5 → ℂ → ℂ)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph Γ η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (g : (applicationGroup g₂ g₃ hadd hneg).Point) (t : Fin 1 → ℂ)
    (i : (applicationGroup g₂ g₃ hadd hneg).FactorIndex) :
    ∃ h : (fun j => applicationLift g₂ g₃ hadd hneg Γ η e S g t ⟨i, j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j => applicationLift g₂ g₃ hadd hneg Γ η e S g t ⟨i, j⟩) h =
        (applicationGroup g₂ g₃ hadd hneg).embedding
          (g + applicationCurve g₂ g₃ hadd hneg Γ η e (t 0)) i := by
  rw [applicationGroup_embedding, map_add, applicationPointEquiv_curve]
  let r := applicationRepresentative g₂ g₃ hadd hneg Γ η e g
  change Fin 2 at i
  fin_cases i
  · change ∃ h : (fun j : Fin 2 => applicationLift g₂ g₃ hadd hneg Γ η e S g t ⟨0, j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j : Fin 2 => applicationLift g₂ g₃ hadd hneg Γ η e S g t ⟨0, j⟩) h =
        additivePoint ℂ ((applicationPointEquiv g₂ g₃ hadd hneg g).1 + t 0)
    have hl : (fun j : Fin 2 => applicationLift g₂ g₃ hadd hneg Γ η e S g t ⟨0, j⟩) =
        ![1, (applicationPointEquiv g₂ g₃ hadd hneg g).1 + t 0] := by
      funext j
      fin_cases j <;> rfl
    rw [hl]
    refine ⟨?_, rfl⟩
    intro hz
    have h := congrFun hz 0
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using h)
  · obtain ⟨hv, hp⟩ := he (r.1 + t 0) r.2
    have hc : e ((extensionPeriodGraph Γ η).mkQ (r.1 + t 0, r.2)) =
        (applicationPointEquiv g₂ g₃ hadd hneg g).2 +
          e ((extensionPeriodGraph Γ η).mkQ (t 0, 0)) := by
      have heq : (r.1 + t 0, r.2) = r + (t 0, 0) := by
        ext <;> simp
      rw [heq, map_add, map_add, applicationRepresentative_spec]
    have hl : (fun j : Fin 5 => applicationLift g₂ g₃ hadd hneg Γ η e S g t ⟨1, j⟩) =
        ![S 0 (r.1 + t 0), S 1 (r.1 + t 0), S 2 (r.1 + t 0),
          S 3 (r.1 + t 0) + r.2 * S 0 (r.1 + t 0),
          S 4 (r.1 + t 0) + r.2 * S 2 (r.1 + t 0)] := by
      funext j
      fin_cases j <;> rfl
    change ∃ h : (fun j : Fin 5 => applicationLift g₂ g₃ hadd hneg Γ η e S g t ⟨1, j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j : Fin 5 => applicationLift g₂ g₃ hadd hneg Γ η e S g t ⟨1, j⟩) h =
        ((applicationPointEquiv g₂ g₃ hadd hneg g).2 +
          e ((extensionPeriodGraph Γ η).mkQ (t 0, 0))).val.val
    rw [hl]
    refine ⟨hv, ?_⟩
    rw [← hc]
    exact hp.symm

end WeierstrassEllipticZeta
end

-- Source: Solutions/WeierstrassAnalyticModel.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
open scoped Topology
open MvPolynomial TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta

variable (g₂ g₃ : ℂ) [AddCommGroup (ProjectiveExtensionChartLocus g₂ g₃)]
    (hadd : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun xy : ProjectiveExtensionChartLocus g₂ g₃ × ProjectiveExtensionChartLocus g₂ g₃ =>
        fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
      (fun xy => fun _ => (xy.1 + xy.2).val.val))
    (hneg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => x.val.val)
      (fun x => fun _ => (-x).val.val))
    (Γ : Submodule ℤ ℂ) (η : Γ →ₗ[ℤ] ℂ)
    (e : GraphQuotientExtension Γ η ≃+ ProjectiveExtensionChartLocus g₂ g₃)
    (S : Fin 5 → ℂ → ℂ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph Γ η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

def applicationAnalyticSubgroup : AnalyticSubgroup (applicationGroup g₂ g₃ hadd hneg) :=
  AnalyticSubgroup.ofGlobalCurve (applicationCurve g₂ g₃ hadd hneg Γ η e)
    (applicationLift g₂ g₃ hadd hneg Γ η e S)
    (applicationLift_analytic g₂ g₃ hadd hneg Γ η e S hS)
    (applicationLift_represents g₂ g₃ hadd hneg Γ η e S he)

theorem applicationAnalyticSubgroup_pullback (Q : MvPolynomial (Fin 7) ℂ)
    (v : ℂ) (t : Fin 1 → ℂ) :
    (applicationAnalyticSubgroup g₂ g₃ hadd hneg Γ η e S hS he).pullback
      (rename extensionProductVariableEquiv Q) (applicationCurve g₂ g₃ hadd hneg Γ η e v) t =
      eval (PhilipponApplication.rawCoordinates S (v + t 0)) Q :=
  applicationLift_pullback g₂ g₃ hadd hneg Γ η e S Q v t

theorem applicationAnalyticSubgroup_carrier :
    (applicationAnalyticSubgroup g₂ g₃ hadd hneg Γ η e S hS he).carrier =
      Set.range (applicationCurve g₂ g₃ hadd hneg Γ η e) :=
  AnalyticSubgroup.ofGlobalCurve_carrier _ _ _ _

theorem applicationAnalyticSubgroup_dimension :
    (applicationAnalyticSubgroup g₂ g₃ hadd hneg Γ η e S hS he).dimension = 1 := by
  let A := applicationAnalyticSubgroup g₂ g₃ hadd hneg Γ η e S hS he
  let G := applicationGroup g₂ g₃ hadd hneg
  let Q : MvPolynomial (Fin 7) ℂ := X 1
  let P : G.CoordinateRing := rename extensionProductVariableEquiv Q
  have hQ : PhilipponApplication.Bihomogeneous Q 1 0 := by
    intro d hd
    simp only [Q, support_X, Finset.mem_singleton] at hd
    subst d
    simp
  have hP : P ∈ G.vanishingIdeal {0} := by
    apply Ideal.subset_span
    refine ⟨⟨![1, 0], applicationGroup_homogeneous g₂ g₃ hadd hneg Q 1 0 hQ⟩, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    have hy0 : y = 0 := hy
    subst y
    have hz := (applicationCurve_zero_locus g₂ g₃ hadd hneg Γ η e S he Q 1 0 hQ 0).mpr
      (by simp [Q, PhilipponApplication.rawCoordinates])
    change G.ambient.eval P (G.embedding (applicationCurve g₂ g₃ hadd hneg Γ η e 0)) = 0 at hz
    simpa only [map_zero] using hz
  let ev : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)
  have hf : A.pullback P 0 = ev := by
    funext t
    change Fin 1 → ℂ at t
    change (applicationAnalyticSubgroup g₂ g₃ hadd hneg Γ η e S hS he).pullback
      (rename extensionProductVariableEquiv (X 1)) 0 t = t 0
    have h := applicationAnalyticSubgroup_pullback g₂ g₃ hadd hneg Γ η e S hS he Q 0 t
    simpa [Q, PhilipponApplication.rawCoordinates] using h
  have hk := A.tangentKernel_eq_bot_of_linear_pullback ev P hP hf
  change 1 - Module.finrank ℂ (A.tangentKernel {0}) = 1
  rw [hk]
  simp

end WeierstrassEllipticZeta
end

-- Source: Solutions/WeierstrassLinearImageClassification.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
open MvPolynomial TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta

variable (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (hadd : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun xy : ProjectiveExtensionChartLocus L.g₂ L.g₃ × ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
      (fun xy => fun _ => (xy.1 + xy.2).val.val))
    (hneg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
      (fun x => fun _ => (-x).val.val))
    (η : L.lattice →ₗ[ℤ] ℂ)
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

/-- The explicit exponential in the paper, expressed in the actual quotient
and projective carrier. This definition makes no assertion about subgroups. -/
def applicationExponential (v : Fin 3 → ℂ) :
    (applicationGroup L.g₂ L.g₃ hadd hneg).Point :=
  (applicationPointEquiv L.g₂ L.g₃ hadd hneg).symm
    (v 0, e ((extensionPeriodGraph L.lattice η).mkQ (v 1, v 2)))

theorem applicationPointEquiv_exponential (v : Fin 3 → ℂ) :
    applicationPointEquiv L.g₂ L.g₃ hadd hneg
      (applicationExponential L hadd hneg η e v) =
        (v 0, e ((extensionPeriodGraph L.lattice η).mkQ (v 1, v 2))) :=
  (applicationPointEquiv L.g₂ L.g₃ hadd hneg).apply_symm_apply _

theorem applicationExponential_surjective :
    Function.Surjective (applicationExponential L hadd hneg η e) := by
  intro g
  obtain ⟨q, hq⟩ := e.surjective (applicationPointEquiv L.g₂ L.g₃ hadd hneg g).2
  obtain ⟨⟨z, u⟩, hzu⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective q
  refine ⟨![(applicationPointEquiv L.g₂ L.g₃ hadd hneg g).1, z, u], ?_⟩
  apply (applicationPointEquiv L.g₂ L.g₃ hadd hneg).injective
  rw [applicationPointEquiv_exponential]
  change ((applicationPointEquiv L.g₂ L.g₃ hadd hneg g).1,
    e ((extensionPeriodGraph L.lattice η).mkQ (z, u))) = _
  rw [hzu, hq]

include he in
theorem applicationExponential_raw_zero_iff
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (v : Fin 3 → ℂ) :
    (applicationGroup L.g₂ L.g₃ hadd hneg).ambient.eval
      (rename extensionProductVariableEquiv Q)
      ((applicationGroup L.g₂ L.g₃ hadd hneg).embedding
        (applicationExponential L hadd hneg η e v)) = 0 ↔
    eval ![1, v 0, S 0 (v 1), S 1 (v 1), S 2 (v 1),
      S 3 (v 1) + v 2 * S 0 (v 1), S 4 (v 1) + v 2 * S 2 (v 1)] Q = 0 := by
  change extensionProductAmbient.eval (rename extensionProductVariableEquiv Q)
    ((applicationGroup L.g₂ L.g₃ hadd hneg).embedding
      (applicationExponential L hadd hneg η e v)) = 0 ↔ _
  rw [applicationGroup_embedding, applicationPointEquiv_exponential]
  obtain ⟨hv, hp⟩ := he (v 1) (v 2)
  simpa using
    extensionProduct_raw_eval_zero_iff Q m n hQ
      (v 0, e ((extensionPeriodGraph L.lattice η).mkQ (v 1, v 2))) _ hv hp

end WeierstrassEllipticZeta

end

-- Source: Solutions/WeierstrassSubgroupAnalyticPreimage.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
open MvPolynomial PhilipponMultiplicity TranscendenceTheory
open scoped Topology
namespace WeierstrassEllipticZeta
open PhilipponApplication

variable (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (hadd : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun xy : ProjectiveExtensionChartLocus L.g₂ L.g₃ × ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
      (fun xy => fun _ => (xy.1 + xy.2).val.val))
    (hneg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
      (fun x => fun _ => (-x).val.val))
    (η : L.lattice →ₗ[ℤ] ℂ)
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

/-- The explicit exponential is an additive homomorphism on C³. -/
def applicationExponentialHom : (Fin 3 → ℂ) →+ (applicationGroup L.g₂ L.g₃ hadd hneg).Point where
  toFun := applicationExponential L hadd hneg η e
  map_zero' := by
    apply (applicationPointEquiv L.g₂ L.g₃ hadd hneg).injective
    rw [applicationPointEquiv_exponential, map_zero]
    change (0, e ((extensionPeriodGraph L.lattice η).mkQ 0)) = 0
    simp
  map_add' v w := by
    apply (applicationPointEquiv L.g₂ L.g₃ hadd hneg).injective
    rw [map_add, applicationPointEquiv_exponential, applicationPointEquiv_exponential,
      applicationPointEquiv_exponential]
    apply Prod.ext
    · rfl
    · change e ((extensionPeriodGraph L.lattice η).mkQ ((v 1, v 2) + (w 1, w 2))) = _
      rw [map_add, map_add]
      rfl

end WeierstrassEllipticZeta

end

-- Source: Solutions/WeierstrassModelExponential.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set MvPolynomial PhilipponMultiplicity TranscendenceTheory
open scoped Topology

namespace WeierstrassEllipticZeta
open PhilipponApplication

/-- The explicit exponential is an actual surjective additive map in every
compatible Model, with exactly the stipulated projective coordinate equations. -/
theorem model_has_exponential_hom
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) :
    ∃ q : (Fin 3 → ℂ) →+ M.group.Point, Function.Surjective q ∧
      ∀ (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ), Bihomogeneous Q m n →
        ∀ v, M.group.ambient.eval (M.polynomial Q) (M.group.embedding (q v)) = 0 ↔
          MvPolynomial.eval (exponentialCoordinates S v) Q = 0 := by
  obtain ⟨η, hη, _⟩ := elliptic_extension_group_geometry L
  obtain ⟨group, e, he, hadd, hneg⟩ :=
    projective_extension_group_with_regular_operations L D S hS hS_value hS_ne η hη
  let := group
  have hE := extensionEmbeddedGroup_dimension L D S hS hS_value hS_ne η e he hadd hneg
  have hDense := extensionProduct_curve_dense L D S hS hS_value hS_ne η e he
  let N : Model S :=
    { factor := applicationFactor L.g₂ L.g₃ hadd hneg
      factor_dimension := applicationFactor_dimension L.g₂ L.g₃ hadd hneg hE
      variableEquiv := extensionProductVariableEquiv
      homogeneous := applicationGroup_homogeneous L.g₂ L.g₃ hadd hneg
      curve := applicationCurve L.g₂ L.g₃ hadd hneg L.lattice η e
      curve_injective := applicationCurve_injective L.g₂ L.g₃ hadd hneg L.lattice η e
      curve_dense := applicationCurve_dense L.g₂ L.g₃ hadd hneg L.lattice η e hDense
      A := applicationAnalyticSubgroup L.g₂ L.g₃ hadd hneg L.lattice η e S hS he
      parameter := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)
      analytic_dimension := applicationAnalyticSubgroup_dimension L.g₂ L.g₃ hadd hneg L.lattice η e S hS he
      analytic_carrier := applicationAnalyticSubgroup_carrier L.g₂ L.g₃ hadd hneg L.lattice η e S hS he
      pullback := applicationAnalyticSubgroup_pullback L.g₂ L.g₃ hadd hneg L.lattice η e S hS he
      zero_locus := applicationCurve_zero_locus L.g₂ L.g₃ hadd hneg L.lattice η e S he }
  obtain ⟨E, hE⟩ := M.exists_group_comparison N
  let q := E.symm.toAddMonoidHom.comp (applicationExponentialHom L hadd hneg η e)
  refine ⟨q, E.symm.surjective.comp (applicationExponential_surjective L hadd hneg η e), ?_⟩
  intro Q m n hQ v
  rw [M.polynomial_zero_iff_comparison N _ Q m n hQ, ← hE]
  change N.group.ambient.eval (N.polynomial Q)
    (N.group.embedding (E (E.symm (applicationExponentialHom L hadd hneg η e v)))) = 0 ↔ _
  rw [E.apply_symm_apply]
  exact applicationExponential_raw_zero_iff L S hadd hneg η e he Q m n hQ v

theorem PhilipponApplication.Model.exponentialPreimage_eq_preimage
    {S : Fin 5 → ℂ → ℂ} (M : Model S) (H : AlgebraicSubgroup M.group)
    (q : (Fin 3 → ℂ) →+ M.group.Point)
    (hq : ∀ (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ), Bihomogeneous Q m n →
      ∀ v, M.group.ambient.eval (M.polynomial Q) (M.group.embedding (q v)) = 0 ↔
        MvPolynomial.eval (exponentialCoordinates S v) Q = 0) :
    M.exponentialPreimage H = q ⁻¹' H.carrier := by
  ext v
  constructor
  · intro hv
    apply H.mem_of_homogeneous_equations
    intro P degrees hP hzero
    let Q := rename M.variableEquiv.symm P
    have hr : M.polynomial Q = P := by simp [Model.polynomial, Q, rename_rename]
    have hd : degrees = ![degrees 0, degrees 1] := by
      funext i
      change Fin 2 at i
      fin_cases i <;> rfl
    have hQ : Bihomogeneous Q (degrees 0) (degrees 1) := (M.homogeneous_iff Q _ _).mp (by
      change M.group.ambient.IsHomogeneous (M.polynomial Q) _
      rw [hr, ← hd]
      exact hP)
    rw [← hr]
    apply (hq Q _ _ hQ v).mpr
    exact hv Q _ _ hQ (by simpa only [hr] using hzero)
  · intro hv Q m n hQ hzero
    exact (hq Q m n hQ v).mp (hzero (q v) hv)

theorem subgroup_exponential_preimage_additive
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group) :
    ∃ K : AddSubgroup (Fin 3 → ℂ), (K : Set (Fin 3 → ℂ)) = M.exponentialPreimage H := by
  obtain ⟨q, _, hq⟩ := model_has_exponential_hom L D S hS hS_value hS_ne M
  exact ⟨H.toAddSubgroup.comap q, (M.exponentialPreimage_eq_preimage H q hq).symm⟩

end WeierstrassEllipticZeta
end

set_option autoImplicit false
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
    (M : Model S) (H : AlgebraicSubgroup M.group) :
    ∃ K : AddSubgroup (Fin 3 → ℂ), (K : Set (Fin 3 → ℂ)) = M.exponentialPreimage H := by
  exact WeierstrassEllipticZeta.subgroup_exponential_preimage_additive L D S hS hS_value hS_ne M H
#print axioms solution
