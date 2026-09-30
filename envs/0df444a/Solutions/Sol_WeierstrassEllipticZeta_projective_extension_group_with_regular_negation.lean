-- Prove2me | solution 1 for WeierstrassEllipticZeta.projective_extension_group_with_regular_negation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T23:34:35.915306+00:00
-- url     : https://prove2.me/submissions/4571a587-1c04-4bce-ac08-89c808f4a28f

import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_group_geometry
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_descent
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_equations
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_chart_cover
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_fiber_model
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_injective
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_surjective


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


set_option autoImplicit false
open TranscendenceTheory
noncomputable section

namespace WeierstrassEllipticZeta

private theorem shear_smul (u c : ℂ) (v : Fin 5 → ℂ) :
    extensionFiberShear u (c • v) = c • extensionFiberShear u v := by
  ext j
  fin_cases j <;> simp [extensionFiberShear] <;> ring

private theorem shear_add (u t : ℂ) (v : Fin 5 → ℂ) :
    extensionFiberShear u (extensionFiberShear t v) = extensionFiberShear (t + u) v := by
  ext j
  fin_cases j <;> simp [extensionFiberShear] <;> ring

theorem projective_descent_intertwines_fiber_action
    (L : PeriodPair) (S : Fin 5 → ℂ → ℂ) (η : L.lattice →ₗ[ℤ] ℂ)
    (P : GraphQuotientExtension L.lattice η → ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (F : ProjectiveExtensionFiberModel L.g₂ L.g₃) :
    ∀ (u : ℂ) (e : GraphQuotientExtension L.lattice η),
      P (e + extensionInclusion L.lattice η u) = F.action u (P e) := by
  intro u e
  obtain ⟨⟨z, t⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective e
  have he : (extensionPeriodGraph L.lattice η).mkQ (z, t) +
      extensionInclusion L.lattice η u =
        (extensionPeriodGraph L.lattice η).mkQ (z, t + u) := by
    change _ + (extensionPeriodGraph L.lattice η).mkQ (0, u) = _
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero]
  rw [he]
  obtain ⟨hv, hp⟩ := hP z t
  obtain ⟨hv', hp'⟩ := hP z (t + u)
  obtain ⟨hw, hact⟩ := F.action_coords u (P ((extensionPeriodGraph L.lattice η).mkQ (z, t)))
  apply Subtype.ext
  apply Subtype.ext
  change (P ((extensionPeriodGraph L.lattice η).mkQ (z, t + u))).val.val = _
  rw [hp', show (F.action u (P ((extensionPeriodGraph L.lattice η).mkQ (z, t)))).val.val =
    Projectivization.mk ℂ _ hw from hact]
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hv
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(c : ℂ)⁻¹, ?_⟩
  change (c : ℂ)⁻¹ • extensionFiberShear u _ = _
  rw [extensionProjectivePoint, hp, ← hc, Units.smul_def, shear_smul, ← mul_smul, inv_mul_cancel₀ c.ne_zero,
    one_smul]
  exact shear_add u t (fun j => S j z)

/-- The analytic quotient is exactly the explicit two-chart projective locus.
This does not assert regularity of the transferred addition law. -/
theorem projective_extension_equivalence
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ) (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
    ∃ e : GraphQuotientExtension L.lattice η ≃ ProjectiveExtensionChartLocus L.g₂ L.g₃,
      ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv := by
  obtain ⟨P, hP, _, _⟩ := elliptic_extension_projective_descent L D S hS hS_value hS_ne η hη
  obtain ⟨_, _, _, Q, hQ⟩ := elliptic_extension_projective_equations L D S hS hS_value η P hP
  have hQP (z u : ℂ) : ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (Q ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv := by
    rw [hQ]
    exact hP z u
  obtain ⟨_, _, R, hR⟩ := elliptic_extension_projective_chart_cover L D S hS hS_value hS_ne η Q hQP
  have hRP (z u : ℂ) : ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (R ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv := by
    rw [hR]
    exact hQP z u
  obtain ⟨F⟩ := elliptic_extension_projective_fiber_model L.g₂ L.g₃
  have hact := projective_descent_intertwines_fiber_action L S η R hRP F
  exact ⟨Equiv.ofBijective R
    ⟨elliptic_extension_projective_injective L D S hS hS_value η R hRP F hact,
      elliptic_extension_projective_surjective L D S hS hS_value hS_ne η R hRP F hact⟩,
    hRP⟩

theorem projective_extension_commutative_group
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
        ∀ z u : ℂ, ∃ hv :
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
          (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv := by
  obtain ⟨e, he⟩ := projective_extension_equivalence L D S hS hS_value hS_ne η hη
  refine ⟨e.symm.addCommGroup, ?_⟩
  letI := e.symm.addCommGroup
  exact ⟨e.symm.addEquiv.symm, he⟩

end WeierstrassEllipticZeta



set_option autoImplicit false
set_option maxHeartbeats 600000
open Filter TranscendenceTheory
open scoped Topology
noncomputable section

namespace WeierstrassEllipticZeta

private lemma zeta_neg (L : PeriodPair) (z : ℂ) :
    weierstrassZeta L (-z) = -weierstrassZeta L z := by
  classical
  have hsum : (∑' l : L.lattice, if -l = 0 then (0 : ℂ) else
      1 / (-z - ((-l : L.lattice) : ℂ)) + 1 / ((-l : L.lattice) : ℂ) +
        -z / ((-l : L.lattice) : ℂ) ^ 2) =
      ∑' l : L.lattice, -(if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by
    apply tsum_congr
    intro l
    by_cases hl : l = 0
    · simp [hl]
    · simp only [neg_eq_zero, if_neg hl, NegMemClass.coe_neg, even_two, Even.neg_pow]
      rw [show -z - -(l : ℂ) = -(z - (l : ℂ)) by ring]
      simp only [div_neg, neg_div]
      ring
  unfold weierstrassZeta
  conv_lhs => arg 2; rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, hsum, tsum_neg, div_neg]
  ring

private lemma sigma_neg (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (z : ℂ) (hz : z ∉ L.lattice) : S.sigma (-z) = -S.sigma z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hd (w : ℂ) (hw : w ∉ L.lattice) :
      HasDerivAt (fun x => S.sigma (-x) / S.sigma x) 0 w := by
    have hm : HasDerivAt (fun x => S.sigma (-x))
        (weierstrassZeta L w * S.sigma (-w)) w := by
      convert! (S.hasDerivAt (-w) (by simpa using hw)).comp w
        (hasDerivAt_id w).neg using 1
      simp [zeta_neg]
    convert! hm.div (S.hasDerivAt w hw) (hne w hw) using 1
    ring
  obtain ⟨c, hc⟩ := hopen.exists_is_const_of_deriv_eq_zero
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv)
  have heq : (fun w => S.sigma (-w)) =ᶠ[𝓝 (0 : ℂ)]
      (fun w => c * S.sigma w) := by
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with w hw
    by_cases hw0 : w = 0
    · simp [hw0, S.zero]
    · have hwL : w ∉ L.lattice := fun h => hw ⟨h, hw0⟩
      exact (div_eq_iff (hne w hwL)).mp (hc w hwL)
  have hm : HasDerivAt (fun w => S.sigma (-w)) (-1) 0 := by
    have hh : HasDerivAt S.sigma 1 (-(0 : ℂ)) := by simpa using S.deriv_zero
    simpa using! hh.comp 0 (hasDerivAt_id (0 : ℂ)).neg
  have hcc := (hm.congr_of_eventuallyEq heq.symm).unique (S.deriv_zero.const_mul c)
  simp only [mul_one] at hcc
  have h := (div_eq_iff (hne z hz)).mp (hc z hz)
  simpa [← hcc] using h

theorem entire_extension_coordinates_neg
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∀ (z : ℂ) (j : Fin 5), S j (-z) = ![-1, -1, 1, 1, -1] j * S j z := by
  have hσne (z : ℂ) (hz : z ∉ L.lattice) : D.sigma z ≠ 0 := by
    intro hz0
    obtain ⟨j, hj⟩ := hS_ne z
    exact hj (by simp [hS_value z hz j, hz0])
  have heq (j : Fin 5) : (fun z : ℂ => S j (-z)) =
      (fun z => ![-1, -1, 1, 1, -1] j * S j z) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (show AnalyticOnNhd ℂ (fun z : ℂ => S j (-z)) Set.univ from
        fun z _ => (hS j (-z) (Set.mem_univ _)).comp (analyticAt_id.neg))
      (show AnalyticOnNhd ℂ (fun z => ![-1, -1, 1, 1, -1] j * S j z) Set.univ from
        fun z _ => analyticAt_const.mul (hS j z (Set.mem_univ _)))
      (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    rw [hS_value (-z) (by simpa using hz) j, hS_value z hz j,
      sigma_neg L D hσne z hz, L.weierstrassP_neg, L.derivWeierstrassP_neg, zeta_neg]
    fin_cases j <;> simp <;> ring
  exact fun z j => congrFun (heq j) z

theorem projective_extension_negation_regular
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
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
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) :
    PhilipponMultiplicity.MultiProjectiveSpace.IsRegularAlong
      (PhilipponMultiplicity.projectiveSpace ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
      (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => (-x).val.val) := by
  let P : Fin 5 → MvPolynomial (Fin 5) ℂ :=
    ![MvPolynomial.X 0, MvPolynomial.X 1, -MvPolynomial.X 2,
      -MvPolynomial.X 3, MvPolynomial.X 4]
  apply PhilipponMultiplicity.projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact (MvPolynomial.isHomogeneous_X ℂ 2).neg
    · exact (MvPolynomial.isHomogeneous_X ℂ 3).neg
    · exact MvPolynomial.isHomogeneous_X ℂ 4
  · intro x
    obtain ⟨q, rfl⟩ := e.surjective x
    obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective q
    obtain ⟨hv, hp⟩ := he z u
    obtain ⟨hvn, hpn⟩ := he (-z) (-u)
    have hneg : e ((extensionPeriodGraph L.lattice η).mkQ (-z, -u)) =
        -e ((extensionPeriodGraph L.lattice η).mkQ (z, u)) := by
      change e ((extensionPeriodGraph L.lattice η).mkQ (-(z, u))) = _
      rw [map_neg, map_neg]
    rw [hneg] at hpn
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hv
    have hcoord : (fun j => MvPolynomial.eval
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val.rep (P j)) =
        (-c.val) •
          ![S 0 (-z), S 1 (-z), S 2 (-z), S 3 (-z) - u * S 0 (-z),
            S 4 (-z) - u * S 2 (-z)] := by
      rw [hp, ← hc]
      ext j
      fin_cases j <;> simp [P, Units.smul_def, entire_extension_coordinates_neg L D S hS hS_value hS_ne]
        <;> ring
    have hn : (fun j => MvPolynomial.eval
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val.rep (P j)) ≠ 0 := by
      rw [hcoord]
      exact smul_ne_zero (neg_ne_zero.mpr c.ne_zero) (by simpa [neg_mul, sub_eq_add_neg] using hvn)
    refine ⟨hn, ?_⟩
    rw [hpn]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨-c.val, ?_⟩
    simpa only [neg_mul, sub_eq_add_neg] using hcoord.symm

theorem projective_extension_group_with_regular_negation_implementation
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
          (PhilipponMultiplicity.projectiveSpace ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => (-x).val.val) := by
  obtain ⟨group, e, he⟩ := projective_extension_commutative_group L D S hS hS_value hS_ne η hη
  letI := group
  exact ⟨group, e, he, projective_extension_negation_regular L D S hS hS_value hS_ne η e he⟩

end WeierstrassEllipticZeta


set_option autoImplicit false
open PhilipponMultiplicity
open WeierstrassEllipticZeta TranscendenceTheory

theorem solution
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
          (PhilipponMultiplicity.projectiveSpace ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => (-x).val.val) := by
  exact WeierstrassEllipticZeta.projective_extension_group_with_regular_negation_implementation L D S hS hS_value hS_ne η hη

#print axioms solution
