-- Prove2me | solution 1 for PhilipponMultiplicity.additive_projective_hilbert_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-24T05:14:23.957365+00:00
-- url     : https://prove2.me/submissions/3b6e7993-a430-4227-813f-aebfea4769f2

import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_PhilipponMultiplicity_Hilbert
import Definitions.Def_PhilipponMultiplicity_Degree


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



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace PhilipponMultiplicity.Hilbert

private abbrev BinaryVariable := (i : Fin 1) × Fin ((fun _ : Fin 1 => 1) i + 1)

private theorem binary_weight (m : BinaryVariable →₀ ℕ) :
    Finsupp.weight (blockWeight 1 (fun _ => 1)) m =
      fun _ => m ⟨0, 0⟩ + m ⟨0, 1⟩ := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Finsupp.weight_eq_sum, blockWeight, Fintype.sum_sigma, Fin.sum_univ_two]

private def binaryMonomialEquiv (n : ℕ) :
    {m : BinaryVariable →₀ ℕ //
      Finsupp.weight (blockWeight 1 (fun _ => 1)) m = fun _ => n} ≃ Fin (n + 1) where
  toFun m := ⟨m.val ⟨0, 1⟩, by
    have h := congrFun m.property 0
    rw [binary_weight] at h
    dsimp at h
    omega⟩
  invFun k := ⟨Finsupp.equivFunOnFinite.symm (fun j => if j.2 = 0 then n - k.val else k.val), by
    rw [binary_weight]
    ext i
    simp
    omega⟩
  left_inv m := by
    apply Subtype.ext
    ext j
    rcases j with ⟨i, j⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have h := congrFun m.property 0
    rw [binary_weight] at h
    dsimp at h
    fin_cases j <;> simp <;> omega
  right_inv k := by
    apply Fin.ext
    simp

/-- Binary homogeneous forms of degree `n` have exactly `n+1` independent
coefficients, for the actual one-block degree-piece definition. -/
theorem binary_degreePiece_finrank (K : Type*) [Field K] (n : ℕ) :
    Module.finrank K (degreePiece K 1 (fun _ => 1) (fun _ => n)) = n + 1 := by
  classical
  unfold degreePiece
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  let e := binaryMonomialEquiv n
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) _).finrank_eq]
  have h := (Finsupp.domLCongr e : (_ →₀ K) ≃ₗ[K] (Fin (n + 1) →₀ K)).finrank_eq
  exact h.trans (by simp)

/-- The quotient by the zero ideal has the same homogeneous-piece dimension. -/
theorem binary_hilbertFunction_bot (K : Type*) [Field K] (n : ℕ) :
    hilbertFunction K 1 (fun _ => 1) ⊥ (fun _ => n) = n + 1 := by
  let e := (AlgEquiv.quotientBot K (CoordinateRing K 1 (fun _ => 1))).symm.toLinearEquiv
  have h := e.finrank_map_eq (degreePiece K 1 (fun _ => 1) (fun _ => n))
  change Module.finrank K (quotientPiece K 1 (fun _ => 1) ⊥ (fun _ => n)) = _
  exact h.trans (binary_degreePiece_finrank K n)

theorem binary_hilbertPolynomial_bot (K : Type*) [Field K] :
    hilbertPolynomial K 1 (fun _ => 1) ⊥ = MvPolynomial.X 0 + 1 := by
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, ?_⟩
  intro d _
  have hd : d = fun _ => d 0 := by ext i; congr 1; exact Subsingleton.elim _ _
  rw [hd, binary_hilbertFunction_bot]
  simp

end PhilipponMultiplicity.Hilbert



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace PhilipponMultiplicity

private theorem single_block_eval_scale {K : Type*} [Field K] {n : ℕ}
    {P : (projectiveSpace K n).CoordinateRing} {D : Fin 1 → ℕ}
    (hP : (projectiveSpace K n).IsHomogeneous P D)
    (X : (projectiveSpace K n).Variable → K) (c : K) :
    MvPolynomial.eval (fun i => c * X i) P = c ^ D 0 * MvPolynomial.eval X P := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd : (∑ i, m i) = D 0 := by
    rw [Fintype.sum_sigma]
    change (∑ i : Fin 1, ∑ j : Fin (n + 1), m ⟨i, j⟩) = D 0
    rw [Fin.sum_univ_one]
    exact hP m hm (0 : Fin 1)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem additiveCarrier_vanishingIdeal_eq_bot (K : Type*) [Field K] [Infinite K] :
    (projectiveSpace K 1).vanishingIdeal
      ((fun p => fun _ => p) '' additiveCarrier K) = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D, hP⟩, hzero⟩
  change P = 0
  apply MvPolynomial.funext_set (fun _ => ({0} : Set K)ᶜ)
    (fun _ => (Set.finite_singleton (0 : K)).infinite_compl)
  intro X hX
  have h0 : X ⟨(0 : Fin 1), 0⟩ ≠ 0 := hX _ (Set.mem_univ _)
  let V : Fin 2 → K := fun j => X ⟨(0 : Fin 1), j⟩
  have hV : V ≠ 0 := by intro hz; exact h0 (congrFun hz 0)
  let p := Projectivization.mk K V hV
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K V hV
  have hp : p ∈ additiveCarrier K := by
    change p.rep 0 ≠ 0
    dsimp only [p]
    rw [← hc]
    exact mul_ne_zero c.ne_zero h0
  have hz := hzero (fun _ => p) ⟨p, hp, rfl⟩
  have hcoords : (projectiveSpace K 1).coordinate (fun _ => p) =
      fun i => c.val * X i := by
    funext i
    rcases i with ⟨i, j⟩
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change p.rep j = _
    dsimp only [p]
    rw [← hc]
    rfl
  change MvPolynomial.eval _ P = 0 at hz
  rw [hcoords, single_block_eval_scale hP] at hz
  have heval := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ c.ne_zero)
  simpa only [map_zero] using heval

theorem additiveEmbeddedGroup_dimension (K : Type*) [Field K] [Infinite K] :
    (additiveEmbeddedGroup K).dimension = 1 := by
  change (Hilbert.hilbertPolynomial K 1 (fun _ => 1)
    ((projectiveSpace K 1).vanishingIdeal ((fun p => fun _ => p) '' additiveCarrier K))).totalDegree = 1
  rw [additiveCarrier_vanishingIdeal_eq_bot, Hilbert.binary_hilbertPolynomial_bot]
  rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt (by simp)]
  simp

/-- The actual projective-closure Hilbert polynomial of the standard affine line. -/
theorem additive_projective_hilbert_polynomial_implementation (K : Type*) [Field K] [Infinite K] :
    Hilbert.hilbertPolynomial K 1 (fun _ => 1)
      ((projectiveSpace K 1).vanishingIdeal
        ((fun p : Projectivization K (Fin 2 → K) => fun _ : Fin 1 => p) ''
          {p : Projectivization K (Fin 2 → K) | p.rep 0 ≠ 0})) =
      MvPolynomial.X 0 + 1 := by
  exact (congrArg (Hilbert.hilbertPolynomial K 1 (fun _ => 1))
    (additiveCarrier_vanishingIdeal_eq_bot K)).trans (Hilbert.binary_hilbertPolynomial_bot K)

end PhilipponMultiplicity

open PhilipponMultiplicity
theorem solution (K : Type*) [Field K] [Infinite K] :
    Hilbert.hilbertPolynomial K 1 (fun _ => 1)
      ((projectiveSpace K 1).vanishingIdeal
        ((fun p : Projectivization K (Fin 2 → K) => fun _ : Fin 1 => p) ''
          {p : Projectivization K (Fin 2 → K) | p.rep 0 ≠ 0})) =
      MvPolynomial.X 0 + 1 := by
  exact PhilipponMultiplicity.additive_projective_hilbert_polynomial_implementation K
