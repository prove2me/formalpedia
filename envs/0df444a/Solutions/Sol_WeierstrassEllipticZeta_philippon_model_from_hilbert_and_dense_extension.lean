-- Prove2me | solution 1 for WeierstrassEllipticZeta.philippon_model_from_hilbert_and_dense_extension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-24T08:00:42.234221+00:00
-- url     : https://prove2.me/submissions/d3b073d9-9c60-49a0-80b4-2c7052f79f52

import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_PhilipponMultiplicity_Hilbert
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen
import Definitions.Def_WeierstrassEllipticZeta_PhilipponModel

-- Source: Solutions.PhilipponProjectiveGeometry
set_option autoImplicit true
set_option maxHeartbeats 200000

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

-- Source: Solutions.WeierstrassEmbeddedGroup
set_option autoImplicit true
set_option maxHeartbeats 200000

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

-- Source: Solutions.PhilipponAdditiveGroup
set_option autoImplicit true
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity
universe u

variable (K : Type u) [Field K]

private theorem PhilipponAdditiveGroup_homogeneous_X (M : MultiProjectiveSpace K) (v : M.Variable) :
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

private theorem PhilipponAdditiveGroup_homogeneous_add (M : MultiProjectiveSpace K)
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

private theorem PhilipponAdditiveGroup_additivePoint_eq_mk {v : Fin 2 → K} (hv : v 0 ≠ 0) :
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
    have hpoint := PhilipponAdditiveGroup_additivePoint_eq_mk K (v := ![x.val.rep 0, -x.val.rep 1]) hx
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

private theorem PhilipponAdditiveGroup_homogeneous_bilinear (a b : Fin 2) :
    (projectiveSquare K 1).IsHomogeneous
      (MvPolynomial.X ⟨(0 : Fin 2), a⟩ * MvPolynomial.X ⟨(1 : Fin 2), b⟩) (fun _ => 1) := by
  have h := (PhilipponAdditiveGroup_homogeneous_X K (projectiveSquare K 1) ⟨(0 : Fin 2), a⟩).mul (projectiveSquare K 1)
    (PhilipponAdditiveGroup_homogeneous_X K (projectiveSquare K 1) ⟨(1 : Fin 2), b⟩)
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
    · exact PhilipponAdditiveGroup_homogeneous_bilinear K 0 0
    · exact PhilipponAdditiveGroup_homogeneous_add K _ (PhilipponAdditiveGroup_homogeneous_bilinear K 1 0) (PhilipponAdditiveGroup_homogeneous_bilinear K 0 1)
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
    simpa only [he, hs] using (PhilipponAdditiveGroup_additivePoint_eq_mk K hv).symm

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


-- Source: Solutions.WeierstrassProductCoordinates
set_option autoImplicit true
set_option maxHeartbeats 200000

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

private theorem WeierstrassProductCoordinates_product_exponent_sums (d : Fin 7 →₀ ℕ) :
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
    exact ⟨(WeierstrassProductCoordinates_product_exponent_sums d).1.symm.trans (hh 0),
      (WeierstrassProductCoordinates_product_exponent_sums d).2.symm.trans (hh 1)⟩
  · intro h d hd i
    obtain ⟨c, hc, hcd⟩ := Finset.mem_image.mp hd
    subst d
    change Fin 2 at i
    fin_cases i
    · exact (WeierstrassProductCoordinates_product_exponent_sums c).1.trans (h c hc).1
    · exact (WeierstrassProductCoordinates_product_exponent_sums c).2.trans (h c hc).2

private theorem WeierstrassProductCoordinates_product_block_scale (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
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
  have hscale := WeierstrassProductCoordinates_product_block_scale Q m n hQ
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
  have hscale := WeierstrassProductCoordinates_product_block_scale Q m n hQ ![1, p.1, v 0, v 1, v 2, v 3, v 4] 1 b.val
  simp at hscale
  rw [hscale]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ b.ne_zero))

end WeierstrassEllipticZeta


-- Source: Solutions.PhilipponBinaryHilbert
set_option autoImplicit true
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace PhilipponMultiplicity.Hilbert

private abbrev PhilipponBinaryHilbert_BinaryVariable := (i : Fin 1) × Fin ((fun _ : Fin 1 => 1) i + 1)

private theorem PhilipponBinaryHilbert_binary_weight (m : PhilipponBinaryHilbert_BinaryVariable →₀ ℕ) :
    Finsupp.weight (blockWeight 1 (fun _ => 1)) m =
      fun _ => m ⟨0, 0⟩ + m ⟨0, 1⟩ := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Finsupp.weight_eq_sum, blockWeight, Fintype.sum_sigma, Fin.sum_univ_two]

private def PhilipponBinaryHilbert_binaryMonomialEquiv (n : ℕ) :
    {m : PhilipponBinaryHilbert_BinaryVariable →₀ ℕ //
      Finsupp.weight (blockWeight 1 (fun _ => 1)) m = fun _ => n} ≃ Fin (n + 1) where
  toFun m := ⟨m.val ⟨0, 1⟩, by
    have h := congrFun m.property 0
    rw [PhilipponBinaryHilbert_binary_weight] at h
    dsimp at h
    omega⟩
  invFun k := ⟨Finsupp.equivFunOnFinite.symm (fun j => if j.2 = 0 then n - k.val else k.val), by
    rw [PhilipponBinaryHilbert_binary_weight]
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
    rw [PhilipponBinaryHilbert_binary_weight] at h
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
  let e := PhilipponBinaryHilbert_binaryMonomialEquiv n
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


-- Source: Solutions.PhilipponAdditiveDimension
set_option autoImplicit true
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace PhilipponMultiplicity

private theorem PhilipponAdditiveDimension_single_block_eval_scale {K : Type*} [Field K] {n : ℕ}
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
  rw [hcoords, PhilipponAdditiveDimension_single_block_eval_scale hP] at hz
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
theorem additive_projective_hilbert_polynomial (K : Type*) [Field K] [Infinite K] :
    Hilbert.hilbertPolynomial K 1 (fun _ => 1)
      ((projectiveSpace K 1).vanishingIdeal
        ((fun p : Projectivization K (Fin 2 → K) => fun _ : Fin 1 => p) ''
          {p : Projectivization K (Fin 2 → K) | p.rep 0 ≠ 0})) =
      MvPolynomial.X 0 + 1 := by
  exact (congrArg (Hilbert.hilbertPolynomial K 1 (fun _ => 1))
    (additiveCarrier_vanishingIdeal_eq_bot K)).trans (Hilbert.binary_hilbertPolynomial_bot K)

end PhilipponMultiplicity


-- Source: Solutions.WeierstrassApplicationProduct
set_option autoImplicit true
set_option maxHeartbeats 200000

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

-- Source: Solutions.PhilipponLocalCurveCarrier
set_option autoImplicit true
set_option maxHeartbeats 200000

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


-- Source: Solutions.WeierstrassAnalyticLifts
set_option autoImplicit true
set_option maxHeartbeats 200000

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

-- Source: Solutions.PhilipponAnalyticGlobalCurve
set_option autoImplicit true
set_option maxHeartbeats 200000

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

-- Source: Solutions.WeierstrassAnalyticModel
set_option autoImplicit true
set_option maxHeartbeats 200000

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

-- Source: Solutions.WeierstrassAnalyticAssembly
set_option autoImplicit true
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MvPolynomial WeierstrassEllipticZeta TranscendenceTheory PhilipponMultiplicity

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ) (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
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
    (hGa : Hilbert.hilbertPolynomial ℂ 1 (fun _ => 1)
      ((projectiveSpace ℂ 1).vanishingIdeal
        ((fun p : Projectivization ℂ (Fin 2 → ℂ) => fun _ : Fin 1 => p) ''
          {p : Projectivization ℂ (Fin 2 → ℂ) | p.rep 0 ≠ 0})) =
      MvPolynomial.X 0 + 1)
    (hExtensionHilbert : Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4)
      ((projectiveSpace ℂ 4).vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          fun _ : Fin 1 => p.val.val))) =
      C 3 * X 0 ^ 2 + C 2)
    (hCurveDense : let M : MultiProjectiveSpace ℂ := ⟨2, by decide, ![1, 4]⟩
    let embedding : (ℂ × ProjectiveExtensionChartLocus L.g₂ L.g₃) → M.Point :=
      fun p => Fin.cons
        (Projectivization.mk ℂ ![1, p.1]
          (by intro h; have hh := congrFun h 0; simpa using hh))
        (Fin.cons p.2.val.val (fun i => Fin.elim0 i))
    @Dense (ℂ × ProjectiveExtensionChartLocus L.g₂ L.g₃)
      (TopologicalSpace.induced embedding M.zariskiTopology)
      (Set.range (fun z : ℂ => (z, e ((extensionPeriodGraph L.lattice η).mkQ (z, 0)))))) :
    Nonempty (WeierstrassEllipticZeta.PhilipponApplication.Model S) := by
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
  have hE : (extensionEmbeddedGroup L.g₂ L.g₃ hadd hneg).dimension = 2 := by
    change (Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4)
      ((projectiveSpace ℂ 4).vanishingIdeal
        ((fun p : Projectivization ℂ (Fin 5 → ℂ) => fun _ : Fin 1 => p) ''
          extensionEmbeddedCarrier L.g₂ L.g₃))).totalDegree = 2
    rw [hcarrier, hExtensionHilbert]
    have hp : (C (3 : ℚ) * (X (0 : Fin 1) ^ 2)).totalDegree = 2 := by
      rw [totalDegree_mul_of_isDomain (by norm_num) (by simp), totalDegree_C, zero_add,
        totalDegree_X_pow]
    rw [totalDegree_add_eq_left_of_totalDegree_lt (by simp [hp]), hp]
  exact ⟨{
    factor := applicationFactor L.g₂ L.g₃ hadd hneg
    factor_dimension := applicationFactor_dimension L.g₂ L.g₃ hadd hneg hE
    variableEquiv := extensionProductVariableEquiv
    homogeneous := applicationGroup_homogeneous L.g₂ L.g₃ hadd hneg
    curve := applicationCurve L.g₂ L.g₃ hadd hneg L.lattice η e
    curve_injective := applicationCurve_injective L.g₂ L.g₃ hadd hneg L.lattice η e
    curve_dense := applicationCurve_dense L.g₂ L.g₃ hadd hneg L.lattice η e hCurveDense
    A := applicationAnalyticSubgroup L.g₂ L.g₃ hadd hneg L.lattice η e S hS he
    parameter := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)
    analytic_dimension := applicationAnalyticSubgroup_dimension L.g₂ L.g₃ hadd hneg L.lattice η e S hS he
    analytic_carrier := applicationAnalyticSubgroup_carrier L.g₂ L.g₃ hadd hneg L.lattice η e S hS he
    pullback := applicationAnalyticSubgroup_pullback L.g₂ L.g₃ hadd hneg L.lattice η e S hS he
    zero_locus := applicationCurve_zero_locus L.g₂ L.g₃ hadd hneg L.lattice η e S he
  }⟩



#print axioms solution
