-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_preserves_homogeneous_ideal_false
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-04T02:37:23.633139+00:00
-- url     : https://prove2.me/submissions/54c70735-19d9-4906-832d-6d1f51f6af77

import Mathlib
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport

set_option autoImplicit false

open PhilipponMultiplicity
noncomputable section

namespace ClosureDisproof

/-- The point [1:1] in ℙ¹ ℂ. -/
def pt : Projectivization ℂ (Fin (1+1) → ℂ) :=
  Projectivization.mk ℂ (fun _ => 1) (by
    intro h
    have h0 := congrFun h 0
    simpa using h0)

/-- Its representative has equal coordinates. -/
lemma rep_eq : pt.rep 0 = pt.rep 1 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := ℂ) (V := Fin (1+1) → ℂ)
    (fun _ => (1 : ℂ)) (by
      intro h
      have h0 := congrFun h 0
      simpa using h0)
  have h0 : pt.rep 0 = (a : ℂ) := by
    have h := congrFun ha 0
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, mul_one] at h
    exact h.symm
  have h1 : pt.rep 1 = (a : ℂ) := by
    have h := congrFun ha 1
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, mul_one] at h
    exact h.symm
  rw [h0, h1]

/-- The common coordinate is nonzero. -/
lemma rep0_ne : pt.rep 0 ≠ 0 := by
  intro h
  have hne := Projectivization.rep_nonzero pt
  apply hne
  funext i
  fin_cases i
  · exact h
  · show pt.rep 1 = 0
    exact rep_eq.symm.trans h

instance : Subsingleton ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) :=
  ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    simp only [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy; rfl⟩

instance : AddCommGroup ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) :=
  { add := fun _ _ => ⟨pt, rfl⟩
    add_assoc := fun _ _ _ => Subsingleton.elim _ _
    zero := ⟨pt, rfl⟩
    zero_add := fun _ => Subsingleton.elim _ _
    add_zero := fun _ => Subsingleton.elim _ _
    nsmul := fun _ _ => ⟨pt, rfl⟩
    neg := fun _ => ⟨pt, rfl⟩
    zsmul := fun _ _ => ⟨pt, rfl⟩
    neg_add_cancel := fun _ => Subsingleton.elim _ _
    add_comm := fun _ _ => Subsingleton.elim _ _ }

-- Named for explicit use in E
instance ptAddCommGroup : AddCommGroup ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) := inferInstance

/-- `X v * C c` is homogeneous of the expected multidegree. -/
lemma isHomogeneous_X_mul_C (M : MultiProjectiveSpace ℂ) (v : M.Variable) (c : ℂ) :
    M.IsHomogeneous (MvPolynomial.X v * MvPolynomial.C c)
      (fun k => if k = v.1 then 1 else 0) := by
  intro m hm k
  have hsub : (MvPolynomial.X v * MvPolynomial.C c).support ⊆ {Finsupp.single v 1} := by
    rw [mul_comm, MvPolynomial.C_mul_X_eq_monomial]
    exact MvPolynomial.support_monomial_subset
  have hm' : m = Finsupp.single v 1 := Finset.mem_singleton.mp (hsub hm)
  rw [hm']
  by_cases hk : k = v.1
  · subst hk
    show ∑ _ : Fin (M.ambientDimension v.1 + 1), (Finsupp.single v 1) ⟨v.1, _⟩ =
      (if v.1 = v.1 then (1 : ℕ) else 0)
    rw [if_pos rfl]
    have hterm : ∀ j : Fin (M.ambientDimension v.1 + 1),
        (Finsupp.single v 1) ⟨v.1, j⟩ = (if v.2 = j then 1 else 0) := by
      intro j
      rw [Finsupp.single_apply]
      show (if (⟨v.1, v.2⟩ : M.Variable) = ⟨v.1, j⟩ then (1 : ℕ) else 0) =
        (if v.2 = j then 1 else 0)
      by_cases h : v.2 = j
      · have h1 : (⟨v.1, v.2⟩ : M.Variable) = ⟨v.1, j⟩ := by rw [h]
        rw [if_pos h1, if_pos h]
      · have h1 : (⟨v.1, v.2⟩ : M.Variable) ≠ ⟨v.1, j⟩ := by
          intro hcon
          apply h
          injection hcon
        rw [if_neg h1, if_neg h]
    simp_rw [hterm]
    simp
  · show ∑ _ : Fin (M.ambientDimension k + 1), (Finsupp.single v 1) ⟨k, _⟩ =
      (if k = v.1 then (1 : ℕ) else 0)
    rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro j _
    rw [Finsupp.single_apply, if_neg]
    intro hcon
    exact hk (Sigma.mk.inj hcon).1.symm

/-- `X v` is homogeneous of the expected multidegree. -/
lemma isHomogeneous_X (M : MultiProjectiveSpace ℂ) (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun k => if k = v.1 then 1 else 0) := by
  have h := isHomogeneous_X_mul_C M v 1
  simpa using h

/-- The constant polynomial `C 1` is homogeneous of multidegree 0. -/
lemma isHomogeneous_C_one (M : MultiProjectiveSpace ℂ) :
    M.IsHomogeneous (MvPolynomial.C 1) (fun _ => 0) := by
  intro m hm i
  have hsub : (MvPolynomial.C (1 : ℂ)).support ⊆ {(0 : M.Variable →₀ ℕ)} := by
    rw [MvPolynomial.C_apply]
    exact MvPolynomial.support_monomial_subset
  have hm0 : m = 0 := Finset.mem_singleton.mp (hsub hm)
  rw [hm0]
  simp

/-- A difference of homogeneous polynomials of the same multidegree is homogeneous. -/
lemma isHomogeneous_sub (M : MultiProjectiveSpace ℂ) (P Q : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  intro m hm k
  have hsub : (P - Q).support ⊆ P.support ∪ Q.support :=
    MvPolynomial.support_sub M.Variable P Q
  rcases Finset.mem_union.mp (hsub hm) with h | h
  · exact hP m h k
  · exact hQ m h k

/-- For `y ≠ x`, a homogeneous polynomial vanishing at `x` but not at `y`. -/
lemma exists_separator (M : MultiProjectiveSpace ℂ) (x y : M.Point) (hyx : y ≠ x) :
    ∃ P : M.CoordinateRing,
      (∃ D : M.FactorIndex → ℕ, M.IsHomogeneous P D) ∧
      M.eval P x = 0 ∧ M.eval P y ≠ 0 := by
  have hne : ∃ i : M.FactorIndex, y i ≠ x i := by
    by_contra hcon
    push_neg at hcon
    exact hyx (funext hcon)
  obtain ⟨i, hi⟩ := hne
  have hrep : ¬ ∃ c : ℂˣ, c • (x i).rep = (y i).rep := by
    rintro ⟨c, hc⟩
    apply hi
    have e1 : Projectivization.mk ℂ (y i).rep (Projectivization.rep_nonzero (y i)) = y i :=
      Projectivization.mk_rep (y i)
    have e2 : Projectivization.mk ℂ (x i).rep (Projectivization.rep_nonzero (x i)) = x i :=
      Projectivization.mk_rep (x i)
    have hmk : Projectivization.mk ℂ (y i).rep (Projectivization.rep_nonzero (y i)) =
        Projectivization.mk ℂ (x i).rep (Projectivization.rep_nonzero (x i)) :=
      (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr ⟨c, hc⟩
    rw [← e1, ← e2]
    exact hmk
  obtain ⟨b, hb⟩ := Function.ne_iff.mp (Projectivization.rep_nonzero (x i))
  rw [Pi.zero_apply] at hb
  have key : ∃ a : Fin (M.ambientDimension i + 1),
      (y i).rep a * (x i).rep b - (y i).rep b * (x i).rep a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    by_cases hub : (y i).rep b = 0
    · have hu0 : (y i).rep = 0 := by
        funext a
        have h := hcon a
        rw [hub, zero_mul, sub_zero] at h
        exact (mul_eq_zero.mp h).resolve_right hb
      exact Projectivization.rep_nonzero (y i) hu0
    · apply hrep
      obtain ⟨c, hc⟩ := isUnit_iff_ne_zero.mpr (div_ne_zero hub hb)
      refine ⟨c, ?_⟩
      funext a
      have h2 : (y i).rep a * (x i).rep b = (y i).rep b * (x i).rep a :=
        sub_eq_zero.mp (hcon a)
      simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul]
      rw [hc]
      field_simp
      linear_combination h2.symm
  obtain ⟨a, ha⟩ := key
  refine ⟨MvPolynomial.X (⟨i, a⟩ : M.Variable) * MvPolynomial.C ((x i).rep b) -
    MvPolynomial.X (⟨i, b⟩ : M.Variable) * MvPolynomial.C ((x i).rep a),
    ⟨fun k => if k = i then 1 else 0, ?_⟩, ?_, ?_⟩
  · exact isHomogeneous_sub M _ _ _ (isHomogeneous_X_mul_C M _ _) (isHomogeneous_X_mul_C M _ _)
  · simp only [MultiProjectiveSpace.eval, map_sub, map_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    have c1 : M.coordinate x (⟨i, a⟩ : M.Variable) = (x i).rep a := rfl
    have c2 : M.coordinate x (⟨i, b⟩ : M.Variable) = (x i).rep b := rfl
    rw [c1, c2]
    ring
  · simp only [MultiProjectiveSpace.eval, map_sub, map_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    have c1 : M.coordinate y (⟨i, a⟩ : M.Variable) = (y i).rep a := rfl
    have c2 : M.coordinate y (⟨i, b⟩ : M.Variable) = (y i).rep b := rfl
    rw [c1, c2]
    exact ha

/-- Every singleton is closed in the Zariski topology of a multiprojective space over ℂ. -/
lemma isClosed_singleton_zariski (M : MultiProjectiveSpace ℂ) (x : M.Point) :
    @IsClosed _ M.zariskiTopology {x} := by
  letI := M.zariskiTopology
  rw [← isOpen_compl_iff]
  have hcompl : ({x} : Set M.Point)ᶜ =
      ⋃ P ∈ {P : M.CoordinateRing | (∃ D, M.IsHomogeneous P D) ∧ M.eval P x = 0},
      {y : M.Point | M.eval P y ≠ 0} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_setOf_eq]
    constructor
    · intro hyx
      obtain ⟨P, hhom, hvan, hne⟩ := exists_separator M x y hyx
      exact ⟨P, ⟨hhom, hvan⟩, hne⟩
    · rintro ⟨P, ⟨hhom, hvan⟩, hne⟩ rfl
      exact hne hvan
  rw [hcompl]
  apply isOpen_biUnion
  intro P hP
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  obtain ⟨⟨D, hD⟩, -⟩ := hP
  exact ⟨P, D, hD, rfl⟩

/-- The addition map of the singleton group is regular (constant `pt` charts). -/
lemma add_regular_aux :
    (projectiveSquare ℂ 1).IsRegularAlong (projectiveSpace ℂ 1)
      (fun xy : ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) × ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) =>
        fun i : Fin 2 => if i.val = 0 then xy.1.val else xy.2.val)
      (fun xy : ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) × ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) =>
        fun _ : Fin 1 => (xy.1 + xy.2).val) := by
  intro xy b
  letI := (projectiveSquare ℂ 1).zariskiTopology
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0,
    fun _ => MvPolynomial.C (1 : ℂ), fun _ => isHomogeneous_C_one _, ?_⟩
  · intro y _
    -- eval (C 1) _ = 1
    have heval1 : ∀ (x : (projectiveSquare ℂ 1).Point),
        (projectiveSquare ℂ 1).eval (MvPolynomial.C (1 : ℂ)) x = 1 := by
      intro x
      simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_C]
    refine ⟨?_, ?_⟩
    · rw [Function.ne_iff]
      refine ⟨0, ?_⟩
      show (projectiveSquare ℂ 1).eval (MvPolynomial.C (1:ℂ)) _ ≠ (0:ℂ)
      simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_C]
      exact one_ne_zero
    · have hfun : (fun j : Fin ((projectiveSpace ℂ 1).ambientDimension b + 1) =>
          (projectiveSquare ℂ 1).eval ((fun _ => MvPolynomial.C (1 : ℂ)) j)
            ((fun xy : ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) × ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) =>
              fun i : Fin 2 => if i.val = 0 then xy.1.val else xy.2.val) y)) =
          (fun _ => (1 : ℂ)) := by
        funext j
        simp only []
        exact heval1 _
      have hfb : ((fun xy : ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) × ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) =>
          fun _ : Fin 1 => (xy.1 + xy.2).val) y) b = pt := by
        show (y.1 + y.2).val = pt
        exact congrArg Subtype.val (Subsingleton.elim (y.1 + y.2) ⟨pt, rfl⟩)
      -- Goal: mk ℂ F h = f y b, where F j = 1 and f y b = pt
      rw [hfb]
      -- pt is definitionally mk ℂ (fun _ => 1) _
      show Projectivization.mk ℂ _ _ = Projectivization.mk ℂ (fun _ => (1:ℂ)) _
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      refine ⟨1, ?_⟩
      rw [one_smul]
      exact hfun.symm

/-- The negation map of the singleton group is regular (constant `pt` charts). -/
lemma neg_regular_aux :
    (projectiveSpace ℂ 1).IsRegularAlong (projectiveSpace ℂ 1)
      (fun x : ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) => fun _ : Fin 1 => x.val)
      (fun x : ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) => fun _ : Fin 1 => (-x).val) := by
  intro x b
  letI := (projectiveSpace ℂ 1).zariskiTopology
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0,
    fun _ => MvPolynomial.C (1 : ℂ), fun _ => isHomogeneous_C_one _, ?_⟩
  · intro y _
    have heval1 : ∀ (x : (projectiveSpace ℂ 1).Point),
        (projectiveSpace ℂ 1).eval (MvPolynomial.C (1 : ℂ)) x = 1 := by
      intro x
      simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_C]
    refine ⟨?_, ?_⟩
    · rw [Function.ne_iff]
      refine ⟨0, ?_⟩
      show (projectiveSpace ℂ 1).eval (MvPolynomial.C (1:ℂ)) _ ≠ (0:ℂ)
      simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_C]
      exact one_ne_zero
    · have hfun : (fun j : Fin ((projectiveSpace ℂ 1).ambientDimension b + 1) =>
          (projectiveSpace ℂ 1).eval ((fun _ => MvPolynomial.C (1 : ℂ)) j)
            ((fun x : ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) => fun _ : Fin 1 => x.val) y)) =
          (fun _ => (1 : ℂ)) := by
        funext j
        simp only []
        exact heval1 _
      have hfb : ((fun x : ↥({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) => fun _ : Fin 1 => (-x).val) y) b = pt := by
        have hneg : ((-y).val : Projectivization ℂ (Fin (1+1) → ℂ)) = pt :=
          congrArg Subtype.val (Subsingleton.elim (-y) ⟨pt, rfl⟩)
        show ((-y).val : Projectivization ℂ (Fin (1+1) → ℂ)) = pt
        exact hneg
      rw [hfb]
      show Projectivization.mk ℂ _ _ = Projectivization.mk ℂ (fun _ => (1:ℂ)) _
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      refine ⟨1, ?_⟩
      rw [one_smul]
      exact hfun.symm

/-- The degenerate embedded group: `ℙ¹` with the singleton carrier `{[1:1]}`. -/
def E : EmbeddedCommutativeGroup ℂ where
  ambientDimension := 1
  carrier := {pt}
  group := ptAddCommGroup
  locallyClosed := by
    -- pt as a multiprojective point
    let ptM : (projectiveSpace ℂ 1).Point := fun _ => pt
    have hclosedM := isClosed_singleton_zariski (projectiveSpace ℂ 1) ptM
    -- The embedding f x = fun _ => x
    have hpre : (fun (x : Projectivization ℂ (Fin (1+1) → ℂ)) (_ : Fin 1) => x) ⁻¹' {ptM} =
        ({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        have := congrFun hx 0
        simpa using this
      · intro hx
        rw [hx]
        rfl
    have hclosed : @IsClosed (Projectivization ℂ (Fin (1+1) → ℂ))
        (TopologicalSpace.induced (fun (x : Projectivization ℂ (Fin (1+1) → ℂ)) (_ : Fin 1) => x)
          (projectiveSpace ℂ 1).zariskiTopology) ({pt} : Set (Projectivization ℂ (Fin (1+1) → ℂ))) := by
      letI : TopologicalSpace (Fin 1 → Projectivization ℂ (Fin (1+1) → ℂ)) :=
        (projectiveSpace ℂ 1).zariskiTopology
      letI : TopologicalSpace (Projectivization ℂ (Fin (1+1) → ℂ)) :=
        TopologicalSpace.induced (fun (x : Projectivization ℂ (Fin (1+1) → ℂ)) (_ : Fin 1) => x)
          (projectiveSpace ℂ 1).zariskiTopology
      exact isClosed_induced_iff.mpr ⟨{ptM}, hclosedM, hpre⟩
    -- Convert to IsLocallyClosed (the function forms are defeq)
    show @IsLocallyClosed _ (TopologicalSpace.induced (fun (x : Projectivization ℂ (Fin (1+1) → ℂ)) (_ : Fin 1) => x) (projectiveSpace ℂ 1).zariskiTopology) _
    letI : TopologicalSpace (Projectivization ℂ (Fin (1+1) → ℂ)) :=
      TopologicalSpace.induced (fun (x : Projectivization ℂ (Fin (1+1) → ℂ)) (_ : Fin 1) => x)
        (projectiveSpace ℂ 1).zariskiTopology
    exact @IsClosed.isLocallyClosed _ _ _ hclosed
  addition_regular := add_regular_aux
  negation_regular := neg_regular_aux

/-! ## The product group, the diagonal hom, and the counterexample polynomial.

`G := singleGroupProduct E`: one factor, so `G.ambient` is (definitionally) `ℙ¹`,
`G.Point` is a subsingleton, and `groupProjectiveClosure G = {s0}`.
`τ` is the identity family. `P = X₀₀² - lam·X₀₀` with `lam = pt.rep 0 ≠ 0`.
`ψ : G.CoordinateRing →+* ℂ[t]` sends every variable to `t`. -/

/-- The degenerate product group: one factor `E`. -/
def G : EmbeddedGroupProduct ℂ := singleGroupProduct E

/-- The unique group point. -/
def g0 : G.Point := fun _ => ⟨pt, rfl⟩

instance : Subsingleton G.Point := by
  constructor
  intro x y
  funext i
  have h1 : (x i).val = pt :=
    Set.mem_singleton_iff.mp (show (x i).val ∈ ({pt} : Set _) from (x i).property)
  have h2 : (y i).val = pt :=
    Set.mem_singleton_iff.mp (show (y i).val ∈ ({pt} : Set _) from (y i).property)
  exact Subtype.ext (h1.trans h2.symm)

/-- The unique ambient point in the closure. -/
def s0 : G.ambient.Point := G.embedding g0

/-- The common representative coordinate. -/
def lam : ℂ := pt.rep 0

lemma lam_ne : lam ≠ 0 := rep0_ne

/-- Every representative coordinate of `pt` equals `lam`. -/
lemma rep_all (j : Fin (1+1)) : pt.rep j = lam := by
  have h2 : ∀ i : Fin 2, pt.rep i = lam := Fin.forall_fin_two.2 ⟨rfl, rep_eq.symm⟩
  exact h2 j

/-- The coordinate function at `s0` is constantly `lam`. -/
lemma coord_s0 (v : G.ambient.Variable) : G.ambient.coordinate s0 v = lam := by
  have hrep : (s0 v.1).rep = pt.rep := rfl
  have h2 : (s0 v.1).rep v.2 = pt.rep v.2 := congrFun hrep v.2
  show (s0 v.1).rep v.2 = lam
  rw [h2]
  exact rep_all v.2

/-- The projective closure is the singleton `{s0}`. -/
lemma closure_eq_s0 : groupProjectiveClosure G = {s0} := by
  have hrange : Set.range G.embedding = {s0} := by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact congrArg G.embedding (Subsingleton.elim x g0)
    · intro hy
      rw [hy]
      exact ⟨g0, rfl⟩
  show @closure _ G.ambient.zariskiTopology (Set.range G.embedding) = {s0}
  rw [hrange]
  exact @IsClosed.closure_eq _ G.ambient.zariskiTopology _
    (isClosed_singleton_zariski G.ambient s0)

/-- `τ` is the identity family of automorphisms. -/
def tau : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G) :=
  fun _ => Equiv.refl _

lemma tau_id (g : G.Point) (x : groupProjectiveClosure G) : (tau g x).val = x.val := rfl

/-- The identity family is regular along the closure. -/
lemma hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
    (fun x : groupProjectiveClosure G => x.val) (fun x => (tau g x).val) := by
  intro g x b
  refine ⟨Set.univ, @isOpen_univ _ G.ambient.zariskiTopology, Set.mem_univ _,
    fun k => if k = b then 1 else 0,
    fun j => MvPolynomial.X (⟨b, j⟩ : G.ambient.Variable),
    fun j => isHomogeneous_X G.ambient (⟨b, j⟩ : G.ambient.Variable), ?_⟩
  intro y _
  show ∃ h : (fun j => G.ambient.eval (MvPolynomial.X (⟨b, j⟩ : G.ambient.Variable)) y.val) ≠ 0,
      Projectivization.mk ℂ
        (fun j => G.ambient.eval (MvPolynomial.X (⟨b, j⟩ : G.ambient.Variable)) y.val) h
        = (tau g y).val b
  have heval : ∀ j : Fin (G.ambient.ambientDimension b + 1),
      G.ambient.eval (MvPolynomial.X (⟨b, j⟩ : G.ambient.Variable)) y.val
        = (y.val b).rep j := by
    intro j
    show MvPolynomial.eval (G.ambient.coordinate y.val)
      (MvPolynomial.X (⟨b, j⟩ : G.ambient.Variable)) = _
    rw [MvPolynomial.eval_X]
    rfl
  have hfun : (fun j => G.ambient.eval (MvPolynomial.X (⟨b, j⟩ : G.ambient.Variable)) y.val)
      = (y.val b).rep := funext heval
  rw [hfun]
  refine ⟨Projectivization.rep_nonzero (y.val b), ?_⟩
  show Projectivization.mk ℂ (y.val b).rep _ = y.val b
  exact Projectivization.mk_rep (y.val b)

/-- The distinguished variable `X₀₀`. -/
def v00 : G.ambient.Variable := ⟨⟨0, G.positive⟩, ⟨0, Nat.succ_pos _⟩⟩

/-- The counterexample polynomial `P = X₀₀² - lam·X₀₀`. -/
def P : G.CoordinateRing :=
  MvPolynomial.X v00 ^ 2 - MvPolynomial.C lam * MvPolynomial.X v00

/-- The diagonal ring hom `ψ : X_v ↦ t`. -/
def psi : G.CoordinateRing →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X)

/-- Evaluating at `s0` is evaluating at the constant `lam`. -/
lemma heval_unfold (Q : G.CoordinateRing) :
    G.ambient.eval Q s0 = MvPolynomial.eval (fun _ => lam) Q := by
  have hfun : G.ambient.coordinate s0 = fun _ => lam := funext coord_s0
  show MvPolynomial.eval (G.ambient.coordinate s0) Q = MvPolynomial.eval (fun _ => lam) Q
  rw [hfun]

/-- A monomial's worth of `c ^ e`'s collapses to `c ^ (∑ D)` under a multidegree hypothesis. -/
lemma prod_pow_eq {M : Type*} [CommMonoid M] (m : G.ambient.Variable →₀ ℕ)
    (D : G.FactorIndex → ℕ)
    (hdeg : ∀ i, ∑ j : Fin (G.ambient.ambientDimension i + 1), m ⟨i, j⟩ = D i)
    (c : M) : m.prod (fun _ e => c ^ e) = c ^ (∑ i, D i) := by
  have h1 : m.prod (fun _ e => c ^ e) = ∏ a ∈ m.support, c ^ (m a) := rfl
  rw [h1, Finset.prod_pow_eq_pow_sum]
  congr 1
  have e1 : (∑ a ∈ m.support, m a) = m.sum (fun _ e => e) := rfl
  have e2 : m.sum (fun _ e => e) = ∑ a : G.ambient.Variable, m a :=
    Finsupp.sum_fintype m (fun _ e => e) (fun _ => rfl)
  rw [e1, e2, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => hdeg i)

/-- `ψ` of a homogeneous polynomial: every monomial lands on the same power of `t`. -/
lemma psi_of_homogeneous (H : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hhom : G.ambient.IsHomogeneous H D) :
    psi H = Polynomial.C (∑ m ∈ H.support, H.coeff m) * Polynomial.X ^ (∑ i, D i) := by
  have hexpand : psi H
      = ∑ m ∈ H.support, psi (MvPolynomial.monomial m (H.coeff m)) := by
    conv_lhs => rw [MvPolynomial.as_sum H]
    rw [map_sum]
  rw [hexpand]
  have hterm : ∀ m ∈ H.support, psi (MvPolynomial.monomial m (H.coeff m))
      = Polynomial.C (H.coeff m) * Polynomial.X ^ (∑ i, D i) := by
    intro m hm
    have hdeg : ∀ i, ∑ j : Fin (G.ambient.ambientDimension i + 1), m ⟨i, j⟩ = D i :=
      fun i => hhom m hm i
    have e1 : psi (MvPolynomial.monomial m (H.coeff m))
        = Polynomial.C (H.coeff m)
          * m.prod (fun n e => (fun _ => Polynomial.X) n ^ e) := by
      have hpsi_eq : psi (MvPolynomial.monomial m (H.coeff m))
          = (MvPolynomial.monomial m (H.coeff m)).eval₂ Polynomial.C
            (fun _ => Polynomial.X) := rfl
      rw [hpsi_eq, MvPolynomial.eval₂_monomial]
    rw [e1]
    congr 1
    exact prod_pow_eq m D hdeg Polynomial.X
  calc ∑ m ∈ H.support, psi (MvPolynomial.monomial m (H.coeff m))
      = ∑ m ∈ H.support, (Polynomial.C (H.coeff m) * Polynomial.X ^ (∑ i, D i)) :=
        Finset.sum_congr rfl hterm
    _ = Polynomial.C (∑ m ∈ H.support, H.coeff m) * Polynomial.X ^ (∑ i, D i) := by
        rw [← Finset.sum_mul, ← map_sum]

/-- Evaluation of a homogeneous polynomial at `s0`. -/
lemma eval_of_homogeneous (H : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hhom : G.ambient.IsHomogeneous H D) :
    G.ambient.eval H s0 = (∑ m ∈ H.support, H.coeff m) * lam ^ (∑ i, D i) := by
  have hexpand : G.ambient.eval H s0
      = ∑ m ∈ H.support,
        MvPolynomial.eval (fun _ => lam) (MvPolynomial.monomial m (H.coeff m)) := by
    rw [heval_unfold]
    conv_lhs => rw [MvPolynomial.as_sum H]
    rw [map_sum]
  rw [hexpand]
  calc ∑ m ∈ H.support,
          MvPolynomial.eval (fun _ => lam) (MvPolynomial.monomial m (H.coeff m))
      = ∑ m ∈ H.support, ((H.coeff m) * lam ^ (∑ i, D i)) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hdeg : ∀ i, ∑ j : Fin (G.ambient.ambientDimension i + 1), m ⟨i, j⟩ = D i :=
          fun i => hhom m hm i
        rw [MvPolynomial.eval_monomial]
        congr 1
        have e1 : m.prod (fun n e => (fun _ => lam) n ^ e)
            = m.prod (fun _ e => lam ^ e) := rfl
        rw [e1]
        exact prod_pow_eq m D hdeg lam
    _ = (∑ m ∈ H.support, H.coeff m) * lam ^ (∑ i, D i) := by
        rw [← Finset.sum_mul]

/-- `ψ` kills every homogeneous generator vanishing at `s0`. -/
lemma psi_kills_gen (H : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hhom : G.ambient.IsHomogeneous H D)
    (hvan : G.ambient.eval H s0 = 0) : psi H = 0 := by
  have hpsi := psi_of_homogeneous H D hhom
  have hev := eval_of_homogeneous H D hhom
  rw [hev] at hvan
  have hlam : lam ^ (∑ i : G.FactorIndex, D i) ≠ 0 := pow_ne_zero _ lam_ne
  have hsum : ∑ m ∈ H.support, H.coeff m = 0 := by
    rcases mul_eq_zero.mp hvan with h | h
    · exact h
    · exact absurd h hlam
  rw [hpsi, hsum, Polynomial.C_0, zero_mul]

/-- The locus `V`: the whole (singleton) closure. -/
def V : Set (groupProjectiveClosure G) := Set.univ

/-- `s0` lies in the transported locus image. -/
lemma s0_mem_image : s0 ∈ Subtype.val '' (tau g0 '' V) := by
  have hmem : s0 ∈ groupProjectiveClosure G := by
    rw [closure_eq_s0]
    exact Set.mem_singleton s0
  exact ⟨tau g0 ⟨s0, hmem⟩, ⟨⟨s0, hmem⟩, Set.mem_univ _, rfl⟩, tau_id g0 ⟨s0, hmem⟩⟩

/-- `ψ P = t² - lam·t ≠ 0`. -/
lemma psiP_ne : psi P ≠ 0 := by
  have hpsi : psi P
      = (Polynomial.X : Polynomial ℂ) ^ 2 - Polynomial.C lam * Polynomial.X := by
    have hP : P = MvPolynomial.X v00 ^ 2 - MvPolynomial.C lam * MvPolynomial.X v00 := rfl
    have eX : psi (MvPolynomial.X v00) = Polynomial.X := by
      have h1 : psi (MvPolynomial.X v00)
          = (MvPolynomial.X v00).eval₂ Polynomial.C (fun _ => Polynomial.X) := rfl
      rw [h1, MvPolynomial.eval₂_X]
    have eC : psi (MvPolynomial.C lam) = Polynomial.C lam := by
      have h1 : psi (MvPolynomial.C lam)
          = (MvPolynomial.C lam).eval₂ Polynomial.C (fun _ => Polynomial.X) := rfl
      rw [h1, MvPolynomial.eval₂_C]
    rw [hP, map_sub, map_mul, map_pow, eX, eC]
  intro hcon
  rw [hpsi] at hcon
  have h2 := congrArg (fun p : Polynomial ℂ => Polynomial.coeff p 2) hcon
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X] at h2
  simp at h2

/-- `P` is NOT in the vanishing ideal of the transported locus. -/
lemma P_not_mem :
    P ∉ G.ambient.vanishingIdeal (Subtype.val '' (tau g0 '' V)) := by
  intro hmem
  have hle : G.ambient.vanishingIdeal (Subtype.val '' (tau g0 '' V))
      ≤ RingHom.ker psi := by
    apply Ideal.span_le.mpr
    intro H hH
    obtain ⟨D, hhom⟩ := hH.1
    apply RingHom.mem_ker.mpr
    apply psi_kills_gen H D hhom
    exact hH.2 s0 s0_mem_image
  have h0 : psi P = 0 := RingHom.mem_ker.mp (hle hmem)
  exact psiP_ne h0

/-- `P` evaluates to `0` at `s0`. -/
lemma evalP_s0 : G.ambient.eval P s0 = 0 := by
  rw [heval_unfold]
  show MvPolynomial.eval (fun _ => lam)
    (MvPolynomial.X v00 ^ 2 - MvPolynomial.C lam * MvPolynomial.X v00) = 0
  rw [map_sub, map_pow, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
  ring

end ClosureDisproof

open ClosureDisproof

/-- Disproof of `PhilipponMultiplicity.closure_action_preserves_homogeneous_ideal`:
the (←) direction is FALSE. With `G = singleGroupProduct E` (closure `{[1:1]}`),
`τ = id`, `V = univ`, `P = X₀₀² - lam·X₀₀`, `Q = 0`: the RHS holds but
`P ∉ vanishingIdeal`, so the biconditional fails.

Note: stated monomorphically at `K : Type` (not `Type*`): a universe-polymorphic
`¬ ∀ (K : Type*)` is unprovable in Lean (the counterexample field `ℂ : Type`
cannot inhabit a rigid `Type u_1`), while refuting the `Type`-instance already
refutes the universal claim. -/
theorem solution : ¬ ∀ (K : Type) [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (V : Set (groupProjectiveClosure G))
    (g : G.Point)
    (P : G.CoordinateRing),
    P ∈ G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)) ↔
      ∃ Q ∈ G.ambient.vanishingIdeal (Subtype.val '' V),
        ∀ x : groupProjectiveClosure G,
          G.ambient.eval P ((τ g x).val) = G.ambient.eval Q x.val := by
  intro h
  have hKc : IsPhilipponBaseField ℂ := by
    refine Or.inl ⟨RingEquiv.refl ℂ, ?_⟩
    intro x1 x2
    rfl
  have hiff := h ℂ hKc G tau hregular V g0 P
  have hRHS : ∃ Q ∈ G.ambient.vanishingIdeal (Subtype.val '' V),
      ∀ x : groupProjectiveClosure G,
        G.ambient.eval P ((tau g0 x).val) = G.ambient.eval Q x.val := by
    refine ⟨0, Ideal.zero_mem _, fun x => ?_⟩
    have hx : x.val = s0 := by
      have hmem : x.val ∈ ({s0} : Set G.ambient.Point) := by
        rw [← closure_eq_s0]
        exact x.property
      exact Set.mem_singleton_iff.mp hmem
    have htau : (tau g0 x).val = s0 := by
      rw [tau_id g0 x]
      exact hx
    rw [htau, evalP_s0]
    show (0 : ℂ) = MvPolynomial.eval (G.ambient.coordinate x.val) 0
    exact (map_zero _).symm
  exact P_not_mem (hiff.mpr hRHS)

/-- Dual-named alias for the pipeline-published negation node (playbook rule 6): the alias MUST carry a type ascription. -/
theorem PhilipponMultiplicity.closure_action_preserves_homogeneous_ideal_false :
¬ ∀ (K : Type) [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (V : Set (groupProjectiveClosure G))
    (g : G.Point)
    (P : G.CoordinateRing),
    P ∈ G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)) ↔
      ∃ Q ∈ G.ambient.vanishingIdeal (Subtype.val '' V),
        ∀ x : groupProjectiveClosure G,
          G.ambient.eval P ((τ g x).val) = G.ambient.eval Q x.val  :=
  solution
