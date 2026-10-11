-- Prove2me | solution 1 for PhilipponMultiplicity.addendum_strengthened_vanishing
-- status  : ACCEPTED   (disprove)
-- author  : @tomasz
-- created : 2026-10-10T13:59:41.711968+00:00
-- url     : https://prove2.me/submissions/47f50117-2eaa-4a18-a780-3ae26dcb545d

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Hilbert
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Data.ZMod.Basic

section
-- Implementation: Solutions.PhilipponProjectiveGeometry

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

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

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

end WeierstrassEllipticZeta
end
end

section
-- Implementation: Solutions.PhilipponHomogeneousOperations

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

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
-- Implementation: Solutions.PhilipponProjectivePointSeparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MvPolynomial
namespace PhilipponMultiplicity.MultiProjectiveSpace

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

end WeierstrassEllipticZeta.PhilipponApplication.Model
end
end

section
-- Implementation: Solutions.PhilipponPointHilbert

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
-- Implementation: Solutions.PhilipponProjectiveContact

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
end

section
-- Implementation: Solutions.PhilipponAnalyticContainment

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
-- Implementation: Solutions.PhilipponProjectiveNullstellensatz

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
-- Implementation: Solutions.PhilipponStandardMonomials

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
-- Implementation: Solutions.PhilipponMonomialCells

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
-- Implementation: Solutions.PhilipponMonomialPartition

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
-- Implementation: Solutions.PhilipponProductDegree

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

end PhilipponMultiplicity.ProductDegree

namespace PhilipponMultiplicity
open SectionThree

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions.PhilipponBinomialPolynomial

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
-- Implementation: Solutions.PhilipponHilbertFoundations

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

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
-- Implementation: Solutions.PhilipponProjectiveHilbertExistence

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

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions.PhilipponProductHilbert

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

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open SectionThree

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions.PhilipponColonHilbert

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

theorem homogeneous_colon (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I.colon {P}) := by
  intro Q hQ d
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hQ ⊢
  have h := hI (P * Q) (by simpa [mul_comm] using hQ) (D + d)
  rw [component_mul_homogeneous M hP Q d, mul_comm] at h
  exact h

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
-- Implementation: Solutions.PhilipponPrimeFiltration

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
-- Implementation: Solutions.PhilipponFiltrationPolynomial

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
-- Implementation: Solutions.PhilipponFiniteDifference

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

end PhilipponMultiplicity.FiniteDifference

end
end

section
-- Implementation: Solutions.PhilipponHilbertDimension

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
-- Implementation: Solutions.PhilipponRelevantHilbert

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
-- Implementation: Solutions.PhilipponIrrelevantHilbert

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
-- Implementation: Solutions.PhilipponPrimeDimension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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
-- Implementation: Solutions.PhilipponMinimalPrimeHomogeneous

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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
-- Implementation: Solutions.PhilipponComponentFormula

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

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity
open SectionThree

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions.PhilipponGroupPrimeComponents

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

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

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions.PhilipponGroupEquidimensional

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]

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

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions.PhilipponHilbertNontrivial

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertPolynomial_zero_iff_trivial (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    hilbertPolynomial K M.factorCount M.ambientDimension I = 0 ↔ ¬ IsNontrivialIdeal M I := by
  classical
  change _ ↔ ¬ ¬ irrelevantIdeal K M.factorCount M.ambientDimension ≤ I.radical
  rw [not_not]
  constructor
  · intro hz
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun q hq => ?_
    by_contra hn
    exact relevant_prime_hilbertPolynomial_ne_zero M q hq.1.1
      (minimalPrime_homogeneous M I q hI hq) hn
      (hilbertPolynomial_zero_of_le M I q hI hq.1.2 hz)
  · intro htriv
    obtain ⟨n, J, P, D, hfirst, hlast, hhom, hstep⟩ := homogeneous_prime_filtration M I hI
    have hmono : Monotone J := Fin.monotone_iff_le_succ.mpr fun j => by
      rw [(hstep j).2.2.1]
      exact le_sup_left
    rw [← hfirst, hilbertPolynomial_filtration_sum M n J P D hhom
      (fun j => ⟨(hstep j).1, (hstep j).2.2.1⟩) hlast]
    apply Finset.sum_eq_zero
    intro j _
    have hIQ : I ≤ (J j.castSucc).colon {P j} :=
      (hfirst.symm.le.trans (hmono (Fin.zero_le _))).trans Ideal.le_colon
    have hprime := (hstep j).2.2.2
    have hirr : irrelevantIdeal K M.factorCount M.ambientDimension ≤
        (J j.castSucc).colon {P j} := htriv.trans (hprime.radical_le_iff.mpr hIQ)
    rw [irrelevant_prime_hilbertPolynomial_zero M _ hprime (fun h => h hirr), map_zero]

end PhilipponMultiplicity.Hilbert

end
end

section
-- Implementation: Solutions.PhilipponTopComponent

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem exists_relevant_minimalPrime_dimension_eq (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hNontrivial : IsNontrivialIdeal M I) :
    ∃ q ∈ I.minimalPrimes, IsRelevant K M.factorCount M.ambientDimension q ∧
      idealDimension M q = idealDimension M I := by
  classical
  have hne : hilbertPolynomial K M.factorCount M.ambientDimension I ≠ 0 :=
    fun h => (hilbertPolynomial_zero_iff_trivial M I hI).mp h hNontrivial
  have htop : homogeneousComponent (idealDimension M I)
      (hilbertPolynomial K M.factorCount M.ambientDimension I) ≠ 0 := by
    obtain ⟨e, he, hed⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr hne) Finsupp.degree
    change idealDimension M I = e.degree at hed
    intro hz
    have hc := congrArg (coeff e) hz
    rw [coeff_homogeneousComponent, if_pos hed.symm, coeff_zero] at hc
    exact (mem_support_iff.mp he) hc
  obtain ⟨n, J, P, D, hfirst, hlast, hhom, hstep⟩ := homogeneous_prime_filtration M I hI
  let Q (j : Fin n) := (J j.castSucc).colon {P j}
  have hQprime (j : Fin n) : (Q j).IsPrime := (hstep j).2.2.2
  have hQhom (j : Fin n) : IsMultihomogeneousIdeal M (Q j) :=
    homogeneous_colon M _ (hhom j.castSucc) _ _ (hstep j).1
  have hmono : Monotone J := Fin.monotone_iff_le_succ.mpr fun j => by
    rw [(hstep j).2.2.1]
    exact le_sup_left
  have hIQ (j : Fin n) : I ≤ Q j := by
    rw [← hfirst]
    exact (hmono (Fin.zero_le _)).trans Ideal.le_colon
  have hpoly := hilbertPolynomial_filtration_sum M n J P D hhom
    (fun j => ⟨(hstep j).1, (hstep j).2.2.1⟩) hlast
  rw [hfirst] at hpoly
  have hex : ∃ j : Fin n, homogeneousComponent (idealDimension M I)
      (hilbertPolynomial K M.factorCount M.ambientDimension (Q j)) ≠ 0 := by
    by_contra! hz
    apply htop
    rw [hpoly, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    change homogeneousComponent (idealDimension M I)
      (FiniteDifference.shift (fun i => (D j i : ℚ))
        (hilbertPolynomial K M.factorCount M.ambientDimension (Q j))) = 0
    rw [ComponentDegree.shift_component_of_le _ _ _
      (idealDimension_antitone M I (Q j) hI (hQhom j) (hIQ j))]
    exact hz j
  obtain ⟨j, hj⟩ := hex
  have hrel : IsRelevant K M.factorCount M.ambientDimension (Q j) := by
    by_contra hn
    apply hj
    rw [irrelevant_prime_hilbertPolynomial_zero M (Q j) (hQprime j) hn, map_zero]
  have hdim : idealDimension M (Q j) = idealDimension M I := by
    apply le_antisymm (idealDimension_antitone M I (Q j) hI (hQhom j) (hIQ j))
    by_contra hn
    exact hj (homogeneousComponent_eq_zero _ _ (lt_of_not_ge hn))
  exact ⟨Q j, top_dimensional_prime_is_minimal M I (Q j) hI (hQprime j)
    (hQhom j) (hIQ j) hrel hdim, hrel, hdim⟩

end PhilipponMultiplicity.Hilbert

end
end

section
-- Implementation: Solutions.PhilipponFiniteEmbeddedGroups

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
namespace MultiProjectiveSpace
universe u
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)

theorem zariski_t1 : @T1Space M.Point M.zariskiTopology := by
  letI := M.zariskiTopology
  constructor
  intro x
  have heq : M.zeroLocus (M.vanishingIdeal {x}) = {x} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      apply M.point_eq_of_homogeneous_implication
      intro P D hP hx
      exact hy P (Ideal.subset_span ⟨⟨D,hP⟩, by simpa using hx⟩)
    · intro hy
      have hyx := Set.mem_singleton_iff.mp hy
      subst y
      exact fun P hP => M.eval_eq_zero_of_mem_vanishingIdeal hP (Set.mem_singleton x)
  rw [← heq]
  exact M.isClosed_zeroLocus_vanishingIdeal {x}

theorem isRegularAlong_of_finite {X : Type u} [Finite X]
    (Q : MultiProjectiveSpace K) (e : X → M.Point) (he : Function.Injective e)
    (f : X → Q.Point) : M.IsRegularAlong Q e f := by
  classical
  letI := M.zariskiTopology
  letI : T1Space M.Point := M.zariski_t1
  intro x b
  let U := (e '' ({x}ᶜ : Set X))ᶜ
  refine ⟨U, (Set.toFinite _).isClosed.isOpen_compl, ?_, 0,
    fun j => C ((f x b).rep j), fun j => M.isHomogeneous_C _, ?_⟩
  · rintro ⟨y,hy,hxy⟩
    exact hy (Set.mem_singleton_iff.mpr (he hxy))
  · intro y hy
    have hyx : y = x := by
      by_contra hn
      exact hy ⟨y,hn,rfl⟩
    subst y
    simpa only [eval,eval_C] using
      (show ∃ h : (f x b).rep ≠ 0, Projectivization.mk K (f x b).rep h = f x b
        from ⟨(f x b).rep_nonzero,(f x b).mk_rep⟩)

theorem vanishingIdeal_range_eq_iInf {B : Type*} (p : B → M.Point) :
    M.vanishingIdeal (Set.range p) = ⨅ b, M.vanishingIdeal {p b} := by
  apply le_antisymm
  · exact le_iInf (fun b => M.vanishingIdeal_antitone
      (Set.singleton_subset_iff.mpr (Set.mem_range_self b)))
  · let J := ⨅ b, M.vanishingIdeal {p b}
    have hJ : IsMultihomogeneousIdeal M J := by
      intro P hP D
      exact Ideal.mem_iInf.mpr (fun b => vanishingIdeal_multihomogeneous K M _
        P (Ideal.mem_iInf.mp hP b) D)
    change J ≤ _
    rw [M.homogeneousIdeal_eq_span J hJ]
    apply Ideal.span_le.mpr
    rintro P ⟨hP,D,hD⟩
    apply Ideal.subset_span
    refine ⟨⟨D,hD⟩,?_⟩
    rintro _ ⟨b,rfl⟩
    exact M.eval_eq_zero_of_mem_vanishingIdeal (Ideal.mem_iInf.mp hP b) (Set.mem_singleton _)

theorem finite_range_dimension_zero {B : Type*} [Finite B] [Nonempty B]
    (p : B → M.Point) :
    SectionThree.idealDimension M (M.vanishingIdeal (Set.range p)) = 0 := by
  classical
  letI := Fintype.ofFinite B
  let I := M.vanishingIdeal (Set.range p)
  have hI : IsMultihomogeneousIdeal M I := vanishingIdeal_multihomogeneous K M _
  have hnontriv : SectionThree.IsNontrivialIdeal M I := by
    apply M.relevant_of_zeroLocus_nonempty I.radical
    obtain ⟨b⟩ := ‹Nonempty B›
    refine ⟨p b,?_⟩
    rintro P ⟨n,hn⟩
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal hn (Set.mem_range_self b)
    exact eq_zero_of_pow_eq_zero (by simpa only [eval,map_pow] using hz)
  obtain ⟨q,hq,_,hdim⟩ := Hilbert.exists_relevant_minimalPrime_dimension_eq M I hI hnontriv
  have hle : (Finset.univ : Finset B).inf (fun b => M.vanishingIdeal {p b}) ≤ q := by
    simpa only [Finset.inf_univ_eq_iInf, ← M.vanishingIdeal_range_eq_iInf p] using hq.le
  obtain ⟨b,_,hb⟩ := hq.isPrime.inf_le'.mp hle
  have hdimle := Hilbert.idealDimension_antitone M _ q
    (vanishingIdeal_multihomogeneous K M _) (Hilbert.minimalPrime_homogeneous M I q hI hq) hb
  simp only [SectionThree.idealDimension, M.hilbertPolynomial_singleton, totalDegree_one] at hdimle
  rw [← hdim]
  exact Nat.eq_zero_of_le_zero hdimle

end MultiProjectiveSpace

namespace FiniteEmbedded
variable {K : Type*} [Field K] {B : Type*} [AddCommGroup B] [Finite B]
  {n : ℕ} (p : B → Projectivization K (Fin (n+1) → K)) (hp : Function.Injective p)

def group : EmbeddedCommutativeGroup K := by
  let e := Equiv.ofInjective p hp
  letI : AddCommGroup (Set.range p) := e.symm.addCommGroup
  letI : Finite (Set.range p) := Finite.of_equiv B e
  letI : TopologicalSpace (projectiveSpace K n).Point := (projectiveSpace K n).zariskiTopology
  letI : T1Space (projectiveSpace K n).Point := (projectiveSpace K n).zariski_t1
  let f : Projectivization K (Fin (n+1) → K) → (projectiveSpace K n).Point := fun x _ => x
  letI : TopologicalSpace (Projectivization K (Fin (n+1) → K)) :=
    TopologicalSpace.induced f (projectiveSpace K n).zariskiTopology
  letI : T1Space (Projectivization K (Fin (n+1) → K)) :=
    @t1Space_of_injective_of_continuous _ (projectiveSpace K n).Point _
      (projectiveSpace K n).zariskiTopology f
      (fun x y h => congrFun h (0 : Fin 1))
      (@continuous_induced_dom _ _ f (projectiveSpace K n).zariskiTopology)
      (projectiveSpace K n).zariski_t1
  refine {
    ambientDimension := n
    carrier := Set.range p
    group := inferInstance
    locallyClosed := (Set.finite_range p).isClosed.isLocallyClosed
    addition_regular := ?_
    negation_regular := ?_ }
  · apply (projectiveSquare K n).isRegularAlong_of_finite
    intro x y h
    apply Prod.ext
    · exact Subtype.ext (by simpa [projectiveSquare] using congrFun h (0 : Fin 2))
    · exact Subtype.ext (by simpa [projectiveSquare] using congrFun h (1 : Fin 2))
  · apply (projectiveSpace K n).isRegularAlong_of_finite
    intro x y h
    exact Subtype.ext (congrFun h (0 : Fin 1))

def equiv : (group p hp).Point ≃+ B := (Equiv.ofInjective p hp).symm.addEquiv

theorem dimension_zero : (group p hp).dimension = 0 := by
  change SectionThree.idealDimension (projectiveSpace K n)
    ((projectiveSpace K n).vanishingIdeal ((fun x => fun _ => x) '' Set.range p)) = 0
  rw [← Set.range_comp]
  exact (projectiveSpace K n).finite_range_dimension_zero _

end FiniteEmbedded
end PhilipponMultiplicity
end
end

section
-- Implementation: Solutions.PhilipponAdditiveGroup

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

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions.PhilipponFiniteBoundaryExamples

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SourceBoundary

variable (m : ℕ) [NeZero m]

def cyclicPoint (b : ZMod m) : Projectivization ℂ (Fin 2 → ℂ) :=
  additivePoint ℂ (b.val : ℂ)

theorem cyclicPoint_injective : Function.Injective (cyclicPoint m) := by
  intro a b h
  have h' : (a.val : ℂ) = (b.val : ℂ) := by
    have hh : (additiveCoordinateEquiv ℂ).symm (a.val : ℂ) =
        (additiveCoordinateEquiv ℂ).symm (b.val : ℂ) := Subtype.ext h
    exact (additiveCoordinateEquiv ℂ).symm.injective hh
  exact ZMod.val_injective m (Nat.cast_injective h')

def cyclicFactor : EmbeddedCommutativeGroup ℂ :=
  FiniteEmbedded.group (cyclicPoint m) (cyclicPoint_injective m)

def cyclicGroup : EmbeddedGroupProduct ℂ := singleGroupProduct (cyclicFactor m)

def cyclicEquiv : (cyclicGroup m).Point ≃+ ZMod m where
  toFun x := FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m) (x (0 : Fin 1))
  invFun b := fun _ => (FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m)).symm b
  left_inv x := by
    funext i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m)).symm_apply_apply _
  right_inv b := (FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m)).apply_symm_apply _
  map_add' x y := (FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m)).map_add _ _

@[simp] theorem cyclic_embedding (b : ZMod m) :
    (cyclicGroup m).embedding ((cyclicEquiv m).symm b) (0 : Fin 1) = cyclicPoint m b := rfl

theorem trivial_carrier (G : EmbeddedGroupProduct ℂ) :
    (AnalyticSubgroup.trivial G).carrier = {0} := by
  change (AddSubgroup.closure (Set.range (fun _ : (AnalyticSubgroup.trivial G).domain =>
    (0 : G.Point))) : Set G.Point) = _
  haveI : Nonempty (AnalyticSubgroup.trivial G).domain :=
    ⟨⟨0,(AnalyticSubgroup.trivial G).zero_mem⟩⟩
  simp [AddSubgroup.closure_singleton_zero]

theorem trivial_order_top (G : EmbeddedGroupProduct ℂ) (P : G.CoordinateRing) (g : G.Point)
    (h : G.ambient.eval P (G.embedding g) = 0) :
    vanishingOrder (AnalyticSubgroup.trivial G) P g = ⊤ := by
  have heq : (AnalyticSubgroup.trivial G).pullback P g = 0 := by
    funext z
    exact h
  simp [vanishingOrder,heq]

def coordinatePolynomial : (cyclicGroup m).CoordinateRing := X ⟨(0 : Fin 1),1⟩

theorem coordinatePolynomial_zero_iff (b : ZMod m) :
    (cyclicGroup m).ambient.eval (coordinatePolynomial m)
      ((cyclicGroup m).embedding ((cyclicEquiv m).symm b)) = 0 ↔ b = 0 := by
  simp only [coordinatePolynomial, MultiProjectiveSpace.eval, MvPolynomial.eval_X,
    MultiProjectiveSpace.coordinate, cyclic_embedding]
  change (cyclicPoint m b).rep 1 = 0 ↔ b = 0
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ ![1,(b.val : ℂ)]
    (by intro h; have := congrFun h 0; simpa using this)
  change (additivePoint ℂ (b.val : ℂ)).rep 1 = 0 ↔ _
  unfold additivePoint
  rw [← hc]
  simp only [Pi.smul_apply,Units.smul_def,smul_eq_mul,Matrix.cons_val_one,Matrix.head_cons,
    mul_eq_zero, c.ne_zero,false_or,Nat.cast_eq_zero]
  change (b.val : ℂ) = 0 ↔ b = 0
  rw [Nat.cast_eq_zero]
  exact ZMod.val_eq_zero b

end PhilipponMultiplicity.SourceBoundary
end
end

section
-- Implementation: Solutions.PhilipponBinaryHilbert

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

theorem binary_degreePiece_finrank (K : Type*) [Field K] (n : ℕ) :
    Module.finrank K (degreePiece K 1 (fun _ => 1) (fun _ => n)) = n + 1 := by
  classical
  unfold degreePiece
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  let e := PhilipponBinaryHilbert_binaryMonomialEquiv n
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) _).finrank_eq]
  have h := (Finsupp.domLCongr e : (_ →₀ K) ≃ₗ[K] (Fin (n + 1) →₀ K)).finrank_eq
  exact h.trans (by simp)

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
end
end

section
-- Implementation: Solutions.PhilipponAdditiveDimension

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

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions.PhilipponDisconnectedSampledObstruction

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.DisconnectedSampled
open SourceBoundary

def G : EmbeddedGroupProduct ℂ :=
  ⟨2,by decide,![additiveEmbeddedGroup ℂ,cyclicFactor 2]⟩

abbrev e0 := additiveEmbeddedGroupEquiv ℂ
abbrev e1 := FiniteEmbedded.equiv (cyclicPoint 2) (cyclicPoint_injective 2)

def point (u : ℂ) (b : ZMod 2) : G.Point :=
  Fin.cons (e0.symm u) (Fin.cons (e1.symm b) (fun i => Fin.elim0 i))

@[simp] theorem point_zero : point 0 0 = 0 := by
  ext i
  change Fin 2 at i
  fin_cases i <;> simp [point]

theorem point_add (u v : ℂ) (b c : ZMod 2) :
    point u b + point v c = point (u+v) (b+c) := by
  ext i
  change Fin 2 at i
  fin_cases i <;> simp [point,map_add]

theorem point_injective : Function.Injective (fun z : ℂ × ZMod 2 => point z.1 z.2) := by
  rintro ⟨u,b⟩ ⟨v,c⟩ h
  have hu : e0.symm u = e0.symm v := congrFun h (0 : Fin 2)
  have hb : e1.symm b = e1.symm c := congrFun h (1 : Fin 2)
  exact Prod.ext (e0.symm.injective hu) (e1.symm.injective hb)

theorem point_surjective : Function.Surjective (fun z : ℂ × ZMod 2 => point z.1 z.2) := by
  intro x
  refine ⟨(e0 (x (0 : Fin 2)),e1 (x (1 : Fin 2))),?_⟩
  ext i
  change Fin 2 at i
  fin_cases i <;> simp [point]

theorem dimension : G.dimension = 1 := by
  change (∑ i : Fin 2, (G.factor i).dimension) = 1
  rw [Fin.sum_univ_two]
  change (additiveEmbeddedGroup ℂ).dimension + (cyclicFactor 2).dimension = 1
  have hd : (cyclicFactor 2).dimension = 0 := FiniteEmbedded.dimension_zero _ _
  rw [additiveEmbeddedGroup_dimension,hd]

def polynomial : G.CoordinateRing := X ⟨(0 : Fin 2),1⟩ * X ⟨(1 : Fin 2),1⟩

theorem polynomial_homogeneous :
    IsMultihomogeneousOfDegree G polynomial (fun _ => 1) := by
  change G.ambient.IsHomogeneous polynomial (fun _ => 1)
  unfold polynomial
  convert (G.ambient.isHomogeneous_X ⟨(0 : Fin 2),1⟩).mul G.ambient
    (G.ambient.isHomogeneous_X ⟨(1 : Fin 2),1⟩) using 1
  all_goals first | rfl | (funext i; fin_cases i <;> rfl)

theorem polynomial_ne_zero : polynomial ≠ 0 := mul_ne_zero (X_ne_zero _) (X_ne_zero _)

theorem polynomial_zero_iff (u : ℂ) (b : ZMod 2) :
    G.ambient.eval polynomial (G.embedding (point u b)) = 0 ↔ u = 0 ∨ b = 0 := by
  have hu : (additivePoint ℂ u).rep 1 = 0 ↔ u = 0 := by
    have h := (additiveCoordinateEquiv ℂ).apply_symm_apply u
    change (additivePoint ℂ u).rep 1 / (additivePoint ℂ u).rep 0 = u at h
    have hn := additivePoint_mem ℂ u
    change (additivePoint ℂ u).rep 0 ≠ 0 at hn
    calc
      (additivePoint ℂ u).rep 1 = 0 ↔
          (additivePoint ℂ u).rep 1 / (additivePoint ℂ u).rep 0 = 0 := by simp [hn]
      _ ↔ u = 0 := by rw [h]
  have hb : (cyclicPoint 2 b).rep 1 = 0 ↔ b = 0 := by
    simpa only [coordinatePolynomial,MultiProjectiveSpace.eval,MvPolynomial.eval_X,
      MultiProjectiveSpace.coordinate,cyclic_embedding] using coordinatePolynomial_zero_iff 2 b
  simp only [polynomial,MultiProjectiveSpace.eval,map_mul,eval_X,MultiProjectiveSpace.coordinate]
  change (additivePoint ℂ u).rep 1 * (cyclicPoint 2 b).rep 1 = 0 ↔ _
  rw [mul_eq_zero,hu,hb]

def sample (N : ℕ) : Finset G.Point := by
  classical
  exact insert (point 0 1) ((Finset.range (N+2)).image (fun k : ℕ => point (k : ℂ) 0))

theorem sample_mem_zero (N : ℕ) : (0 : G.Point) ∈ sample N := by
  classical
  have h : point 0 0 ∈ sample N := Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨0,by simp,by norm_num⟩)
  simpa only [point_zero] using h

theorem sample_mem_one (N : ℕ) : point 1 0 ∈ sample N := by
  classical
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨1,by simp,by norm_num⟩)

theorem sample_mem_other (N : ℕ) : point 0 1 ∈ sample N := by
  classical
  exact Finset.mem_insert_self _ _

theorem sample_card_lower (N : ℕ) : N+2 ≤ (sample N).card := by
  classical
  have hinj : Function.Injective (fun k : ℕ => point (k : ℂ) 0) := by
    intro k l h
    have he := congrArg Prod.fst (point_injective (a₁ := ((k : ℂ),0)) (a₂ := ((l : ℂ),0)) h)
    exact Nat.cast_injective he
  have h := Finset.card_le_card (show
      (Finset.range (N+2)).image (fun k : ℕ => point (k : ℂ) 0) ⊆ sample N from
    Finset.subset_insert _ _)
  rw [Finset.card_image_of_injective _ hinj,Finset.card_range] at h
  exact h

theorem sample_vanishes (N : ℕ) (x : G.Point) (hx : x ∈ sample N) :
    G.ambient.eval polynomial (G.embedding x) = 0 := by
  classical
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact (polynomial_zero_iff 0 1).mpr (Or.inl rfl)
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    exact (polynomial_zero_iff _ 0).mpr (Or.inr rfl)

theorem sample_contact (N T : ℕ) : ∀ x ∈ sumset (sample N) G.dimension,
    ((G.dimension*T+1 : ℕ) : WithTop ℕ) ≤
      vanishingOrder (AnalyticSubgroup.trivial G) polynomial x := by
  classical
  intro x hx
  rw [dimension] at hx
  simp only [sumset,Finset.mem_image,Finset.mem_univ,true_and] at hx
  obtain ⟨f,rfl⟩ := hx
  rw [Fin.sum_univ_one]
  rw [trivial_order_top G polynomial _ (sample_vanishes N _ (f 0).property)]
  exact le_top

theorem subgroup_eq_zero (N : ℕ) (H : AlgebraicSubgroup G)
    (hvanish : ∀ g ∈ sample N, translate g H.carrier ⊆ zeroLocusOnGroup G polynomial) :
    H.carrier = {0} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨H.toAddSubgroup.zero_mem,?_⟩
  intro h hh
  obtain ⟨⟨u,b⟩,rfl⟩ := point_surjective h
  have hzero := hvanish 0 (sample_mem_zero N) ⟨point u b,hh,zero_add _⟩
  have hone := hvanish (point 1 0) (sample_mem_one N) ⟨point u b,hh,rfl⟩
  have hother := hvanish (point 0 1) (sample_mem_other N) ⟨point u b,hh,rfl⟩
  change G.ambient.eval polynomial (G.embedding (point u b)) = 0 at hzero
  change G.ambient.eval polynomial (G.embedding (point 1 0 + point u b)) = 0 at hone
  change G.ambient.eval polynomial (G.embedding (point 0 1 + point u b)) = 0 at hother
  rw [polynomial_zero_iff] at hzero
  rw [point_add,zero_add,polynomial_zero_iff] at hone
  have hb : b = 0 := by
    by_contra hb
    have hu := hzero.resolve_right hb
    have hu1 := hone.resolve_right hb
    simpa [hu] using hu1
  rw [point_add,hb,zero_add,add_zero,polynomial_zero_iff] at hother
  have hu : u = 0 := hother.resolve_right one_ne_zero
  simp [hu,hb]

theorem cosetCount_zero (N : ℕ) : cosetCount (sample N) ({0} : Set G.Point) = (sample N).card := by
  classical
  unfold cosetCount
  apply Finset.card_image_of_injective
  intro g h he
  have : ({g} : Set G.Point) = {h} := by simpa [translate] using he
  exact Set.singleton_injective this

theorem no_sampled_bound (B : ℝ) :
    ∃ N : ℕ, ¬ ∃ H : AlgebraicSubgroup G,
      (∀ g ∈ sample N, translate g H.carrier ⊆ zeroLocusOnGroup G polynomial) ∧
      ((Nat.choose (1 + analyticCodimension (AnalyticSubgroup.trivial G) H.carrier)
        (analyticCodimension (AnalyticSubgroup.trivial G) H.carrier) : ℝ) *
          (cosetCount (sample N) H.carrier : ℝ) *
          hilbertDegreeForm G H.carrier (fun _ => 1) ≤ B) := by
  obtain ⟨N,hN⟩ := exists_nat_gt B
  refine ⟨N,?_⟩
  rintro ⟨H,hvan,hbound⟩
  have hs : analyticCodimension (AnalyticSubgroup.trivial G) H.carrier = 0 :=
    analyticCodimension_eq_zero_of_carrier_subset _ H (by
      rw [trivial_carrier]
      exact Set.singleton_subset_iff.mpr H.toAddSubgroup.zero_mem)
  rw [hs] at hbound
  rw [subgroup_eq_zero N H hvan,cosetCount_zero,hilbertDegreeForm_singleton] at hbound
  norm_num only [Nat.choose_zero_right,Nat.cast_one,one_mul,mul_one] at hbound
  have hcard : (N : ℝ) ≤ ((sample N).card : ℝ) := by
    exact_mod_cast (show N ≤ (sample N).card from (by omega : N ≤ N+2).trans (sample_card_lower N))
  exact (not_le_of_gt hN) (hcard.trans hbound)

theorem no_addendum : ¬ (∀
    (K : Type) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K),
    ∃ c : EmbeddedCommutativeGroup K → ℕ,
      (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K), 0 < G.dimension →
      ∀ (A : AnalyticSubgroup G)
        (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        ∃ H : AlgebraicSubgroup G,
          H.IsConnected ∧
          HasIncompleteDefinition G H.carrier (fun i => c (G.factor i) * D i) ∧
          (∀ g ∈ sample, translate g H.carrier ⊆ zeroLocusOnGroup G P) ∧
          ((Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
              (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
            hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * D i))) := by
  intro claim
  obtain ⟨c,hc,hclaim⟩ := claim ℂ (Or.inl ⟨RingEquiv.refl ℂ,isometry_id⟩)
  obtain ⟨N,hN⟩ := no_sampled_bound (hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * 1))
  obtain ⟨H,hconn,hdef,hvan,hbound⟩ := hclaim G (by rw [dimension]; decide)
    (AnalyticSubgroup.trivial G) (sample N) (sample_mem_zero N) 1 (fun _ => 1)
    polynomial polynomial_ne_zero polynomial_homogeneous (sample_contact N 1)
  exact hN ⟨H,hvan,hbound⟩

end PhilipponMultiplicity.DisconnectedSampled

end
end

open PhilipponMultiplicity
open scoped BigOperators Topology

theorem solution : ¬ (∀
    (K : Type) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K),
    ∃ c : EmbeddedCommutativeGroup K → ℕ,
      (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K), 0 < G.dimension →
      ∀ (A : AnalyticSubgroup G)
        (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        ∃ H : AlgebraicSubgroup G,
          H.IsConnected ∧
          HasIncompleteDefinition G H.carrier (fun i => c (G.factor i) * D i) ∧
          (∀ g ∈ sample, PhilipponMultiplicity.translate g H.carrier ⊆ zeroLocusOnGroup G P) ∧
          ((Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
              (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
            hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * D i))) := by
  exact DisconnectedSampled.no_addendum
