-- Prove2me | solution 1 for PhilipponMultiplicity.addendum_strengthened_vanishing_common_shift
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-10T16:24:18.075364+00:00
-- url     : https://prove2.me/submissions/37ea9f20-5e8f-4d41-8f21-d52490078a47

import Theorems.Thm_PhilipponMultiplicity_proposition_4_3
import Theorems.Thm_PhilipponMultiplicity_proposition_4_4
import Theorems.Thm_PhilipponMultiplicity_translation_operator_foundations
import Definitions.Def_PhilipponMultiplicity_ErratumCorrections
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_IteratedJets
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.KrullDimension
import Theorems.Thm_PhilipponMultiplicity_exists_uniformly_bounded_translation_atlas
import Theorems.Thm_PhilipponMultiplicity_section_five_bounded_translated_chain
import Theorems.Thm_PhilipponMultiplicity_section_five_construction
import Theorems.Thm_PhilipponMultiplicity_section_five_contact_coset_multiplicity
import Theorems.Thm_PhilipponMultiplicity_section_five_counting_inequality
import Theorems.Thm_PhilipponMultiplicity_section_five_differential_containment
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
-- Implementation: Solutions/PhilipponAnalyticUnitOrder.lean

set_option autoImplicit false
open scoped Topology BigOperators ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity
variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

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

private theorem bd_PhilipponProjectiveContact_coordinate_ratio {K : Type*} [Field K] {ι : Type*}
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
    exact (bd_PhilipponProjectiveContact_coordinate_ratio heq (j i) (hj i)).1
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
      exact (bd_PhilipponProjectiveContact_coordinate_ratio heq (j v.1) (hjz v.1)).2 v.2
    rw [hcoords, M.eval_block_scale P D hP]
  have hgP : AnalyticAt K (fun z => MvPolynomial.eval (g z) P) x := by
    change AnalyticAt K (fun z => aeval (g z) P) x
    exact AnalyticAt.aeval_mvPolynomial hg P
  exact (jetOrder_congr hfg).trans (jetOrder_mul_unit hgP hu hux)

private theorem bd_PhilipponProjectiveContact_completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact bd_PhilipponProjectiveContact_completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact bd_PhilipponProjectiveContact_completeSpace_of_isometric_ringEquiv e he

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

end MultiProjectiveSpace

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

end WeierstrassEllipticZeta
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

end PhilipponMultiplicity
end
end

section
-- Implementation: Solutions/PhilipponMonomialPartition.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MonomialCells

variable (p : ℕ) (N : Fin p → ℕ)

abbrev Var := Sigma fun i : Fin p => Fin (N i + 1)

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

end PhilipponMultiplicity.MonomialCells

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
    rw [MonomialCells.weight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

end PhilipponMultiplicity

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

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity

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

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

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

end PhilipponMultiplicity.Hilbert

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

end PhilipponMultiplicity.OperatorSupport
end
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

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Implementation: Solutions/PhilipponSectionFiveChain.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem zero_mem_sumset {X : Type*} [AddCommGroup X]
    (S : Finset X) (h0 : 0 ∈ S) (n : ℕ) : 0 ∈ sumset S n := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(fun _ => ⟨0,h0⟩),Finset.mem_univ _,by simp⟩

theorem sumset_mono {X : Type*} [AddCommGroup X]
    (S : Finset X) (h0 : 0 ∈ S) : Monotone (sumset S) := by
  classical
  apply monotone_nat_of_le_succ
  intro n x hx
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨Fin.cons ⟨0,h0⟩ f,Finset.mem_univ _,?_⟩
  simp [Fin.sum_univ_succ]

variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
open OperatorSupport

theorem groupIdeal_le_pointKernel (x : G.Point) :
    G.vanishingIdeal Set.univ ≤ RingHom.ker
      (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
  exact fun P hP => G.ambient.eval_eq_zero_of_mem_vanishingIdeal hP
    (Set.mem_image_of_mem G.embedding (Set.mem_univ x))

theorem SectionFiveInput.chain_homogeneous [CompleteSpace K]
    (C : SectionFiveInput G A) (n : ℕ) :
    IsMultihomogeneousIdeal G.ambient (C.idealChain n) := by
  cases n with
  | zero => exact vanishingIdeal_multihomogeneous K _ _
  | succ n =>
    cases n with
    | zero =>
      exact Hilbert.homogeneous_sup_span G.ambient _ (vanishingIdeal_multihomogeneous K _ _)
        C.polynomial C.degrees C.polynomial_homogeneous
    | succ n =>
      simp only [idealChain]
      unfold EmbeddedGroupProduct.vanishingIdeal MultiProjectiveSpace.vanishingIdeal
      rw [← Ideal.span_union]
      apply homogeneous_span
      rintro Q (hQ | ⟨g,hg,a,k,hk,dirs,rfl⟩)
      · exact hQ.1
      · exact ⟨_,polynomialOperator_homogeneous _ _ _ _ _ C.polynomial_homogeneous⟩

theorem polynomialOperator_zero_on_chart_iff [CompleteSpace K]
    {g : G.Point} (chart : TranslationChart A g) (x : G.Point) (hx : x ∈ chart.domain)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.eval (polynomialOperator chart 0 Fin.elim0 P) (G.embedding x) = 0 ↔
      G.ambient.eval P (G.embedding (g+x)) = 0 := by
  rw [polynomialOperator_eval]
  simp only [iteratedFDeriv_zero_apply]
  apply G.ambient.eval_eq_zero_iff_of_lift _ _ _ P D hP
  obtain ⟨hz,hrep⟩ := (chart.represents x hx).self_of_nhds
  intro i
  simpa only [A.map_zero,add_zero,add_comm x g] using hrep i

theorem SectionFiveInput.chain_zero_antitone [CompleteSpace K]
    (C : SectionFiveInput G A) :
    Antitone (fun n => idealZeroLocusOnGroup G (C.idealChain n)) := by
  apply antitone_nat_of_succ_le
  intro n
  cases n with
  | zero => exact fun x _ => groupIdeal_le_pointKernel x
  | succ n =>
    cases n with
    | zero =>
      intro x hx
      change C.idealChain 1 ≤ RingHom.ker _
      apply sup_le (groupIdeal_le_pointKernel x)
      rw [Ideal.span_singleton_le_iff_mem]
      obtain ⟨a,ha⟩ := (C.atlas 0).covers x
      have hop := hx (polynomialOperator ((C.atlas 0).chart a) 0 Fin.elim0 C.polynomial)
        (Ideal.mem_sup_right (Ideal.subset_span
          ⟨0,zero_mem_sumset C.samplingSet C.zero_mem 1,a,0,Nat.zero_le _,Fin.elim0,rfl⟩))
      have hP := (polynomialOperator_zero_on_chart_iff _ x ha _ _
        C.polynomial_homogeneous).mp hop
      change G.ambient.eval C.polynomial (G.embedding x) = 0
      simpa only [zero_add] using hP
    | succ n =>
      intro x hx
      have hle : C.idealChain (n+2) ≤ C.idealChain (n+3) := by
        apply sup_le_sup_left
        apply Ideal.span_mono
        rintro Q ⟨g,hg,a,k,hk,dirs,rfl⟩
        exact ⟨g,sumset_mono C.samplingSet C.zero_mem (by omega) hg,a,k,
          hk.trans (Nat.mul_le_mul_right _ (by omega)),dirs,rfl⟩
      exact fun P hP => hx P (hle hP)

end PhilipponMultiplicity
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

theorem EmbeddedGroupProduct.translation_regular (G : EmbeddedGroupProduct K) (a : G.Point) :
    G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (x + a)) := by
  intro x b
  have hp := (G.ambient.projection_regular b).comp_domain G.embedding
  have ht := ((G.factor b).translation_regular (a b)).comp_domain (fun y : G.Point => y b)
  obtain ⟨U, hU, hx, D, P, hP, hl⟩ := (hp.comp ht) x (0 : Fin 1)
  exact ⟨U, hU, hx, D, P, hP, hl⟩

end PhilipponMultiplicity
end
end

section
-- Implementation: Solutions/PhilipponTranslatedJetGerms.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

end PhilipponMultiplicity.JetSupport

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem projective_ratios_eq {ι : Type*} (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk K v hv = Projectivization.mk K w hw) (i j : ι) :
    v i / v j = w i / w j := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp h
  have he (k : ι) : v k = (a : K) * w k := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm
  rw [he i,he j,mul_div_mul_left _ _ a.ne_zero]

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Implementation: Solutions/PhilipponFiniteBasicCover.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity

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

end PhilipponMultiplicity

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



end PhilipponMultiplicity.TranslationSupport
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
-- Implementation: Solutions/PhilipponSectionFiveContact.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport

theorem add_mem_sumset_succ {X : Type*} [AddCommGroup X]
    (S : Finset X) {g h : X} (hg : g ∈ S) {n : ℕ} (hh : h ∈ sumset S n) :
    g+h ∈ sumset S (n+1) := by
  classical
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hh
  apply Finset.mem_image.mpr
  exact ⟨Fin.cons ⟨g,hg⟩ f,Finset.mem_univ _,by simp [Fin.sum_univ_succ]⟩

variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem SectionFiveInput.polynomial_contact_of_chain_zero
    (hK : IsPhilipponBaseField K) (C : SectionFiveInput G A)
    (n : ℕ) (x : G.Point) (hx : x ∈ idealZeroLocusOnGroup G (C.idealChain (n+2)))
    (g : G.Point) (hg : g ∈ sumset C.samplingSet (n+1)) :
    (((n+1)*C.contactParameter : ℕ) : WithTop ℕ) < vanishingOrder A C.polynomial (g+x) := by
  letI : CompleteSpace K := hK.completeSpace
  obtain ⟨a,ha⟩ := (C.atlas g).covers x
  rw [projective_lift_contact_invariance K hK G A (g+x) C.polynomial C.degrees
    C.polynomial_homogeneous
    (fun z v => evaluateCoefficientPolynomial A (((C.atlas g).chart a).coordinates v) x z)
    (chart_evaluation_analytic ((C.atlas g).chart a) x)
    (by simpa only [add_comm x g] using ((C.atlas g).chart a).represents x ha)]
  apply (natCast_lt_jetOrder_iff _ 0 _).mpr
  intro k hk
  apply (derivative_eq_zero_iff_basis _).mpr
  intro directions
  rw [← polynomialOperator_eval]
  exact hx _ (Ideal.mem_sup_right (Ideal.subset_span ⟨g,hg,a,k,hk,directions,rfl⟩))

theorem differentialIdeal_le_point_iff [CompleteSpace K] (hK : IsPhilipponBaseField K)
    (g x : G.Point) (T : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (atlas : TranslationAtlas A g) :
    (∀ P ∈ differentialIdeal A g T I, G.ambient.eval P (G.embedding x) = 0) ↔
      I ≤ jetIdeal A (g+x) T := by
  letI : CompleteSpace K := hK.completeSpace
  rw [← ((translation_operator_foundations K hK).2.2.2.1
    G A g atlas T I I hI hI).1]
  rw [proposition_4_4 K hK G A g x T I hI atlas]
  exact forall₂_congr (fun P _ => (mem_jetIdeal_iff A (g+x) T P).symm)

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions/PhilipponSectionFiveDifferentialContainment.lean
namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]
 {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
theorem SectionFiveConstruction.differential_containment
    (hK : IsPhilipponBaseField K) (C : SectionFiveConstruction G A)
    (g : G.Point) (hg : g ∈ C.samplingSet) :
    differentialIdeal A g C.contactParameter C.chosenIdeal ≤ C.componentPrime := section_five_differential_containment K hK G A C g hg
end PhilipponMultiplicity
end

section
-- Implementation: Solutions/PhilipponSectionFiveTransporter.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem normalizedPullback_zero (g x : G.Point) (b : CoordinateChart G)
    (P : G.CoordinateRing) :
    normalizedPullback A g b P x 0 = chartValue G b P (g+x) := by
  obtain ⟨hz,hrep⟩ := (A.lift_represents (g+x)).self_of_nhds
  unfold normalizedPullback chartValue
  apply congrArg (fun f : G.ambient.Variable → K => MvPolynomial.eval f P)
  funext v
  obtain ⟨hv,he⟩ := hrep v.1
  have he' : Projectivization.mk K (fun j => A.lift (g+x) 0 ⟨v.1,j⟩) hv =
      G.embedding (g+x) v.1 := by simpa only [A.map_zero,add_zero] using he
  exact projective_ratios_eq _ _ hv (G.embedding (g+x) v.1).rep_nonzero
    (he'.trans (G.embedding (g+x) v.1).mk_rep.symm) v.2 (b v.1)

theorem differentialIdeal_zero_eq_translatedIdeal (g : G.Point)
    (I : Ideal G.CoordinateRing) : differentialIdeal A g 0 I = translatedIdeal G g I := by
  have heq : differentialSections A g 0 I = translationSections G g I := by
    ext f
    constructor
    · rintro ⟨P,hP,hD,b,j,rfl⟩
      rcases j with ⟨k,hk,directions⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      refine ⟨P,hP,hD,b,?_⟩
      congr 1
      funext x
      simp only [normalizedJet,iteratedFDeriv_zero_apply]
      exact normalizedPullback_zero g x b P
    · rintro ⟨P,hP,hD,b,rfl⟩
      refine ⟨P,hP,hD,b,⟨0,le_rfl,Fin.elim0⟩,?_⟩
      congr 1
      funext x
      simp only [normalizedJet,iteratedFDeriv_zero_apply]
      exact (normalizedPullback_zero g x b P).symm
  exact congrArg (locallyGeneratedIdeal G) heq

theorem translatedIdeal_homogeneous (g : G.Point) (I : Ideal G.CoordinateRing) :
    IsMultihomogeneousIdeal G.ambient (translatedIdeal G g I) := by
  apply homogeneous_span
  exact fun _ h => h.1

theorem translatedIdeal_iSup_homogeneous (I : Ideal G.CoordinateRing) (V : Set G.Point) :
    IsMultihomogeneousIdeal G.ambient
      (⨆ v : V, translatedIdeal G v.val I) := by
  unfold translatedIdeal locallyGeneratedIdeal
  rw [← Ideal.span_iUnion]
  apply homogeneous_span
  intro P hP
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hP
  exact hv.1

theorem translatedIdeal_iSup_contact_locus (hK : IsPhilipponBaseField K)
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (V : Set G.Point) (T : ℕ) (atlas : ∀ g : G.Point, TranslationAtlas A g)
    (g : G.Point) :
    g ∈ idealZeroLocusOnGroup G
      (differentialIdeal A 0 T (⨆ v : V, translatedIdeal G v.val I)) ↔
    translate g V ⊆ idealZeroLocusOnGroup G (differentialIdeal A 0 T I) := by
  have hcompose (v : G.Point) :
      differentialIdeal A 0 T (translatedIdeal G v I) = differentialIdeal A v T I := by
    rw [← differentialIdeal_zero_eq_translatedIdeal (A := A)]
    have hlocal (z : G.Point) (k : ℕ) (J : Ideal G.CoordinateRing)
        (hJ : IsMultihomogeneousIdeal G.ambient J) :
        retainedPolynomialOperatorIdeal (atlas z) k J = differentialIdeal A z k J :=
      ((translation_operator_foundations K hK).2.2.2.1 G A z (atlas z) k J J hJ hJ).1
    have hinner : IsMultihomogeneousIdeal G.ambient (differentialIdeal A v 0 I) := by
      rw [differentialIdeal_zero_eq_translatedIdeal]
      exact translatedIdeal_homogeneous v I
    have hcomposition :
        retainedPolynomialOperatorIdeal (atlas 0) T
            (retainedPolynomialOperatorIdeal (atlas v) 0 I) =
          differentialIdeal A v T I := by
      have hc := (proposition_4_3 K hK G A 0 v T 0 I hI (atlas 0) (atlas 0)).2
        (atlas v) (atlas (0 + v))
      rw [hlocal (0 + v) (T + 0) I hI] at hc
      simpa only [zero_add, Nat.add_zero] using hc
    calc
      differentialIdeal A 0 T (differentialIdeal A v 0 I) =
          retainedPolynomialOperatorIdeal (atlas 0) T (differentialIdeal A v 0 I) :=
        (hlocal 0 T _ hinner).symm
      _ = retainedPolynomialOperatorIdeal (atlas 0) T
          (retainedPolynomialOperatorIdeal (atlas v) 0 I) := by rw [hlocal v 0 I hI]
      _ = differentialIdeal A v T I := hcomposition
  change (∀ P ∈ differentialIdeal A 0 T (⨆ v : V, translatedIdeal G v.val I),
    G.ambient.eval P (G.embedding g) = 0) ↔ _
  rw [differentialIdeal_le_point_iff hK 0 g T _ (translatedIdeal_iSup_homogeneous I V)
    (atlas 0),zero_add,iSup_le_iff]
  constructor
  · intro h
    rintro _ ⟨v,hv,rfl⟩
    have hz := (differentialIdeal_le_point_iff hK 0 g T (translatedIdeal G v I)
      (translatedIdeal_homogeneous v I) (atlas 0)).mpr (by simpa only [zero_add] using h ⟨v,hv⟩)
    rw [hcompose] at hz
    have hj := (differentialIdeal_le_point_iff hK v g T I hI (atlas v)).mp hz
    apply (differentialIdeal_le_point_iff hK 0 (g+v) T I hI (atlas 0)).mpr
    simpa only [zero_add,add_comm v g] using hj
  · intro h v
    have hz := h (Set.mem_image_of_mem (fun x : G.Point => g+x) v.property)
    have hj := (differentialIdeal_le_point_iff hK 0 (g+v.val) T I hI (atlas 0)).mp hz
    suffices translatedIdeal G v.val I ≤ jetIdeal A (0+g) T by simpa only [zero_add] using this
    apply (differentialIdeal_le_point_iff hK 0 g T (translatedIdeal G v.val I)
      (translatedIdeal_homogeneous v.val I) (atlas 0)).mp
    rw [hcompose]
    apply (differentialIdeal_le_point_iff hK v.val g T I hI (atlas v.val)).mpr
    simpa only [zero_add,add_comm g v.val] using hj

theorem SectionFiveConstruction.sample_mem_translated_contact_locus
    (hK : IsPhilipponBaseField K) (C : SectionFiveConstruction G A)
    (g : G.Point) (hg : g ∈ C.samplingSet) :
    g ∈ idealZeroLocusOnGroup G
      (differentialIdeal A 0 C.contactParameter
        (⨆ v : C.component, translatedIdeal G v.val C.chosenIdeal)) := by
  rw [translatedIdeal_iSup_contact_locus hK C.chosenIdeal
    (C.toSectionFiveInput.chain_homogeneous C.index) C.component C.contactParameter C.atlas g]
  rintro _ ⟨v,hv,rfl⟩
  have hz : ∀ P ∈ differentialIdeal A g C.contactParameter C.chosenIdeal,
      G.ambient.eval P (G.embedding v) = 0 :=
    fun P hP => hv P (C.differential_containment hK g hg hP)
  have hj := (differentialIdeal_le_point_iff hK g v C.contactParameter C.chosenIdeal
    (C.toSectionFiveInput.chain_homogeneous C.index) (C.atlas g)).mp hz
  apply (differentialIdeal_le_point_iff hK 0 (g+v) C.contactParameter C.chosenIdeal
    (C.toSectionFiveInput.chain_homogeneous C.index) (C.atlas 0)).mpr
  simpa only [zero_add] using hj

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions/PhilipponContactCosetMultiplicity.lean
namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]
 {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
theorem SectionFiveConstruction.contact_coset_multiplicity
    (hK : IsPhilipponBaseField K) (C : SectionFiveConstruction G A)
    (H : AlgebraicSubgroup G) (hH : H.carrier = C.stabilizer.identityComponent)
    (hconn : H.IsConnected) (g : G.Point)
    (hg : g ∈ idealZeroLocusOnGroup G (differentialIdeal A 0 C.contactParameter
      (⨆ v : C.component, translatedIdeal G v.val C.chosenIdeal))) :
    IncompletelyDefinesWithMultiplicityAtLeast G
      (⨆ v : C.component, translatedIdeal G v.val C.chosenIdeal) (translate g H.carrier)
      (Nat.choose (C.contactParameter + analyticCodimension A H.carrier)
        (analyticCodimension A H.carrier)) := section_five_contact_coset_multiplicity K hK G A C H hH hconn g hg
end PhilipponMultiplicity
end

section
-- Implementation: Solutions/PhilipponSectionFiveBoundedReplacement.lean
namespace PhilipponMultiplicity
theorem section_five_bounded_replacement_established
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveInput G A) (n : ℕ) (V : Set G.Point) (hV : V.Nonempty) :
    ∃ J' : Ideal G.CoordinateRing,
      G.vanishingIdeal Set.univ ≤ J' ∧ IsMultihomogeneousIdeal G.ambient J' ∧
      Hilbert.HasEquationsOfDegreeAtMost K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) J' C.scaledDegrees ∧
      retainOnGroup G J' = retainOnGroup G (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) ∧
      (∀ x : GroupHomogeneousRepresentative G,
        J'.map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) =
        (⨆ v : V, translatedIdeal G v.val (C.idealChain n)).map
          (algebraMap G.CoordinateRing
            (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal))) ∧
      (∀ W : Set G.Point, ∀ ell : ℕ,
        IncompletelyDefinesWithMultiplicityAtLeast G J' W ell ↔
        IncompletelyDefinesWithMultiplicityAtLeast G
          (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) W ell) := section_five_bounded_translated_chain K G A C n V hV
end PhilipponMultiplicity
end

section
-- Implementation: Solutions/PhilipponTheorem21Complete.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem SectionFiveConstruction.exists_obstructing_subgroup
    (hK : IsPhilipponBaseField K) (C : SectionFiveConstruction G A) :
    ∃ H : AlgebraicSubgroup G,
      H.IsConnected ∧ HasIncompleteDefinition G H.carrier C.scaledDegrees ∧
      (∃ g : G.Point, H.carrier ⊆ translate g (zeroLocusOnGroup G C.polynomial)) ∧
      ((Nat.choose (C.contactParameter + analyticCodimension A H.carrier)
        (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount C.samplingSet H.carrier : ℝ) * hilbertDegreeForm G H.carrier C.degrees ≤
            hilbertDegreeForm G Set.univ C.scaledDegrees) := by
  letI : CompleteSpace K := hK.completeSpace
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨H,hH,hconn,_⟩ := (section_five_construction K hK G A).2.1 C.stabilizer
  obtain ⟨J,hG,hJ,hbounded,_,_,htransfer⟩ :=
    section_five_bounded_replacement_established K G A C.toSectionFiveInput C.index
      C.component C.meets_group
  have hzero := C.sample_mem_translated_contact_locus hK 0 C.zero_mem
  have hm := C.contact_coset_multiplicity hK H hH hconn 0 hzero
  have htz : translate (0 : G.Point) H.carrier = H.carrier := by simp [translate]
  rw [htz] at hm
  have hdef : HasIncompleteDefinition G H.carrier C.scaledDegrees :=
    ⟨J,hJ,hbounded,((htransfer H.carrier _).mpr hm).1⟩
  have hbound := section_five_counting_inequality K hK G A C
  dsimp only at hbound
  rw [← hH] at hbound
  refine ⟨H,hconn,hdef,?_,hbound⟩
  obtain ⟨v,hv⟩ := C.meets_group
  refine ⟨-v,fun x hx => ?_⟩
  have hxH : x ∈ C.stabilizer.carrier := by
    rw [hH] at hx
    exact connectedComponentIn_subset C.stabilizer.carrier 0 hx
  have hstable : translate x C.component = C.component := hxH
  have hxv : x+v ∈ C.component := hstable ▸ (show x+v ∈ translate x C.component from ⟨v,hv,rfl⟩)
  have hn : x+v ∈ idealZeroLocusOnGroup G (C.toSectionFiveInput.idealChain (C.index+1)) :=
    fun P hP => hxv P (C.minimal_at_next.le hP)
  have h1 := C.toSectionFiveInput.chain_zero_antitone (show 1 ≤ C.index+1 by omega) hn
  have hP : x+v ∈ zeroLocusOnGroup G C.polynomial :=
    h1 C.polynomial (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton C.polynomial)))
  exact ⟨x+v,hP,by abel⟩

end PhilipponMultiplicity

end
end

section
-- Reused implementation: PhilipponConnectedPointedComponent (ambient primality)

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport

variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem EmbeddedGroupProduct.vanishingIdeal_univ_prime_of_connected
    (hG : @_root_.IsConnected _ G.zariskiTopology Set.univ) :
    (G.vanishingIdeal Set.univ).IsPrime := by
  let H : AlgebraicSubgroup G :=
    { toAddSubgroup := ⊤
      isClosed := @isClosed_univ _ G.zariskiTopology }
  have hconn : H.IsConnected := hG
  have hprime := H.translated_vanishingIdeal_isPrime hconn 0
  simpa [translate,H,AlgebraicSubgroup.carrier] using hprime

end PhilipponMultiplicity
end
end

section
-- Reused implementation: PhilipponConnectedShiftedAddendum

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem SectionFiveConstruction.index_pos_of_connected
    (C : SectionFiveConstruction G A)
    (hG : @_root_.IsConnected _ G.zariskiTopology Set.univ)
    (hP : ∃ x : G.Point, x ∉ zeroLocusOnGroup G C.polynomial) : 1 ≤ C.index := by
  by_contra hnot
  have hi : C.index = 0 := by omega
  letI := G.vanishingIdeal_univ_prime_of_connected hG
  have hqeq : C.selectedPrime.asIdeal = G.vanishingIdeal Set.univ := by
    have hq := C.minimal_at_index
    simpa only [hi,SectionFiveInput.idealChain,Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff] using hq
  have hPI : C.polynomial ∈ G.vanishingIdeal Set.univ := by
    rw [← hqeq]
    apply C.minimal_at_next.le
    simp only [hi,zero_add,SectionFiveInput.idealChain]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨x,hx⟩ := hP
  exact hx (G.ambient.eval_eq_zero_of_mem_vanishingIdeal hPI ⟨x,Set.mem_univ x,rfl⟩)

theorem SectionFiveConstruction.exists_shifted_sampled_subgroup
    (hK : IsPhilipponBaseField K) (C : SectionFiveConstruction G A)
    (hpos : 1 ≤ C.index) :
    ∃ H : AlgebraicSubgroup G,
      H.IsConnected ∧ HasIncompleteDefinition G H.carrier C.scaledDegrees ∧
      (∃ v : G.Point, ∀ g ∈ C.samplingSet, ∀ h ∈ H.carrier,
        ((C.contactParameter+1 : ℕ) : WithTop ℕ) ≤
          vanishingOrder A C.polynomial (g+v+h)) ∧
      ((Nat.choose (C.contactParameter + analyticCodimension A H.carrier)
        (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount C.samplingSet H.carrier : ℝ) * hilbertDegreeForm G H.carrier C.degrees ≤
            hilbertDegreeForm G Set.univ C.scaledDegrees) := by
  letI : CompleteSpace K := hK.completeSpace
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨H,hH,hconn,_⟩ := (section_five_construction K hK G A).2.1 C.stabilizer
  obtain ⟨J,hG,hJ,hbounded,_,_,htransfer⟩ :=
    section_five_bounded_replacement_established K G A C.toSectionFiveInput C.index
      C.component C.meets_group
  have hzero := C.sample_mem_translated_contact_locus hK 0 C.zero_mem
  have hm := C.contact_coset_multiplicity hK H hH hconn 0 hzero
  have htz : translate (0 : G.Point) H.carrier = H.carrier := by simp [translate]
  rw [htz] at hm
  have hdef : HasIncompleteDefinition G H.carrier C.scaledDegrees :=
    ⟨J,hJ,hbounded,((htransfer H.carrier _).mpr hm).1⟩
  have hbound := section_five_counting_inequality K hK G A C
  dsimp only at hbound
  rw [← hH] at hbound
  refine ⟨H,hconn,hdef,?_,hbound⟩
  obtain ⟨v,hv⟩ := C.meets_group
  refine ⟨v,fun g hg h hh => ?_⟩
  have hhS : h ∈ C.stabilizer.carrier := by
    rw [hH] at hh
    exact connectedComponentIn_subset C.stabilizer.carrier 0 hh
  have hstable : translate h C.component = C.component := hhS
  have hhv : h+v ∈ C.component := hstable ▸
    (show h+v ∈ translate h C.component from ⟨v,hv,rfl⟩)
  have hz : h+v ∈ idealZeroLocusOnGroup G (C.toSectionFiveInput.idealChain (C.index+1)) :=
    fun P hP => hhv P (C.minimal_at_next.le hP)
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : C.index ≠ 0)
  rw [hn] at hz
  have hg1 : g ∈ sumset C.samplingSet 1 := by
    simpa only [add_zero] using add_mem_sumset_succ C.samplingSet hg
      (zero_mem_sumset C.samplingSet C.zero_mem 0)
  have hcontact := C.toSectionFiveInput.polynomial_contact_of_chain_zero hK n (h+v) hz g
    (sumset_mono C.samplingSet C.zero_mem (by omega) hg1)
  have hle : C.contactParameter ≤ (n+1)*C.contactParameter := by
    simpa only [one_mul] using Nat.mul_le_mul_right C.contactParameter
      (show 1 ≤ n+1 by omega)
  have horder : ((C.contactParameter+1 : ℕ) : WithTop ℕ) ≤
      vanishingOrder A C.polynomial (g+(h+v)) := by
    apply ENat.natCast_add_one_le_iff.mpr
    exact lt_of_le_of_lt (by exact_mod_cast hle) hcontact
  simpa only [add_assoc,add_comm h v] using horder

end PhilipponMultiplicity

end
end

section
-- Reused implementation: PhilipponCommonShiftForward

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport

variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem zero_of_contact_order_succ [CompleteSpace K] (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : IsMultihomogeneousOfDegree G P D)
    (x : G.Point) (T : ℕ)
    (hcontact : ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P x) :
    x ∈ zeroLocusOnGroup G P := by
  have hj := (natCast_lt_jetOrder_iff (A.pullback P x) 0 T).mp
    (ENat.natCast_add_one_le_iff.mp hcontact) 0 (Nat.zero_le _)
  have hz : A.pullback P x 0 = 0 := by
    simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.zero_apply] using
      congrArg (fun L => L (fun i => Fin.elim0 i)) hj
  obtain ⟨_, hrep⟩ := (A.lift_represents x).self_of_nhds
  apply (G.ambient.eval_eq_zero_iff_of_lift _ (A.lift x 0) _ P D hP).mp hz
  intro i
  simpa only [A.map_zero, add_zero] using hrep i

theorem SectionFiveConstruction.exists_common_shift_subgroup
    (hK : IsPhilipponBaseField K) (C : SectionFiveConstruction G A)
    (hG : G.IsConnected) :
    ∃ H : AlgebraicSubgroup G,
      H.IsConnected ∧ HasIncompleteDefinition G H.carrier C.scaledDegrees ∧
      (∃ v : G.Point, ∀ g ∈ C.samplingSet,
        translate (g + v) H.carrier ⊆ zeroLocusOnGroup G C.polynomial) ∧
      ((Nat.choose (C.contactParameter + analyticCodimension A H.carrier)
        (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount C.samplingSet H.carrier : ℝ) * hilbertDegreeForm G H.carrier C.degrees ≤
            hilbertDegreeForm G Set.univ C.scaledDegrees) := by
  classical
  letI : CompleteSpace K := hK.completeSpace
  by_cases hall : ∀ x : G.Point, x ∈ zeroLocusOnGroup G C.polynomial
  · obtain ⟨H, hconn, hdef, _, hbound⟩ := C.exists_obstructing_subgroup hK
    exact ⟨H, hconn, hdef, ⟨0, fun _ _ x _ => hall x⟩, hbound⟩
  · have hnonzero : ∃ x : G.Point, x ∉ zeroLocusOnGroup G C.polynomial := by
      simpa only [not_forall] using hall
    obtain ⟨H, hconn, hdef, ⟨v, hv⟩, hbound⟩ :=
      C.exists_shifted_sampled_subgroup hK (C.index_pos_of_connected hG hnonzero)
    refine ⟨H, hconn, hdef, ⟨v, ?_⟩, hbound⟩
    intro g hg x hx
    obtain ⟨h, hh, rfl⟩ := hx
    exact zero_of_contact_order_succ C.polynomial C.degrees C.polynomial_homogeneous
      _ C.contactParameter (hv g hg h hh)

theorem addendum_common_shift_proved
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∃ c : EmbeddedCommutativeGroup K → ℕ,
      (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K), G.IsConnected → 0 < G.dimension →
      ∀ (A : AnalyticSubgroup G)
        (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        ∃ H : AlgebraicSubgroup G,
          H.IsConnected ∧
          HasIncompleteDefinition G H.carrier (fun i => c (G.factor i) * D i) ∧
          (∃ v : G.Point,
            ∀ g ∈ sample,
              translate (g + v) H.carrier ⊆ zeroLocusOnGroup G P) ∧
          ((Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
              (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
            hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * D i)) := by
  classical
  letI : CompleteSpace K := hK.completeSpace
  obtain ⟨c, hc, hatlas⟩ := exists_uniformly_bounded_translation_atlas K hK
  refine ⟨c, hc, fun G hG _hn A sample hzero T D P hP hhom hcontact => ?_⟩
  choose atlas hbound using hatlas G A
  let I : SectionFiveInput G A :=
    { samplingSet := sample
      zero_mem := hzero
      contactParameter := T
      degrees := D
      polynomial := P
      polynomial_ne_zero := hP
      polynomial_homogeneous := hhom
      contact := hcontact
      coordinateBounds := fun i => c (G.factor i)
      coordinateBounds_pos := fun i => hc _
      atlas := atlas
      atlas_bound := hbound }
  obtain ⟨C, hC⟩ := (section_five_construction K hK G A).1 I
  have h := C.exists_common_shift_subgroup hK hG
  change ∃ H : AlgebraicSubgroup G, H.IsConnected ∧
    HasIncompleteDefinition G H.carrier C.toSectionFiveInput.scaledDegrees ∧
    (∃ v, ∀ g ∈ C.toSectionFiveInput.samplingSet,
      translate (g + v) H.carrier ⊆ zeroLocusOnGroup G C.toSectionFiveInput.polynomial) ∧
    ((Nat.choose (C.toSectionFiveInput.contactParameter + analyticCodimension A H.carrier)
      (analyticCodimension A H.carrier) : ℝ) *
        (cosetCount C.toSectionFiveInput.samplingSet H.carrier : ℝ) *
        hilbertDegreeForm G H.carrier C.toSectionFiveInput.degrees ≤
      hilbertDegreeForm G Set.univ C.toSectionFiveInput.scaledDegrees) at h
  rw [hC] at h
  exact h

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∃ c : EmbeddedCommutativeGroup K → ℕ,
      (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K), G.IsConnected → 0 < G.dimension →
      ∀ (A : AnalyticSubgroup G)
        (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        ∃ H : AlgebraicSubgroup G,
          H.IsConnected ∧
          HasIncompleteDefinition G H.carrier (fun i => c (G.factor i) * D i) ∧
          (∃ v : G.Point,
            ∀ g ∈ sample,
              PhilipponMultiplicity.translate (g + v) H.carrier ⊆ zeroLocusOnGroup G P) ∧
          ((Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
              (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
            hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * D i)) := by
  exact addendum_common_shift_proved K hK
