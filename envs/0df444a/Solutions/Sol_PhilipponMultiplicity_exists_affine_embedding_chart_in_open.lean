-- Prove2me | solution 1 for PhilipponMultiplicity.exists_affine_embedding_chart_in_open
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T20:31:10.032492+00:00
-- url     : https://prove2.me/submissions/fc579a7c-acec-4fa9-8bbf-d1c9826084fa

import Theorems.Thm_PhilipponMultiplicity_affine_locally_closed_has_polynomial_fraction_charts
import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib

section
-- Included implementation: Solutions.PhilipponProjectiveContact
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
-- Included implementation: Solutions.PhilipponAffineMapFractions

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

/-- A balanced homogeneous fraction is unchanged when each projective block
is replaced by another nonzero representative. -/
theorem eval_ratio_of_lift (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P Q : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    MvPolynomial.eval v P / MvPolynomial.eval v Q = M.eval P p / M.eval Q p := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h (p i).rep_nonzero).mp
      (he.trans (p i).mk_rep.symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K)),
    M.eval_block_scale Q D hQ (M.coordinate p) (fun i => (a i : K))]
  exact mul_div_mul_left _ _ hne


end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Included implementation: Solutions.PhilipponProjectiveGeometry

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


end MultiProjectiveSpace
end PhilipponMultiplicity
end
end


section
-- Included implementation: Solutions.PhilipponHomogeneousOperations

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
-- Included implementation: Solutions.PhilipponAdditiveSubgroups

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
-- Included implementation: Solutions.PhilipponRegularMapTopology

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


end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Included implementation: Solutions.PhilipponMultihomogenization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Padding every monomial in each chosen chart coordinate homogenizes a
block-degree-bounded polynomial without changing it on the normalized chart. -/
theorem exists_multihomogenization_on_chart
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hbound : ∀ m ∈ P.support, ∀ i,
      (∑ k : Fin (M.ambientDimension i + 1), m ⟨i,k⟩) ≤ D i) :
    ∃ H : M.CoordinateRing, M.IsHomogeneous H D ∧
      ∀ v : M.Variable → K, (∀ i, v ⟨i,j i⟩ = 1) →
        MvPolynomial.eval v H = MvPolynomial.eval v P := by
  classical
  let a (m : M.Variable →₀ ℕ) (i : M.FactorIndex) :=
    ∑ k : Fin (M.ambientDimension i + 1), m ⟨i,k⟩
  let T (m : M.Variable →₀ ℕ) : M.CoordinateRing :=
    monomial m (coeff m P) * ∏ i, X (⟨i,j i⟩ : M.Variable) ^ (D i - a m i)
  refine ⟨∑ m ∈ P.support, T m,?_,?_⟩
  · apply M.isHomogeneous_sum
    intro m hm
    have hmon : M.IsHomogeneous (monomial m (coeff m P)) (a m) := by
      intro n hn i
      have hn' : n = m := Finset.mem_singleton.mp (support_monomial_subset hn)
      subst n
      rfl
    have hpowers := M.isHomogeneous_prod Finset.univ
      (fun i => X (⟨i,j i⟩ : M.Variable) ^ (D i - a m i))
      (fun i k => (D i - a m i) * (if k = i then 1 else 0))
      (fun i _ => (M.isHomogeneous_X ⟨i,j i⟩).pow M (D i - a m i))
    have hdeg : a m + (∑ i : M.FactorIndex,
        fun k => (D i - a m i) * (if k = i then 1 else 0)) = D := by
      funext i
      simp only [Pi.add_apply,Finset.sum_apply,mul_ite,mul_one,mul_zero]
      simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
      exact Nat.add_sub_of_le (hbound m hm i)
    rw [← hdeg]
    exact hmon.mul M hpowers
  · intro v hv
    rw [map_sum]
    calc
      ∑ m ∈ P.support, MvPolynomial.eval v (T m) =
          ∑ m ∈ P.support, MvPolynomial.eval v (monomial m (coeff m P)) := by
        apply Finset.sum_congr rfl
        intro m hm
        simp [T,map_prod,hv]
      _ = MvPolynomial.eval v P := by
        rw [← map_sum,support_sum_monomial_coeff]


end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Included implementation: Solutions.PhilipponAffineClosedPoints

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace PhilipponMultiplicity.AffineClosedPoints

open MvPolynomial
open Topology

variable {K : Type*} [Field K] {σ τ : Type*}

/-- The ordinary Zariski topology on an affine algebraic zero set, induced by its
evaluation ideals in the polynomial prime spectrum. -/
@[instance_reducible] def locusTopology (I : Ideal (MvPolynomial σ K)) :
    TopologicalSpace (zeroLocus K I) :=
  TopologicalSpace.induced (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
    inferInstance

theorem nonzero_sets_basis (I : Ideal (MvPolynomial σ K)) :
    letI := locusTopology I
    TopologicalSpace.IsTopologicalBasis
      (Set.range (fun P : MvPolynomial σ K => {x : zeroLocus K I | aeval x.val P ≠ 0})) := by
  let _ := locusTopology I
  have hb := PrimeSpectrum.isTopologicalBasis_basic_opens.induced
    (fun x : zeroLocus K I => pointToPoint (k := K) x.val)
  have hpre (P : MvPolynomial σ K) :
      (fun x : zeroLocus K I => pointToPoint (k := K) x.val) ⁻¹'
        (PrimeSpectrum.basicOpen P : Set (PrimeSpectrum (MvPolynomial σ K))) =
      {x : zeroLocus K I | aeval x.val P ≠ 0} := by
    ext x
    change (P ∉ vanishingIdeal K {x.val}) ↔ aeval x.val P ≠ 0
    rw [mem_vanishingIdeal_singleton_iff]
  simpa only [← Set.range_comp, Function.comp_def, hpre] using hb


end PhilipponMultiplicity.AffineClosedPoints
end
end


section
-- Included implementation: Solutions.PhilipponStandardAffineChart

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.StandardAffineChart
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

def domain : Set M.Point := {x | ∀ i, (x i).rep (b i) ≠ 0}

def equations : Ideal M.CoordinateRing :=
  Ideal.span (Set.range (fun i : M.FactorIndex => X (⟨i, b i⟩ : M.Variable) - 1))

def ideal : Ideal M.CoordinateRing := (equations M b).radical

theorem ideal_isRadical : (ideal M b).IsRadical := Ideal.radical_isRadical _

theorem mem_locus (v : M.Variable → K) :
    v ∈ zeroLocus K (ideal M b) ↔ ∀ i, v ⟨i, b i⟩ = 1 := by
  constructor
  · intro hv i
    have h := hv _ (Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i)))
    simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using h
  · intro hv
    have hI : equations M b ≤ RingHom.ker (aeval v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change aeval v (X (⟨i, b i⟩ : M.Variable) - 1) = 0
      simp [hv i]
    intro P hP
    exact radical_le_vanishingIdeal_zeroLocus (K := K) (equations M b) hP v
      (fun F hF => hI hF)

def normalize (x : domain M b) : zeroLocus K (ideal M b) :=
  ⟨fun v => (x.val v.1).rep v.2 / (x.val v.1).rep (b v.1),
    (mem_locus M b _).mpr (fun i => div_self (x.property i))⟩

theorem block_ne_zero (v : zeroLocus K (ideal M b)) (i : M.FactorIndex) :
    (fun j => v.val ⟨i, j⟩) ≠ 0 := by
  intro h
  have h0 := congrFun h (b i)
  have h1 := (mem_locus M b v.val).mp v.property i
  exact one_ne_zero (h1.symm.trans h0)

def projectivePoint (v : zeroLocus K (ideal M b)) : M.Point :=
  fun i => Projectivization.mk K (fun j => v.val ⟨i, j⟩) (block_ne_zero M b v i)

theorem projectivePoint_mem (v : zeroLocus K (ideal M b)) :
    projectivePoint M b v ∈ domain M b := by
  intro i hz
  have hlift (k : M.FactorIndex) : ∃ h : (fun j => v.val ⟨k, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v.val ⟨k, j⟩) h = projectivePoint M b v k :=
    ⟨block_ne_zero M b v k, rfl⟩
  have hn := (M.eval_eq_zero_iff_of_lift _ v.val hlift (X ⟨i, b i⟩) _
    (M.isHomogeneous_X _)).mpr (by
      simpa only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate] using hz)
  have h1 := (mem_locus M b v.val).mp v.property i
  exact one_ne_zero (h1.symm.trans (by simpa using hn))

def denormalize (v : zeroLocus K (ideal M b)) : domain M b :=
  ⟨projectivePoint M b v, projectivePoint_mem M b v⟩

theorem normalize_denormalize (v : zeroLocus K (ideal M b)) :
    normalize M b (denormalize M b v) = v := by
  apply Subtype.ext
  funext t
  have hlift (i : M.FactorIndex) : ∃ h : (fun j => v.val ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v.val ⟨i, j⟩) h = projectivePoint M b v i :=
    ⟨block_ne_zero M b v i, rfl⟩
  have h := M.eval_ratio_of_lift _ v.val hlift (X t) (X ⟨t.1, b t.1⟩) _
    (M.isHomogeneous_X t) (M.isHomogeneous_X ⟨t.1, b t.1⟩)
  have h1 := (mem_locus M b v.val).mp v.property t.1
  simpa only [normalize, denormalize, MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate,
    eval_X, h1, div_one] using h.symm

theorem denormalize_normalize (x : domain M b) :
    denormalize M b (normalize M b x) = x := by
  apply Subtype.ext
  funext i
  apply Eq.trans ?_ (x.val i).mk_rep
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨((x.val i).rep (b i))⁻¹, ?_⟩
  funext j
  change ((x.val i).rep (b i))⁻¹ * (x.val i).rep j =
    (x.val i).rep j / (x.val i).rep (b i)
  simp only [div_eq_mul_inv, mul_comm]

def equiv : domain M b ≃ zeroLocus K (ideal M b) where
  toFun := normalize M b
  invFun := denormalize M b
  left_inv := denormalize_normalize M b
  right_inv := normalize_denormalize M b

theorem domain_isOpen : @IsOpen M.Point M.zariskiTopology (domain M b) := by
  letI := M.zariskiTopology
  change IsOpen {x : M.Point | ∀ i, (x i).rep (b i) ≠ 0}
  rw [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  simpa only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate] using
    M.isOpen_basic (X ⟨i, b i⟩) _ (M.isHomogeneous_X _)

theorem normalize_represents (x : domain M b) (i : M.FactorIndex) :
    ∃ h : (fun j => (normalize M b x).val ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => (normalize M b x).val ⟨i, j⟩) h = x.val i := by
  refine ⟨block_ne_zero M b (normalize M b x) i, ?_⟩
  exact congrFun (congrArg Subtype.val (denormalize_normalize M b x)) i

theorem normalize_continuous :
    letI := M.zariskiTopology
    letI := AffineClosedPoints.locusTopology (ideal M b)
    Continuous (normalize M b) := by
  classical
  letI := M.zariskiTopology
  letI := AffineClosedPoints.locusTopology (ideal M b)
  apply (AffineClosedPoints.nonzero_sets_basis (ideal M b)).continuous_iff.mpr
  rintro _ ⟨P, rfl⟩
  let D : M.FactorIndex → ℕ := fun i =>
    ∑ m ∈ P.support, ∑ j : Fin (M.ambientDimension i + 1), m ⟨i, j⟩
  obtain ⟨H, hH, heval⟩ := M.exists_multihomogenization_on_chart P D b (by
    intro m hm i
    dsimp only [D]
    exact Finset.single_le_sum
      (f := fun m : M.Variable →₀ ℕ => ∑ j : Fin (M.ambientDimension i + 1), m ⟨i, j⟩)
      (fun _ _ => Nat.zero_le _) hm)
  have hset : (normalize M b) ⁻¹' {v | aeval v.val P ≠ 0} =
      {x : domain M b | M.eval H x.val ≠ 0} := by
    ext x
    have hn := heval (normalize M b x).val
      ((mem_locus M b _).mp (normalize M b x).property)
    have hiff := M.eval_eq_zero_iff_of_lift x.val (normalize M b x).val
      (normalize_represents M b x) H D hH
    rw [hn] at hiff
    exact hiff.not
  rw [hset]
  exact (M.isOpen_basic H D hH).preimage continuous_subtype_val

theorem denormalize_continuous :
    letI := M.zariskiTopology
    letI := AffineClosedPoints.locusTopology (ideal M b)
    Continuous (denormalize M b) := by
  classical
  letI := M.zariskiTopology
  letI := AffineClosedPoints.locusTopology (ideal M b)
  apply Continuous.subtype_mk
  change Continuous (projectivePoint M b)
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have hset : (projectivePoint M b) ⁻¹' {p | M.eval P p ≠ 0} =
      {v : zeroLocus K (ideal M b) | aeval v.val P ≠ 0} := by
    ext v
    have hlift (i : M.FactorIndex) : ∃ h : (fun j => v.val ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => v.val ⟨i, j⟩) h = projectivePoint M b v i :=
      ⟨block_ne_zero M b v i, rfl⟩
    exact (M.eval_eq_zero_iff_of_lift _ v.val hlift P D hP).not.symm
  rw [hset]
  exact (AffineClosedPoints.nonzero_sets_basis (ideal M b)).isOpen (Set.mem_range_self P)

/-- A standard multiprojective open is homeomorphic to the affine zero set
cut out by setting each chosen pivot coordinate equal to one. -/
def homeomorph :
    letI := M.zariskiTopology
    letI := AffineClosedPoints.locusTopology (ideal M b)
    domain M b ≃ₜ zeroLocus K (ideal M b) := by
  letI := M.zariskiTopology
  letI := AffineClosedPoints.locusTopology (ideal M b)
  exact { equiv M b with
    continuous_toFun := normalize_continuous M b
    continuous_invFun := denormalize_continuous M b }

theorem exists_domain (x : M.Point) :
    ∃ c : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1), x ∈ domain M c := by
  classical
  choose c hc using fun i => Function.ne_iff.mp (x i).rep_nonzero
  exact ⟨c, hc⟩

end PhilipponMultiplicity.StandardAffineChart

end
end


section
-- Included implementation: Solutions.PhilipponAffineNeighborhoodReduction
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set Topology
open scoped BigOperators

namespace PhilipponMultiplicity
universe u

namespace StandardAffineChart
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

theorem homogenize_fraction (P Q : M.CoordinateRing) :
    ∃ (D : M.FactorIndex → ℕ) (A B : M.CoordinateRing),
      M.IsHomogeneous A D ∧ M.IsHomogeneous B D ∧
      ∀ x : domain M b, aeval (normalize M b x).val Q ≠ 0 →
        M.eval B x.val ≠ 0 ∧
        aeval (normalize M b x).val P / aeval (normalize M b x).val Q =
          M.eval A x.val / M.eval B x.val := by
  classical
  let D : M.FactorIndex → ℕ := fun i =>
    ∑ m ∈ P.support ∪ Q.support, ∑ j : Fin (M.ambientDimension i + 1), m ⟨i, j⟩
  have hbound (m : M.Variable →₀ ℕ) (hm : m ∈ P.support ∪ Q.support) (i) :
      (∑ j : Fin (M.ambientDimension i + 1), m ⟨i, j⟩) ≤ D i := by
    exact Finset.single_le_sum
      (f := fun m : M.Variable →₀ ℕ => ∑ j : Fin (M.ambientDimension i + 1), m ⟨i,j⟩)
      (fun _ _ => Nat.zero_le _) hm
  obtain ⟨A, hA, hAP⟩ := M.exists_multihomogenization_on_chart P D b
    (fun m hm => hbound m (Finset.mem_union_left _ hm))
  obtain ⟨B, hB, hBQ⟩ := M.exists_multihomogenization_on_chart Q D b
    (fun m hm => hbound m (Finset.mem_union_right _ hm))
  refine ⟨D, A, B, hA, hB, ?_⟩
  intro x hQ
  have hn := (mem_locus M b _).mp (normalize M b x).property
  have hAP' := hAP (normalize M b x).val hn
  have hBQ' := hBQ (normalize M b x).val hn
  have hiff := M.eval_eq_zero_iff_of_lift x.val (normalize M b x).val
    (normalize_represents M b x) B D hB
  have hratio := M.eval_ratio_of_lift x.val (normalize M b x).val
    (normalize_represents M b x) A B D hA hB
  rw [hBQ'] at hiff
  rw [hAP', hBQ'] at hratio
  exact ⟨hiff.not.mp hQ, hratio⟩

end StandardAffineChart

theorem embedding_charts_of_affine_neighborhoods
    (K : Type u) [Field K] [IsAlgClosed K]
    (M : MultiProjectiveSpace K) (X : Type u) (e : X → M.Point)
    (he : Function.Injective e)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (x : X) (W : Set X)
    (hW : @IsOpen X (TopologicalSpace.induced e M.zariskiTopology) W)
    (hxW : x ∈ W)
    (hcharts : ∀ (σ : Type) [Finite σ] (I : Ideal (MvPolynomial σ K))
    (X : Type u) [TopologicalSpace X],
    letI : TopologicalSpace (MvPolynomial.zeroLocus K I) :=
      TopologicalSpace.induced
        (fun z : MvPolynomial.zeroLocus K I => MvPolynomial.pointToPoint (k := K) z.val)
        inferInstance
    ∀ (d : X → MvPolynomial.zeroLocus K I), Topology.IsEmbedding d →
      IsLocallyClosed (Set.range d) →
      ∀ (x : X) (W : Set X), IsOpen W → x ∈ W →
        ∃ S : Set X, IsOpen S ∧ x ∈ S ∧ S ⊆ W ∧
          ∃ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
          ∃ a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
              (TopologicalSpace.induced
                (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
                inferInstance),
            (∃ L : σ → MvPolynomial (Fin n) K,
              ∀ z : S, ∀ t, (d z.val).val t = MvPolynomial.aeval (a z).val (L t)) ∧
            (∀ i : Fin n, ∃ P Q : MvPolynomial σ K,
              ∀ z : S, MvPolynomial.aeval (d z.val).val Q ≠ 0 ∧
                (a z).val i = MvPolynomial.aeval (d z.val).val P /
                  MvPolynomial.aeval (d z.val).val Q)) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ S : Set X, IsOpen S ∧ x ∈ S ∧ S ⊆ W ∧
      ∃ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
      ∃ a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance),
        (∃ L : M.Variable → MvPolynomial (Fin n) K,
          ∀ z : S, ∀ b, ∃ h :
            (fun i => MvPolynomial.aeval (a z).val (L ⟨b, i⟩)) ≠ 0,
            Projectivization.mk K
              (fun i => MvPolynomial.aeval (a z).val (L ⟨b, i⟩)) h = e z.val b) ∧
        (∀ i : Fin n, ∃ (D : M.FactorIndex → ℕ) (P Q : M.CoordinateRing),
          M.IsHomogeneous P D ∧ M.IsHomogeneous Q D ∧
          ∀ z : S, M.eval Q (e z.val) ≠ 0 ∧
            (a z).val i = M.eval P (e z.val) / M.eval Q (e z.val)) := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  obtain ⟨b, hb⟩ := StandardAffineChart.exists_domain M (e x)
  let V : Set X := e ⁻¹' StandardAffineChart.domain M b
  have hemb : IsEmbedding e := he.isEmbedding_induced
  have hV : IsOpen V := (StandardAffineChart.domain_isOpen M b).preimage hemb.continuous
  let φ : V → StandardAffineChart.domain M b := fun z => ⟨e z.val, z.property⟩
  have hφ : IsEmbedding φ := IsEmbedding.subtypeVal.of_comp_iff.mp
    (hemb.comp IsEmbedding.subtypeVal)
  let I := StandardAffineChart.ideal M b
  letI : TopologicalSpace (zeroLocus K I) := AffineClosedPoints.locusTopology I
  let c := StandardAffineChart.homeomorph M b
  let d : V → zeroLocus K I := c ∘ φ
  have hd : IsEmbedding d := c.isEmbedding.comp hφ
  have hrφ : Set.range φ = Subtype.val ⁻¹' Set.range e := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, rfl⟩
    · rintro ⟨y, hy⟩
      refine ⟨⟨y, ?_⟩, ?_⟩
      · change e y ∈ StandardAffineChart.domain M b
        rw [hy]
        exact z.property
      · exact Subtype.ext hy
  have hlφ : IsLocallyClosed (Set.range φ) := by
    rw [hrφ]
    exact hX.preimage continuous_subtype_val
  have hrd : Set.range d = c.symm ⁻¹' Set.range φ := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, c.symm_apply_apply (φ y) |>.symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change c (φ y) = z
      rw [hy, c.apply_symm_apply]
  have hld : IsLocallyClosed (Set.range d) := by
    rw [hrd]
    exact hlφ.preimage c.symm.continuous
  obtain ⟨U, hU, hxU, hUW, n, J, hJ, a, ⟨L, hL⟩, hfrac⟩ :=
    hcharts M.Variable I V d hd hld ⟨x, hb⟩ (Subtype.val ⁻¹' W)
      (hW.preimage continuous_subtype_val) hxW
  let S : Set X := Subtype.val '' U
  let f : U ≃ₜ S := IsEmbedding.subtypeVal.homeomorphImage U
  letI : TopologicalSpace (zeroLocus K J) := AffineClosedPoints.locusTopology J
  let aS : S ≃ₜ zeroLocus K J := f.symm.trans a
  have hf (z : S) : (f.symm z).val.val = z.val := by
    exact congrArg Subtype.val (f.apply_symm_apply z)
  refine ⟨S, hV.isOpenMap_subtype_val _ hU, ⟨⟨x, hb⟩, hxU, rfl⟩,
    ?_, n, J, hJ, aS, ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact hUW hy
  · refine ⟨L, ?_⟩
    intro z i
    have hrep := StandardAffineChart.normalize_represents M b (φ (f.symm z).val) i
    have hval : (StandardAffineChart.normalize M b (φ (f.symm z).val)).val =
        fun t => aeval (aS z).val (L t) := by
      funext t
      exact hL (f.symm z) t
    rw [hval] at hrep
    simpa only [φ, hf z] using hrep
  · intro i
    obtain ⟨P, Q, hPQ⟩ := hfrac i
    obtain ⟨D, A, B, hA, hB, hAB⟩ := StandardAffineChart.homogenize_fraction M b P Q
    refine ⟨D, A, B, hA, hB, ?_⟩
    intro z
    have hz := hPQ (f.symm z)
    have hABz := hAB (φ (f.symm z).val) hz.1
    refine ⟨?_, ?_⟩
    · simpa only [φ, hf z] using hABz.1
    · change (a (f.symm z)).val i = _
      rw [hz.2]
      exact hABz.2.trans (by simp only [φ, hf z])

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K]
    (M : MultiProjectiveSpace K) (X : Type u) (e : X → M.Point)
    (he : Function.Injective e)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (x : X) (W : Set X)
    (hW : @IsOpen X (TopologicalSpace.induced e M.zariskiTopology) W)
    (hxW : x ∈ W) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ S : Set X, IsOpen S ∧ x ∈ S ∧ S ⊆ W ∧
      ∃ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
      ∃ a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance),
        (∃ L : M.Variable → MvPolynomial (Fin n) K,
          ∀ z : S, ∀ b, ∃ h :
            (fun i => MvPolynomial.aeval (a z).val (L ⟨b, i⟩)) ≠ 0,
            Projectivization.mk K
              (fun i => MvPolynomial.aeval (a z).val (L ⟨b, i⟩)) h = e z.val b) ∧
        (∀ i : Fin n, ∃ (D : M.FactorIndex → ℕ) (P Q : M.CoordinateRing),
          M.IsHomogeneous P D ∧ M.IsHomogeneous Q D ∧
          ∀ z : S, M.eval Q (e z.val) ≠ 0 ∧
            (a z).val i = M.eval P (e z.val) / M.eval Q (e z.val)) := by
  exact embedding_charts_of_affine_neighborhoods K M X e he hX x W hW hxW
    (affine_locally_closed_has_polynomial_fraction_charts K)
