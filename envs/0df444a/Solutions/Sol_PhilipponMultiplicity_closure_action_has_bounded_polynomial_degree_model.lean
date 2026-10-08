-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_bounded_polynomial_degree_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T10:22:58.148003+00:00
-- url     : https://prove2.me/submissions/762ee419-6f5b-411d-8588-46bcb1410be9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_line_polynomial_degree_model
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous


section

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace HomogeneousDiagonal

variable {R σ : Type*} [CommSemiring R] [Fintype σ]

/-- Enumerate the occurrences of each variable to multilinearize a monomial.
Symmetry is not required, and the empty monomial gives a zero-ary map. -/
theorem monomial (m : σ →₀ ℕ) (d : ℕ) (hm : ∑ i, m i = d) :
    ∃ L : MultilinearMap R (fun _ : Fin d => σ → R) R,
      ∀ x, L (fun _ => x) = ∏ i, x i ^ m i := by
  classical
  have hcard : Fintype.card ((i : σ) × Fin (m i)) = d := by
    simpa using hm
  let e : Fin d ≃ ((i : σ) × Fin (m i)) :=
    (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨(MultilinearMap.mkPiAlgebra R (Fin d) R).compLinearMap
    (fun j => LinearMap.proj (e j).1), ?_⟩
  intro x
  change (∏ j : Fin d, x (e j).1) = _
  rw [Fintype.prod_equiv e (fun j => x (e j).1) (fun j => x j.1) (by intro j; rfl)]
  simp [Fintype.prod_sigma]

/-- Every homogeneous polynomial on a finite free module is the diagonal of a
multilinear map, over any commutative semiring and in every degree. -/
theorem polynomial (P : MvPolynomial σ R) (d : ℕ) (hP : P.IsHomogeneous d) :
    ∃ L : MultilinearMap R (fun _ : Fin d => σ → R) R,
      ∀ x, L (fun _ => x) = MvPolynomial.eval x P := by
  classical
  have hm : ∀ m : P.support, ∑ i, m.val i = d := by
    intro m
    have h := hP.degree_eq_sum_deg_support m.property
    rw [h]
    exact (Finsupp.sum_fintype m.val (fun _ n => n) (by simp)).symm
  choose L hL using fun m : P.support => monomial (R := R) m.val d (hm m)
  refine ⟨∑ m : P.support, P.coeff m.val • L m, ?_⟩
  intro x
  simp only [sum_apply, smul_apply, hL, smul_eq_mul]
  conv_rhs => rw [← P.support_sum_monomial_coeff]
  simp only [map_sum, MvPolynomial.eval_monomial]
  rw [← Finset.sum_coe_sort P.support]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  exact (Finsupp.prod_fintype m.val (fun i n => x i ^ n) (by simp)).symm

/-- Restrict the rational diagonal form to an integer lattice. -/
theorem integer_lattice (P : MvPolynomial σ ℚ) (d : ℕ) (hP : P.IsHomogeneous d) :
    ∃ L : MultilinearMap ℤ (fun _ : Fin d => σ → ℤ) ℚ,
      ∀ x, L (fun _ => x) = MvPolynomial.eval (fun i => (x i : ℚ)) P := by
  obtain ⟨L,hL⟩ := polynomial P d hP
  let cast : (σ → ℤ) →ₗ[ℤ] (σ → ℚ) :=
    LinearMap.pi (fun i =>
      ((Int.castRingHom ℚ).toAddMonoidHom.toIntLinearMap).comp (LinearMap.proj i))
  refine ⟨(L.restrictScalars ℤ).compLinearMap (fun _ => cast), ?_⟩
  intro x
  exact hL (fun i => (x i : ℚ))

end HomogeneousDiagonal
end

end


section

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace HomogeneousExtraction
variable {R σ : Type*} [Field R] [CharZero R] [Fintype σ]

/-- Scaling every coordinate of a homogeneous polynomial scales its value by
the corresponding power, also in degree zero. -/
theorem eval_scale (P : MvPolynomial σ R) (d : ℕ) (hP : P.IsHomogeneous d)
    (x : σ → R) (t : R) :
    MvPolynomial.eval (fun i => t * x i) P = t ^ d * MvPolynomial.eval x P := by
  obtain ⟨L,hL⟩ := HomogeneousDiagonal.polynomial P d hP
  have h := L.map_smul_univ (fun _ => t) (fun _ => x)
  have hx : t • x = (fun i => t * x i) := rfl
  simpa only [hx, smul_eq_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, hL] using h

/-- Restrict a multivariate polynomial to the line through an arbitrary vector. -/
theorem ray_eval (P : MvPolynomial σ R) (x : σ → R) (t : R) :
    Polynomial.eval t
      (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (x i) * Polynomial.X) P) =
        MvPolynomial.eval (fun i => t * x i) P := by
  change (Polynomial.evalRingHom t) (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (x i) * Polynomial.X) P) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id R := by
    ext r
    simp
  rw [hc, MvPolynomial.eval₂_id]
  have hf : (⇑(Polynomial.evalRingHom t) ∘
      (fun i => Polynomial.C (x i) * Polynomial.X)) = (fun i => t * x i) := by
    funext i
    change Polynomial.eval t (Polynomial.C (x i) * Polynomial.X) = t * x i
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_comm]
  rw [hf]

/-- The coefficient of each power on a ray is the corresponding homogeneous
component evaluated at the direction vector. No coordinates must be nonzero. -/
theorem ray_eq_sum (P : MvPolynomial σ R) (x : σ → R) :
    MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (x i) * Polynomial.X) P =
      ∑ n ∈ Finset.range (P.totalDegree + 1),
        Polynomial.monomial n (MvPolynomial.eval x (MvPolynomial.homogeneousComponent n P)) := by
  apply Polynomial.funext
  intro t
  rw [ray_eval]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  calc
    MvPolynomial.eval (fun i => t * x i) P =
        ∑ n ∈ Finset.range (P.totalDegree + 1),
          MvPolynomial.eval (fun i => t * x i) (MvPolynomial.homogeneousComponent n P) := by
            rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [eval_scale _ n (MvPolynomial.homogeneousComponent_isHomogeneous _ _)]
      exact mul_comm _ _

theorem ray_coeff (P : MvPolynomial σ R) (x : σ → R) (d : ℕ) :
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (x i) * Polynomial.X) P).coeff d =
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent d P) := by
  classical
  rw [ray_eq_sum, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hd : d < P.totalDegree + 1
  · simp [Finset.mem_range, hd]
  · have hlt : P.totalDegree < d := by omega
    simp [Finset.mem_range, hd, MvPolynomial.homogeneousComponent_eq_zero d P hlt]

/-- Positive integral dilations suffice to isolate a prescribed homogeneous
component. Other components may exist but vanish at the given direction. -/
theorem component_eval_of_scaling (P : MvPolynomial σ R) (x : σ → R) (d : ℕ)
    (hscale : ∀ n : ℕ, 0 < n →
      MvPolynomial.eval (fun i => (n : R) * x i) P =
        (n : R) ^ d * MvPolynomial.eval x P) :
    MvPolynomial.eval x (MvPolynomial.homogeneousComponent d P) =
      MvPolynomial.eval x P := by
  have heq : MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (x i) * Polynomial.X) P =
      Polynomial.monomial d (MvPolynomial.eval x P) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinj : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : R)) := by
      intro a b h
      exact Nat.add_right_cancel (Nat.cast_injective h)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨n,rfl⟩
    change Polynomial.eval _ _ = Polynomial.eval _ _
    rw [ray_eval, Polynomial.eval_monomial, hscale (n+1) (Nat.succ_pos n)]
    exact mul_comm _ _
  have h := congrArg (fun Q : Polynomial R => Q.coeff d) heq
  simpa only [ray_coeff, Polynomial.coeff_monomial_same] using h

/-- Integral linear actions commute with scaling a degree vector, after
embedding lattice coordinates into the rationals. -/
theorem lattice_dilate {ι κ : Type*} [Fintype ι]
    (e : (κ → ℤ) ≃ₗ[ℤ] (κ → ℤ)) (c : ι → κ → ℤ) (D : ι → ℕ) (n : ℕ) (j : κ) :
    (e (∑ i, ((n * D i : ℕ) : ℤ) • c i) j : ℚ) =
      (n : ℚ) * (e (∑ i, (D i : ℤ) • c i) j : ℚ) := by
  have h : (∑ i, ((n * D i : ℕ) : ℤ) • c i) =
      (n : ℤ) • ∑ i, (D i : ℤ) • c i := by
    simp only [Nat.cast_mul, Finset.smul_sum, mul_smul]
  rw [h, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]

end HomogeneousExtraction

namespace PhilipponMultiplicity.SectionThree
variable {K : Type*} [Field K]

/-- Scaling the block degrees scales the actual Hilbert degree form by the
Hilbert-polynomial dimension. No geometric comparison is needed. -/
theorem locusDegreeValue_scale (M : MultiProjectiveSpace K) (V : Set M.Point)
    (D : M.FactorIndex → ℕ) (n : ℕ) :
    locusDegreeValue M V (fun i => n * D i) =
      (n : ℚ) ^ locusDimension M V * locusDegreeValue M V D := by
  let P := Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal V)
  have hhom : (Hilbert.degreeForm K M.factorCount M.ambientDimension
      (M.vanishingIdeal V)).IsHomogeneous P.totalDegree := by
    exact (MvPolynomial.homogeneousSubmodule M.FactorIndex ℚ P.totalDegree).smul_mem _
      (MvPolynomial.homogeneousComponent_mem P.totalDegree P)
  simpa only [locusDegreeValue, idealDegreeValue, Hilbert.degreeValue,
    locusDimension, idealDimension, Nat.cast_mul, P] using
    HomogeneousExtraction.eval_scale _ _ hhom (fun i => (D i : ℚ)) (n : ℚ)

end PhilipponMultiplicity.SectionThree
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section

namespace IntegerLinePolynomial

/-- Integer points determine a rational multivariate polynomial. -/
theorem eq_of_integer_evals {σ : Type*} {P Q : MvPolynomial σ ℚ}
    (h : ∀ z : σ → ℤ, MvPolynomial.eval (fun i => (z i : ℚ)) P =
      MvPolynomial.eval (fun i => (z i : ℚ)) Q) : P = Q := by
  classical
  apply MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℚ))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective)
  intro x hx
  have hx' : ∀ i, ∃ z : ℤ, (z : ℚ) = x i := fun i => hx i (Set.mem_univ i)
  choose z hz using hx'
  simpa only [hz] using h z

/-- Lagrange reconstruction at the consecutive nodes zero through d. -/
theorem eval_interpolation (d : ℕ) (q : Polynomial ℚ) (hq : q.natDegree ≤ d)
    (t : ℚ) :
    q.eval t = ∑ k ∈ Finset.range (d+1),
      q.eval (k : ℚ) * (Lagrange.basis (Finset.range (d+1)) (Nat.cast : ℕ → ℚ) k).eval t := by
  have hinj : Set.InjOn (Nat.cast : ℕ → ℚ) (Finset.range (d+1)) :=
    Nat.cast_injective.injOn
  have hdeg : q.degree < ((Finset.range (d+1)).card : WithBot ℕ) := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt q.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hq)
  have h := congrArg (Polynomial.eval t) (Lagrange.eq_interpolate hinj hdeg)
  simpa only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C] using h

/-- Repeated one-variable interpolation constructs a polynomial on the whole
integer lattice. The sharp total-degree bound is proved separately using rays. -/
theorem exists_polynomial_of_lines (m d : ℕ) (f : (Fin m → ℤ) → ℚ)
    (hline : ∀ x y : Fin m → ℤ, ∃ q : Polynomial ℚ,
      q.natDegree ≤ d ∧ ∀ t : ℤ, f (fun i => x i + t * y i) = q.eval (t : ℚ)) :
    ∃ P : MvPolynomial (Fin m) ℚ,
      ∀ z : Fin m → ℤ, MvPolynomial.eval (fun i => (z i : ℚ)) P = f z := by
  classical
  induction m with
  | zero =>
      refine ⟨MvPolynomial.C (f 0), ?_⟩
      intro z
      have hz : z = 0 := Subsingleton.elim _ _
      simp [hz]
  | succ m ih =>
      have hslice (k : ℕ) : ∃ P : MvPolynomial (Fin m) ℚ,
          ∀ z : Fin m → ℤ, MvPolynomial.eval (fun i => (z i : ℚ)) P =
            f (Fin.cons (k : ℤ) z) := by
        apply ih (fun z => f (Fin.cons (k : ℤ) z))
        intro x y
        obtain ⟨q, hq, heq⟩ := hline (Fin.cons (k : ℤ) x) (Fin.cons 0 y)
        refine ⟨q, hq, ?_⟩
        intro t
        convert heq t using 1
        congr 1
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      choose P hP using hslice
      let B (k : ℕ) : MvPolynomial (Fin (m+1)) ℚ :=
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
          (Lagrange.basis (Finset.range (d+1)) (Nat.cast : ℕ → ℚ) k)
      refine ⟨∑ k ∈ Finset.range (d+1), MvPolynomial.rename Fin.succ (P k) * B k, ?_⟩
      intro z
      have hB (k : ℕ) : MvPolynomial.eval (fun i => (z i : ℚ)) (B k) =
          (Lagrange.basis (Finset.range (d+1)) (Nat.cast : ℕ → ℚ) k).eval (z 0 : ℚ) := by
        dsimp only [B]
        rw [Polynomial.hom_eval₂]
        have hc : (MvPolynomial.eval (fun i => (z i : ℚ))).comp MvPolynomial.C =
            RingHom.id ℚ := by ext r; simp
        rw [hc, MvPolynomial.eval_X, Polynomial.eval₂_id]
      have heval : MvPolynomial.eval (fun i => (z i : ℚ))
          (∑ k ∈ Finset.range (d+1), MvPolynomial.rename Fin.succ (P k) * B k) =
          ∑ k ∈ Finset.range (d+1), f (Fin.cons (k : ℤ) (fun i => z i.succ)) *
            (Lagrange.basis (Finset.range (d+1)) (Nat.cast : ℕ → ℚ) k).eval (z 0 : ℚ) := by
        simp only [map_sum, map_mul, MvPolynomial.eval_rename, hB]
        apply Finset.sum_congr rfl
        intro k _
        change MvPolynomial.eval (fun i => (z i.succ : ℚ)) (P k) * _ = _
        rw [hP]
      rw [heval]
      obtain ⟨q, hq, heq⟩ := hline
        (Fin.cons 0 (fun i => z i.succ)) (Fin.cons 1 (fun _ => 0))
      have hqeval (t : ℤ) : f (Fin.cons t (fun i => z i.succ)) = q.eval (t : ℚ) := by
        convert heq t using 1
        congr 1
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      have hz : Fin.cons (z 0) (fun i => z i.succ) = z := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have hfz : f z = q.eval (z 0 : ℚ) := by rw [← hqeval, hz]
      rw [hfz, eval_interpolation d q hq]
      apply Finset.sum_congr rfl
      intro k _
      rw [hqeval]
      simp

/-- If all integer rays have degree at most d, every higher homogeneous
component of the representing multivariate polynomial vanishes. -/
theorem totalDegree_le_of_rays {m d : ℕ} (P : MvPolynomial (Fin m) ℚ)
    (hline : ∀ y : Fin m → ℤ, ∃ q : Polynomial ℚ, q.natDegree ≤ d ∧
      ∀ t : ℤ, MvPolynomial.eval (fun i => ((t * y i : ℤ) : ℚ)) P = q.eval (t : ℚ)) :
    P.totalDegree ≤ d := by
  classical
  by_contra! hdeg
  have htop : MvPolynomial.homogeneousComponent P.totalDegree P = 0 := by
    apply eq_of_integer_evals
    intro y
    obtain ⟨q, hq, heq⟩ := hline y
    have hray : MvPolynomial.eval₂ Polynomial.C
        (fun i => Polynomial.C (y i : ℚ) * Polynomial.X) P = q := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (Set.infinite_range_of_injective (Int.cast_injective (α := ℚ))).mono
      rintro _ ⟨t, rfl⟩
      change Polynomial.eval (t : ℚ) _ = _
      rw [HomogeneousExtraction.ray_eval]
      simpa only [Int.cast_mul] using heq t
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff P.totalDegree) hray
    rw [HomogeneousExtraction.ray_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hq.trans_lt hdeg)] at hc
    simpa only [map_zero] using hc
  have hP : P ≠ 0 := by intro h; simp [h] at hdeg
  have hs : P.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h => hP (MvPolynomial.support_eq_empty.mp h))
  obtain ⟨e, he, hdegree⟩ := Finset.exists_mem_eq_sup P.support hs
    (fun e : Fin m →₀ ℕ => e.sum (fun _ n => n))
  have hed : e.degree = P.totalDegree := hdegree.symm
  have hc := congrArg (MvPolynomial.coeff e) htop
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos hed, MvPolynomial.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp he) hc

/-- Polynomial behavior of uniformly bounded degree on all integer affine
lines implies a multivariate polynomial with that same total-degree bound. -/
theorem exists_polynomial (m d : ℕ) (f : (Fin m → ℤ) → ℚ)
    (hline : ∀ x y : Fin m → ℤ, ∃ q : Polynomial ℚ,
      q.natDegree ≤ d ∧ ∀ t : ℤ, f (fun i => x i + t * y i) = q.eval (t : ℚ)) :
    ∃ P : MvPolynomial (Fin m) ℚ, P.totalDegree ≤ d ∧
      ∀ z : Fin m → ℤ, MvPolynomial.eval (fun i => (z i : ℚ)) P = f z := by
  obtain ⟨P, hP⟩ := exists_polynomial_of_lines m d f hline
  refine ⟨P, totalDegree_le_of_rays P ?_, hP⟩
  intro y
  obtain ⟨q, hq, heq⟩ := hline 0 y
  refine ⟨q, hq, ?_⟩
  intro t
  rw [hP]
  simpa only [Pi.zero_apply, zero_add] using heq t

end IntegerLinePolynomial
end

end


section

set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

theorem bounded_degree_model_of_integer_lines
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hgeometry : ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ f : (Fin m → ℤ) → ℚ,
          (∀ x y : Fin m → ℤ, ∃ q : Polynomial ℚ,
            q.natDegree ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
            ∀ t : ℤ, f (fun j => x j + t * y j) = q.eval (t : ℚ)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) :
    ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ P : MvPolynomial (Fin m) ℚ,
          P.totalDegree ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              MvPolynomial.eval
                (fun j => (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P := by
  obtain ⟨m, α, c, h⟩ := hgeometry
  refine ⟨m, α, c, ?_⟩
  intro V hV
  obtain ⟨f, hline, hdegree⟩ := h V hV
  obtain ⟨P, hP, heval⟩ := IntegerLinePolynomial.exists_polynomial m
    (SectionThree.locusDimension G.ambient (Subtype.val '' V)) f hline
  refine ⟨P, hP, ?_⟩
  intro g D hD
  exact (hdegree g D hD).trans (heval _).symm

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ P : MvPolynomial (Fin m) ℚ,
          P.totalDegree ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              MvPolynomial.eval
                (fun j => (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P := by
  exact bounded_degree_model_of_integer_lines K hK G τ hzero hadd hregular
    (closure_action_has_line_polynomial_degree_model K hK G τ hzero hadd hregular)
