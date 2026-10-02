-- Prove2me | solution 1 for PhilipponMultiplicity.exists_quadratic_addition_local_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T18:34:12.003837+00:00
-- url     : https://prove2.me/submissions/dfbeea7e-d8b7-4743-8ddd-b84f914696dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_quadratic_affine_addition_local_cover
import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

section

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

/-- Simultaneous homogenization uses one multidegree for an entire tuple.
On an arbitrary lift in the chart, the whole tuple changes by a single
nonzero scalar, so its projective value is preserved. -/
theorem exists_common_multihomogeneous_chart_lifts
    {ι : Type*} (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hbound : ∀ t, ∀ m ∈ (P t).support, ∀ i,
      (∑ k : Fin (M.ambientDimension i + 1), m ⟨i,k⟩) ≤ D i) :
    ∃ H : ι → M.CoordinateRing, (∀ t, M.IsHomogeneous (H t) D) ∧
      ∀ v : M.Variable → K, (∀ i, v ⟨i,j i⟩ ≠ 0) →
        ∃ c : K, c ≠ 0 ∧ ∀ t,
          MvPolynomial.eval v (H t) = c * MvPolynomial.eval
            (fun z : M.Variable => v z / v ⟨z.1,j z.1⟩) (P t) := by
  classical
  choose H hhom heval using fun t => M.exists_multihomogenization_on_chart
    (P t) D j (hbound t)
  refine ⟨H,hhom,?_⟩
  intro v hv
  let u (z : M.Variable) := v z / v ⟨z.1,j z.1⟩
  have hnorm (i : M.FactorIndex) : u ⟨i,j i⟩ = 1 := div_self (hv i)
  have hcoords : (fun z : M.Variable => v ⟨z.1,j z.1⟩ * u z) = v := by
    funext z
    exact mul_div_cancel₀ (v z) (hv z.1)
  refine ⟨∏ i, v ⟨i,j i⟩ ^ D i,
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hv i)),?_⟩
  intro t
  have hscale := M.eval_block_scale (H t) D (hhom t) u (fun i => v ⟨i,j i⟩)
  rw [hcoords,heval t u hnorm] at hscale
  exact hscale

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
variable {K : Type*} [Field K]

/-- Finitely many polynomials quadratic in the first block have a common
bounding bidegree whose first entry is exactly two. -/
theorem exists_common_bidegree_bound_quadratic_first
    (n : ℕ) {ι : Type*} [Fintype ι]
    (P : ι → (projectiveSquare K n).CoordinateRing)
    (hfirst : ∀ t, ∀ m ∈ (P t).support,
      (∑ k : Fin (n+1), m ⟨(0 : Fin 2),k⟩) ≤ 2) :
    ∃ D : (projectiveSquare K n).FactorIndex → ℕ, D (0 : Fin 2) = 2 ∧
      ∀ t, ∀ m ∈ (P t).support, ∀ i,
        (∑ k : Fin (n+1), m ⟨i,k⟩) ≤ D i := by
  classical
  let B := ∑ t, ∑ m ∈ (P t).support, ∑ k : Fin (n+1), m ⟨(1 : Fin 2),k⟩
  refine ⟨fun i => if i = (0 : Fin 2) then 2 else B,by simp,?_⟩
  intro t m hm i
  fin_cases i
  · simpa using hfirst t m hm
  · change (∑ k : Fin (n+1), m ⟨(1 : Fin 2),k⟩) ≤ B
    have hm' : (∑ k : Fin (n+1), m ⟨(1 : Fin 2),k⟩) ≤
        ∑ a ∈ (P t).support, ∑ k : Fin (n+1), a ⟨(1 : Fin 2),k⟩ :=
      Finset.single_le_sum
        (fun a _ => Nat.zero_le (∑ k : Fin (n+1), a ⟨(1 : Fin 2),k⟩)) hm
    exact hm'.trans (Finset.single_le_sum
      (fun a _ => Nat.zero_le (∑ m ∈ (P a).support,
        ∑ k : Fin (n+1), m ⟨(1 : Fin 2),k⟩)) (Finset.mem_univ t))

end PhilipponMultiplicity

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

/-- Homogenization of affine formulas supplies the common bihomogeneous
degree and preserves their nonzero projective values on the same open set. -/
theorem quadratic_addition_cover_of_affine_formulas
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (hgeometry : ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ c : (projectiveSquare K F.ambientDimension).FactorIndex →
              Fin (F.ambientDimension+1),
          (∀ xy ∈ U, ∀ i : (projectiveSquare K F.ambientDimension).FactorIndex,
            (projectiveSquare K F.ambientDimension).coordinate
              (F.additionPair xy.1 xy.2) ⟨i,c i⟩ ≠ 0) ∧
          ∃ Q : Fin (F.ambientDimension+1) →
            (projectiveSquare K F.ambientDimension).CoordinateRing,
          (∀ t, ∀ m ∈ (Q t).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) ≤ 2) ∧
          ∀ xy ∈ U, ∃ h :
            (fun t => MvPolynomial.eval
              (fun v : (projectiveSquare K F.ambientDimension).Variable =>
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) v /
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
                  ⟨v.1,c v.1⟩) (Q t)) ≠ 0,
            Projectivization.mk K (fun t => MvPolynomial.eval
              (fun v : (projectiveSquare K F.ambientDimension).Variable =>
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) v /
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
                  ⟨v.1,c v.1⟩) (Q t)) h = (xy.1+xy.2).val) :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ D : (projectiveSquare K F.ambientDimension).FactorIndex → ℕ,
          ∃ P : Fin (F.ambientDimension+1) →
            (projectiveSquare K F.ambientDimension).CoordinateRing,
          D (0 : Fin 2) ≤ 2 ∧
          (∀ j, (projectiveSquare K F.ambientDimension).IsHomogeneous (P j) D) ∧
          ∀ xy ∈ U, ∃ h :
            (fun j => (projectiveSquare K F.ambientDimension).eval (P j)
              (F.additionPair xy.1 xy.2)) ≠ 0,
            Projectivization.mk K (fun j => (projectiveSquare K F.ambientDimension).eval
              (P j) (F.additionPair xy.1 xy.2)) h = (xy.1+xy.2).val := by
  classical
  intro E hconnected
  obtain ⟨F,hF,hcharts⟩ := hgeometry E hconnected
  refine ⟨F,hF,?_⟩
  intro x y
  obtain ⟨U,hU,hxy,c,hc,Q,hbound,hrep⟩ := hcharts x y
  obtain ⟨D,hD,hbounds⟩ := exists_common_bidegree_bound_quadratic_first
    F.ambientDimension Q hbound
  obtain ⟨P,hP,hscale⟩ :=
    (projectiveSquare K F.ambientDimension).exists_common_multihomogeneous_chart_lifts
      Q D c hbounds
  refine ⟨U,hU,hxy,D,P,hD.le,hP,?_⟩
  intro xy hxyU
  obtain ⟨a,ha,hvalues⟩ := hscale
    ((projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2))
    (hc xy hxyU)
  obtain ⟨hQ,hQrep⟩ := hrep xy hxyU
  have hPne : (fun t => (projectiveSquare K F.ambientDimension).eval
      (P t) (F.additionPair xy.1 xy.2)) ≠ 0 := by
    intro hz
    apply hQ
    funext t
    have hzt := congrFun hz t
    change MvPolynomial.eval
      ((projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2))
      (P t) = 0 at hzt
    rw [hvalues t] at hzt
    exact (mul_eq_zero.mp hzt).resolve_left ha
  refine ⟨hPne,Eq.trans ?_ hQrep⟩
  apply (Projectivization.mk_eq_mk_iff' K _ _ hPne hQ).mpr
  refine ⟨a,?_⟩
  funext t
  simpa only [Pi.smul_apply,smul_eq_mul,MultiProjectiveSpace.eval] using (hvalues t).symm

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ D : (projectiveSquare K F.ambientDimension).FactorIndex → ℕ,
          ∃ P : Fin (F.ambientDimension+1) →
            (projectiveSquare K F.ambientDimension).CoordinateRing,
          D (0 : Fin 2) ≤ 2 ∧
          (∀ j, (projectiveSquare K F.ambientDimension).IsHomogeneous (P j) D) ∧
          ∀ xy ∈ U, ∃ h :
            (fun j => (projectiveSquare K F.ambientDimension).eval (P j)
              (F.additionPair xy.1 xy.2)) ≠ 0,
            Projectivization.mk K (fun j => (projectiveSquare K F.ambientDimension).eval
              (P j) (F.additionPair xy.1 xy.2)) h = (xy.1+xy.2).val := by
  exact quadratic_addition_cover_of_affine_formulas K
    (exists_quadratic_affine_addition_local_cover K)
