-- Prove2me | solution 1 for PhilipponMultiplicity.exists_quadratic_affine_addition_local_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T21:29:31.561323+00:00
-- url     : https://prove2.me/submissions/3c28b241-3bc5-4cbf-8396-ad9f3ed3f910
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_quadratic_addition_local_fractions
import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.ParameterFractions
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Multiplication adds bounds on the degree in one chosen block. -/
theorem block_degree_le_mul (i : M.FactorIndex) (d e : ℕ)
    (P Q : M.CoordinateRing)
    (hP : ∀ a ∈ P.support, (∑ j, a ⟨i,j⟩) ≤ d)
    (hQ : ∀ a ∈ Q.support, (∑ j, a ⟨i,j⟩) ≤ e) :
    ∀ a ∈ (P * Q).support, (∑ j, a ⟨i,j⟩) ≤ d + e := by
  classical
  intro a ha
  obtain ⟨b,hb,c,hc,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q ha)
  simpa only [Finsupp.add_apply,Finset.sum_add_distrib] using
    Nat.add_le_add (hP b hb) (hQ c hc)

/-- Taking a finite sum preserves a common block-degree bound. -/
theorem block_degree_le_sum {ι : Type*} (s : Finset ι) (i : M.FactorIndex)
    (d : ℕ) (P : ι → M.CoordinateRing)
    (hP : ∀ t ∈ s, ∀ a ∈ (P t).support, (∑ j, a ⟨i,j⟩) ≤ d) :
    ∀ a ∈ (∑ t ∈ s, P t).support, (∑ j, a ⟨i,j⟩) ≤ d := by
  classical
  intro a ha
  obtain ⟨t,ht,hat⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ha)
  exact hP t ht a hat

/-- Products of parameter polynomials introduce no degree in the other block. -/
theorem block_degree_zero_prod {ι : Type*} (s : Finset ι) (i : M.FactorIndex)
    (B : ι → M.CoordinateRing)
    (hB : ∀ t ∈ s, ∀ a ∈ (B t).support, (∑ j, a ⟨i,j⟩) ≤ 0) :
    ∀ a ∈ (∏ t ∈ s, B t).support, (∑ j, a ⟨i,j⟩) ≤ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro a ha
      have ha0 : a = 0 := by simpa using ha
      simp [ha0]
  | @insert t s ht ih =>
      rw [Finset.prod_insert ht]
      simpa only [zero_add] using block_degree_le_mul M i 0 0 (B t)
        (∏ u ∈ s, B u) (hB t (Finset.mem_insert_self t s))
        (ih (fun u hu => hB u (Finset.mem_insert_of_mem hu)))

/-- Clearing one summand by the product of all other denominators. -/
theorem eval_mul_other_denominators {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : M.CoordinateRing) (B : ι → M.CoordinateRing)
    (v : M.Variable → K) (t : ι) (ht : MvPolynomial.eval v (B t) ≠ 0) :
    MvPolynomial.eval v (A * ∏ a ∈ Finset.univ.erase t, B a) =
      (∏ a, MvPolynomial.eval v (B a)) *
        (MvPolynomial.eval v A / MvPolynomial.eval v (B t)) := by
  simp only [map_mul,map_prod]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun a => MvPolynomial.eval v (B a)) (Finset.mem_univ t)]
  field_simp

/-- A finite tuple of finite sums of fractions admits one nonzero common
multiplier at every point where the denominators do not vanish. If those
denominators have block degree zero, clearing them preserves the numerator
bound in that block. -/
theorem exists_cleared_parameter_fractions {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i : M.FactorIndex) (d : ℕ) (A B : ι → κ → M.CoordinateRing)
    (hA : ∀ t a, ∀ m ∈ (A t a).support, (∑ j, m ⟨i,j⟩) ≤ d)
    (hB : ∀ t a, ∀ m ∈ (B t a).support, (∑ j, m ⟨i,j⟩) ≤ 0) :
    ∃ P : ι → M.CoordinateRing,
      (∀ t, ∀ m ∈ (P t).support, (∑ j, m ⟨i,j⟩) ≤ d) ∧
      ∀ v : M.Variable → K, (∀ t a, MvPolynomial.eval v (B t a) ≠ 0) →
        ∃ c : K, c ≠ 0 ∧ ∀ t,
          MvPolynomial.eval v (P t) =
            c * ∑ a, MvPolynomial.eval v (A t a) / MvPolynomial.eval v (B t a) := by
  classical
  let P (t : ι) : M.CoordinateRing :=
    ∑ a : κ, A t a * ∏ p ∈ Finset.univ.erase (t,a), B p.1 p.2
  refine ⟨P,?_,?_⟩
  · intro t
    apply block_degree_le_sum M Finset.univ i d
    intro a _
    simpa only [add_zero] using block_degree_le_mul M i d 0 (A t a)
      (∏ p ∈ Finset.univ.erase (t,a), B p.1 p.2) (hA t a)
      (block_degree_zero_prod M (Finset.univ.erase (t,a)) i
        (fun p : ι × κ => B p.1 p.2) (fun p _ => hB p.1 p.2))
  · intro v hBv
    refine ⟨∏ p : ι × κ, MvPolynomial.eval v (B p.1 p.2),
      Finset.prod_ne_zero_iff.mpr (fun p _ => hBv p.1 p.2),?_⟩
    intro t
    simp only [P,map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact eval_mul_other_denominators M (A t a) (fun p : ι × κ => B p.1 p.2)
      v (t,a) (hBv t a)

end PhilipponMultiplicity.ParameterFractions
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

/-- Clear all parameter denominators with one common nonzero multiplier.
The first-block bound, projective values, charts, and reembedding are preserved. -/
theorem quadratic_affine_addition_of_parameter_fractions
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
          ∃ (r : ℕ) (A B : Fin (F.ambientDimension+1) → Fin r →
              (projectiveSquare K F.ambientDimension).CoordinateRing),
          (∀ t a, ∀ m ∈ (A t a).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) ≤ 2) ∧
          (∀ t a, ∀ m ∈ (B t a).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) = 0) ∧
          ∀ xy ∈ U,
            let v : (projectiveSquare K F.ambientDimension).Variable → K :=
              fun w =>
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) w /
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
                  ⟨w.1,c w.1⟩
            (∀ t a, MvPolynomial.eval v (B t a) ≠ 0) ∧
            ∃ h : (fun t => ∑ a, MvPolynomial.eval v (A t a) /
                MvPolynomial.eval v (B t a)) ≠ 0,
              Projectivization.mk K (fun t => ∑ a, MvPolynomial.eval v (A t a) /
                MvPolynomial.eval v (B t a)) h = (xy.1+xy.2).val) :
    ∀ (E : EmbeddedCommutativeGroup K),
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
                  ⟨v.1,c v.1⟩) (Q t)) h = (xy.1+xy.2).val := by
  classical
  intro E hconnected
  obtain ⟨F,hF,hcharts⟩ := hgeometry E hconnected
  refine ⟨F,hF,?_⟩
  intro x y
  obtain ⟨U,hU,hxy,c,hc,r,A,B,hA,hB,hrep⟩ := hcharts x y
  obtain ⟨Q,hQbound,hclear⟩ :=
    ParameterFractions.exists_cleared_parameter_fractions
      (projectiveSquare K F.ambientDimension) (0 : Fin 2) 2 A B hA
      (fun t a m hm => (hB t a m hm).le)
  refine ⟨U,hU,hxy,c,hc,Q,hQbound,?_⟩
  intro xy hxyU
  let v : (projectiveSquare K F.ambientDimension).Variable → K :=
    fun w =>
      (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) w /
      (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
        ⟨w.1,c w.1⟩
  obtain ⟨hBne,hAne,hArep⟩ := hrep xy hxyU
  obtain ⟨d,hd,hvalues⟩ := hclear v hBne
  have hQne : (fun t => MvPolynomial.eval v (Q t)) ≠ 0 := by
    intro hz
    apply hAne
    funext t
    have hzt := congrFun hz t
    change MvPolynomial.eval v (Q t) = 0 at hzt
    rw [hvalues t] at hzt
    exact (mul_eq_zero.mp hzt).resolve_left hd
  refine ⟨hQne,Eq.trans ?_ hArep⟩
  apply (Projectivization.mk_eq_mk_iff' K _ _ hQne hAne).mpr
  refine ⟨d,?_⟩
  funext t
  simpa only [Pi.smul_apply,smul_eq_mul] using (hvalues t).symm

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
                  ⟨v.1,c v.1⟩) (Q t)) h = (xy.1+xy.2).val := by
  exact quadratic_affine_addition_of_parameter_fractions K
    (exists_quadratic_addition_local_fractions K)
