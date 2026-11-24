-- Prove2me | solution 1 for PaleyWeil.split_monic_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:30:56.41511+00:00
-- url     : https://prove2.me/submissions/2740ea49-c18d-420e-9f31-78e91dda0371

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitQuadraticWeight
import Definitions.Def_Sensitivity214439_Phase0_ZetaLean_PrivateStock_FiniteIsMonicOfDegree
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial

section


open Polynomial Finset

namespace PaleyWeil

set_option maxHeartbeats 800000

private theorem sum_weight_zero_of_isolator {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (hK : ringChar K ≠ 2) (s : Finset K) (a : K) (ha : a ∈ s)
    (n : ℕ) (r : K[X]) (hr : r.natDegree < n) (hra : r.eval a ≠ 0)
    (hrb : ∀ b ∈ s.erase a, r.eval b = 0) :
    ∑' P : {P : K[X] // IsMonicOfDegree P n}, splitQuadraticWeight s P = 0 := by
  classical
  letI : Finite {P : K[X] // IsMonicOfDegree P n} := finite_isMonicOfDegree n
  letI : Fintype {P : K[X] // IsMonicOfDegree P n} := Fintype.ofFinite _
  rw [tsum_fintype]
  have hdegree (t : K) : (C t * r).natDegree < n :=
    (natDegree_C_mul_le t r).trans_lt hr
  have hshift (t : K) :
      ∑ P : {P : K[X] // IsMonicOfDegree P n},
        splitQuadraticWeight s ((P : K[X]) + C t * r) =
      ∑ P : {P : K[X] // IsMonicOfDegree P n}, splitQuadraticWeight s P := by
    let e : {P : K[X] // IsMonicOfDegree P n} ≃
        {P : K[X] // IsMonicOfDegree P n} :=
      { toFun := fun P ↦ ⟨(P : K[X]) + C t * r, P.2.add_right (hdegree t)⟩
        invFun := fun P ↦ ⟨(P : K[X]) - C t * r, P.2.sub (hdegree t)⟩
        left_inv := fun P ↦ Subtype.ext (add_sub_cancel_right (P : K[X]) (C t * r))
        right_inv := fun P ↦ Subtype.ext (sub_add_cancel (P : K[X]) (C t * r)) }
    exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  have hpoint (P : {P : K[X] // IsMonicOfDegree P n}) :
      ∑ t : K, splitQuadraticWeight s ((P : K[X]) + C t * r) = 0 := by
    have hform (t : K) :
        splitQuadraticWeight s ((P : K[X]) + C t * r) =
          (quadraticChar K ((-1 : K) ^ (s.card * n)) *
            ∏ b ∈ s.erase a, quadraticChar K ((P : K[X]).eval b)) *
          quadraticChar K ((P : K[X]).eval a + t * r.eval a) := by
      have hothers :
          (∏ b ∈ s.erase a, quadraticChar K (((P : K[X]) + C t * r).eval b)) =
            ∏ b ∈ s.erase a, quadraticChar K ((P : K[X]).eval b) := by
        apply Finset.prod_congr rfl
        intro b hb
        simp [hrb b hb]
      unfold splitQuadraticWeight
      rw [(P.2.add_right (hdegree t)).natDegree_eq, map_mul, map_prod]
      rw [← Finset.prod_erase_mul s _ ha, hothers]
      simp only [eval_add, eval_mul, eval_C]
      ring
    simp_rw [hform]
    rw [← Finset.mul_sum]
    have hzero : ∑ t : K, quadraticChar K ((P : K[X]).eval a + t * r.eval a) = 0 := by
      calc
        _ = ∑ y : K, quadraticChar K y :=
          Fintype.sum_equiv
            ((Equiv.mulRight₀ (r.eval a) hra).trans (Equiv.addLeft ((P : K[X]).eval a)))
            _ _ (fun _ ↦ rfl)
        _ = 0 := quadraticChar_sum_zero hK
    rw [hzero, mul_zero]
  have htotal :
      ∑ t : K, ∑ P : {P : K[X] // IsMonicOfDegree P n},
        splitQuadraticWeight s ((P : K[X]) + C t * r) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun P _ ↦ hpoint P)
  simp_rw [hshift] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htotal
  exact (mul_eq_zero.mp htotal).resolve_left (by exact_mod_cast Fintype.card_ne_zero)





end PaleyWeil

end

open Polynomial Finset
open PaleyWeil
set_option maxHeartbeats 800000

theorem solution {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hK : ringChar K ≠ 2) (s : Finset K) (hs : s.Nonempty) (n : ℕ) (hn : s.card ≤ n) :
    ∑' P : {P : K[X] // IsMonicOfDegree P n}, splitQuadraticWeight s P = 0 := by
  classical
  obtain ⟨a, ha⟩ := hs
  let r : K[X] := ∏ b ∈ s.erase a, (X - C b)
  have hdegree : r.natDegree < n := by
    have hrdeg : r.natDegree = (s.erase a).card := by
      dsimp [r]
      rw [natDegree_prod_of_monic (s.erase a) (fun b ↦ X - C b)]
      · simp
      · intro b _
        exact monic_X_sub_C b
    rw [hrdeg, Finset.card_erase_of_mem ha]
    have hspos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  have heval (y : K) : r.eval y = ∏ b ∈ s.erase a, (y - b) := by
    simp only [r, eval_prod, eval_sub, eval_X, eval_C]
  apply sum_weight_zero_of_isolator hK s a ha n r hdegree
  · rw [heval]
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm
  · intro b hb
    rw [heval]
    exact Finset.prod_eq_zero hb (sub_self b)
