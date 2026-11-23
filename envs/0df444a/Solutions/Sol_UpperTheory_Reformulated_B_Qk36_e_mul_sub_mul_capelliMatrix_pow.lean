-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk36.e_mul_sub_mul_capelliMatrix_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:03.164821+00:00
-- url     : https://prove2.me/submissions/3f6d7745-4b5f-4bfa-96ca-028166391a09

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qk36.commutator_matrix_pow {R : Type*} [Ring R] {n : Nat}
    (M : Matrix (Fin n) (Fin n) R) (x : R) (a b : Fin n)
    (h : ∀ c d, x * M c d - M c d * x
      = (if b = c then M a d else 0) - (if d = a then M c b else 0))
    (k : Nat) (c d : Fin n) :
    x * (M ^ k) c d - (M ^ k) c d * x
      = (if b = c then (M ^ k) a d else 0) - (if d = a then (M ^ k) c b else 0) := by
  induction k generalizing d with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      sub_self]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, eq_comm (a := a), eq_comm (a := c)]
  | succ k ih =>
    have key : ∀ j, x * ((M ^ k) c j * M j d) - (M ^ k) c j * M j d * x
        = ((if b = c then (M ^ k) a j else 0) - (if j = a then (M ^ k) c b else 0)) * M j d
          + (M ^ k) c j * ((if b = j then M a d else 0) - (if d = a then M j b else 0)) := by
      intro j
      rw [← ih j, ← h j d]
      noncomm_ring
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun j _ => key j)]
    simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;>
      simp only [h1, h2, if_true, if_false, Finset.sum_const_zero] <;> abel
private theorem UpperTheory.Reformulated.B.Qk36.E_comm {n : Nat} (a b c d : Fin n) :
    UpperTheory.Reformulated.B.Qk36.E (a, b) * UpperTheory.Reformulated.B.Qk36.E (c, d)
        - UpperTheory.Reformulated.B.Qk36.E (c, d) * UpperTheory.Reformulated.B.Qk36.E (a, b)
      = (if b = c then UpperTheory.Reformulated.B.Qk36.E (a, d) else 0)
        - (if d = a then UpperTheory.Reformulated.B.Qk36.E (c, b) else 0) := by
  have h : ∀ p q r s : Fin n, UpperTheory.Reformulated.B.Qk36.E (p, q) * UpperTheory.Reformulated.B.Qk36.E (r, s)
      = if q = r then UpperTheory.Reformulated.B.Qk36.E (p, s) else 0 := by
    intro p q r s
    unfold UpperTheory.Reformulated.B.Qk36.E
    split_ifs with hqr
    · subst hqr
      simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ hqr _
  rw [h, h]
private theorem UpperTheory.Reformulated.B.Qk36.e_comm {n : Nat} (a b c d : Fin n) :
    UpperTheory.Reformulated.B.Qk36.e (a, b) * UpperTheory.Reformulated.B.Qk36.e (c, d)
        - UpperTheory.Reformulated.B.Qk36.e (c, d) * UpperTheory.Reformulated.B.Qk36.e (a, b)
      = (if b = c then UpperTheory.Reformulated.B.Qk36.e (a, d) else 0)
        - (if d = a then UpperTheory.Reformulated.B.Qk36.e (c, b) else 0) := by
  letI : LieRing (UpperTheory.Reformulated.B.Qk36.gl n) := LieRing.ofAssociativeRing
  letI : LieRing (UpperTheory.Reformulated.B.Qk36.U n) := LieRing.ofAssociativeRing
  unfold UpperTheory.Reformulated.B.Qk36.e
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie,
    LieRing.of_associative_ring_bracket, UpperTheory.Reformulated.B.Qk36.E_comm, map_sub]
  congr 1 <;> split_ifs <;> first | rfl | exact map_zero _
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk36
theorem _root_.solution :
    ∀ {n : Nat} (a b : Fin n) (k : Nat) (c d : Fin n),
      @Eq (UpperTheory.Reformulated.B.Qk36.U n)
        (@HSub.hSub (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n)
          (@instHSub (UpperTheory.Reformulated.B.Qk36.U n)
            (@SubNegMonoid.toSub (UpperTheory.Reformulated.B.Qk36.U n)
              (@AddGroup.toSubNegMonoid (UpperTheory.Reformulated.B.Qk36.U n)
                (@AddGroupWithOne.toAddGroup (UpperTheory.Reformulated.B.Qk36.U n)
                  (@Ring.toAddGroupWithOne (UpperTheory.Reformulated.B.Qk36.U n)
                    (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                      (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                      (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                        Complex.commRing
                        (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                          (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                          (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))))))
          (@HMul.hMul (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n)
            (@instHMul (UpperTheory.Reformulated.B.Qk36.U n)
              (@Distrib.toMul (UpperTheory.Reformulated.B.Qk36.U n)
                (@instDistribOfSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                  (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                    (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                      (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                      (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                        Complex.commRing
                        (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                          (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                          (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))))
            (@UpperTheory.Reformulated.B.Qk36.e n (@Prod.mk (Fin n) (Fin n) a b))
            (@HPow.hPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
              (@instHPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat
                (@NPow.toPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                  (@Monoid.toNPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                      (@Matrix.semiring (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)
                        (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                          (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing)
                              Complex Complex.commRing
                              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                                (@CommRing.toCommSemiring Complex Complex.commRing)
                                (@Ring.toSemiring Complex Complex.instRing)
                                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Qk36.capelliMatrix n) k c d))
          (@HMul.hMul (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n)
            (@instHMul (UpperTheory.Reformulated.B.Qk36.U n)
              (@Distrib.toMul (UpperTheory.Reformulated.B.Qk36.U n)
                (@instDistribOfSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                  (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                    (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                      (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                      (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                        Complex.commRing
                        (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                          (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                          (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))))
            (@HPow.hPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
              (@instHPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat
                (@NPow.toPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                  (@Monoid.toNPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                      (@Matrix.semiring (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)
                        (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                          (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing)
                              Complex Complex.commRing
                              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                                (@CommRing.toCommSemiring Complex Complex.commRing)
                                (@Ring.toSemiring Complex Complex.instRing)
                                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Qk36.capelliMatrix n) k c d)
            (@UpperTheory.Reformulated.B.Qk36.e n (@Prod.mk (Fin n) (Fin n) a b))))
        (@HSub.hSub (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n)
          (@instHSub (UpperTheory.Reformulated.B.Qk36.U n)
            (@SubNegMonoid.toSub (UpperTheory.Reformulated.B.Qk36.U n)
              (@AddGroup.toSubNegMonoid (UpperTheory.Reformulated.B.Qk36.U n)
                (@AddGroupWithOne.toAddGroup (UpperTheory.Reformulated.B.Qk36.U n)
                  (@Ring.toAddGroupWithOne (UpperTheory.Reformulated.B.Qk36.U n)
                    (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                      (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                      (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                        Complex.commRing
                        (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                          (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                          (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))))))
          (@ite (UpperTheory.Reformulated.B.Qk36.U n) (@Eq (Fin n) b c) (instDecidableEqFin n b c)
            (@HPow.hPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
              (@instHPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat
                (@NPow.toPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                  (@Monoid.toNPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                      (@Matrix.semiring (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)
                        (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                          (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing)
                              Complex Complex.commRing
                              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                                (@CommRing.toCommSemiring Complex Complex.commRing)
                                (@Ring.toSemiring Complex Complex.instRing)
                                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Qk36.capelliMatrix n) k a d)
            (@OfNat.ofNat (UpperTheory.Reformulated.B.Qk36.U n) (nat_lit 0)
              (@Zero.toOfNat0 (UpperTheory.Reformulated.B.Qk36.U n)
                (@MulZeroClass.toZero (UpperTheory.Reformulated.B.Qk36.U n)
                  (@instMulZeroClassOfSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                    (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                      (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                        (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                        (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                          Complex.commRing
                          (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                            (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                            (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))))))
          (@ite (UpperTheory.Reformulated.B.Qk36.U n) (@Eq (Fin n) d a) (instDecidableEqFin n d a)
            (@HPow.hPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
              (@instHPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat
                (@NPow.toPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                  (@Monoid.toNPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                      (@Matrix.semiring (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)
                        (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                          (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing)
                              Complex Complex.commRing
                              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                                (@CommRing.toCommSemiring Complex Complex.commRing)
                                (@Ring.toSemiring Complex Complex.instRing)
                                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Qk36.capelliMatrix n) k c b)
            (@OfNat.ofNat (UpperTheory.Reformulated.B.Qk36.U n) (nat_lit 0)
              (@Zero.toOfNat0 (UpperTheory.Reformulated.B.Qk36.U n)
                (@MulZeroClass.toZero (UpperTheory.Reformulated.B.Qk36.U n)
                  (@instMulZeroClassOfSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                    (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                      (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                        (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                        (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                          Complex.commRing
                          (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                            (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                            (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))))))) := by
  intro n a b k c d
  exact UpperTheory.Reformulated.B.Qk36.commutator_matrix_pow UpperTheory.Reformulated.B.Qk36.capelliMatrix _ a b
    (fun c d => UpperTheory.Reformulated.B.Qk36.e_comm a b c d) k c d
end UpperTheory.Reformulated.B.Qk36
