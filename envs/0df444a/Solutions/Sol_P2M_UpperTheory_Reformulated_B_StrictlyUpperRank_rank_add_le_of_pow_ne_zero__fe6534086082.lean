-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_StrictlyUpperRank_rank_add_le_of_pow_ne_zero__fe6534086082
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:15:08.26449+00:00
-- url     : https://prove2.me/submissions/443b7b5a-3883-4abe-a557-69ca37a69bd8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StrictlyUpperRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.StrictlyUpperRank.rank_add_le_of_pow_ne_zero
theorem _root_.solution.{u_1, u_2} :
    ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_1 : Fintype n] [inst_2 : LinearOrder n] {X : Matrix n n 𝕜},
      @UpperTheory.Reformulated.B.StrictlyUpperRank.IsStrictUpper 𝕜 inst n inst_2 X →
        ∀ (k : Nat) (i j : n),
          @Ne 𝕜
              (@HPow.hPow (Matrix n n 𝕜) Nat (Matrix n n 𝕜)
                (@instHPow (Matrix n n 𝕜) Nat
                  (@NPow.toPow (Matrix n n 𝕜)
                    (@Monoid.toNPow (Matrix n n 𝕜)
                      (@Semiring.toMonoid (Matrix n n 𝕜)
                        (@Matrix.semiring n 𝕜
                          (@DivisionSemiring.toSemiring 𝕜
                            (@Semifield.toDivisionSemiring 𝕜
                              (@Field.toSemifield 𝕜
                                (@NormedField.toField 𝕜
                                  (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst))))))
                          inst_1 fun (a b : n) ↦ @LinearOrder.toDecidableEq n inst_2 a b)))))
                X k i j)
              (@OfNat.ofNat 𝕜 (nat_lit 0)
                (@Zero.toOfNat0 𝕜
                  (@MulZeroClass.toZero 𝕜
                    (@instMulZeroClassOfSemiring 𝕜
                      (@DivisionSemiring.toSemiring 𝕜
                        (@Semifield.toDivisionSemiring 𝕜
                          (@Field.toSemifield 𝕜
                            (@NormedField.toField 𝕜
                              (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst)))))))))) →
            @LE.le Nat instLENat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 i) k)
              (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 j) := by
  intro 𝕜 _ n _ _ X hX k
  induction k with
  | zero =>
    intro i j h
    have hij : i = j := by
      by_contra hne
      exact h (by rw [pow_zero]; exact Matrix.one_apply_ne hne)
    subst hij
    exact le_rfl
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih i l (left_ne_zero_of_mul hl)
    have hlj : l < j := by
      by_contra hle
      exact right_ne_zero_of_mul hl (hX l j (not_lt.mp hle))
    have h2 : UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow l < UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow j := by
      unfold UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans hlj
      · have hm := @hsub l (by simpa using hlj)
        simp at hm
    omega
end UpperTheory.Reformulated.B.StrictlyUpperRank.rank_add_le_of_pow_ne_zero
