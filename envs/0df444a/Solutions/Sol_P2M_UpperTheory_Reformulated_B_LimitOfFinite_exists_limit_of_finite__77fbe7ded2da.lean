-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_LimitOfFinite_exists_limit_of_finite__77fbe7ded2da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:17:44.18408+00:00
-- url     : https://prove2.me/submissions/295b7d1c-1be0-42ea-a9b5-884c243de404

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LimitOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.LimitOfFinite.aux {A : Type*} {M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (I : Ideal A) (hI : IsPrecomplete I A) (f : ℕ → M)
    (hf : ∀ m, f m - f (m + 1) ∈ (I ^ m • ⊤ : Submodule A M)) :
    ∃ L : M, ∀ m, f m - L ∈ (I ^ m • ⊤ : Submodule A M) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have key : ∀ (J : Ideal A) (x : M), x ∈ (J • ⊤ : Submodule A M) →
      ∃ d : Fin n → A, (∀ i, d i ∈ J) ∧ ∑ i, d i • s i = x := by
    intro J x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      have hy : y ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
      refine ⟨fun i => r * c i, fun i => J.mul_mem_right _ hr, ?_⟩
      rw [← hc, Finset.smul_sum]
      simp [mul_smul]
    · rintro x y ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
      refine ⟨fun i => d i + e i, fun i => J.add_mem (hd i) (he i), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
  choose d hd hdf using fun m => key (I ^ m) _ (hf m)
  let g : ℕ → Fin n → A := fun m i => ∑ k ∈ Finset.range m, d k i
  have hg : ∀ m, f m = f 0 - ∑ i, g m i • s i := by
    intro m
    induction m with
    | zero => simp [g]
    | succ m ih =>
      have h1 : ∑ i, g (m + 1) i • s i = ∑ i, g m i • s i + ∑ i, d m i • s i := by
        simp [g, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib]
      rw [h1, hdf m, ← sub_sub, ← ih]
      abel
  have hc : ∀ i, ∀ m k, m ≤ k → g m i - g k i ∈ I ^ m := by
    intro i m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have h1 : g m i - g (k + 1) i = g m i - g k i - d k i := by
        simp only [g, Finset.sum_range_succ]; ring
      rw [h1]
      exact (I ^ m).sub_mem ih (Ideal.pow_le_pow_right hmk (hd k i))
  have hl : ∀ i, ∃ a : A, ∀ m, g m i - a ∈ I ^ m := by
    intro i
    obtain ⟨a, ha⟩ := hI.prec (f := fun m => g m i) (by
      intro m k hmk
      rw [SModEq.sub_mem]
      simpa using hc i m k hmk)
    refine ⟨a, fun m => ?_⟩
    have := ha m
    rw [SModEq.sub_mem] at this
    simpa using this
  choose a ha using hl
  refine ⟨f 0 - ∑ i, a i • s i, fun m => ?_⟩
  have h2 : f m - (f 0 - ∑ i, a i • s i) = -∑ i, (g m i - a i) • s i := by
    rw [hg m]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [h2]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem_smul (ha i m) Submodule.mem_top)
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite
theorem _root_.solution.{u_1, u_2} :
    ∀ {A : Type u_1} {M : Type u_2} [inst : CommRing A] [inst_1 : AddCommGroup M]
      [inst_2 :
        @_root_.Module A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
          (@AddCommGroup.toAddCommMonoid M inst_1)]
      [@Module.Finite A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
          (@AddCommGroup.toAddCommMonoid M inst_1) inst_2]
      (I : @Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))),
      @IsPrecomplete A inst I A (@Ring.toAddCommGroup A (@CommRing.toRing A inst))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) →
        ∀ (f : Nat → M),
          (∀ (m : Nat),
              @Membership.mem M
                (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                  (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                (@SetLike.instMembership
                  (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  M
                  (@Submodule.setLike A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2))
                (@HSMul.hSMul (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  (@instHSMul (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    (@Submodule.instSMul A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) A
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) M
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                      (@IsScalarTower.left A M
                        (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@DistribMulAction.toMulAction A M
                          (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_1))
                          (@Module.toDistribMulAction A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))))
                  (@HPow.hPow (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) Nat
                    (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@instHPow (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) Nat
                      (@Submodule.instPowNat A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) A
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@IsScalarTower.right A A (@CommRing.toCommSemiring A inst)
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                          (@Algebra.id A (@CommRing.toCommSemiring A inst)))))
                    I m)
                  (@Top.top
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    (@Submodule.instTop A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))
                (@HSub.hSub M M M
                  (@instHSub M (@SubNegMonoid.toSub M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))
                  (f m)
                  (f
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
            ∃ (L : M),
              ∀ (m : Nat),
                @Membership.mem M
                  (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  (@SetLike.instMembership
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    M
                    (@Submodule.setLike A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2))
                  (@HSMul.hSMul (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    (@instHSMul (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                      (@Submodule.instSMul A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) A
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) M
                        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                        (@IsScalarTower.left A M
                          (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@DistribMulAction.toMulAction A M
                            (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                            (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_1))
                            (@Module.toDistribMulAction A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                              (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))))
                    (@HPow.hPow (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) Nat
                      (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@instHPow (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) Nat
                        (@Submodule.instPowNat A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) A
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@IsScalarTower.right A A (@CommRing.toCommSemiring A inst)
                            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                            (@Algebra.id A (@CommRing.toCommSemiring A inst)))))
                      I m)
                    (@Top.top
                      (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                      (@Submodule.instTop A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))
                  (@HSub.hSub M M M
                    (@instHSub M (@SubNegMonoid.toSub M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))
                    (f m) L) := by
  intro A M _ _ _ _ I hI f hf
  exact UpperTheory.Reformulated.B.LimitOfFinite.aux I hI f hf
end UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite
