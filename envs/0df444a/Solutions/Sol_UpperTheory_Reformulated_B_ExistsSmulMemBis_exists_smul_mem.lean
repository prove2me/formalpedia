-- Prove2me | solution 1 for UpperTheory.Reformulated.B.ExistsSmulMemBis.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:40.971596+00:00
-- url     : https://prove2.me/submissions/e7355e5a-4fa8-4864-a3a4-1b8910cb2591

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private lemma exists_ne_zero_smul_mem_of_span_eq_top_alt {O LL V : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (h : Submodule.span LL (T : Set V) = ⊤) (v : V) :
    ∃ a : O, a ≠ 0 ∧ a • v ∈ T := by
  have hv : v ∈ Submodule.span LL (T : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact T.smul_mem _ hax
    · rw [mul_smul]; exact T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hd : (d : O) ≠ 0 := nonZeroDivisors.ne_zero d.2
    refine ⟨(d : O) * a, mul_ne_zero hd ha, ?_⟩
    have key : ((d : O) * a) • c • x = n • a • x := by
      have e : ∀ (r : O) (y : V), r • y = (algebraMap O LL r) • y :=
        fun r y => (algebraMap_smul LL r y).symm
      have hnd' : c * algebraMap O LL (d : O) = algebraMap O LL n := hnd
      rw [e ((d : O) * a), e n, e a, smul_smul, smul_smul, map_mul, ← hnd']
      congr 1
      ring
    rw [key]
    exact T.smul_mem _ hax
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ExistsSmulMemBis
theorem _root_.solution :
    ∀ {G : Type} [inst : Group.{0} G] [inst_1 : TopologicalSpace.{0} G] {Qp LL O : Type} [inst_2 : Field.{0} Qp]
      [inst_3 : Field.{0} LL]
      [inst_4 :
        @Algebra.{0, 0} Qp LL (@Semifield.toCommSemiring.{0} Qp (@Field.toSemifield.{0} Qp inst_2))
          (@DivisionSemiring.toSemiring.{0} LL (@Semifield.toDivisionSemiring.{0} LL (@Field.toSemifield.{0} LL inst_3)))]
      [inst_5 : CommRing.{0} O]
      [inst_6 :
        @Algebra.{0, 0} O LL (@CommRing.toCommSemiring.{0} O inst_5)
          (@DivisionSemiring.toSemiring.{0} LL (@Semifield.toDivisionSemiring.{0} LL (@Field.toSemifield.{0} LL inst_3)))]
      [inst_7 : TopologicalSpace.{0} LL]
      (A : @Formalism.MainNotions.N.GRep G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7)
      (LA :
        @Formalism.WeaklyAdmissibleFiltrations.Lattice G inst LL inst_3 O inst_5
          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.modLL G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.ρ G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
      [@IsDomain.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))]
      [@IsFractionRing.{0, 0} O (@CommRing.toCommSemiring.{0} O inst_5) LL
          (@Semifield.toCommSemiring.{0} LL (@Field.toSemifield.{0} LL inst_3)) inst_6]
      (v : @Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A),
      ∃ (a : O),
        And
          (@Ne.{1} O a
            (@OfNat.ofNat.{0} O (nat_lit 0)
              (@Zero.toOfNat0.{0} O
                (@MulZeroClass.toZero.{0} O
                  (@instMulZeroClassOfSemiring.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5)))))))
          (@Membership.mem.{0, 0} (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
            (@Submodule.{0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
              (@AddCommGroup.toAddCommMonoid.{0}
                (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
              (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
                (@AddCommGroup.toAddCommMonoid.{0}
                  (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                  (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
                (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Submodule.setLike.{0, 0} O
                (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
                (@AddCommGroup.toAddCommMonoid.{0}
                  (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                  (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
                (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)))
            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_3 O inst_5
              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.modLL G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.ρ G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A) LA)
            (@HSMul.hSMul.{0, 0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@instHSMul.{0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@SMulZeroClass.toSMul.{0, 0} O
                  (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                  (@AddZero.toZero.{0} (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                    (@AddZeroClass.toAddZero.{0}
                      (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                      (@AddMonoid.toAddZeroClass.{0}
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@SubNegMonoid.toAddMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@AddGroup.toSubNegMonoid.{0}
                            (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                            (@AddCommGroup.toAddGroup.{0}
                              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                              (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)))))))
                  (@DistribSMul.toSMulZeroClass.{0, 0} O
                    (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                    (@AddMonoid.toAddZeroClass.{0}
                      (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                      (@SubNegMonoid.toAddMonoid.{0}
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@AddGroup.toSubNegMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@AddCommGroup.toAddGroup.{0}
                            (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                            (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)))))
                    (@DistribMulAction.toDistribSMul.{0, 0} O
                      (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                      (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5)))
                      (@SubNegMonoid.toAddMonoid.{0}
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@AddGroup.toSubNegMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@AddCommGroup.toAddGroup.{0}
                            (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                            (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))))
                      (@Module.toDistribMulAction.{0, 0} O
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
                        (@AddCommGroup.toAddCommMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
                        (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))))))
              a v)) := by
  intro G _ _ Qp LL O _ _ _ _ _ _ A LA _ _ v
  letI := A.acg
  letI := A.modLL
  letI := A.modO
  haveI := A.towO
  obtain ⟨T, _, _, _, hs⟩ := LA
  exact exists_ne_zero_smul_mem_of_span_eq_top_alt T hs v
end UpperTheory.Reformulated.B.ExistsSmulMemBis
