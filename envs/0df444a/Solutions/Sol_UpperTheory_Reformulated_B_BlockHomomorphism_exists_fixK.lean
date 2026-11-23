-- Prove2me | solution 1 for UpperTheory.Reformulated.B.BlockHomomorphism.exists_fixK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:58.114842+00:00
-- url     : https://prove2.me/submissions/c04e6f9b-26ce-496a-8efb-e99eacf4bb5b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlockHomomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.BlockHomomorphism.continuous_blkAt {k : Type} [Field k] [TopologicalSpace k]
    (n N : ℕ) (h : n ≤ N) : Continuous (UpperTheory.Reformulated.B.BlockHomomorphism.blkAt k n N h) := by
  have h1 : Continuous (UpperTheory.Reformulated.B.BlockHomomorphism.blkGL k n (N - n)) := by
    unfold UpperTheory.Reformulated.B.BlockHomomorphism.blkGL
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin n) (Fin n) k =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin (N - n)) (Fin (N - n)) k))
    exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  have h2 : ∀ {a b : ℕ} (e : a = b), Continuous (UpperTheory.Reformulated.B.BlockHomomorphism.glCongr k e) := by
    intro a b e
    unfold UpperTheory.Reformulated.B.BlockHomomorphism.glCongr
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin a) (Fin a) k =>
      Matrix.reindex (finCongr e) (finCongr e) A
    exact continuous_id.matrix_reindex _ _
  exact (h2 _).comp h1
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.BlockHomomorphism
theorem _root_.solution :
    ∀ {k : Type} [inst : Field k]
      [inst_1 :
        @ValuativeRel k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))]
      [inst_2 : TopologicalSpace k] [@IsNonarchimedeanLocalField k inst inst_1 inst_2] {m N : Nat}
      {h :
        @LE.le Nat instLENat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) N}
      {V : Type} [inst_4 : AddCommGroup V]
      [inst_5 : @_root_.Module Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_4)]
      {π :
        @Representation Complex
          (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
          V Complex.instSemiring
          (@Units.instMonoid (Matrix (Fin N) (Fin N) k)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N))))
          (@AddCommGroup.toAddCommMonoid V inst_4) inst_5},
      @UpperTheory.Reformulated.B.BlockHomomorphism.IsSmooth Complex
          (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
          V Complex.instField
          (@Units.instGroup (Matrix (Fin N) (Fin N) k)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N))))
          inst_4 inst_5
          (@Units.instTopologicalSpaceUnits (Matrix (Fin N) (Fin N) k)
            (@instTopologicalSpaceMatrix (Fin N) (Fin N) k inst_2)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N))))
          π →
        ∀ (v w : V),
          ∃ (K :
            @Subgroup
              (@Matrix.GeneralLinearGroup
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                k
                (instDecidableEqFin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin.fintype
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@Units.instGroup
                (Matrix
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k)
                (@Semiring.toMonoid
                  (Matrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k)
                  (@Matrix.semiring
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))),
            And
              (@IsOpen
                (@Matrix.GeneralLinearGroup
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k
                  (instDecidableEqFin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin.fintype
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (@Units.instTopologicalSpaceUnits
                  (Matrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k)
                  (@instTopologicalSpaceMatrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k inst_2)
                  (@Semiring.toMonoid
                    (Matrix
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k)
                    (@Matrix.semiring
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (@SetLike.coe
                  (@Subgroup
                    (@Matrix.GeneralLinearGroup
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@Units.instGroup
                      (Matrix
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        k)
                      (@Semiring.toMonoid
                        (Matrix
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k)
                        (@Matrix.semiring
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                          (Fin.fintype
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (instDecidableEqFin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  (@Matrix.GeneralLinearGroup
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k
                    (instDecidableEqFin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                  (@Subgroup.instSetLike
                    (@Matrix.GeneralLinearGroup
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@Units.instGroup
                      (Matrix
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        k)
                      (@Semiring.toMonoid
                        (Matrix
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k)
                        (@Matrix.semiring
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                          (Fin.fintype
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (instDecidableEqFin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  K))
              (And
                (@UpperTheory.Reformulated.B.BlockHomomorphism.FixK k inst m N
                  (@Decidable.byContradiction
                    (@LE.le Nat instLENat
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      N)
                    ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).decLe
                      N)
                    fun
                      (a :
                        Not
                          (@LE.le Nat instLENat
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            N)) ↦
                    @UpperTheory.Reformulated.B.BlockHomomorphism.aux9 m N h a)
                  V inst_4 inst_5 π K v)
                (@UpperTheory.Reformulated.B.BlockHomomorphism.FixK k inst m N
                  (@Decidable.byContradiction
                    (@LE.le Nat instLENat
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      N)
                    ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).decLe
                      N)
                    fun
                      (a :
                        Not
                          (@LE.le Nat instLENat
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            N)) ↦
                    @UpperTheory.Reformulated.B.BlockHomomorphism.aux9 m N h a)
                  V inst_4 inst_5 π K w)) := by
  intro k _ _ _ _ m N h V _ _ π hπ v w
  have hle : m + 1 ≤ N := by omega
  refine ⟨(UpperTheory.Reformulated.B.BlockHomomorphism.fixer π v ⊓ UpperTheory.Reformulated.B.BlockHomomorphism.fixer π w).comap
    (UpperTheory.Reformulated.B.BlockHomomorphism.blkAt k (m + 1) N hle), ?_, fun g hg => hg.1, fun g hg => hg.2⟩
  exact ((hπ v).inter (hπ w)).preimage (UpperTheory.Reformulated.B.BlockHomomorphism.continuous_blkAt (m + 1) N hle)
end UpperTheory.Reformulated.B.BlockHomomorphism
