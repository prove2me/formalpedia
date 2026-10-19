-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_weaklyRegular_fin_syzygy_lifts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/102bc904-14a9-4b52-891c-250f015cce75

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_fin_last_mem_span_of_weaklyRegular

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R S : Type*} [CommRing R] [CommRing S]
    (q : R →+* S) (hq : Function.Surjective q) :
    ∀ (n : ℕ) (f : Fin n → R),
      RingTheory.Sequence.IsWeaklyRegular S
        (List.ofFn fun i => q (f i)) →
      ∀ a : Fin n → S,
        (∑ i, a i * q (f i)) = 0 →
          ∃ b : Fin n → R,
            (∀ i, q (b i) = a i) ∧
              (∑ i, b i * f i) = 0 := by
  intro n
  induction n with
  | zero =>
      intro f hregular a hrelation
      refine ⟨Fin.elim0, ?_, ?_⟩
      · exact fun i => Fin.elim0 i
      · simp
  | succ n ih =>
      intro f hregular a hrelation
      have hlist :
          List.ofFn (fun i : Fin (n + 1) => q (f i)) =
            (List.ofFn fun i : Fin n => q (f i.castSucc)) ++
              [q (f (Fin.last n))] :=
        List.ofFn_succ_last
      have hprefix :
          RingTheory.Sequence.IsWeaklyRegular S
            (List.ofFn fun i : Fin n => q (f i.castSucc)) := by
        have hsplit :=
          (RingTheory.Sequence.isWeaklyRegular_append_iff S
            (List.ofFn fun i : Fin n => q (f i.castSucc))
            [q (f (Fin.last n))]).mp
            (hlist ▸ hregular)
        exact hsplit.1
      have hsum :
          (∑ i : Fin n, a i.castSucc * q (f i.castSucc)) +
            a (Fin.last n) * q (f (Fin.last n)) = 0 := by
        simpa [Fin.sum_univ_castSucc] using hrelation
      have hproduct :
          q (f (Fin.last n)) * a (Fin.last n) ∈
            Ideal.span
              (Set.range fun i : Fin n => q (f i.castSucc)) := by
        apply Ideal.mem_span_range_iff_exists_fun.mpr
        refine ⟨fun i => -a i.castSucc, ?_⟩
        calc
          (∑ i : Fin n, -a i.castSucc * q (f i.castSucc)) =
              -(∑ i : Fin n, a i.castSucc * q (f i.castSucc)) := by
                simp
          _ = q (f (Fin.last n)) * a (Fin.last n) := by
                linear_combination -hsum
      have hlast :
          a (Fin.last n) ∈
            Ideal.span
              (Set.range fun i : Fin n => q (f i.castSucc)) :=
        homogeneousMap_allRank_fin_last_mem_span_of_weaklyRegular
          (fun i : Fin (n + 1) => q (f i)) hregular hproduct
      obtain ⟨t, ht⟩ :=
        Ideal.mem_span_range_iff_exists_fun.mp hlast
      choose d hd using fun i : Fin n => hq (t i)
      have hcorrected :
          (∑ i : Fin n,
            (a i.castSucc + t i * q (f (Fin.last n))) *
              q (f i.castSucc)) = 0 := by
        calc
          (∑ i : Fin n,
            (a i.castSucc + t i * q (f (Fin.last n))) *
              q (f i.castSucc)) =
            (∑ i : Fin n, a i.castSucc * q (f i.castSucc)) +
              (∑ i : Fin n, t i * q (f i.castSucc)) *
                q (f (Fin.last n)) := by
                  simp_rw [add_mul]
                  rw [Finset.sum_add_distrib, Finset.sum_mul]
                  congr 1
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
          _ = 0 := by
            rw [ht]
            linear_combination hsum
      obtain ⟨b, hb, hbsum⟩ :=
        ih (fun i : Fin n => f i.castSucc) hprefix
          (fun i : Fin n => a i.castSucc +
            t i * q (f (Fin.last n))) hcorrected
      let blast : R := ∑ i : Fin n, d i * f i.castSucc
      let result : Fin (n + 1) → R :=
        Fin.snoc
          (fun i : Fin n => b i - d i * f (Fin.last n)) blast
      refine ⟨result, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            simp only [result, Fin.snoc_last]
            change q (∑ i : Fin n, d i * f i.castSucc) =
              a (Fin.last n)
            simpa [map_sum, map_mul, hd] using ht
        | cast i =>
            simp only [result, Fin.snoc_castSucc]
            rw [map_sub, map_mul, hb i, hd i]
            ring
      · rw [Fin.sum_univ_castSucc]
        simp only [result, Fin.snoc_castSucc, Fin.snoc_last]
        change
          (∑ i : Fin n,
            (b i - d i * f (Fin.last n)) * f i.castSucc) +
            (∑ i : Fin n, d i * f i.castSucc) *
              f (Fin.last n) = 0
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib, Finset.sum_mul, hbsum]
        simp only [zero_sub]
        have hcomm :
            (∑ i : Fin n,
              d i * f (Fin.last n) * f i.castSucc) =
            ∑ i : Fin n,
              d i * f i.castSucc * f (Fin.last n) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hcomm]
        exact neg_add_cancel _
end PermanentRollout
