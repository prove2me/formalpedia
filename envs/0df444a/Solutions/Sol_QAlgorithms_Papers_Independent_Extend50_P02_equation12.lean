-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P02.equation12
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:04:20.450793+00:00
-- url     : https://prove2.me/submissions/85968501-9850-4d6e-9a49-2e86cd9ff9c8

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

open scoped Matrix ComplexConjugate ComplexOrder
attribute [local instance] Classical.decEq Classical.propDecidable
open QAlgorithms.Papers.Independent.Extend50.P02
open QAlgorithms (Superop IsChannel)
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

theorem s110_eq12_core {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty B] (W : BiOp A B C D) (M : ExtOp A B C D)
    (hswap : swapExtension M = M)
    (hmarg : ∀ a a' b b' e e' c c' d d',
      (∑ f, M ((a,(b,e)),(c,(d,f))) ((a',(b',e')),(c',(d',f)))) =
        W ((a,b),(c,d)) ((a',b'),(c',d')) * (if e = e' then 1 else 0)) :
    BobToAliceNS W := by
  intro a a' b b' c c'
  set S : B → B → ℂ := fun b b' => ∑ d, W ((a,b),(c,d)) ((a',b'),(c',d)) with hS
  have key : ∀ b b' e e', S b b' * (if e = e' then 1 else 0) = S e e' * (if b = b' then 1 else 0) := by
    intro b b' e e'
    simp only [hS, Finset.sum_mul]
    simp_rw [← hmarg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro d _
    have := congrFun (congrFun hswap ((a,(e,b)),(c,(f,d)))) ((a',(e',b')),(c',(f,d)))
    rw [← this]
    rfl
  have hdiag : ∀ b b' e, S b b' = S e e * (if b = b' then 1 else 0) := by
    intro b b' e
    have := key b b' e e
    simpa using this
  show S b b' = _
  have hsum : ∑ b0, S b0 b0 = (Fintype.card B : ℂ) * S b b := by
    rw [Finset.sum_congr rfl (fun b0 _ => by rw [hdiag b0 b0 b])]
    simp
  have hB : (Fintype.card B : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change S b b' = (if b = b' then 1 else 0) * (Fintype.card B : ℂ)⁻¹ * ∑ b0, S b0 b0
  rw [hsum, hdiag b b' b]
  field_simp

theorem solution {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (N : Superop (A × B) (C × D)) (hN : IsChannel N)
    (hext : HasExtension false false (choi N)) : BobToAliceNS (choi N) := by
  obtain ⟨M, ⟨_, _, hswap, hmarg⟩, _, _⟩ := hext
  exact s110_eq12_core _ M hswap hmarg
