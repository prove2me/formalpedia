-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P47.hardy_ratio_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:01:58.953233+00:00
-- url     : https://prove2.me/submissions/f121e717-5336-4125-bb82-0f638c76a9dc

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

open scoped ComplexConjugate

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P47 in
theorem solution (p : Behavior) (w : PairLaw)
    (hp : IsBehavior p) (hw : IsPairLaw w) (hwpos : ∀ A B, 0 < w A B)
    (hh1 : 0 < hardyStatistics p 0)
    (hsigma : 0 < aliceMass p w false) :
    aliceMass p w false = hardyStatistics p 0 * w false false -
      hardyStatistics p 2 * w false true ∧
    ∀ p2 : Behavior, IsBehavior p2 → hardyStatistics p2 = hardyStatistics p →
      aliceMass p2 w false = aliceMass p w false ∧
      0 < siftingProbability p2 w ∧
      (aliceMarginal (acceptedLaw p w) false ≤ aliceMarginal (acceptedLaw p2 w) false ↔
        aliceMass p2 w true ≤ aliceMass p w true) ∧
      (aliceMarginal (acceptedLaw p w) true ≤ aliceMarginal (acceptedLaw p2 w) true ↔
        aliceMass p w true ≤ aliceMass p2 w true) := by
  have hsplit : ∀ q : Behavior, siftingProbability q w = aliceMass q w false + aliceMass q w true := by
    intro q
    unfold siftingProbability aliceMass
    rw [Fintype.sum_bool (fun A => ∑ B, acceptedMass q w A B)]
    ring
  have hmarg : ∀ (q : Behavior) (A : Bool),
      aliceMarginal (acceptedLaw q w) A = aliceMass q w A / siftingProbability q w := by
    intro q A
    simp only [aliceMarginal, acceptedLaw, aliceMass, Finset.sum_div]
  have hm0 : ∀ q : Behavior, aliceMass q w false =
      w false true * q false true false false + w false false * q false false false false := by
    intro q
    simp only [aliceMass, acceptedMass, Fintype.sum_bool]
  have hnn : ∀ q : Behavior, IsBehavior q → 0 ≤ aliceMass q w true := by
    intro q hq
    unfold aliceMass acceptedMass
    exact Finset.sum_nonneg (fun B _ => mul_nonneg (hwpos _ _).le (hq.1 _ _ _ _))
  have h0 : hardyStatistics p 0 = p false false false false := rfl
  have h2 : hardyStatistics p 2 = -p false true false false := rfl
  refine ⟨?_, ?_⟩
  · rw [hm0, h0, h2]
    ring
  · intro p2 hp2 hH
    have e0 : p2 false false false false = p false false false false := congrFun hH 0
    have e2 : -p2 false true false false = -p false true false false := congrFun hH 2
    have e2' : p2 false true false false = p false true false false := neg_inj.1 e2
    have hmeq : aliceMass p2 w false = aliceMass p w false := by
      rw [hm0, hm0, e0, e2']
    have ht := hnn p (hp)
    have ht2 := hnn p2 hp2
    have hpos1 : 0 < aliceMass p w false + aliceMass p w true := by linarith
    have hpos2 : 0 < aliceMass p w false + aliceMass p2 w true := by linarith
    refine ⟨hmeq, ?_, ?_, ?_⟩
    · rw [hsplit, hmeq]
      linarith
    · rw [hmarg, hmarg, hsplit p, hsplit p2, hmeq,
        div_le_div_iff₀ hpos1 hpos2]
      constructor
      · intro h
        nlinarith
      · intro h
        nlinarith
    · rw [hmarg, hmarg, hsplit p, hsplit p2, hmeq,
        div_le_div_iff₀ hpos1 hpos2]
      constructor
      · intro h
        nlinarith
      · intro h
        nlinarith
