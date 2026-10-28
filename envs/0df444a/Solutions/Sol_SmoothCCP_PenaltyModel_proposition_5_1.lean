-- Prove2me | solution 1 for SmoothCCP.PenaltyModel.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:01:56.160317+00:00
-- url     : https://prove2.me/submissions/d8bfe5d9-9d6a-404f-b3de-5eb68cb61331

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

open Filter Topology

namespace Aux_SCCP51
open SmoothCCP.PenaltyModel SmoothCCP.Feasibility

lemma B_nonneg (a b : ℝ) :
    0 ≤ (a^4 + a^3*b + a^2*b^2 + a*b^3 + b^4)/5 - 2*(a^2 + a*b + b^2)/3 + 1 := by
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (a - b), sq_nonneg (a + b),
    sq_nonneg (a*b - 1), sq_nonneg (a^2 + b^2 - 2), sq_nonneg (a^2 - b^2), sq_nonneg (a*b + 1),
    sq_nonneg (a^2 + a*b + b^2 - 3/2)]

lemma qanti (ε : ℝ) (he : 0 < ε) : Antitone (quarticGamma ε) := by
  intro y1 y2 h
  have key : quarticGamma ε y1 - quarticGamma ε y2 = 15 / 16 * (y2 / ε - y1 / ε) *
      (((y1/ε)^4 + (y1/ε)^3*(y2/ε) + (y1/ε)^2*(y2/ε)^2 + (y1/ε)*(y2/ε)^3 + (y2/ε)^4)/5
        - 2*((y1/ε)^2 + (y1/ε)*(y2/ε) + (y2/ε)^2)/3 + 1) := by
    unfold quarticGamma; ring
  have hB := B_nonneg (y1/ε) (y2/ε)
  have h1 : 0 ≤ y2 / ε - y1 / ε := by
    rw [← sub_div]; exact div_nonneg (by linarith) he.le
  have : 0 ≤ quarticGamma ε y1 - quarticGamma ε y2 := by
    rw [key]; positivity
  linarith

lemma q_neg (ε : ℝ) (he : 0 < ε) : quarticGamma ε (-ε) = 1 := by
  unfold quarticGamma
  rw [neg_div, div_self he.ne']
  norm_num

lemma q_pos (ε : ℝ) (he : 0 < ε) : quarticGamma ε ε = 0 := by
  unfold quarticGamma
  rw [div_self he.ne']
  norm_num

lemma Gam_anti (ε : ℝ) (he : 0 < ε) : Antitone (Gam ε (quarticGamma ε)) := by
  intro y1 y2 h
  have qa := qanti ε he
  unfold Gam
  split_ifs <;> first
    | (exfalso; linarith)
    | exact le_refl _
    | exact qa h
    | (have := qa (show -ε ≤ y2 by linarith); rw [q_neg ε he] at this; exact this)
    | (have := qa (show y1 ≤ ε by linarith); rw [q_pos ε he] at this; exact this)
    | (norm_num; done)

lemma Gam_val0 (ε : ℝ) (y : ℝ) (hy : ε ≤ y) (he : 0 < ε) : Gam ε (quarticGamma ε) y = 0 := by
  unfold Gam
  rw [if_neg (by linarith), if_neg (by linarith)]

lemma Gam_val1 (ε : ℝ) (y : ℝ) (hy : y ≤ -ε) : Gam ε (quarticGamma ε) y = 1 := by
  unfold Gam
  rw [if_pos hy]

lemma sq_mono (ε α : ℝ) (he : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1) {N : ℕ} (hN : 1 ≤ N) (z z' : Fin N → ℝ)
    (hz : ∀ i, z i ≤ z' i) :
    smoothQuantile ε (quarticGamma ε) α z ≤ smoothQuantile ε (quarticGamma ε) α z' := by
  unfold smoothQuantile
  have hNpos : (0 : ℝ) < (1 - α) * N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  apply csInf_le_csInf
  · refine ⟨-(∑ i, |z i|) - ε, fun q hq => ?_⟩
    by_contra hlt
    push_neg at hlt
    have h0 : ∀ i, Gam ε (quarticGamma ε) (z i - q) = 0 := by
      intro i
      apply Gam_val0 ε _ _ he
      have : |z i| ≤ ∑ j, |z j| :=
        Finset.single_le_sum (f := fun j => |z j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      have := neg_abs_le (z i)
      linarith
    have hq : (1 - α) * N ≤ ∑ i, Gam ε (quarticGamma ε) (z i - q) := hq
    simp only [h0, Finset.sum_const_zero] at hq
    linarith
  · refine ⟨∑ i, |z' i| + ε, ?_⟩
    show (1 - α) * N ≤ ∑ i, Gam ε (quarticGamma ε) (z' i - (∑ i, |z' i| + ε))
    have h1 : ∀ i, Gam ε (quarticGamma ε) (z' i - (∑ i, |z' i| + ε)) = 1 := by
      intro i
      apply Gam_val1
      have : |z' i| ≤ ∑ j, |z' j| :=
        Finset.single_le_sum (f := fun j => |z' j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      have := le_abs_self (z' i)
      linarith
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  · intro q hq
    have hq' : (1 - α) * N ≤ ∑ i, Gam ε (quarticGamma ε) (z' i - q) := hq
    show (1 - α) * N ≤ ∑ i, Gam ε (quarticGamma ε) (z i - q)
    refine le_trans hq' (Finset.sum_le_sum (fun i _ => Gam_anti ε he ?_))
    linarith [hz i]

end Aux_SCCP51

open SmoothCCP.PenaltyModel in
theorem solution {n m p N : ℕ} {Ξ : Type} (hm : 1 ≤ m) (hN : 1 ≤ N) (ξs : Fin N → Ξ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ)
    (ε α : ℝ) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1) (hαN : ∀ k : ℤ, (1 - α) * N ≠ k)
    (hg : ∀ k, Differentiable ℝ (g k))
    (xstar : EuclideanSpace ℝ (Fin n))
    (hfeas : (∀ k, g k xstar ≤ 0) ∧ smoothQuantile ε (quarticGamma ε) α (CN hm c ξs xstar) ≤ 0)
    (hmin : IsLocalMinOn f
      {x | (∀ k, g k x ≤ 0) ∧ smoothQuantile ε (quarticGamma ε) α (CN hm c ξs x) ≤ 0} xstar) :
    (xstar, CN hm c ξs xstar) ∈
        {q : EuclideanSpace ℝ (Fin n) × (Fin N → ℝ) | (∀ k, g k q.1 ≤ 0) ∧
          (∀ i j, c j q.1 (ξs i) ≤ q.2 i) ∧ smoothQuantile ε (quarticGamma ε) α q.2 ≤ 0} ∧
    IsLocalMinOn (fun q : EuclideanSpace ℝ (Fin n) × (Fin N → ℝ) => f q.1)
      {q | (∀ k, g k q.1 ≤ 0) ∧ (∀ i j, c j q.1 (ξs i) ≤ q.2 i) ∧
        smoothQuantile ε (quarticGamma ε) α q.2 ≤ 0}
      (xstar, CN hm c ξs xstar) := by
  refine ⟨⟨hfeas.1, fun i j => ?_, hfeas.2⟩, ?_⟩
  · unfold CN
    exact Finset.le_sup' (fun j => c j xstar (ξs i)) (Finset.mem_univ j)
  · have hmaps : Set.MapsTo Prod.fst
        {q : EuclideanSpace ℝ (Fin n) × (Fin N → ℝ) | (∀ k, g k q.1 ≤ 0) ∧
          (∀ i j, c j q.1 (ξs i) ≤ q.2 i) ∧ smoothQuantile ε (quarticGamma ε) α q.2 ≤ 0}
        {x | (∀ k, g k x ≤ 0) ∧ smoothQuantile ε (quarticGamma ε) α (CN hm c ξs x) ≤ 0} := by
      rintro ⟨x, z⟩ ⟨h1, h2, h3⟩
      refine ⟨h1, le_trans (Aux_SCCP51.sq_mono ε α hε hα0 hα1 hN _ _ (fun i => ?_)) h3⟩
      unfold CN
      exact Finset.sup'_le _ _ (fun j _ => h2 i j)
    have ht := continuous_fst.continuousWithinAt.tendsto_nhdsWithin hmaps
      (x := (xstar, CN hm c ξs xstar))
    exact ht.eventually hmin
