-- Prove2me | solution 1 for ObjectCentric.mechanism_rank_eq_slot_dim
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:46:33.353655+00:00
-- url     : https://prove2.me/submissions/5303a6c3-f804-4f69-b593-a56213d7e0f6

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

lemma oc_inj {K M N : ℕ} (X : Set (Obs N)) (f : Lat K M → Obs N) (g : Obs N → Lat K M)
    (hf : IsDiffeoWithInv f g X) (z : Lat K M) : Function.Injective (fderiv ℝ f z) := by
  obtain ⟨hfc, hgc, hr, hgf⟩ := hf
  have hfd : HasFDerivAt f (fderiv ℝ f z) z :=
    (hfc.differentiable one_ne_zero z).hasFDerivAt
  have hmem : f z ∈ X := hr ▸ ⟨z, rfl⟩
  have hgd : HasFDerivWithinAt g (fderivWithin ℝ g X (f z)) X (f z) :=
    ((hgc.differentiableOn one_ne_zero) (f z) hmem).hasFDerivWithinAt
  have hcomp := hgd.comp_hasFDerivAt z hfd (Filter.Eventually.of_forall fun x => hr ▸ ⟨x, rfl⟩)
  have hid : g ∘ f = id := funext hgf
  rw [hid] at hcomp
  have huniq := hcomp.unique (hasFDerivAt_id z)
  intro u v huv
  have := congrArg (fun L => L u) huniq
  have h2 := congrArg (fun L => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
  rw [← this, ← h2, huv]

end ObjectCentric

open ObjectCentric in
theorem solution {K M N : ℕ} (hM : 0 < M)
    (X : Set (Obs N)) (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) :
    ∀ (z : Lat K M) (k : Fin K), subRank f z (indexSet f z k) = M := by
  intro z k
  classical
  set S := indexSet f z k with hS
  set J := jac f z with hJ
  set A := J.submatrix (fun n : S => (n : Fin N)) id with hA
  set B : Matrix S (Fin M) ℝ := Matrix.of fun n m => A n (k, m) with hB
  set E : Matrix (Fin M) (Fin K × Fin M) ℝ := Matrix.of fun m c => if c.1 = k ∧ c.2 = m then 1 else 0 with hE
  set E' : Matrix (Fin K × Fin M) (Fin M) ℝ := Matrix.of fun c m => if c.1 = k ∧ c.2 = m then 1 else 0 with hE'
  have hzero : ∀ n : S, ∀ j m, j ≠ k → A n (j, m) = 0 := by
    intro n j m hjk
    have hn : (n : Fin N) ∈ indexSet f z k := n.2
    have hnj : (n : Fin N) ∉ indexSet f z j := fun h =>
      Set.disjoint_left.mp (hfc z k j (Ne.symm hjk)) hn h
    simp only [indexSet, Set.mem_ofPred_eq, not_not] at hnj
    have := congrFun hnj m
    simpa [slotGrad, hA, hJ] using this
  have hAB : A = B * E := by
    ext n ⟨j, m'⟩
    rw [Matrix.mul_apply]; simp only [hB, hE, Matrix.of_apply]
    by_cases hjk : j = k
    · subst hjk
      rw [Finset.sum_eq_single m']
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · rw [hzero n j m' hjk]
      simp [hjk]
  have hBA : B = A * E' := by
    ext n m
    rw [Matrix.mul_apply]; simp only [hB, hE', Matrix.of_apply]
    rw [Finset.sum_eq_single (k, m)]
    · simp
    · rintro ⟨j, m'⟩ _ hb
      by_cases h : j = k ∧ m' = m
      · exact absurd (by rw [h.1, h.2]) hb
      · simp [h]
    · simp
  have hinj : Function.Injective B.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : ∀ n : S, ∑ m, B n m * v m = 0 := fun n => by
      have := congrFun hv n
      simpa [Matrix.mulVec, dotProduct] using this
    set w : Lat K M := Pi.single k v with hw
    have hwsum : w = ∑ m, v m • (Pi.single k (Pi.single m (1 : ℝ)) : Lat K M) := by
      funext j m
      rw [Finset.sum_apply, Finset.sum_apply]
      simp only [hw, Pi.smul_apply, smul_eq_mul]
      by_cases hj : j = k
      · subst hj; simp [Pi.single_apply]
      · simp [hj]
    have hDw : fderiv ℝ f z w = 0 := by
      funext n
      rw [hwsum, map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases hn : n ∈ S
      · have := hv' ⟨n, hn⟩
        simpa [hB, hA, hJ, jac, mul_comm, Matrix.of_apply] using this
      · have hn' : slotGrad f z n k = 0 := by
          simpa [hS, indexSet] using hn
        refine Finset.sum_eq_zero fun m _ => ?_
        have := congrFun hn' m
        simp only [slotGrad, jac, Pi.zero_apply] at this
        rw [this, mul_zero]
    have hw0 : w = 0 := oc_inj X f g hf z (by rw [hDw, map_zero])
    funext m
    have := congrFun (congrFun hw0 k) m
    simpa [hw] using this
  have hrB : B.rank = M := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj]; simp
  have h1 : A.rank ≤ M := by
    rw [hAB]; exact (Matrix.rank_mul_le_left _ _).trans hrB.le
  have h2 : M ≤ A.rank := by
    calc M = B.rank := hrB.symm
      _ ≤ A.rank := by rw [hBA]; exact Matrix.rank_mul_le_left _ _
  show A.rank = M
  omega
