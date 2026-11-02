-- Prove2me | solution 1 for SeqMechExPost.Optimal.lemma_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:09:34.558196+00:00
-- url     : https://prove2.me/submissions/08adda43-c77a-49cf-a3bc-e7f4c8beb1af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model
import Definitions.Def_SeqMechExPost_Optimal_Tradeoff
import Theorems.Thm_SeqMechExPost_Optimal_lemma_3
import Theorems.Thm_SeqMechExPost_Optimal_tight_utility_bounds

open MeasureTheory

namespace SeqMechExPost.Optimal.L4Aux

open SeqMechExPost.Optimal

variable {k : ℕ}

lemma ae_box (I : Instance k) : ∀ᵐ w ∂I.law, I.InBox w := by
  have h : ∀ j, ∀ᵐ w ∂I.law, w j ∈ Set.Icc (I.lo j) (I.hi j) := by
    intro j
    have hm := measurePreserving_eval I.μ j
    have h1 : ∀ᵐ t ∂I.μ j, t ∈ Set.Icc (I.lo j) (I.hi j) := by
      rw [ae_iff]
      have := I.support j
      have e : {a : ℝ | ¬ a ∈ Set.Icc (I.lo j) (I.hi j)} = (Set.Icc (I.lo j) (I.hi j))ᶜ := rfl
      rw [e]; exact this
    exact hm.quasiMeasurePreserving.ae h1
  exact ae_all_iff.mpr h

/-- `adjust ∘ unadjust` has the same adjusted objective as an adjusted-feasible mechanism. -/
lemma adjObj_au (I : Instance k) (A : AdjMech k)
    (hpre : ∀ i v, I.InBox v → (adjust I (unadjust I A)).pHat i v = A.pHat i v) :
    (adjust I (unadjust I A)).adjObj I = A.adjObj I := by
  unfold AdjMech.adjObj
  refine integral_congr_ae ?_
  filter_upwards [ae_box I] with v hv
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · exact hpre i v hv
  · rfl

end SeqMechExPost.Optimal.L4Aux

open SeqMechExPost.Optimal SeqMechExPost.Optimal.L4Aux

theorem solution {k : ℕ} (I : Instance k) :
    (∃ M : SeqMech k, M.IsOptimal I ∧
      ∀ i v, I.InBox v → i.val + 1 < k → M.p i v = v i * M.x i v) ∧
    (∀ M : SeqMech k, M.Feasible I →
      ∃ M' : SeqMech k, M'.Feasible I ∧ M'.x = M.x ∧ M'.revenue I = M.revenue I ∧
        ∀ i v, I.InBox v → i.val + 1 < k → M'.p i v = v i * M'.x i v) := by
  have L3 := lemma_3 I
  have T := tight_utility_bounds I
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hAopt, hbind⟩ := T.2
    obtain ⟨hMF, hpre⟩ := L3.2 A hAopt.1
    refine ⟨unadjust I A, ⟨hMF, fun M' hM' => ?_⟩, fun i v hv hi => ?_⟩
    · have h1 := L3.1 M' hM'.1
      rw [h1.2.1, (L3.1 _ hMF.1).2.1, adjObj_au I A hpre]
      exact hAopt.2 _ (h1.1.mp hM')
    · have := hbind i v hv hi
      show A.pHat i v + A.nextU I i v = v i * A.x i v
      linarith
  · intro M hM
    have hM3 := L3.1 M hM.1
    obtain ⟨A', hA'F, hx, hobj, hbind⟩ := T.1 (adjust I M) (hM3.1.mp hM)
    obtain ⟨hM'F, hpre⟩ := L3.2 A' hA'F
    refine ⟨unadjust I A', hM'F, ?_, ?_, fun i v hv hi => ?_⟩
    · show A'.x = M.x
      rw [hx]; rfl
    · rw [(L3.1 _ hM'F.1).2.1, adjObj_au I A' hpre, hobj, hM3.2.1]
    · have := hbind i v hv hi
      show A'.pHat i v + A'.nextU I i v = v i * A'.x i v
      linarith
