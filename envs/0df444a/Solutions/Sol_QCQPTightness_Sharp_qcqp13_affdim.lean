-- Prove2me | solution 1 for QCQPTightness.Sharp.qcqp13_affdim
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T12:20:47.422796+00:00
-- url     : https://prove2.me/submissions/0b798539-c857-4b62-8d2e-a13a53d35606

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP
import Definitions.Def_QCQPTightness_Sharp_Mult
import Definitions.Def_QCQPTightness_Sharp_Examples
import Definitions.Def_QCQPTightness_Sharp_Faces

open QCQPTightness.Sharp Matrix

theorem solution (n k : ℕ) (hn : 0 < n) :
    affdim ((qcqp13 n k hn).bγ '' {γ | γ 0 = 1}) = k := by
  set e := blockEquiv (Nat.mul_comm k n)
  set z : Fin n := ⟨0, hn⟩
  set v : Fin k → Fin (n * k) → ℝ := fun j => Pi.single (e (j, z)) (1 / 2 : ℝ) with hv
  set S := (qcqp13 n k hn).bγ '' {γ | γ 0 = 1} with hS
  have hb : ∀ γ : Fin (k + 1) → ℝ, (qcqp13 n k hn).bγ γ = ∑ j, γ j.succ • v j := by
    intro γ
    simp [QCQP.bγ, qcqp13, Fin.sum_univ_succ, hv, e, z]
  have h0 : (0 : Fin (n * k) → ℝ) ∈ S :=
    ⟨Fin.cases 1 (fun _ => 0), by simp, by rw [hb]; simp⟩
  have hspan : vectorSpan ℝ S = Submodule.span ℝ (Set.range v) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ h0]
    have : ((· -ᵥ (0 : Fin (n * k) → ℝ)) '' S) = S := by
      simp [vsub_eq_sub]
    rw [this]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨γ, _, rfl⟩
      rw [hb]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span ⟨Fin.cases 1 (Pi.single j 1), by simp, ?_⟩
      rw [hb]
      simp [Pi.single_apply]
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrFun hg (e (i, z))
    simp only [Finset.sum_apply, Pi.smul_apply, hv, Pi.single_apply, smul_eq_mul,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, and_true, Pi.zero_apply] at this
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    linarith
  unfold affdim
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]
