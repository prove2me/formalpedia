-- Prove2me | solution 4 for TeschlQM.KatoRellich.kato_rellich
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T00:21:51.737144+00:00
-- url     : https://prove2.me/submissions/a9caec69-00fc-4736-8a66-5b8346145a4a

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Theorems.Thm_TeschlQM_KatoRellich_kato_rellich_essentiallySelfAdjoint

open scoped ENNReal

namespace TeschlQM.KatoRellich.Goal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma closure_eq_self {S : H →ₗ.[ℂ] H} (hS : S.IsClosed) : S.closure = S := by
  have h := hS.isClosable.graph_closure_eq_closure_graph
  rw [hS.submodule_topologicalClosure_eq] at h
  exact (LinearPMap.eq_of_eq_graph h).symm

lemma ess_of_selfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hcl : A.IsClosed) :
    TeschlQM.Shared.IsEssentiallySelfAdjoint A := by
  unfold TeschlQM.Shared.IsEssentiallySelfAdjoint
  rw [closure_eq_self hcl]
  exact hA

lemma domain_le_right_of_sum_domain_eq {A B : H →ₗ.[ℂ] H} (hdom : (A + B).domain = A.domain) :
    A.domain ≤ B.domain := by
  intro x hx
  have : x ∈ A.domain ⊓ B.domain := by
    rw [← LinearPMap.add_domain, hdom]
    exact hx
  exact this.2

lemma sum_eq_sum_closure_right {A B : H →ₗ.[ℂ] H} (hdom : (A + B).domain = A.domain) :
    A + B = A + B.closure := by
  have hBd : A.domain ≤ B.domain := domain_le_right_of_sum_domain_eq hdom
  have hDomEq : (A + B).domain = (A + B.closure).domain := by
    calc
      (A + B).domain = A.domain := hdom
      _ = A.domain ⊓ B.closure.domain := (inf_eq_left.mpr (hBd.trans B.le_closure.1)).symm
      _ = (A + B.closure).domain := by rw [← LinearPMap.add_domain]
  apply LinearPMap.ext hDomEq
  intro x hg hg'
  have hxA : x ∈ A.domain := by simpa [hdom] using hg
  have hxB : x ∈ B.domain := hBd hxA
  have hxBcl : x ∈ B.closure.domain := B.le_closure.1 hxB
  simp only [LinearPMap.add_apply, hg, hg', hxA, hxB, hxBcl,
    B.le_closure.2 (x := ⟨x, hxB⟩) (y := ⟨x, hxBcl⟩) rfl]

lemma selfAdjoint_of_esa_and_closure_eq {T : H →ₗ.[ℂ] H}
    (hE : TeschlQM.Shared.IsEssentiallySelfAdjoint T) (hcl : T.closure = T) :
    IsSelfAdjoint T := by
  unfold TeschlQM.Shared.IsEssentiallySelfAdjoint at hE
  rwa [hcl] at hE

end TeschlQM.KatoRellich.Goal

open TeschlQM.KatoRellich in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : TeschlQM.Shared.IsSymmetric B)
    (hbound : relativeBound A B < 1) :
    (A + B).domain = A.domain ∧ IsSelfAdjoint (A + B) ∧
      ∀ γ a b : ℝ, a < 1 → IsRelativelyBoundedWith A B a b →
        TeschlQM.Shared.IsBoundedBelowBy A γ →
        TeschlQM.Shared.IsBoundedBelowBy (A + B) (γ - max (a * |γ| + b) (b / (1 - a))) := by
  have hAesa := TeschlQM.KatoRellich.Goal.ess_of_selfAdjoint hA hA.isClosed
  rcases kato_rellich_essentiallySelfAdjoint A B hAesa hB hbound with
    ⟨hdom, hESA, _, hsumcl, hlb⟩
  refine ⟨hdom, ?_, hlb⟩
  have hA' := TeschlQM.KatoRellich.Goal.closure_eq_self hA.isClosed
  have hABcl : (A + B).closure = A + B := by
    rw [hsumcl, hA', TeschlQM.KatoRellich.Goal.sum_eq_sum_closure_right hdom]
  exact TeschlQM.KatoRellich.Goal.selfAdjoint_of_esa_and_closure_eq hESA hABcl
