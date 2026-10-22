-- Prove2me | solution 1 for TsengBCD.Stationary.argmin_attained
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:17:08.435246+00:00
-- url     : https://prove2.me/submissions/65ff423d-e34c-415c-9556-b7d6ba2f453f

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

set_option autoImplicit false
open Filter Topology

theorem solution {N : ℕ} {n : Fin N → ℕ} (f : TsengBCD.Stationary.X n → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (x0 : TsengBCD.Stationary.X n) (hx0 : f x0 ≠ ⊤)
    (hcpt : IsCompact (TsengBCD.Stationary.levelSet f x0))
    (hcont : ∀ y ∈ TsengBCD.Stationary.levelSet f x0, ContinuousAt f y) :
    ∀ y ∈ TsengBCD.Stationary.levelSet f x0, ∀ k : Fin N, ∃ a : EuclideanSpace ℝ (Fin (n k)),
      ∀ b : EuclideanSpace ℝ (Fin (n k)),
        f (Function.update y k a) ≤ f (Function.update y k b) := by
  intro y hy k
  have hy' : f y ≤ f x0 := hy
  have hcl : IsClosed (TsengBCD.Stationary.levelSet f x0) := hcpt.isClosed
  have hupd : Continuous (fun a : EuclideanSpace ℝ (Fin (n k)) => Function.update y k a) :=
    continuous_const.update k continuous_id
  set T : Set (EuclideanSpace ℝ (Fin (n k))) :=
    {a | Function.update y k a ∈ TsengBCD.Stationary.levelSet f x0} with hTdef
  have hT : IsClosed T := hcl.preimage hupd
  have hg : ContinuousOn (fun a : EuclideanSpace ℝ (Fin (n k)) => f (Function.update y k a)) T :=
    fun a ha => ((hcont _ ha).comp hupd.continuousAt).continuousWithinAt
  set S : Set (EuclideanSpace ℝ (Fin (n k))) := {a | f (Function.update y k a) ≤ f y} with hSdef
  have hST : S ⊆ T := fun a ha => le_trans ha hy'
  have hSeq : S = T ∩ (fun a : EuclideanSpace ℝ (Fin (n k)) => f (Function.update y k a)) ⁻¹' Set.Iic (f y) := by
    ext a
    constructor
    · intro ha; exact ⟨hST ha, ha⟩
    · intro ha; exact ha.2
  have hSc : IsClosed S := by
    rw [hSeq]
    exact hg.preimage_isClosed_of_isClosed hT isClosed_Iic
  have hSsub : S ⊆ (fun x : TsengBCD.Stationary.X n => x k) '' TsengBCD.Stationary.levelSet f x0 := by
    intro a ha
    exact ⟨Function.update y k a, le_trans ha hy', by simp⟩
  have hSb : Bornology.IsBounded S :=
    (hcpt.image (continuous_apply k)).isBounded.subset hSsub
  have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSc hSb
  have hne : S.Nonempty := ⟨y k, by simp [hSdef]⟩
  obtain ⟨a, haS, hmin⟩ := hScomp.exists_isMinOn hne (hg.mono hST)
  refine ⟨a, fun b => ?_⟩
  by_cases hb : f (Function.update y k b) ≤ f y
  · exact isMinOn_iff.mp hmin b hb
  · exact haS.trans (le_of_lt (not_le.mp hb))
