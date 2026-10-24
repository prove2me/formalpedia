-- Prove2me | solution 1 for SKAlgorithm.Qudit.base_case
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:11:39.332818+00:00
-- url     : https://prove2.me/submissions/499928c4-872b-4357-b10c-e4b6ae0413dc

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit.BaseCaseProof

open scoped Matrix.Norms.Elementwise in
theorem isCompact_specialUnitary (d : ℕ) :
    IsCompact (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  have hclosed : IsClosed
      (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
    have heq : (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) =
        (unitary (Matrix (Fin d) (Fin d) ℂ) : Set (Matrix (Fin d) (Fin d) ℂ)) ∩
          {A | A.det = 1} := by
      ext A
      exact Matrix.mem_specialUnitaryGroup_iff
    rw [heq]
    exact isClosed_unitary.inter (isClosed_eq continuous_id.matrix_det continuous_const)
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨hclosed, (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, ?_⟩⟩
  intro A hA
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    entrywise_sup_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup hA)

open scoped Matrix.Norms.L2Operator in
theorem continuous_opDist_left {d : ℕ} (V : SU d) :
    Continuous (fun U : SU d => opDist U V) := by
  change Continuous (fun U : SU d =>
    ‖(U : Matrix (Fin d) (Fin d) ℂ) - (V : Matrix (Fin d) (Fin d) ℂ)‖)
  exact (continuous_subtype_val.sub continuous_const).norm

end SKAlgorithm.Qudit.BaseCaseProof

theorem solution {d : ℕ} (G : Finset (SKAlgorithm.Qudit.SU d))
    (hG : SKAlgorithm.Qudit.IsInstructionSet G) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ l₀ : ℕ, ∀ U : SKAlgorithm.Qudit.SU d,
      ∃ S : List (SKAlgorithm.Qudit.SU d), (∀ g ∈ S, g ∈ G) ∧ S.length ≤ l₀ ∧
        SKAlgorithm.Qudit.opDist U (SKAlgorithm.Qudit.seqUnitary S) < ε₀ := by
  classical
  let : CompactSpace (SKAlgorithm.Qudit.SU d) :=
    isCompact_iff_compactSpace.mp (SKAlgorithm.Qudit.BaseCaseProof.isCompact_specialUnitary d)
  let W := {S : List (SKAlgorithm.Qudit.SU d) // ∀ g ∈ S, g ∈ G}
  let O : W → Set (SKAlgorithm.Qudit.SU d) := fun S =>
    {U | SKAlgorithm.Qudit.opDist U (SKAlgorithm.Qudit.seqUnitary S.val) < ε₀}
  have hopen : ∀ S : W, IsOpen (O S) := fun S =>
    isOpen_lt (SKAlgorithm.Qudit.BaseCaseProof.continuous_opDist_left _) continuous_const
  have hcover : (Set.univ : Set (SKAlgorithm.Qudit.SU d)) ⊆ ⋃ S : W, O S := by
    intro U _
    obtain ⟨S, hS, hdist⟩ := hG.2 U ε₀ hε₀
    exact Set.mem_iUnion.mpr ⟨⟨S, hS⟩, hdist⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hopen hcover
  refine ⟨t.sup (fun S => S.val.length), ?_⟩
  intro U
  obtain ⟨S, hSt, hU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ U))
  exact ⟨S.val, S.property, Finset.le_sup (f := fun S : W => S.val.length) hSt, hU⟩
