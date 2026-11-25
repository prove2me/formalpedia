-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_exists_subfamily_card_eq_finrank_7faf8527523a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:57.364555+00:00
-- url     : https://prove2.me/submissions/9e748817-7fde-4109-b70b-e73588b139b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Module Submodule
open GroundTheory.Heights₂.Heights
universe u v w
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLemmas.HadamardQuotient
namespace GroundTheory.Heights₂.Heights.LatticeLemmas.HadamardQuotient
theorem _root_.solution {R M : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (F : Submodule R M)
    {ι : Type*} (x : ι → M) (hx : finrank R (span R (Set.range x)) = finrank R M) :
    ∃ s : Set ι, LinearIndepOn R (F.mkQ ∘ x) s ∧ Finite s ∧ Nat.card s = finrank R (M ⧸ F) := by
  classical
  set y : ι → M ⧸ F := F.mkQ ∘ x with hy_def
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn R y
  have hfin : Finite s := LinearIndependent.finite_of_isNoetherian hs
  set S : Submodule R (M ⧸ F) := span R (y '' s) with hS_def

  have hy : ∀ i, S.mkQ (y i) ∈ torsion R ((M ⧸ F) ⧸ S) := by
    intro i
    by_cases hi : i ∈ s
    · have h0 : S.mkQ (y i) = 0 :=
        (Submodule.Quotient.mk_eq_zero S).mpr (subset_span ⟨i, hi, rfl⟩)
      rw [h0]
      exact zero_mem _
    · obtain ⟨a, ha, h⟩ := hmax i hi
      refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
      change a • S.mkQ (y i) = 0
      rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h
  have hspan : span R (Set.range y) ≤ (torsion R ((M ⧸ F) ⧸ S)).comap S.mkQ :=
    span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hy i)

  set N : Submodule R M := span R (Set.range x) with hN_def
  have hN : finrank R (M ⧸ N) = 0 := by
    have h := rank_quotient_add_rank_of_isDomain N
    rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at h
    norm_cast at h
    omega

  have hQS : finrank R ((M ⧸ F) ⧸ S) = 0 := by
    rw [Module.finrank_eq_zero_iff]
    intro q
    obtain ⟨q, rfl⟩ := S.mkQ_surjective q
    obtain ⟨m, rfl⟩ := F.mkQ_surjective q
    obtain ⟨a, ha, ham⟩ := Module.finrank_eq_zero_iff.mp hN (N.mkQ m)
    have h1 : a • m ∈ N := by
      rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero] at ham
      exact ham
    have h2 : F.mkQ (a • m) ∈ span R (Set.range y) := by
      have h := Submodule.mem_map_of_mem (f := F.mkQ) h1
      rwa [hN_def, Submodule.map_span, ← Set.range_comp] at h
    obtain ⟨⟨b, hb⟩, hbm⟩ := hspan h2
    refine ⟨b * a, mul_ne_zero (nonZeroDivisors.ne_zero hb) ha, ?_⟩
    change b • S.mkQ (F.mkQ (a • m)) = 0 at hbm
    rw [mul_smul, ← map_smul, ← map_smul, ← map_smul, ← map_smul]
    rw [map_smul, map_smul] at hbm
    rw [map_smul, map_smul]
    exact hbm
  have hadd := rank_quotient_add_rank_of_isDomain S
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at hadd
  norm_cast at hadd
  have := Fintype.ofFinite s
  have hSr : finrank R S = Nat.card s := by
    rw [hS_def, Set.image_eq_range, Nat.card_eq_fintype_card]
    exact finrank_span_eq_card hs
  exact ⟨s, hs, hfin, by omega⟩
end GroundTheory.Heights₂.Heights.LatticeLemmas.HadamardQuotient
