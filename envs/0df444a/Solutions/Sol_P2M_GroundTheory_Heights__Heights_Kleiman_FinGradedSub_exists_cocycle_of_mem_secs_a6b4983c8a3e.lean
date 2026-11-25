-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_cocycle_of_mem_secs_a6b4983c8a3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:54.048517+00:00
-- url     : https://prove2.me/submissions/a759fcd9-86b5-4216-86a0-af301f0f48a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_locCone_eq_db25ae5cb6f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_injective_5a9f3d67e677
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_locRes_374e5d5036f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMod_subsingleton_903ca61ffd0a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution {c : ℤ} {v : Ω} (hv : v ∈ (M.tildeSys c).secs) :
    ∃ z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0,
      ∀ K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0, K.1.1 ⊆ support x →
        M.cellCone K.1 (z K) = coneSingle S x c v := by
  classical
  rw [SubSystem.secs, Submodule.mem_iInf] at hv
  have hl : ∀ (I : StdCell N) (h : I.1 ⊆ support x), ∃ z ∈ degLoc M.coneGraded c I,
      locCone M I.1 h z = coneSingle S x c v :=
    fun I h => exists_locCone_eq M c I h (hv ⟨I.1, I.2.1, h⟩)
  choose w hw hwv using hl
  let u : ∀ I : StdCell N, LocMod S N M.coneSub I.1 := fun I =>
    if h : I.1 ⊆ support x then w I h else 0
  have hcompat : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (u I) = u J := by
    intro I J h
    by_cases hJ : J.1 ⊆ support x
    · apply locCone_injective M J.1 hJ
      have hI : I.1 ⊆ support x := h.trans hJ
      simp only [u, dif_pos hJ, dif_pos hI]
      rw [hwv J hJ]
      exact (locCone_locRes M h hJ (w I hI)).trans (hwv I hI)
    · obtain ⟨i, hiJ, hi⟩ : ∃ i ∈ J.1, x i = 0 := by
        by_contra hne
        push Not at hne
        exact hJ fun i hi => (mem_support x).mpr (hne i hi)
      have := locMod_subsingleton M hiJ hi
      exact Subsingleton.elim _ _
  refine ⟨fun K => u K.1, ⟨LinearMap.mem_ker.mpr (Cech.d_zero_of_compat u hcompat), fun K _ => ?_⟩,
    fun K hK => ?_⟩
  · change u K.1 ∈ degLoc M.coneGraded c K.1
    by_cases hK : K.1.1 ⊆ support x
    · simp only [u, dif_pos hK]; exact hw K.1 hK
    · simp only [u, dif_neg hK]; exact zero_mem _
  · change M.cellCone K.1 (u K.1) = _
    simp only [u, dif_pos hK, M.cellCone_of_subset hK]
    exact hwv K.1 hK
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
