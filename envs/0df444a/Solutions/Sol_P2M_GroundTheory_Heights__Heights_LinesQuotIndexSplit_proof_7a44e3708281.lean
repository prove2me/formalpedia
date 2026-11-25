-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesQuotIndexSplit_proof_7a44e3708281
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:46.913329+00:00
-- url     : https://prove2.me/submissions/899a75c5-e18c-475f-92b0-7dc24497ae92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndexSplit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndexSplit_colSpan_fg_span_765789730e9f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Matrix
noncomputable section
open KLinesQuotIndexSplit
namespace GroundTheory.Heights₂.Heights
namespace LinesQuotIndexSplit
theorem _root_.solution (h1 : LinesQuotIndex.Statement) (h2 : LinesCoordImage.Statement)
    (h3 : LinesCoordDet.Statement) (h4 : LinesIsLattice.Statement)
    (h5 : LinesGenIndexTrans.Statement) (h6 : LinesStdIndexDet.Statement)
    (h7 : LinesProjLattice.Statement) : LinesQuotIndexSplit.Statement := by
  intro K _ _ n m k a B b c τ ha hb hτ hinj hli
  set V := (B.toMatrix (Sum.elim b c)).toBlocks₂₂ with hVdef
  have hdet : V.det ≠ 0 := (h3 K n m k B b c hb hli).2
  have hbB : (fun i => B (Sum.inl i)) = b := funext hb
  have hc : coordProj B ∘ c = fun j => V *ᵥ (Pi.single j 1 : Fin k → K) :=
    funext fun j => h2 K n m k B b c j
  rw [← hbB, h1 K n m k B (idealLattice a) c, hc]
  obtain ⟨hPfg, hPspan, -⟩ := h7 K n m k a B τ ha hτ hinj
  have hP := h4 K (Fin k) _ hPfg hPspan
  have hSfg : ((stdLattice K k).restrictScalars ℤ).FG :=
    (Submodule.fg_span (Set.finite_range _)).restrictScalars
  have hSspan : Submodule.span K ((stdLattice K k : Submodule (𝓞 K) (Fin k → K)) :
      Set (Fin k → K)) = ⊤ := by
    rw [stdLattice, Submodule.span_span_of_tower]
    have : (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
        Set.range (Pi.basisFun K (Fin k)) := by
      ext v; simp [Pi.basisFun_apply]
    rw [this, (Pi.basisFun K (Fin k)).span_eq]
  have hS := h4 K (Fin k) _ hSfg hSspan
  obtain ⟨hCfg, hCspan⟩ := colSpan_fg_span K k V hdet
  have hC := h4 K (Fin k) _ hCfg hCspan
  have e : genIndex ((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))).toAddSubgroup
        (stdLattice K k).toAddSubgroup *
      genIndex (stdLattice K k).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup =
      genIndex ((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup :=
    (h5 (Fin k → K) _ _ _ hP hS hC).2
  rw [← e, h6 K k V hdet]
end LinesQuotIndexSplit
end GroundTheory.Heights₂.Heights
