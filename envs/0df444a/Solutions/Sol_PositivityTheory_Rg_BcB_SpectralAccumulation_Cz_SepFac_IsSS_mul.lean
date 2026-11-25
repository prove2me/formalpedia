-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:50:47.244565+00:00
-- url     : https://prove2.me/submissions/3b53600b-4b8e-4cf5-ab1d-db556dd3b3d1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_of_decomp
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_exists_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
namespace IsSS
theorem _root_.solution {x y : A} (hx : IsSS x) (hy : IsSS y) (h : Commute x y) : IsSS (x * y) := by
  obtain ⟨s, e, hse, hxe, hce⟩ := hx.exists_decomp
  obtain ⟨t, f, htf, hyf, -⟩ := hy.exists_decomp
  refine isSS_of_decomp (s ×ˢ t) (fun p => e p.1 * f p.2) (fun p => p.1 * p.2) ?_ ?_
  · rw [Finset.sum_product, ← hse]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only
    rw [← Finset.mul_sum, htf, mul_one]
  · rintro ⟨v, w⟩ hvw
    rw [Finset.mem_product] at hvw
    have hey : y * e v = e v * y := ((hce v y h).eq).symm
    calc x * y * (e v * f w) = x * ((y * e v) * f w) := by simp only [mul_assoc]
      _ = x * (e v * (y * f w)) := by rw [hey, mul_assoc]
      _ = x * (e v * (w • f w)) := by rw [hyf w hvw.2]
      _ = w • ((x * e v) * f w) := by rw [mul_smul_comm, mul_smul_comm, mul_assoc]
      _ = (v * w) • (e v * f w) := by rw [hxe v hvw.1, smul_mul_assoc, smul_smul, mul_comm w v]
end IsSS
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
