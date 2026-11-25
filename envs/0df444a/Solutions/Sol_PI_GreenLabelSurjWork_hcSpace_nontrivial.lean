-- Prove2me | solution 1 for PI.GreenLabelSurjWork.hcSpace_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:53.577424+00:00
-- url     : https://prove2.me/submissions/79d40a68-a000-44c7-842c-3ed0846019c0

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Theorems.Thm_PI_GreenLabelSurjWork_infl_mul
import Theorems.Thm_PI_GreenLabelSurjWork_infl_one
import Theorems.Thm_PI_GreenLabelSurjWork_exists_ne_zero_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
namespace PI.GreenLabelSurjWork
theorem _root_.solution (hl : ∀ c, Nontrivial (lam c)) : Nontrivial (hcSpace K b lam) := by
  classical
  obtain ⟨v, hv⟩ := exists_ne_zero_tensor b lam hl
  let f : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type)) := fun x =>
    if hx : x ∈ parab K b then infl K b lam ⟨x, hx⟩ v else 0
  have hf : f ∈ hcSpace K b lam := by
    show ∀ (p : parab K b) (x : GL ι K), f (p.1 * x) = infl K b lam p (f x)
    intro p x
    by_cases hx : x ∈ parab K b
    · have hpx : p.1 * x ∈ parab K b := mul_mem p.2 hx
      simp only [f, dif_pos hx, dif_pos hpx]
      rw [show (⟨p.1 * x, hpx⟩ : parab K b) = p * ⟨x, hx⟩ from rfl, infl_mul]
      rfl
    · have hpx : p.1 * x ∉ parab K b := fun h => hx (by
        have := mul_mem (inv_mem p.2) h
        rwa [inv_mul_cancel_left] at this)
      simp only [f, dif_neg hx, dif_neg hpx, map_zero]
  refine ⟨⟨⟨f, hf⟩, 0, fun h => hv ?_⟩⟩
  have h1 := congrFun (congrArg Subtype.val h) 1
  simp only [f, dif_pos (one_mem (parab K b))] at h1
  rw [show (⟨1, one_mem (parab K b)⟩ : parab K b) = 1 from rfl, infl_one] at h1
  exact h1
end PI.GreenLabelSurjWork
