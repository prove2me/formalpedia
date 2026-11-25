-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:32.123631+00:00
-- url     : https://prove2.me/submissions/d6748e36-bb3c-4d1e-83aa-01e620c96056

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_commute_aeval

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
theorem _root_.solution {x : A} (hx : IsSS x) : ∃ (s : Finset ℂ) (e : ℂ → A), ∑ v ∈ s, e v = 1 ∧
    (∀ v ∈ s, x * e v = v • e v) ∧ ∀ v, ∀ y : A, Commute x y → Commute (e v) y := by
  classical
  obtain ⟨s, hs⟩ := hx
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have h10 : (1 : A) = 0 := by simpa using hs
    have : Subsingleton A := subsingleton_of_zero_eq_one h10.symm
    exact ⟨{0}, fun _ => 1, by simp, fun _ _ => Subsingleton.elim _ _, fun _ _ _ => Commute.one_left _⟩
  refine ⟨s, fun v => aeval x (Lagrange.basis s id v), ?_, fun v hv => ?_, fun v y h => commute_aeval h _⟩
  · rw [← map_sum, Lagrange.sum_basis (Set.injOn_id _) hne, map_one]
  · have key : (X - C v) * Lagrange.basis s id v = (∏ j ∈ s.erase v, C (v - j)⁻¹) * ∏ j ∈ s, (X - C j) := by
      rw [← Finset.mul_prod_erase s (fun j => X - C j) hv, Lagrange.basis]
      simp only [Lagrange.basisDivisor, id, Finset.prod_mul_distrib]
      ring
    have h0 : aeval x ((X - C v) * Lagrange.basis s id v) = 0 := by
      rw [key, map_mul, hs, mul_zero]
    rw [map_mul, map_sub, aeval_X, aeval_C, sub_mul, sub_eq_zero, ← Algebra.smul_def] at h0
    exact h0
end IsSS
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
