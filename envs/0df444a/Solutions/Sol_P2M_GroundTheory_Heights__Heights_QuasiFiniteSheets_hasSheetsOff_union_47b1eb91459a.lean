-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_union_47b1eb91459a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:53.17984+00:00
-- url     : https://prove2.me/submissions/29c772a1-fd5f-469d-851e-72ba11abe385

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PQuasiFiniteSheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.QuasiFiniteSheets
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.QuasiFiniteSheets
theorem _root_.solution {S T : Set (Fin n → ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {c c' e : MvPolynomial (Fin d) ℂ} (h₁ : HasSheetsOff S A c) (h₂ : HasSheetsOff T A c')
    (he : ∀ x ∈ S ∩ T, eval (A.mulVec x) e = 0) : HasSheetsOff (S ∪ T) A (c * c' * e) := by
  intro y hy
  simp only [map_mul, ne_eq, mul_eq_zero, not_or] at hy
  obtain ⟨⟨hc, hc'⟩, hey⟩ := hy
  obtain ⟨U₁, N₁, s₁, hU₁, hyU₁, hd₁, hs₁⟩ := h₁ y hc
  obtain ⟨U₂, N₂, s₂, hU₂, hyU₂, hd₂, hs₂⟩ := h₂ y hc'
  refine ⟨U₁ ∩ U₂ ∩ {w | eval w e ≠ 0}, N₁ + N₂, Fin.append s₁ s₂,
    (hU₁.inter hU₂).inter (isOpen_ne_fun (MvPolynomial.continuous_eval e) continuous_const),
    ⟨⟨hyU₁, hyU₂⟩, hey⟩, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact (hd₁ j).mono fun w hw => hw.1.1
    · rw [Fin.append_right]; exact (hd₂ j).mono fun w hw => hw.1.2
  rintro w ⟨⟨hw₁, hw₂⟩, hwe⟩
  obtain ⟨hm₁, hi₁, hr₁⟩ := hs₁ w hw₁
  obtain ⟨hm₂, hi₂, hr₂⟩ := hs₂ w hw₂
  have hcross : ∀ i j, s₁ i w ≠ s₂ j w := by
    intro i j hij
    apply hwe
    rw [← (hm₁ i).2]
    exact he _ ⟨(hm₁ i).1, hij ▸ (hm₂ j).1⟩
  refine ⟨fun j => ?_, fun i j hij => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact ⟨Or.inl (hm₁ j).1, (hm₁ j).2⟩
    · rw [Fin.append_right]; exact ⟨Or.inr (hm₂ j).1, (hm₂ j).2⟩
  · induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => simp only [Fin.append_left] at hij; rw [hi₁ hij]
      | right j => simp only [Fin.append_left, Fin.append_right] at hij; exact (hcross i j hij).elim
    | right i =>
      induction j using Fin.addCases with
      | left j => simp only [Fin.append_left, Fin.append_right] at hij; exact (hcross j i hij.symm).elim
      | right j => simp only [Fin.append_right] at hij; rw [hi₂ hij]
  · rintro x ⟨hx | hx, hAx⟩
    · obtain ⟨j, rfl⟩ := hr₁ ⟨hx, hAx⟩
      exact ⟨Fin.castAdd N₂ j, by simp only [Fin.append_left]⟩
    · obtain ⟨j, rfl⟩ := hr₂ ⟨hx, hAx⟩
      exact ⟨Fin.natAdd N₁ j, by simp only [Fin.append_right]⟩
end GroundTheory.Heights₂.Heights.QuasiFiniteSheets
