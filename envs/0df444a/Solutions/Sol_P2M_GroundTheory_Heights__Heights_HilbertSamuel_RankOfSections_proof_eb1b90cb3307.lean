-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_proof_eb1b90cb3307
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:41:40.826009+00:00
-- url     : https://prove2.me/submissions/7e728c60-32a1-42b4-b3fe-83092da95836

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRankOfSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_const_nsmul_a1ffba80053a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_bound_of_eventually_613d97591c0c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections
theorem _root_.solution (hP : HilbertPrime.Statement.{0}) (hM : MixedNumberPolynomial.Statement.{0}) :
    RankOfSections.Statement := by
  intro ι₀ _ q D hq hdim
  have hdim' : ringKrullDim (MRing (fun _ : Unit => ι₀) ℚ ⧸ q) =
      ((D + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    simpa using hdim
  obtain ⟨a₀, C, hC⟩ := hP D ℚ Unit (fun _ => ι₀) q hq hdim'
  have hadd := (hM ℚ Unit (fun _ => ι₀) q D hq hdim').2
  have hhom : ∀ n : ℕ, intNum ℚ q (fun _ : Fin D => fun _ : Unit => (n : ℤ)) =
      (n : ℤ) ^ D * intNum ℚ q (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) := by
    intro n
    have := const_nsmul (fun bs => intNum ℚ q bs) hadd n (fun _ : Unit => (1 : ℤ))
    have e : (n • fun _ : Unit => (1 : ℤ)) = fun _ : Unit => (n : ℤ) := by
      funext u
      simp
    rw [e] at this
    exact this
  apply bound_of_eventually _ _ a₀ C
  intro n hn
  have h := hC (fun _ => n) (fun _ => hn)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [hhom n] at h
  convert h using 3
  push_cast
  ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections
