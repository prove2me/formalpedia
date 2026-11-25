-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionNorm_chartMonomial_ne_zero_33456487209d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:34.081883+00:00
-- url     : https://prove2.me/submissions/81a3f51b-5751-4044-8c49-c2a06fabbfb3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_chartMonomial_ae75ba626c28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38


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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionNorm
namespace GroundTheory.Heights₂.Heights.SectionNorm
theorem _root_.solution {P : ArithVariety n} (D : AddBlockData P) {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (D.size + 1)) (hgz : evalCone z (g c j) ≠ 0) :
    evalCone z (chartMonomial c d) ≠ 0 := by
  intro hm
  have hc : P.IsLive c := by
    by_contra hc
    exact hgz (by rw [hg.dead c hc j]; simp [evalCone])
  have hex : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c' hc' using hex
  have hlive : P.IsLive c' := by
    intro k hk
    apply hc' k
    have := hz.2 _ hk
    simpa [evalCone, eval₂_X] using this
  have hmem : chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc j, hg.value c' hlive j]
    ring
  have h0 := hz.2 _ hmem
  have hsub : evalCone z (chartMonomial c' d * g c j - chartMonomial c d * g c' j) =
      evalCone z (chartMonomial c' d) * evalCone z (g c j) -
        evalCone z (chartMonomial c d) * evalCone z (g c' j) := by
    simp [evalCone, eval₂_sub, eval₂_mul]
  rw [hsub, hm, zero_mul, sub_zero] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · rw [evalCone_chartMonomial] at h
    exact Finset.prod_ne_zero_iff.mpr (fun k _ ↦ pow_ne_zero _ (hc' k)) h
  · exact hgz h
end GroundTheory.Heights₂.Heights.SectionNorm
