-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_cross_3f7d63056fd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:58.767216+00:00
-- url     : https://prove2.me/submissions/d6523235-ab96-4f53-9c5a-8e2d6696309a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_isLive_of_mem_points_f34985632ea7
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
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0)
    (c' : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)) :
    evalCone z (g c' j) =
      evalCone z (chartMonomial c' d) * evalCone z (g c j) / evalCone z (chartMonomial c d) := by
  have hc : P.IsLive c := isLive_of_mem_points hz hzc
  have hm : evalCone z (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
  by_cases hc' : P.IsLive c'
  · have hmem : chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
      rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc j, hg.value c' hc' j]
      ring
    have h0 := hz.2 _ hmem
    rw [eq_div_iff hm]
    simp only [evalCone, eval₂_sub, eval₂_mul, sub_eq_zero] at h0 ⊢
    rw [h0]
    ring
  · obtain ⟨k, hk⟩ : ∃ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∈ P.ideal := by
      by_contra h
      exact hc' fun k hk ↦ h ⟨k, hk⟩
    have hzk : z k (c' k) = 0 := by simpa [evalCone] using hz.2 _ hk
    have hm' : evalCone z (chartMonomial c' d) = 0 := by
      rw [evalCone_chartMonomial]
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [hzk]
      exact zero_pow (by have := hg.pos k; omega)
    rw [hg.dead c' hc' j, hm']
    simp [evalCone]
end GroundTheory.Heights₂.Heights.SmallSections
