-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_exists_form_not_mem_587f4c48195d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:29:55.560503+00:00
-- url     : https://prove2.me/submissions/6a4ffed3-17cc-4199-ba91-8a43a24b9370

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_mem_8765b3f76011
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_X_ne_zero_6e1224960199
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_exists_common_denom_4d33b8a3a3b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_chartMonomial_mul_chartPow_10a98fec4d52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_chartMonomial_mem_primeCompl_232337c8b957
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution (hg : D.IsFormSystem d g) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {W : Ideal (MvPolynomial (Coord D.extSizes) ℤ)} [W.IsPrime] (hPW : D.extIdeal ≤ W)
    (hW : ∀ k, (X (D.oldCoord ⟨k, c k⟩) : MvPolynomial _ ℤ) ∉ W) :
    ∃ i, D.liftOld (g c i) ∉ W := by
  obtain ⟨u, hu, hsum⟩ := D.generating c hc
  obtain ⟨E, f, hf⟩ := exists_common_denom hc hu
  have hsum' : ∑ j, u j * D.elt j = P.chartPow c D.deg := by
    have hcp : P.chartPow c D.deg ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (mkF_X_ne_zero hc k)
    rw [← one_mul (P.chartPow c D.deg), ← hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp
  set Q := chartMonomial c fun k ↦ ((d k : ℤ) + D.deg k).toNat
  have hmem : ∑ j, f j * g c j - chartMonomial c 1 ^ E * Q ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_sum, map_mul, map_pow,
      ← mkF_chartMonomial_mul_chartPow D hg.nonneg hc, ← hsum', sub_eq_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, ← hf j, hg.value c hc j]
    ring
  by_contra h
  simp only [not_exists, not_not] at h
  have h1 := hPW (liftOld_mem D hmem)
  have h2 : D.liftOld (∑ j, f j * g c j) ∈ W := by
    rw [map_sum]
    exact W.sum_mem fun j _ ↦ by rw [map_mul]; exact W.mul_mem_left _ (h j)
  have h3 : D.liftOld (chartMonomial c 1 ^ E * Q) ∈ W := by
    have := W.sub_mem h2 h1
    rwa [map_sub, sub_sub_cancel] at this
  rw [map_mul, map_pow] at h3
  exact (Ideal.mem_primeCompl_iff.mp (W.primeCompl.mul_mem
    (W.primeCompl.pow_mem (liftOld_chartMonomial_mem_primeCompl D hW 1) E)
    (liftOld_chartMonomial_mem_primeCompl D hW _))) h3
end GroundTheory.Heights₂.Heights.SectionCycle
