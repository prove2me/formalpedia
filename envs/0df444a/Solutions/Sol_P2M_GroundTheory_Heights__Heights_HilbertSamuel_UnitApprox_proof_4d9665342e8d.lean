-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_UnitApprox_proof_4d9665342e8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:13.03099+00:00
-- url     : https://prove2.me/submissions/23ad4ab5-14ea-4d48-b9dc-e7a2bd422c3e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsUnitApprox
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PUnitApprox

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
open NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace UnitApprox
theorem _root_.solution : UnitApprox.Statement := by
  intro F _ _ u hconj hsum
  classical
  let uw : InfinitePlace F → ℝ := fun w => u w.embedding
  have hu_mk : ∀ sg, u sg = uw (InfinitePlace.mk sg) := by
    intro sg
    rcases embedding_mk_eq sg with h | h
    · simp only [uw, h]
    · simp only [uw, h, hconj]
  have hsum' : ∑ w : InfinitePlace F, (mult w : ℝ) * uw w = 0 := by
    rw [← hsum, ← Finset.sum_fiberwise Finset.univ (fun sg => InfinitePlace.mk sg) u]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => uw w), Finset.sum_const, nsmul_eq_mul,
      card_filter_mk_eq]
    intro sg hsg
    rw [Finset.mem_filter] at hsg
    rw [hu_mk, hsg.2]
  let b := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  let R : ℝ := ∑ i, ‖b i‖
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
  refine ⟨Fintype.card (InfinitePlace F) * R, fun n => ?_⟩
  let v : logSpace F := fun w => n * ((mult w.val : ℝ) * uw w.val)
  have hfl : ((ZSpan.floor b v : _) : logSpace F) ∈ unitLattice F := by
    rw [← (basisUnitLattice F).ofZLatticeBasis_span ℝ (unitLattice F)]
    exact (ZSpan.floor b v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hfl
  refine ⟨Additive.toMul x, ?_⟩
  set ε := Additive.toMul x with hε
  have hfr : ‖v - (ZSpan.floor b v : logSpace F)‖ ≤ R := by
    simpa [ZSpan.fract_apply] using ZSpan.norm_fract_le b v
  let e : InfinitePlace F → ℝ := fun w =>
    mult w * (Real.log (w ((ε : 𝓞 F) : F)) - n * uw w)
  have he_ne : ∀ w (hw : w ≠ w₀), |e w| ≤ R := by
    intro w hw
    have h1 := norm_le_pi_norm (v - (ZSpan.floor b v : logSpace F)) ⟨w, hw⟩
    rw [← hx] at h1
    have h2 : (logEmbedding F).toIntLinearMap x ⟨w, hw⟩
        = mult w * Real.log (w ((ε : 𝓞 F) : F)) := rfl
    rw [Pi.sub_apply, h2, Real.norm_eq_abs] at h1
    have h3 : e w = -(v ⟨w, hw⟩ - mult w * Real.log (w ((ε : 𝓞 F) : F))) := by
      simp only [e, v]; ring
    rw [h3, abs_neg]
    rw [← hx] at hfr
    linarith
  have he_sum : ∑ w, e w = 0 := by
    have h := sum_mult_mul_log ε
    have h2 : ∑ w : InfinitePlace F, (mult w : ℝ) * (n * uw w)
        = n * ∑ w, (mult w : ℝ) * uw w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [e, mul_sub, Finset.sum_sub_distrib, h2, hsum', mul_zero, sub_zero]
    exact h
  have he : ∀ w, |e w| ≤ Fintype.card (InfinitePlace F) * R := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      have h := Finset.add_sum_erase Finset.univ e (Finset.mem_univ w₀)
      rw [he_sum] at h
      have h3 : e w₀ = -∑ w ∈ Finset.univ.erase w₀, e w := by linarith
      rw [h3, abs_neg]
      calc |∑ w ∈ Finset.univ.erase w₀, e w| ≤ ∑ w ∈ Finset.univ.erase w₀, |e w| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w ∈ Finset.univ.erase w₀, R :=
            Finset.sum_le_sum fun w hw => he_ne w (Finset.ne_of_mem_erase hw)
        _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    · exact (he_ne w hw).trans (le_mul_of_one_le_left hR0 hcard)
  intro sg
  have hm : (1 : ℝ) ≤ mult (InfinitePlace.mk sg) := one_le_mult
  have h4 : |Real.log ‖sg ((ε : 𝓞 F) : F)‖ - n * u sg| ≤ |e (InfinitePlace.mk sg)| := by
    simp only [e, abs_mul, hu_mk sg, InfinitePlace.apply, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) hm
  exact h4.trans (he _)
end UnitApprox
end GroundTheory.Heights₂.Heights.HilbertSamuel
