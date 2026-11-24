-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_MinkowskiCovolumeBound_proof_2210cebcfdbc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:17.429035+00:00
-- url     : https://prove2.me/submissions/a3aad749-d46c-411d-b583-1997d2947444

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PMinkowskiCovolumeBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real MeasureTheory Module
universe u
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace MinkowskiCovolumeBound
theorem _root_.solution : MinkowskiCovolumeBound.Statement.{u} := by
  intro V _ _ _ _ _ hm L _ _
  set m := finrank ℝ V with hm_def
  set lam := firstMinimum L with hlam
  set c := lam / √(m : ℝ) with hc

  have hlow : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖ := by
    intro v hv hv0
    exact csInf_le ⟨0, fun x ⟨_, _, _, hx⟩ => hx ▸ norm_nonneg _⟩ ⟨v, hv, hv0, rfl⟩
  have hlam0 : 0 ≤ lam := Real.sInf_nonneg (fun x ⟨_, _, _, hx⟩ => hx ▸ norm_nonneg _)
  have hcov : 0 ≤ ZLattice.covolume L := (ZLattice.covolume_pos L).le
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hc0' : 0 ≤ c := div_nonneg hlam0 (Real.sqrt_nonneg _)
  rcases hc0'.eq_or_lt with hc0 | hc0
  · rw [← hc0, zero_pow (by omega)]
    exact hcov
  by_contra hlt
  push Not at hlt

  let b := stdOrthonormalBasis ℝ V
  let f : V → (Fin m → ℝ) := fun x => WithLp.ofLp (b.repr x)
  have hf : MeasurePreserving f volume volume :=
    (PiLp.volume_preserving_ofLp (Fin m)).comp b.measurePreserving_repr
  let S : Set V := f ⁻¹' Metric.ball 0 c
  have hS_vol : volume S = ENNReal.ofReal ((2 * c) ^ m) := by
    rw [hf.measure_preimage measurableSet_ball.nullMeasurableSet, Real.volume_pi_ball _ hc0,
      Fintype.card_fin]
  have hS_symm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simpa [S, f, Metric.mem_ball, dist_zero_right, norm_neg] using hx
  have hS_conv : Convex ℝ S := by
    have hlin : IsLinearMap ℝ f := by
      constructor
      · intro x y; simp [f]
      · intro a x; simp [f]
    exact (convex_ball (0 : Fin m → ℝ) c).is_linear_preimage hlin

  let bZ := Free.chooseBasis ℤ L
  have fund := ZLattice.isAddFundamentalDomain bZ (volume : Measure V)
  have hcovF := ZLattice.covolume_eq_measure_fundamentalDomain L volume fund
  have hF_fin : volume (ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hbig : volume (ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ)) * 2 ^ finrank ℝ V
      < volume S := by
    rw [hS_vol, ← ENNReal.ofReal_toReal hF_fin, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_lt_ofReal_iff (pow_pos (by positivity) _), mul_pow, ← hm_def,
      mul_comm _ (2 ^ m)]
    have : (volume (ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ))).toReal
        = ZLattice.covolume L := by rw [hcovF]; rfl
    rw [this]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  have : Countable L.toAddSubgroup := (inferInstance : Countable L)
  obtain ⟨x, hx0, hxS⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (L := L.toAddSubgroup) fund
      hS_symm hS_conv hbig

  have hxL : (x : V) ∈ L := x.2
  have hxne : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hcoord : ∀ i, |b.repr (x : V) i| < c := by
    intro i
    have := hxS
    simp only [S, f, Set.mem_preimage, mem_ball_zero_iff] at this
    exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (WithLp.ofLp (b.repr (x : V))) i) this
  have hnormsq : ‖(x : V)‖ ^ 2 < lam ^ 2 := by
    rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖b.repr (x : V) i‖ ^ 2 < ∑ _i : Fin m, c ^ 2 := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
          · intro i _
            rw [Real.norm_eq_abs]
            exact pow_lt_pow_left₀ (hcoord i) (abs_nonneg _) (by norm_num)
      _ = lam ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc, div_pow,
            Real.sq_sqrt hm0.le]
          field_simp
  have := hlow _ hxL hxne
  nlinarith [norm_nonneg (x : V)]
end MinkowskiCovolumeBound
end GroundTheory.Heights₂.Heights.LowerBound
