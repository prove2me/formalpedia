-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.exists_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:24:28.76106+00:00
-- url     : https://prove2.me/submissions/f43566cb-023c-4e67-82c2-8cefb92c2589

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_exists_pow_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Vf
open Matrix GlobalTheory.WeilM
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]
variable {c} {J : Matrix β β A}
namespace PositivityTheory.ThKG.Loc.Cone.Vf
theorem _root_.solution {K : Type} [Field K] [Finite K] {k k' : Matrix β β K} (hk : k' * k = 1) {h δ : K} (hh : h + h = 1)
    (hδ : δ ≠ 0) : ∃ N, (1 + (1 - k) * ((-h) • 1 + δ • (1 - (1 + 1 + k + k') ^ N))).det ≠ 0 := by
  obtain ⟨N, hN, he⟩ := exists_pow_idem (1 + 1 + k + k')
  refine ⟨N, fun h0 => ?_⟩
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hk' : k * k' = 1 := mul_eq_one_comm.1 hk
  set x := 1 + 1 + k + k' with hx
  set u := 1 + k with hu
  have hxu : x = k' * (u * u) := by
    have : k' * (u * u) = k' + (k' * k) + (k' * k) + (k' * k) * k := by rw [hu]; noncomm_ring
    rw [this, hk, hx]; noncomm_ring
  have ck : Commute k x := by
    rw [hx]
    exact (((Commute.one_right k).add_right (Commute.one_right k)).add_right (Commute.refl k)).add_right (hk'.trans hk.symm)
  have cu : Commute u x := (Commute.one_left x).add_left ck
  set e := x ^ N with hed
  have ce : Commute k e := ck.pow_right N
  have h2 : (2 : K) * h = 1 := by rw [two_mul, hh]
  have hh0 : h ≠ 0 := fun h0 => by simp [h0] at hh
  have f1 : e * (1 + (1 - k) * ((-h) • 1 + δ • (1 - e))) = h • (u * e) := by
    have a1 : e * ((1 - k) * (1 - e)) = 0 := by
      rw [← Matrix.mul_assoc, ← ((Commute.one_left e).sub_left ce).eq, Matrix.mul_assoc, Matrix.mul_sub, he]; simp
    have a2 : e * (1 - k) = e - k * e := by rw [Matrix.mul_sub, ce.eq, Matrix.mul_one]
    rw [Matrix.mul_add (1 - k), Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, a1,
      Matrix.mul_one, Matrix.mul_one, a2, hu, Matrix.add_mul, Matrix.one_mul]
    have : e = (h + h) • e := by rw [hh, one_smul]
    conv_lhs => rw [smul_zero, add_zero]; enter [1]; rw [this]
    module
  have y1 : (u * e) *ᵥ y = 0 := by
    have := congrArg (e *ᵥ ·) hy
    simp only [Matrix.mulVec_mulVec, f1, Matrix.mulVec_zero, Matrix.smul_mulVec] at this
    exact (smul_eq_zero.1 this).resolve_left hh0
  have y2 : e *ᵥ y = 0 := by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have : e = x ^ N' * k' * u * (u * e) := by
      conv_lhs => rw [← he]
      rw [hed, pow_succ x N', hxu]; noncomm_ring
    rw [this, ← Matrix.mulVec_mulVec, y1, Matrix.mulVec_zero]
  have y3 : y = ((δ - h) / (2 * δ)) • (u *ᵥ y) := by
    have h20 : (2 : K) ≠ 0 := fun h0 => by simp [h0] at h2
    have a : (1 + (1 - k) * ((-h) • 1 + δ • (1 - e))) = (2 * δ) • 1 - (δ - h) • u - δ • ((1 - k) * e) := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hu]
      have : (1 : Matrix β β K) = (h + h) • 1 := by rw [hh, one_smul]
      conv_lhs => enter [1]; rw [this]
      module
    rw [a, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, y2, Matrix.mulVec_zero, smul_zero, sub_zero, Matrix.one_mulVec, sub_eq_zero] at hy
    rw [div_eq_inv_mul, mul_smul, ← hy, smul_smul, inv_mul_cancel₀ (mul_ne_zero h20 hδ), one_smul]
  have y4 : ∀ j : ℕ, y = ((δ - h) / (2 * δ)) ^ j • (u ^ j *ᵥ y) := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ u, ← Matrix.mulVec_mulVec, pow_succ, mul_smul, ← Matrix.mulVec_smul, ← y3]; exact ih
  have hux : u * u = k * x := by rw [hxu, ← Matrix.mul_assoc, hk', Matrix.one_mul]
  have : u ^ (2 * N) = k ^ N * e := by rw [pow_mul, pow_two, hux, ck.mul_pow]
  apply hy0
  rw [y4 (2 * N), this, ← Matrix.mulVec_mulVec, y2, Matrix.mulVec_zero, smul_zero]
end PositivityTheory.ThKG.Loc.Cone.Vf
