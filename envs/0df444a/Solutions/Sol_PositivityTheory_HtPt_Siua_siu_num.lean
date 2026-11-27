-- Prove2me | solution 1 for PositivityTheory.HtPt.Siua.siu_num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:51.958439+00:00
-- url     : https://prove2.me/submissions/8dedaebf-206b-4502-88eb-b85a82dfc802

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_SiuaNum
import Theorems.Thm_PositivityTheory_HtPt_Siua_form_cast
import Theorems.Thm_PositivityTheory_HtPt_Siua_form_smul
import Theorems.Thm_PositivityTheory_HtPt_Siua_form_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.Siua
open Filter Topology
namespace PositivityTheory.HtPt.Siua
theorem _root_.solution : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e) := by
  intro M _ d f μ e hf
  obtain ⟨x2, hx2⟩ : ∃ x2 : Fin (d + 1) → ℚ, x2 = Fin.snoc (α := fun _ => ℚ) (fun _ : Fin d => (1 : ℚ)) 0 :=
    ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y2 : Fin (d + 1) → ℚ, y2 = Fin.snoc (α := fun _ => ℚ) (fun _ : Fin d => (1 : ℚ)) 2 :=
    ⟨_, rfl⟩
  have hc1 : Continuous fun t : ℚ =>
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) :=
    PositivityTheory.HtPt.Siua.form_cont f μ e _ (fun _ => 1)
  have hc2 : Continuous fun t : ℚ => PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) :=
    PositivityTheory.HtPt.Siua.form_cont f μ e x2 y2
  have hc : Continuous fun t : ℚ =>
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) -
        ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) :=
    hc1.sub (continuous_const.mul hc2)
  have h10 : PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * 0) = (f (fun _ => μ) : ℚ) := by
    have h := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => 1) (fun _ => 0)
    simp only [one_smul, zero_smul, add_zero, Int.cast_one, Int.cast_zero] at h
    simp only [mul_zero]
    exact h.symm
  have h20 : PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * 0) = 0 := by
    simp only [PositivityTheory.HtPt.Siua.form, mul_zero]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [Finset.prod_eq_zero (f := fun i => if i ∈ s then x2 i else 0) (Finset.mem_univ (Fin.last d))
      (by simp [hx2]), zero_mul]
  have hG0 : (0 : ℚ) < PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * 0) -
      ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * 0) := by
    rw [h10, h20]
    simpa using hf
  have hev := (hc.tendsto 0).eventually (lt_mem_nhds hG0)
  obtain ⟨t, hGt, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℚ) ∈ 𝓝[>] 0)).exists
  have hGt' : (0 : ℚ) < PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) -
      ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) := hGt
  refine ⟨t, ht, ?_⟩
  intro a m ha hm
  have hR : (f (fun _ => a • μ + m • e) : ℚ) =
      (a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) := by
    have h := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => (a : ℤ)) (fun _ => m)
    rw [← PositivityTheory.HtPt.Siua.form_smul]
    simp only [natCast_zsmul] at h
    rw [h]
    congr 1
    · funext i
      simp
    · funext i
      simp [hm]
  have hfun : (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) =
      fun i => (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => (a : ℤ)) 0 i) • μ +
        (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => m) (2 * m) i) • e := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [natCast_zsmul]
  have hL : (f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) : ℚ) =
      (a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) := by
    have h := PositivityTheory.HtPt.Siua.form_cast f μ e
      (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => (a : ℤ)) 0)
      (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => m) (2 * m))
    rw [← PositivityTheory.HtPt.Siua.form_smul, hfun, h]
    congr 1
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [hx2]
      · simp [hx2]
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hy2]
        simp only [Fin.snoc_last, Int.cast_mul, Int.cast_ofNat, hm]
        ring
      · simp [hy2, hm]
  have hpos : (0 : ℚ) < (a : ℚ) ^ (d + 1) := pow_pos (by exact_mod_cast (show 0 < a by omega)) _
  have hlt : ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) <
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) := by
    linarith
  rw [← Int.cast_lt (R := ℚ), Int.cast_mul, hL, hR]
  calc (((d + 1 : ℕ) : ℤ) : ℚ) * ((a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t))
      = (a : ℚ) ^ (d + 1) * (((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t)) := by
        push_cast
        ring
    _ < (a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) :=
        mul_lt_mul_of_pos_left hlt hpos
end PositivityTheory.HtPt.Siua
