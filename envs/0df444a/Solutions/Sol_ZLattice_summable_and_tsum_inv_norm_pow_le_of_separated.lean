-- Prove2me | solution 1 for ZLattice.summable_and_tsum_inv_norm_pow_le_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8f8fab07-552b-5598-af34-39510e7d6176

import Mathlib.Algebra.Module.ZLattice.Summable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZLattice_summable_and_tsum_inv_norm_pow_le_of_separated

set_option autoImplicit false

noncomputable section

open Function Module

namespace H2Sol

section Lattice

variable (W : Type*) [Fintype W]

abbrev supLattice : Submodule ℤ (W → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ W))

theorem finrank_supLattice : Module.finrank ℤ (supLattice W) = Fintype.card W := by
  rw [ZLattice.rank ℝ, Module.finrank_fintype_fun_eq_card]

def latticeConst (k : ℕ) : ℝ := ∑' x : supLattice W, ‖x‖⁻¹ ^ k

theorem summable_inv_norm_pow_supLattice {k : ℕ} (hk : Fintype.card W < k) :
    Summable fun x : supLattice W => ‖x‖⁻¹ ^ k :=
  ZLattice.summable_norm_pow_inv _ k (by rwa [finrank_supLattice])

theorem latticeConst_nonneg (k : ℕ) : 0 ≤ latticeConst W k :=
  tsum_nonneg fun _ => by positivity

theorem intCast_mem_supLattice (z : W → ℤ) : (fun w => (z w : ℝ)) ∈ supLattice W := by
  rw [Basis.mem_span_iff_repr_mem]
  intro w
  exact ⟨z w, by simp⟩

end Lattice

section Packing

variable {W : Type*} [Fintype W] {ι : Type*}

theorem abs_intCast_floor_le (x : ℝ) : |((⌊x⌋ : ℤ) : ℝ)| ≤ |x| + 1 := by
  rw [abs_le]
  refine ⟨?_, (Int.floor_le x).trans ((le_abs_self x).trans (le_add_of_nonneg_right zero_le_one))⟩
  have h1 := Int.lt_floor_add_one x
  have h2 := neg_abs_le x
  linarith

def gaugeBox (r : ℝ) (v : W → ℝ) : supLattice W :=
  ⟨fun w => ((⌊2 * v w / r⌋ : ℤ) : ℝ), intCast_mem_supLattice W _⟩

@[scoped simp] theorem coe_gaugeBox_apply (r : ℝ) (v : W → ℝ) (w : W) :
    (gaugeBox r v : W → ℝ) w = ((⌊2 * v w / r⌋ : ℤ) : ℝ) := rfl

theorem norm_sub_lt_of_gaugeBox_eq {r : ℝ} (hr : 0 < r) {v v' : W → ℝ} (h : gaugeBox r v = gaugeBox r v') :
    ‖v - v'‖ < r := by
  rw [pi_norm_lt_iff hr]
  intro w
  have hw : ⌊2 * v w / r⌋ = ⌊2 * v' w / r⌋ := by
    have h' := congrArg (fun x : supLattice W => (x : W → ℝ) w) h
    simpa only [coe_gaugeBox_apply, Int.cast_inj] using h'
  have h1 : |2 * v w / r - 2 * v' w / r| < 1 := Int.abs_sub_lt_one_of_floor_eq_floor hw
  have h2 : |2 * v w / r - 2 * v' w / r| = 2 / r * |v w - v' w| := by
    rw [← abs_of_pos (div_pos two_pos hr), ← abs_mul]
    congr 1
    ring
  rw [Pi.sub_apply, Real.norm_eq_abs]
  rw [h2] at h1
  have h3 : 2 / r * |v w - v' w| < 2 / r * (r / 2) := by
    rw [show 2 / r * (r / 2) = 1 by field_simp]
    exact h1
  have h4 : |v w - v' w| < r / 2 := lt_of_mul_lt_mul_left h3 (div_pos two_pos hr).le
  linarith

theorem gaugeBox_injective_of_separated {r : ℝ} (hr : 0 < r) {v : ι → W → ℝ}
    (hsep : ∀ i j, i ≠ j → r ≤ ‖v i - v j‖) : Injective fun i => gaugeBox r (v i) := by
  intro i j h
  by_contra hij
  exact absurd (norm_sub_lt_of_gaugeBox_eq hr h) (not_lt.mpr (hsep i j hij))

theorem norm_gaugeBox_le {r : ℝ} (hr : 0 < r) {v : W → ℝ} (hv : r ≤ ‖v‖) :
    ‖gaugeBox r v‖ ≤ 3 / r * ‖v‖ := by
  have h0 : 0 ≤ 3 / r * ‖v‖ := by positivity
  rw [Submodule.coe_norm, pi_norm_le_iff_of_nonneg h0]
  intro w
  rw [coe_gaugeBox_apply, Real.norm_eq_abs]
  refine (abs_intCast_floor_le _).trans ?_
  have h1 : |2 * v w / r| = 2 / r * |v w| := by
    rw [← abs_of_pos (div_pos two_pos hr), ← abs_mul]
    congr 1
    ring
  have h2 : |v w| ≤ ‖v‖ := by
    have := norm_le_pi_norm v w
    rwa [Real.norm_eq_abs] at this
  have h3 : (1 : ℝ) ≤ 1 / r * ‖v‖ := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hr, one_mul]
    exact hv
  calc |2 * v w / r| + 1 ≤ 2 / r * ‖v‖ + 1 / r * ‖v‖ := by
        rw [h1]
        exact add_le_add (mul_le_mul_of_nonneg_left h2 (div_pos two_pos hr).le) h3
    _ = 3 / r * ‖v‖ := by ring

theorem one_le_norm_gaugeBox {r : ℝ} (hr : 0 < r) {v : W → ℝ} (hv : r ≤ ‖v‖) : 1 ≤ ‖gaugeBox r v‖ := by

  obtain ⟨w, hw⟩ : ∃ w, r ≤ |v w| := by
    by_contra h
    simp only [not_exists, not_le] at h
    exact absurd ((pi_norm_lt_iff hr).mpr fun w => by rw [Real.norm_eq_abs]; exact h w) (not_lt.mpr hv)
  rw [Submodule.coe_norm]
  refine le_trans ?_ (norm_le_pi_norm (gaugeBox r v : W → ℝ) w)
  rw [coe_gaugeBox_apply, Real.norm_eq_abs]

  rcases le_abs'.mp hw with hneg | hpos
  ·
    have h1 : 2 * v w / r ≤ -2 := by
      rw [div_le_iff₀ hr]
      linarith
    have h2 : ((⌊2 * v w / r⌋ : ℤ) : ℝ) ≤ -2 := (Int.floor_le _).trans h1
    rw [le_abs']
    left
    linarith
  ·
    have h1 : (2 : ℝ) ≤ 2 * v w / r := by
      rw [le_div_iff₀ hr]
      linarith
    have h2 : (2 : ℤ) ≤ ⌊2 * v w / r⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
    have h3 : (2 : ℝ) ≤ ((⌊2 * v w / r⌋ : ℤ) : ℝ) := by exact_mod_cast h2
    rw [le_abs']
    right
    linarith

theorem inv_norm_pow_le_gaugeBox {r : ℝ} (hr : 0 < r) {v : W → ℝ} (hv : r ≤ ‖v‖) (k : ℕ) :
    ‖v‖⁻¹ ^ k ≤ (3 / r) ^ k * ‖gaugeBox r v‖⁻¹ ^ k := by
  have hz : 0 < ‖gaugeBox r v‖ := one_pos.trans_le (one_le_norm_gaugeBox hr hv)
  have hvpos : 0 < ‖v‖ := hr.trans_le hv
  have h1 : (3 / r * ‖v‖)⁻¹ ≤ ‖gaugeBox r v‖⁻¹ := inv_anti₀ hz (norm_gaugeBox_le hr hv)
  have h2 : ‖v‖⁻¹ = 3 / r * (3 / r * ‖v‖)⁻¹ := by
    field_simp
  have h3 : ‖v‖⁻¹ ≤ 3 / r * ‖gaugeBox r v‖⁻¹ := by
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  calc ‖v‖⁻¹ ^ k ≤ (3 / r * ‖gaugeBox r v‖⁻¹) ^ k := pow_le_pow_left₀ (by positivity) h3 k
    _ = (3 / r) ^ k * ‖gaugeBox r v‖⁻¹ ^ k := mul_pow _ _ _

theorem packing {r : ℝ} (hr : 0 < r) {v : ι → W → ℝ}
    (hsep : ∀ i j, i ≠ j → r ≤ ‖v i - v j‖) (hfar : ∀ i, r ≤ ‖v i‖) {k : ℕ} (hk : Fintype.card W < k) :
    Summable (fun i => ‖v i‖⁻¹ ^ k) ∧ ∑' i, ‖v i‖⁻¹ ^ k ≤ (3 / r) ^ k * latticeConst W k := by
  set g : supLattice W → ℝ := fun x => ‖x‖⁻¹ ^ k with hg_def
  have hg : Summable g := summable_inv_norm_pow_supLattice W hk
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hinj : Injective fun i => gaugeBox r (v i) := gaugeBox_injective_of_separated hr hsep
  have hcomp : Summable (g ∘ fun i => gaugeBox r (v i)) := hg.comp_injective hinj
  have hcomp' : Summable fun i => (3 / r) ^ k * g (gaugeBox r (v i)) := hcomp.mul_left _
  have hle : ∀ i, ‖v i‖⁻¹ ^ k ≤ (3 / r) ^ k * g (gaugeBox r (v i)) := fun i =>
    inv_norm_pow_le_gaugeBox hr (hfar i) k
  have hsum : Summable fun i => ‖v i‖⁻¹ ^ k := Summable.of_nonneg_of_le (fun i => by positivity) hle hcomp'
  refine ⟨hsum, ?_⟩
  calc ∑' i, ‖v i‖⁻¹ ^ k ≤ ∑' i, (3 / r) ^ k * g (gaugeBox r (v i)) := hsum.tsum_le_tsum hle hcomp'
    _ = (3 / r) ^ k * ∑' i, g (gaugeBox r (v i)) := tsum_mul_left
    _ ≤ (3 / r) ^ k * latticeConst W k :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hg hg0 hinj) (by positivity)

end Packing

end H2Sol
p2m_reactivate "P2MW.S_ZLattice_summable_and_tsum_inv_norm_pow_le_of_separated.H2Sol"

end
p2m_reactivate "P2MW.S_ZLattice_summable_and_tsum_inv_norm_pow_le_of_separated.H2Sol"

theorem solution
    {W : Type} [Fintype W] {ι : Type} {r : ℝ} (hr : 0 < r) {v : ι → W → ℝ}
    (hsep : ∀ i j, i ≠ j → r ≤ ‖v i - v j‖) (hfar : ∀ i, r ≤ ‖v i‖) {k : ℕ} (hk : Fintype.card W < k) :
    Summable (fun i => ‖v i‖⁻¹ ^ k) ∧
      ∑' i, ‖v i‖⁻¹ ^ k ≤ (3 / r) ^ k * ∑' x : Submodule.span ℤ (Set.range (Pi.basisFun ℝ W)), ‖x‖⁻¹ ^ k := by
  exact H2Sol.packing hr hsep hfar hk

#print axioms solution

end S_ZLattice_summable_and_tsum_inv_norm_pow_le_of_separated
end P2MW
export P2MW.S_ZLattice_summable_and_tsum_inv_norm_pow_le_of_separated (solution)
