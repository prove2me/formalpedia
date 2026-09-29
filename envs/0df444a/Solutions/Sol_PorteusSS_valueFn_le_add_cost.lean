-- Prove2me | solution 1 for PorteusSS.valueFn_le_add_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:04:29.551557+00:00
-- url     : https://prove2.me/submissions/f71efbae-ce2b-4916-af08-8eae591c5160

import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost
import Definitions.Def_PorteusSS_Model

open MeasureTheory Filter Topology Set

namespace PorteusSS

theorem aux_vfle_subadd (c : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ici 0) c) (h0 : c 0 = 0)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : c (a + b) ≤ c a + c b := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hs | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0; subst hb0; simp [h0]
  · have h0mem : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr (le_refl 0)
    have hsmem : a + b ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr (le_of_lt hs)
    have k1 := hconc.2 h0mem hsmem (div_nonneg hb hs.le) (div_nonneg ha hs.le)
      (by field_simp; try ring)
    have k2 := hconc.2 h0mem hsmem (div_nonneg ha hs.le) (div_nonneg hb hs.le)
      (by field_simp; try ring)
    simp only [smul_eq_mul, mul_zero, zero_add, h0] at k1 k2
    have e1 : a / (a + b) * (a + b) = a := by field_simp
    have e2 : b / (a + b) * (a + b) = b := by field_simp
    rw [e1] at k1
    rw [e2] at k2
    have : a / (a + b) * c (a + b) + b / (a + b) * c (a + b) = c (a + b) := by
      rw [← add_mul, ← add_div, div_self hs.ne', one_mul]
    linarith

end PorteusSS

open PorteusSS
open MeasureTheory Filter Topology Set

theorem solution (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ)
    (hmodel : IsModel c m φ α c0 K0 cInf KInf) (n : ℕ) (hn : 1 ≤ n)
    (hfin : ∀ x : ℝ, BddBelow (range fun w : Ici x => c ((w : ℝ) - x) + hFn c m φ f0 α n w))
    (x y : ℝ) (hxy : x ≤ y) :
    valueFn c m φ f0 α n x ≤ valueFn c m φ f0 α n y + c (y - x) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hF : ∀ w : ℝ, hFn c m φ f0 α (k + 1) w = hStep m φ α (valueFn c m φ f0 α k) w :=
    fun _ => rfl
  simp only [hF] at hfin
  have hx := hfin x
  show (⨅ w : Ici x, c ((w : ℝ) - x) + hStep m φ α (valueFn c m φ f0 α k) w) ≤
    (⨅ w : Ici y, c ((w : ℝ) - y) + hStep m φ α (valueFn c m φ f0 α k) w) + c (y - x)
  rw [← sub_le_iff_le_add]
  have : Nonempty (Ici y) := ⟨⟨y, le_refl y⟩⟩
  apply le_ciInf
  intro w
  have hwx : x ≤ (w : ℝ) := le_trans hxy w.2
  have h1 := ciInf_le hx (⟨(w : ℝ), hwx⟩ : Ici x)
  have h2 := aux_vfle_subadd c hmodel.cost.concave hmodel.cost.zero ((w : ℝ) - y) (y - x)
    (sub_nonneg.mpr w.2) (sub_nonneg.mpr hxy)
  have e : (w : ℝ) - y + (y - x) = (w : ℝ) - x := by ring
  rw [e] at h2
  simp only at h1
  linarith
