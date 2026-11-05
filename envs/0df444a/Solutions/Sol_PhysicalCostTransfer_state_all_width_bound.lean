-- Prove2me | solution 1 for PhysicalCostTransfer.state_all_width_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/0c831946-250c-4b2e-91c4-12896d64d874

import Definitions.Def_SelectedFloorTransfer
import Definitions.Def_PhysicalCostTransfer
import Theorems.Thm_FloorDepth_child_pos
import Theorems.Thm_FloorRecurrence_floor_child_power
import Theorems.Thm_FloorRecurrence_one_le_width_power


set_option autoImplicit true
open PhysicalCostTransfer
open scoped BigOperators
namespace PhysicalCostTransfer
theorem _root_.solution {S ι : Type} (rows : List ι)
    (rank count : ι → ℕ) (m W : ℕ)
    (width : S → ℕ) (volume cost : S → ℝ)
    (child : S → (r : ι) → Fin (count r) → S)
    (p A B C γ : ℝ) (hm : 0 < m) (hW : 0 < W) (hp : 0 ≤ p)
    (hA : 0 ≤ A) (hBA : B ≤ A) (hbudget : C ≤ A * (1 - γ))
    (hvolume : ∀ s, 0 ≤ volume s)
    (hrank : ∀ r ∈ rows, 0 < rank r) (hrankm : ∀ r ∈ rows, rank r < m)
    (hγ : γ = (rows.map (fun r => (count r : ℝ) / W * ((rank r : ℝ) / m) ^ p)).sum)
    (hγ1 : γ < 1)
    (child_width : ∀ s, m ≤ width s → ∀ r ∈ rows, ∀ j,
      width (child s r j) = rank r * (width s / m))
    (child_volume : ∀ s, m ≤ width s → ∀ r ∈ rows, ∀ j,
      volume (child s r j) = volume s / W)
    (uniform_base : ∀ s, 0 < width s → width s < m → cost s ≤ B * volume s)
    (physical_recurrence : ∀ s, m ≤ width s → cost s ≤ C * volume s +
      (rows.map (fun r => ∑ j : Fin (count r), cost (child s r j))).sum) :
    ∀ s, 0 < width s → cost s ≤ A * volume s * (width s : ℝ) ^ p := by
  have main : ∀ e, ∀ s, width s = e → 0 < e → cost s ≤ A * volume s * (e : ℝ) ^ p := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
      intro s hwidth he
      have hAV : 0 ≤ A * volume s := mul_nonneg hA (hvolume s)
      have hepow := FloorRecurrence.one_le_width_power e p he hp
      by_cases hb : e < m
      · calc
          cost s ≤ B * volume s := uniform_base s (by simpa [hwidth] using he) (by simpa [hwidth] using hb)
          _ ≤ A * volume s := mul_le_mul_of_nonneg_right hBA (hvolume s)
          _ ≤ A * volume s * (e : ℝ) ^ p := by simpa using mul_le_mul_of_nonneg_left hepow hAV
      · have hem : m ≤ e := Nat.le_of_not_gt hb
        have hinternal : m ≤ width s := by simpa [hwidth] using hem
        have hrow : ∀ r ∈ rows, (∑ j : Fin (count r), cost (child s r j)) ≤
            (count r : ℝ) * (A * (volume s / W) * (((rank r : ℝ) / m) ^ p * (e : ℝ) ^ p)) := by
          intro r hr
          have hpoint : ∀ j : Fin (count r), cost (child s r j) ≤
              A * (volume s / W) * (((rank r : ℝ) / m) ^ p * (e : ℝ) ^ p) := by
            intro j
            have hcw : width (child s r j) = FloorDepth.child m (rank r) e := by
              simpa [FloorDepth.child, hwidth] using child_width s hinternal r hr j
            have hcpos := FloorDepth.child_pos m (rank r) e hm (hrank r hr) hem
            have hclt := FloorDepth.child_lt m (rank r) e (hrankm r hr) hem
            have hbnd := ih (FloorDepth.child m (rank r) e) hclt (child s r j) hcw hcpos
            rw [child_volume s hinternal r hr j] at hbnd
            have hfactor : 0 ≤ A * (volume s / W) :=
              mul_nonneg hA (div_nonneg (hvolume s) (by exact_mod_cast hW.le))
            exact hbnd.trans (mul_le_mul_of_nonneg_left
              (FloorRecurrence.floor_child_power m (rank r) e p hm hp) hfactor)
          calc
            _ ≤ ∑ _j : Fin (count r),
                A * (volume s / W) * (((rank r : ℝ) / m) ^ p * (e : ℝ) ^ p) :=
              Finset.sum_le_sum (fun j _ => hpoint j)
            _ = _ := by simp
        have hsum : (rows.map (fun r => (count r : ℝ) *
            (A * (volume s / W) * (((rank r : ℝ) / m) ^ p * (e : ℝ) ^ p)))).sum =
            A * volume s * γ * (e : ℝ) ^ p := by
          calc
            _ = (rows.map (fun r => ((count r : ℝ) / W * ((rank r : ℝ) / m) ^ p) *
                (A * volume s * (e : ℝ) ^ p))).sum := by
              congr 1
              apply List.map_congr_left
              intro r hr
              ring
            _ = γ * (A * volume s * (e : ℝ) ^ p) := by rw [List.sum_map_mul_right, ← hγ]
            _ = _ := by ring
        have hgap : 0 ≤ A * volume s * (1 - γ) := mul_nonneg hAV (by linarith)
        have hover : C * volume s ≤ A * volume s * (1 - γ) := by
          have h := mul_le_mul_of_nonneg_right hbudget (hvolume s)
          nlinarith
        have hpaid : C * volume s ≤ A * volume s * (1 - γ) * (e : ℝ) ^ p :=
          hover.trans (by simpa using mul_le_mul_of_nonneg_left hepow hgap)
        calc
          cost s ≤ C * volume s + (rows.map (fun r => ∑ j : Fin (count r), cost (child s r j))).sum :=
            physical_recurrence s hinternal
          _ ≤ C * volume s + (rows.map (fun r => (count r : ℝ) *
              (A * (volume s / W) * (((rank r : ℝ) / m) ^ p * (e : ℝ) ^ p)))).sum :=
            add_le_add (le_refl (C * volume s)) (List.sum_le_sum hrow)
          _ = C * volume s + A * volume s * γ * (e : ℝ) ^ p := by rw [hsum]
          _ ≤ A * volume s * (e : ℝ) ^ p := by nlinarith [hpaid]
  intro s hs
  exact main (width s) s rfl hs
end PhysicalCostTransfer
