-- Prove2me | solution 2 for PinwheelDensity.ExactRange.theorem_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:58:52.350532+00:00
-- url     : https://prove2.me/submissions/5294ceee-ea1b-41ed-ad95-612ba0dfc20b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP
import Definitions.Def_RealPinwheel_FiveSixths_Instance
import Theorems.Thm_RealPinwheel_FiveSixths_Supplement_seventeen_twentieths_periodic
import Theorems.Thm_PinwheelDensity_ExactRange_prop_2_3

set_option autoImplicit false

namespace PinwheelDensity.ExactRange.AltRoute

open PinwheelDensity.ExactRange
open RealPinwheel.FiveSixths

lemma density_cast_eq (A : List ℕ) : ((density A : ℚ) : ℝ) = ∑ i, (1 : ℝ) / (A.get i : ℝ) := by
  have hlist : (List.ofFn fun i => (1 : ℝ) / (A.get i : ℝ)) =
      A.map (fun a => (1 : ℝ) / (a : ℝ)) := by
    calc
      (List.ofFn fun i => (1 : ℝ) / (A.get i : ℝ)) =
          (List.ofFn A.get).map (fun a : ℕ => (1 : ℝ) / (a : ℝ)) := by
        rw [List.map_ofFn]
        rfl
      _ = A.map (fun a => (1 : ℝ) / (a : ℝ)) := by
        rw [List.ofFn_get]
        induction A with
        | nil => rfl
        | cons a t ih => simp_all
  rw [← List.sum_ofFn, hlist]
  change (((A.map fun a => (1 : ℚ) / (a : ℚ)).sum : ℚ) : ℝ) = _
  simp only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_one]
  induction A with
  | nil => rfl
  | cons a t ih => simp_all

/-- The integer minimum-period-four guarantee follows from the real-period companion theorem. -/
theorem guarantee_four_of_real_supplement : Guarantee 4 (17 / 20) := by
  intro A hA hd
  by_cases hne : A = []
  · subst A
    refine ⟨fun _ => none, ?_⟩
    intro i
    exact Fin.elim0 i
  · have hk : 1 ≤ A.length := List.length_pos_of_ne_nil hne
    set σ : Equiv.Perm (Fin A.length) := Tuple.sort A.get with hσ
    have hmono : Monotone (A.get ∘ σ) := Tuple.monotone_sort A.get
    let R : RealPinwheel.FiveSixths.Instance A.length :=
      { positive_dimension := hk
        period := fun i => (A.get (σ i) : ℝ)
        one_le := fun i => by
          have hi := (hA (A.get (σ i)) (List.get_mem A (σ i))).1
          exact_mod_cast hi
        ordered := fun a b hab => by
          have hh := hmono hab
          simp only [Function.comp] at hh
          show (A.get (σ a) : ℝ) ≤ (A.get (σ b) : ℝ)
          exact_mod_cast hh }
    have hmin : 4 ≤ R.period ⟨0, hk⟩ := by
      change (4 : ℝ) ≤ (A.get (σ ⟨0, hk⟩) : ℝ)
      have hi := (hA (A.get (σ ⟨0, hk⟩)) (List.get_mem A (σ ⟨0, hk⟩))).2
      exact_mod_cast hi
    have hD : RealPinwheel.FiveSixths.density R ≤ (17 : ℝ) / 20 := by
      have hreindex : RealPinwheel.FiveSixths.density R =
          ∑ i, (1 : ℝ) / (A.get i : ℝ) := by
        unfold RealPinwheel.FiveSixths.density
        exact Equiv.sum_comp σ (fun i => (1 : ℝ) / (A.get i : ℝ))
      rw [hreindex, ← density_cast_eq]
      have hcast : ((density A : ℚ) : ℝ) ≤ ((17 / 20 : ℚ) : ℝ) := by exact_mod_cast hd
      norm_num at hcast ⊢
      exact hcast
    obtain ⟨L, S, hL, hbound, hper, hV⟩ :=
      RealPinwheel.FiveSixths.Supplement.seventeen_twentieths_periodic R hmin hD
    refine ⟨fun d => some (σ (S d)), ?_⟩
    intro j n
    have hc := hV (σ.symm j) 1 one_pos n
    have hceil : ⌈((1 : ℕ) : ℝ) * R.period (σ.symm j)⌉₊ = A.get j := by
      simp [R]
    rw [hceil] at hc
    have hpos : 0 < ((Finset.range (A.get j)).filter fun t => S (n + t) = σ.symm j).card := by
      unfold windowCount at hc
      omega
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter, Finset.mem_range] at ht
    refine ⟨n + t, by omega, by omega, ?_⟩
    simp [ht.2]

/-- Sharpness from Proposition 2.3 turns the attained guarantee into the exact threshold. -/
theorem exact_of_guarantee (m : ℕ) (hm : 4 ≤ m) (hG : Guarantee m (c m)) :
    G m = ((c m : ℚ) : ℝ) ∧ IsGreatest (ThresholdSet m) ((c m : ℚ) : ℝ) := by
  have hmem : ((c m : ℚ) : ℝ) ∈ ThresholdSet m := by
    intro A hA hd
    exact hG A hA (by exact_mod_cast hd)
  have hub : ((c m : ℚ) : ℝ) ∈ upperBounds (ThresholdSet m) := by
    intro δ hδ
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (δ - ((c m : ℚ) : ℝ)))
    set x : ℕ := n + m with hx
    have hpos : 0 < δ - ((c m : ℚ) : ℝ) := sub_pos.mpr hlt
    have hxpos : (0 : ℝ) < x := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      rw [hx]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hxbig : 1 / (δ - ((c m : ℚ) : ℝ)) < x := by
      rw [hx]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hinv : (1 : ℝ) / x ≤ δ - ((c m : ℚ) : ℝ) := by
      rw [div_le_iff₀ hxpos]
      rw [div_lt_iff₀ hpos] at hxbig
      linarith
    have h1 : 1 ≤ m := by omega
    obtain ⟨hns, hdens⟩ := (prop_2_3 m h1).1 x (by rw [hx]; omega)
    apply hns
    apply hδ
    · intro a ha
      simp only [sharpCore, List.cons_append, List.mem_cons, List.mem_append,
        List.mem_replicate, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | ⟨_, rfl⟩ | rfl
      · omega
      · omega
      · rw [hx]; omega
    · rw [hdens]
      push_cast
      linarith
  have hgr : IsGreatest (ThresholdSet m) ((c m : ℚ) : ℝ) := ⟨hmem, hub⟩
  exact ⟨hgr.csSup_eq, hgr⟩

theorem c_four : c 4 = 17 / 20 := by norm_num [c]

end PinwheelDensity.ExactRange.AltRoute

open PinwheelDensity.ExactRange
open PinwheelDensity.ExactRange.AltRoute

/-- Theorem 1.2 (Minimum period four), p. 2, including attainment of the supremum. -/
theorem solution :
    Guarantee 4 (17 / 20) ∧ G 4 = 17 / 20 ∧ IsGreatest (ThresholdSet 4) (17 / 20) := by
  have hG : Guarantee 4 (17 / 20) := guarantee_four_of_real_supplement
  have hG' : Guarantee 4 (c 4) := by rw [c_four]; exact hG
  obtain ⟨h1, h2⟩ := exact_of_guarantee 4 (le_refl _) hG'
  rw [c_four] at h1 h2
  refine ⟨hG, ?_, ?_⟩
  · rw [h1]; norm_num
  · convert h2 using 1; norm_num
