-- Prove2me | solution 1 for StrategicAlloc.EFXTwoThirds.theorem_2_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:54:58.324228+00:00
-- url     : https://prove2.me/submissions/d572fede-de89-4b9c-9107-325f4dbad233

import Mathlib
import Definitions.Def_StrategicAlloc_EFXTwoThirds_Setting

set_option autoImplicit false
open StrategicAlloc.EFXTwoThirds

theorem mms_le_aux {m : ℕ} (v : Fin m → ℝ) (B : ℝ)
    (hB : ∀ f : Fin m → Fin 2, ∃ j0 : Fin 2,
      ∑ g ∈ Finset.univ.filter (fun g => f g = j0), v g ≤ B) :
    LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v g) 2 Finset.univ ≤ B := by
  classical
  unfold LittleCharity.MMS.mms
  apply ciSup_le
  intro f
  obtain ⟨j0, hj0⟩ := hB f
  refine le_trans (ciInf_le (Set.finite_range _).bddBelow j0) ?_
  convert hj0

theorem part_sum_aux {m : ℕ} (v : Fin m → ℝ) (f : Fin m → Fin 2) :
    ∑ g ∈ Finset.univ.filter (fun g => f g = 0), v g +
      ∑ g ∈ Finset.univ.filter (fun g => f g = 1), v g = ∑ g, v g := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g => f g = 0)]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext g
  have : ∀ x : Fin 2, ¬ x = 0 ↔ x = 1 := by decide
  simp [this]

theorem efx2_aux {m : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) (X Y : Finset (Fin m))
    (hdisj : Disjoint X Y) (hU : X ∪ Y = Finset.univ)
    (hefx : ∀ g ∈ Y, 0 < v g → ∑ h ∈ Y.erase g, v h ≤ ∑ h ∈ X, v h) :
    2 / 3 * LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v g) 2 Finset.univ ≤ ∑ g ∈ X, v g := by
  have hT : ∑ g, v g = ∑ g ∈ X, v g + ∑ g ∈ Y, v g := by
    rw [← Finset.sum_union hdisj, hU]
  have ha : 0 ≤ ∑ g ∈ X, v g := Finset.sum_nonneg (fun g _ => hv g)
  have hb : 0 ≤ ∑ g ∈ Y, v g := Finset.sum_nonneg (fun g _ => hv g)
  set a := ∑ g ∈ X, v g with hadef
  set b := ∑ g ∈ Y, v g with hbdef
  by_cases hb2 : b ≤ 2 * a
  · have hmms : LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v g) 2 Finset.univ ≤ (a + b) / 2 := by
      apply mms_le_aux
      intro f
      have hps := part_sum_aux v f
      rw [hT] at hps
      by_cases h : ∑ g ∈ Finset.univ.filter (fun g => f g = 0), v g ≤ (a + b) / 2
      · exact ⟨0, h⟩
      · exact ⟨1, by linarith⟩
    linarith
  · push_neg at hb2
    -- some positive good in Y
    obtain ⟨g0, hg0Y, hg0pos⟩ : ∃ g ∈ Y, 0 < v g := by
      by_contra hcon
      push_neg at hcon
      have : b = 0 := Finset.sum_eq_zero (fun g hg => le_antisymm (hcon g hg) (hv g))
      linarith
    have hefxg : ∀ g ∈ Y, 0 < v g → b - v g ≤ a := by
      intro g hg hpos
      have := hefx g hg hpos
      rw [Finset.sum_erase_eq_sub hg] at this
      exact this
    have hbig : ∀ g ∈ Y, 0 < v g → b < 2 * v g := by
      intro g hg hpos
      have := hefxg g hg hpos
      linarith
    -- all other goods of Y are worthless
    have hzero : ∀ h ∈ Y, h ≠ g0 → v h = 0 := by
      intro h hh hne
      by_contra hne0
      have hpos : 0 < v h := lt_of_le_of_ne (hv h) (Ne.symm hne0)
      have h1 := hbig h hh hpos
      have h2 := hbig g0 hg0Y hg0pos
      have hpair : v h + v g0 ≤ b := by
        have : ∑ x ∈ ({h, g0} : Finset (Fin m)), v x ≤ ∑ x ∈ Y, v x :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
            (fun x _ _ => hv x)
        rwa [Finset.sum_pair hne] at this
      linarith
    have hbv : b = v g0 := by
      rw [hbdef, ← Finset.add_sum_erase Y v hg0Y]
      have : ∑ x ∈ Y.erase g0, v x = 0 :=
        Finset.sum_eq_zero (fun x hx => hzero x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx))
      rw [this, add_zero]
    have hmms : LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v g) 2 Finset.univ ≤ a := by
      apply mms_le_aux
      intro f
      have hrest : ∑ g ∈ Finset.univ.erase g0, v g = a := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ g0), hT, hbv]; ring
      by_cases h0 : f g0 = 0
      · refine ⟨1, ?_⟩
        rw [← hrest]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          rintro rfl
          rw [h0] at hx
          exact absurd hx (by decide)
        · intro x _ _; exact hv x
      · refine ⟨0, ?_⟩
        rw [← hrest]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          rintro rfl
          exact h0 hx
        · intro x _ _; exact hv x
    linarith

theorem solution {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (A : Fin 2 → Finset (Fin m)) (hA : IsAllocation A) (hEFX : IsEFX v A) :
    StrategicAlloc.EFXFour.IsApproxMMS (2 / 3) v A := by
  have hU : A 0 ∪ A 1 = Finset.univ := by
    have := hA.2
    ext g
    constructor
    · intro _; exact Finset.mem_univ g
    · intro _
      have hg : g ∈ Finset.univ.biUnion A := by rw [this]; exact Finset.mem_univ g
      rw [Finset.mem_biUnion] at hg
      obtain ⟨k, _, hk⟩ := hg
      fin_cases k
      · exact Finset.mem_union_left _ hk
      · exact Finset.mem_union_right _ hk
  have hd01 : Disjoint (A 0) (A 1) := hA.1 (by decide)
  have hd10 : Disjoint (A 1) (A 0) := hA.1 (by decide)
  intro i
  fin_cases i
  · show 2 / 3 * LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v 0 g) 2 Finset.univ ≤ ∑ g ∈ A 0, v 0 g
    refine efx2_aux (v 0) (hv 0) (A 0) (A 1) hd01 hU ?_
    intro g hg hpos
    exact hEFX 0 1 ⟨g, hg⟩ g hg hpos
  · show 2 / 3 * LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v 1 g) 2 Finset.univ ≤ ∑ g ∈ A 1, v 1 g
    refine efx2_aux (v 1) (hv 1) (A 1) (A 0) hd10 (by rw [Finset.union_comm]; exact hU) ?_
    intro g hg hpos
    exact hEFX 1 0 ⟨g, hg⟩ g hg hpos
