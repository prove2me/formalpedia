-- Prove2me | solution 1 for StrategicAlloc.RRExists.equilibrium_transfer
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:24:11.449989+00:00
-- url     : https://prove2.me/submissions/eb8bac21-1dec-40d2-9b9b-488bf0c03138

import Mathlib
import Definitions.Def_StrategicAlloc_RRExists_Setting

set_option autoImplicit false

lemma bundleGap_pos {m : ℕ} (w : Fin m → ℝ) : 0 < StrategicAlloc.RRExists.bundleGap w := by
  unfold StrategicAlloc.RRExists.bundleGap
  simp only
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    rw [Finset.mem_image] at hm
    obtain ⟨p, hp, hpe⟩ := hm
    rw [Finset.mem_filter] at hp
    rw [← hpe]
    exact abs_pos.mpr (sub_ne_zero.mpr hp.2)
  · exact one_pos

lemma bundleGap_le {m : ℕ} (w : Fin m → ℝ) (T T' : Finset (Fin m))
    (hne : ∑ g ∈ T, w g ≠ ∑ g ∈ T', w g) :
    StrategicAlloc.RRExists.bundleGap w ≤ |∑ g ∈ T, w g - ∑ g ∈ T', w g| := by
  unfold StrategicAlloc.RRExists.bundleGap
  simp only
  have hmem : |∑ g ∈ T, w g - ∑ g ∈ T', w g| ∈
      ((Finset.univ.powerset ×ˢ Finset.univ.powerset).filter
      (fun p : Finset (Fin m) × Finset (Fin m) => ∑ g ∈ p.1, w g ≠ ∑ g ∈ p.2, w g)).image
    (fun p => |∑ g ∈ p.1, w g - ∑ g ∈ p.2, w g|) := by
    rw [Finset.mem_image]
    exact ⟨(T, T'), by simp [hne], rfl⟩
  rw [dif_pos ⟨_, hmem⟩]
  exact Finset.min'_le _ _ hmem

theorem solution {n m : ℕ} [NeZero n] (v v' : Fin n → Fin m → ℝ)
    (hclose : ∀ i (T : Finset (Fin m)), StrategicAlloc.RRFair.val v i T ≤ StrategicAlloc.RRFair.val v' i T ∧
      StrategicAlloc.RRFair.val v' i T ≤ StrategicAlloc.RRFair.val v i T + 2 * StrategicAlloc.RRExists.bundleGap (v i) / 3)
    (d : Fin n → Fin m → ℝ) (hd : StrategicAlloc.RRFair.IsPNE StrategicAlloc.RRFair.roundRobin v' d) :
    StrategicAlloc.RRFair.IsPNE StrategicAlloc.RRFair.roundRobin v d := by
  obtain ⟨hbid, hbr⟩ := hd
  refine ⟨hbid, fun i b' hb' => ?_⟩
  have h1 := hbr i b' hb'
  set T := StrategicAlloc.RRFair.roundRobin (Function.update d i b') i with hT
  set A := StrategicAlloc.RRFair.roundRobin d i with hA
  have c1 := (hclose i T).1
  have c2 := (hclose i A).2
  by_contra hcon
  push_neg at hcon
  have hne : ∑ g ∈ T, v i g ≠ ∑ g ∈ A, v i g := by
    intro h
    unfold StrategicAlloc.RRFair.val at hcon
    linarith
  have hle := bundleGap_le (v i) T A hne
  have hpos := bundleGap_pos (v i)
  unfold StrategicAlloc.RRFair.val at hcon c1 c2 h1
  rw [abs_of_pos (by linarith)] at hle
  linarith
