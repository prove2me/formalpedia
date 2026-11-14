-- Prove2me | solution 1 for ProbabilityTheory.isCadlag_piecewisePath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:35:45.293412+00:00
-- url     : https://prove2.me/submissions/5a5f708f-cf5f-4c80-8dc8-07b687be480a

import Mathlib
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff
import Theorems.Thm_ProbabilityTheory_jumpCount_mono
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory Filter Set Topology
variable {x₀ b : ℝ} {T Y : ℕ → ℝ}
namespace ProbabilityTheory
private theorem exists_lt_jumpCount_const (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (s : ℝ) : ∃ a < s, ∃ L : ℕ, ∀ u ∈ Set.Ioo a s, jumpCount T u = L := by
  classical
  have hBfin : ({n | T n < s} : Set ℕ).Finite := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htop.eventually_gt_atTop s)
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    intro n hn
    by_contra hcon
    exact absurd (hN n (not_lt.mp hcon)) (not_lt.mpr (le_of_lt hn))
  by_cases hBne : ({n | T n < s} : Set ℕ).Nonempty
  · obtain ⟨x0, hx0⟩ := hBne
    have hFne : hBfin.toFinset.Nonempty := ⟨x0, (Set.Finite.mem_toFinset hBfin).mpr hx0⟩
    obtain ⟨M, hMmem, hM_le⟩ : ∃ M ∈ hBfin.toFinset, ∀ n, T n < s → n ≤ M :=
      ⟨hBfin.toFinset.max' hFne, hBfin.toFinset.max'_mem hFne,
        fun n hn => hBfin.toFinset.le_max' n ((Set.Finite.mem_toFinset hBfin).mpr hn)⟩
    have hMs : T M < s := (Set.Finite.mem_toFinset hBfin).mp hMmem
    refine ⟨T M, hMs, M + 1, ?_⟩
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hlb : M < jumpCount T u := (lt_jumpCount_iff hmono htop M u).mpr (le_of_lt hu1)
    have hub : ¬ (M + 1 < jumpCount T u) := by
      intro hc
      have hTu : T (M + 1) ≤ u := (lt_jumpCount_iff hmono htop (M + 1) u).mp hc
      have hsle : s ≤ T (M + 1) := by
        by_contra hlt
        exact Nat.not_succ_le_self M (hM_le (M + 1) (not_le.mp hlt))
      linarith
    omega
  · refine ⟨s - 1, by linarith, 0, ?_⟩
    intro u hu
    obtain ⟨_, hu2⟩ := hu
    by_contra hne0
    have hpos : 0 < jumpCount T u := Nat.pos_of_ne_zero hne0
    have hT0 : T 0 ≤ u := (lt_jumpCount_iff hmono htop 0 u).mp hpos
    exact hBne ⟨0, lt_of_le_of_lt hT0 hu2⟩
private theorem continuousWithinAt_piecewisePath_Ici (hmono : StrictMono T)
    (htop : Tendsto T atTop atTop) (s : ℝ) :
    ContinuousWithinAt (piecewisePath x₀ b T Y) (Set.Ici s) s := by
  have hne : {m | s < T m}.Nonempty := (htop.eventually_gt_atTop s).exists
  have hsJ : s < T (jumpCount T s) := Nat.sInf_mem hne
  have hconst : ∀ u ∈ Set.Ico s (T (jumpCount T s)), jumpCount T u = jumpCount T s := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hlb : jumpCount T s ≤ jumpCount T u := jumpCount_mono hmono htop hu1
    have hub : jumpCount T u ≤ jumpCount T s := by
      by_contra hh
      exact absurd ((lt_jumpCount_iff hmono htop _ u).mp (not_le.mp hh)) (not_le.mpr hu2)
    omega
  set g : ℝ → ℝ := fun u => (x₀ + ∑ i ∈ Finset.range (jumpCount T s), Y i) + b * u with hg
  have heqOn : Set.EqOn (piecewisePath x₀ b T Y) g (Set.Ico s (T (jumpCount T s))) := by
    intro u hu
    simp only [piecewisePath, hconst u hu, hg]
    ring
  have hmem : Set.Ico s (T (jumpCount T s)) ∈ 𝓝[Set.Ici s] s := by
    rw [← Set.Ici_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds hsJ)
  have hgc : ContinuousWithinAt g (Set.Ici s) s := (by fun_prop : Continuous g).continuousWithinAt
  refine hgc.congr_of_eventuallyEq (Filter.eventually_of_mem hmem fun u hu => heqOn hu) ?_
  exact heqOn (Set.left_mem_Ico.mpr hsJ)
end ProbabilityTheory
theorem solution (hmono : StrictMono T) (htop : Tendsto T atTop atTop) :
    IsCadlag (piecewisePath x₀ b T Y) := by
  intro s
  refine ⟨continuousWithinAt_piecewisePath_Ici hmono htop s, ?_⟩
  obtain ⟨a, has, L, hconst⟩ := exists_lt_jumpCount_const hmono htop s
  set g : ℝ → ℝ := fun u => (x₀ + ∑ i ∈ Finset.range L, Y i) + b * u with hg
  refine ⟨g s, ?_⟩
  have heqOn : Set.EqOn (piecewisePath x₀ b T Y) g (Set.Ioo a s) := by
    intro u hu
    simp only [piecewisePath, hconst u hu, hg]
    ring
  have hmem : Set.Ioo a s ∈ 𝓝[Set.Iio s] s := by
    rw [← Set.Ioi_inter_Iio, Set.inter_comm]
    exact inter_mem_nhdsWithin _ (Ioi_mem_nhds has)
  have hgc : Tendsto g (𝓝[Set.Iio s] s) (𝓝 (g s)) := by
    have : Continuous g := by fun_prop
    exact this.continuousWithinAt
  exact Filter.Tendsto.congr' (Filter.eventually_of_mem hmem fun u hu => (heqOn hu).symm) hgc
