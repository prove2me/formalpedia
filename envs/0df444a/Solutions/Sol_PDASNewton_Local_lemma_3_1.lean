-- Prove2me | solution 1 for PDASNewton.Local.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:26:40.606121+00:00
-- url     : https://prove2.me/submissions/b1569497-b457-4b95-ab21-43cdbdc4d5cb

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting
set_option autoImplicit false
open PDASNewton.Local Matrix Filter Topology Asymptotics

theorem solution {n : ℕ} (δ : Fin n → ℝ) :
    IsSlantingFunction (fun y : Fin n → ℝ => fun i => max 0 (y i)) (Gm δ) Set.univ := by
  intro x _
  have pt : ∀ z k d : ℝ, (z = 0 ∨ |k| < |z|) →
      max 0 (z + k) - max 0 z - (if z + k < 0 then 0 else if 0 < z + k then 1 else d) * k = 0 := by
    intro z k d h
    rcases h with h | h
    · subst h
      rcases lt_trichotomy k 0 with hk | hk | hk
      · simp [hk, hk.le]
      · simp [hk]
      · simp [hk, hk.le, not_lt.mpr hk.le]
    · rcases lt_trichotomy z 0 with hz | hz | hz
      · have := abs_lt.mp (show |k| < -z from by rwa [abs_of_neg hz] at h)
        have hlt : z + k < 0 := by linarith [this.2]
        simp [hlt, max_eq_left hz.le, max_eq_left hlt.le]
      · subst hz; simp only [abs_zero] at h; exact absurd h (not_lt.mpr (abs_nonneg k))
      · have := abs_lt.mp (show |k| < z from by rwa [abs_of_pos hz] at h)
        have hlt : 0 < z + k := by linarith [this.1]
        simp [hlt, not_lt.mpr hlt.le, max_eq_right hz.le, max_eq_right hlt.le]
  have hev : ∀ᶠ h in 𝓝 (0 : Fin n → ℝ), ∀ i, (x i = 0 ∨ |h i| < |x i|) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hxi : x i = 0
    · exact Filter.Eventually.of_forall fun _ => Or.inl hxi
    · have hopen : IsOpen {h : Fin n → ℝ | |h i| < |x i|} :=
        isOpen_lt (continuous_abs.comp (continuous_apply i)) continuous_const
      have : (0 : Fin n → ℝ) ∈ {h : Fin n → ℝ | |h i| < |x i|} := by
        simpa using abs_pos.mpr hxi
      exact Filter.mem_of_superset (hopen.mem_nhds this) fun h hh => Or.inr hh
  have hzero : (fun h : Fin n → ℝ => (fun i => max 0 ((x + h) i)) - (fun i => max 0 (x i)) - Gm δ (x + h) h)
      =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hev] with h hh
    funext i
    have := pt (x i) (h i) (δ i) (hh i)
    have hGm : ∀ (w h : Fin n → ℝ) (i : Fin n), Gm δ w h i = gm δ w i * h i := by
      intro w h i; simp [Gm]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, hGm, gm]
    exact this
  exact (Asymptotics.isLittleO_zero _ _).congr' (hzero.mono fun h hh => hh.symm) Filter.EventuallyEq.rfl
