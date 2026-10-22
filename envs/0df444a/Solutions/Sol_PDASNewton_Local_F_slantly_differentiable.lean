-- Prove2me | solution 1 for PDASNewton.Local.F_slantly_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:27:18.574383+00:00
-- url     : https://prove2.me/submissions/5c5ed164-5ed2-4ea5-9118-515cac5c55a6

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting
set_option autoImplicit false
open PDASNewton.Local Matrix Filter Topology Asymptotics

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ)
    (c : ℝ) (hc : 0 < c) :
    IsSlantingFunction (Fmap A f ψ c) (GF A ψ c) Set.univ := by
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
  obtain ⟨y, l⟩ := x
  have hev : ∀ᶠ h in 𝓝 (0 : (Fin n → ℝ) × (Fin n → ℝ)), ∀ i,
      (l i + c * (y i - ψ i) = 0 ∨ |h.2 i + c * h.1 i| < |l i + c * (y i - ψ i)|) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hxi : l i + c * (y i - ψ i) = 0
    · exact Filter.Eventually.of_forall fun _ => Or.inl hxi
    · have hcont : Continuous (fun h : (Fin n → ℝ) × (Fin n → ℝ) => |h.2 i + c * h.1 i|) :=
        continuous_abs.comp ((((continuous_apply i).comp continuous_snd)).add
          (continuous_const.mul ((continuous_apply i).comp continuous_fst)))
      have hopen : IsOpen {h : (Fin n → ℝ) × (Fin n → ℝ) | |h.2 i + c * h.1 i| < |l i + c * (y i - ψ i)|} :=
        isOpen_lt hcont continuous_const
      have : (0 : (Fin n → ℝ) × (Fin n → ℝ)) ∈
          {h : (Fin n → ℝ) × (Fin n → ℝ) | |h.2 i + c * h.1 i| < |l i + c * (y i - ψ i)|} := by
        simpa using abs_pos.mpr hxi
      exact Filter.mem_of_superset (hopen.mem_nhds this) fun h hh => Or.inr hh
  have hGm : ∀ (w h : Fin n → ℝ) (i : Fin n), Gm 0 w h i = gm 0 w i * h i := by
    intro w h i; simp [Gm]
  have hzero : (fun h : (Fin n → ℝ) × (Fin n → ℝ) => Fmap A f ψ c ((y, l) + h) - Fmap A f ψ c (y, l)
        - GF A ψ c ((y, l) + h) h) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hev] with h hh
    obtain ⟨hy, hl⟩ := h
    refine Prod.ext ?_ ?_
    · simp [Fmap, GF, Matrix.mulVec_add]
      abel
    · funext i
      have := pt (l i + c * (y i - ψ i)) (hl i + c * hy i) 0 (hh i)
      have hF2 : ∀ (a b : Fin n → ℝ), (Fmap A f ψ c (a, b)).2 i = b i - max 0 (b i + c * (a i - ψ i)) := by
        intro a b; simp [Fmap]
      have hGF2 : (GF A ψ c (y + hy, l + hl) (hy, hl)).2 i =
          hl i - gm 0 (l + hl + c • (y + hy - ψ)) i * (hl i + c * hy i) := by
        simp [GF, hGm]
        ring
      have hw : (l + hl + c • (y + hy - ψ)) i = l i + c * (y i - ψ i) + (hl i + c * hy i) := by
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      have hm : (l + hl) i + c * ((y + hy) i - ψ i) = l i + c * (y i - ψ i) + (hl i + c * hy i) := by
        simp only [Pi.add_apply]; ring
      have hlh : (l + hl) i = l i + hl i := rfl
      show (Fmap A f ψ c (y + hy, l + hl)).2 i - (Fmap A f ψ c (y, l)).2 i
        - (GF A ψ c (y + hy, l + hl) (hy, hl)).2 i = 0
      rw [hF2, hF2, hGF2]
      simp only [gm, Pi.zero_apply]
      rw [hw, hm, hlh]
      linarith
  exact (Asymptotics.isLittleO_zero _ _).congr' (hzero.mono fun h hh => hh.symm) Filter.EventuallyEq.rfl
