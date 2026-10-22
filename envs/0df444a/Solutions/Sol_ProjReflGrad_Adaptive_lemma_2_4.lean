-- Prove2me | solution 1 for ProjReflGrad.Adaptive.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:06:03.999343+00:00
-- url     : https://prove2.me/submissions/bb1d9ee5-c17e-462e-b9e6-c80662549e5d

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

set_option autoImplicit false

theorem prl_proj_char {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hCcl : IsClosed C) (hCcv : Convex ℝ C) (hne : C.Nonempty) (z : H) :
    ProjReflGrad.Weak.proj C z ∈ C ∧
      ∀ w ∈ C, inner ℝ (z - ProjReflGrad.Weak.proj C z) (w - ProjReflGrad.Weak.proj C z) ≤ 0 := by
  have hex : ∃ p, ProjReflGrad.Weak.IsProj C z p := by
    obtain ⟨v, hv, hvn⟩ := exists_norm_eq_iInf_of_complete_convex hne hCcl.isComplete hCcv z
    refine ⟨v, hv, fun q hq => ?_⟩
    rw [hvn]
    exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨q, hq⟩ : C)
  have hp : ProjReflGrad.Weak.proj C z = hex.choose := by
    unfold ProjReflGrad.Weak.proj; rw [dif_pos hex]
  have hs := hex.choose_spec
  rw [hp]
  refine ⟨hs.1, ?_⟩
  have : ‖z - hex.choose‖ = ⨅ w : C, ‖z - w‖ := by
    apply le_antisymm
    · haveI : Nonempty C := hne.to_subtype
      exact le_ciInf (fun q => hs.2 q q.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨hex.choose, hs.1⟩ : C)
  exact (norm_eq_iInf_iff_real_inner_le_zero hCcv hs.1).mp this

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (M : Set H) (hne : M.Nonempty)
    (hcl : IsClosed M) (hcv : Convex ℝ M) (x : H) :
    ∀ l : ℝ, 0 < l → ProjReflGrad.Weak.proj M (ProjReflGrad.Weak.proj M x + l • (x - ProjReflGrad.Weak.proj M x)) = ProjReflGrad.Weak.proj M x := by
  intro l hl
  set xb := ProjReflGrad.Weak.proj M x with hxb
  set z := xb + l • (x - xb) with hz
  obtain ⟨hxbM, hxbc⟩ := prl_proj_char hcl hcv hne x
  obtain ⟨hpM, hpc⟩ := prl_proj_char hcl hcv hne z
  set p := ProjReflGrad.Weak.proj M z with hp
  have h1 := hpc xb hxbM
  have h2 := hxbc p hpM
  have hzx : z - xb = l • (x - xb) := by rw [hz]; abel
  have h3 : inner ℝ (z - xb) (p - xb) ≤ 0 := by
    rw [hzx, inner_smul_left]
    simp only [conj_trivial]
    nlinarith
  have e3 : inner ℝ (z - p) (xb - p) + inner ℝ (z - xb) (p - xb) = inner ℝ (xb - p) (xb - p) := by
    have e4 : p - xb = -(xb - p) := by abel
    rw [e4, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
    congr 1; abel
  have h4 : ‖xb - p‖ ^ 2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq]; linarith
  have : xb - p = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h4 (sq_nonneg _))
    exact norm_eq_zero.1 this
  exact (sub_eq_zero.1 this).symm
