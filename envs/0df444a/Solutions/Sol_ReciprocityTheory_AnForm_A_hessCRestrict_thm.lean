-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessCRestrict_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:18.813798+00:00
-- url     : https://prove2.me/submissions/96bde81b-09c7-41f7-af89-cc407d7b7823

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : HessCRestrictStatement := by
  intro n φ U j hU hφ y hy
  obtain ⟨Lc, hLc⟩ : ∃ Lc : (Fin n → ℂ) →L[ℝ] (Fin (n + 1) → ℂ),
      ∀ y, Lc y = Fin.insertNth (α := fun _ => ℂ) j 0 y := by
    refine ⟨ContinuousLinearMap.pi fun i => Fin.insertNth
      (α := fun _ => (Fin n → ℂ) →L[ℝ] ℂ) j 0
      (fun k => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k) i, ?_⟩
    intro y
    funext m
    by_cases hm : m = j
    · rw [hm]; simp
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hm
      simp
  have hs : ∀ (c : ℂ) (i : Fin n), Lc (c • Pi.single i 1) = c • Pi.single (j.succAbove i) 1 := by
    intro c i
    rw [hLc]
    funext m
    by_cases hm : m = j
    · rw [hm]; simp [Pi.single_apply, (Fin.succAbove_ne j i).symm]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hm
      simp [Pi.single_apply]
  have hs1 : ∀ i : Fin n, Lc (Pi.single i 1) = Pi.single (j.succAbove i) 1 := by
    intro i; simpa using hs 1 i
  have hfun : (fun y' => φ (Fin.insertNth (α := fun _ => ℂ) j 0 y')) = φ ∘ Lc := by
    funext y'; simp only [Function.comp_apply, hLc]
  rw [hfun, ← hLc y]
  rw [← hLc y] at hy
  have hφa : ∀ x ∈ U, ContDiffAt ℝ 2 φ x := fun x hx => hφ.contDiffAt (hU.mem_nhds hx)
  have hev : fderiv ℝ (φ ∘ Lc) =ᶠ[nhds y] fun y' => (fderiv ℝ φ (Lc y')).comp Lc := by
    have hU' : ∀ᶠ y' in nhds y, Lc y' ∈ U :=
      Lc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
    filter_upwards [hU'] with y' hy'
    rw [fderiv_comp y' ((hφa _ hy').differentiableAt
      (by first | exact one_le_two | exact two_ne_zero | norm_num)) Lc.differentiableAt,
      Lc.fderiv]
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) (Lc y) :=
    ((hφa _ hy).fderiv_right (m := 1)
      (by first | exact le_rfl | exact one_add_one_eq_two.le | norm_num)).differentiableAt
      (by first | exact le_rfl | exact one_ne_zero)
  have hc : DifferentiableAt ℝ (fun y' => fderiv ℝ φ (Lc y')) y :=
    hd1.comp y Lc.differentiableAt
  have hH : ∀ v w, fderiv ℝ (fderiv ℝ (φ ∘ Lc)) y v w =
      fderiv ℝ (fderiv ℝ φ) (Lc y) (Lc v) (Lc w) := by
    intro v w
    rw [hev.fderiv_eq, fderiv_clm_comp (c := fun y' => fderiv ℝ φ (Lc y')) (d := fun _ => Lc) hc
      (differentiableAt_const Lc), fderiv_comp' y hd1 Lc.differentiableAt, Lc.fderiv]
    simp
  refine Matrix.ext fun a b => ?_
  simp only [hessC, Matrix.submatrix_apply, hH, hs, hs1]
end ReciprocityTheory.AnForm.A
