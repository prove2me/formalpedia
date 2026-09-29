-- Prove2me | solution 1 for contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/593dbf3e-3852-50f2-8a00-abd801cb0a37

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add

set_option autoImplicit false

open MeasureTheory

namespace SliceDeriv

theorem norm_iteratedFDeriv_iteratedFDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (N j : ℕ) (x : E) :
    ‖iteratedFDeriv 𝕜 N (iteratedFDeriv 𝕜 j f) x‖ = ‖iteratedFDeriv 𝕜 (N + j) f x‖ := by
  induction N generalizing j with
  | zero =>
    rw [norm_iteratedFDeriv_zero, Nat.zero_add]
  | succ N ih =>
    have hf : fderiv 𝕜 (iteratedFDeriv 𝕜 j f) =
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (j + 1) => E) F) ∘ iteratedFDeriv 𝕜 (j + 1) f := by
      funext y
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp
    calc ‖iteratedFDeriv 𝕜 (N + 1) (iteratedFDeriv 𝕜 j f) x‖
        = ‖iteratedFDeriv 𝕜 N (fderiv 𝕜 (iteratedFDeriv 𝕜 j f)) x‖ := norm_iteratedFDeriv_fderiv.symm
      _ = ‖iteratedFDeriv 𝕜 N (iteratedFDeriv 𝕜 (j + 1) f) x‖ := by
          rw [hf, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      _ = ‖iteratedFDeriv 𝕜 (N + (j + 1)) f x‖ := ih (j + 1)
      _ = ‖iteratedFDeriv 𝕜 (N + 1 + j) f x‖ := by
          have key : ∀ a b : ℕ, a = b → ‖iteratedFDeriv 𝕜 a f x‖ = ‖iteratedFDeriv 𝕜 b f x‖ := by
            rintro a b rfl; rfl
          exact key _ _ (by omega)

end SliceDeriv

theorem solution
    {n : ℕ} (Φ : ℝ × (Fin n → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (j : ℕ) (x : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) ∧
    ∀ (N : ℕ) (y : Fin n → ℝ),
      ‖iteratedFDeriv ℝ N (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) y‖ ≤
        ‖iteratedFDeriv ℝ (N + j) Φ (x, y)‖ := by

  let inl : ℝ →L[ℝ] ℝ × (Fin n → ℝ) := ContinuousLinearMap.inl ℝ ℝ (Fin n → ℝ)
  let inr : (Fin n → ℝ) →L[ℝ] ℝ × (Fin n → ℝ) := ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  let m₀ : Fin j → ℝ × (Fin n → ℝ) := fun _ => ((1 : ℝ), (0 : Fin n → ℝ))
  let ev : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ × (Fin n → ℝ)) ℂ →L[ℝ] ℂ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ × (Fin n → ℝ)) ℂ m₀
  have hΦ' : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ j Φ) :=
    hΦ.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)

  have hslice : (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) =
      ev ∘ iteratedFDeriv ℝ j Φ ∘ fun y' : Fin n → ℝ => ((x, y') : ℝ × (Fin n → ℝ)) := by
    funext y'
    rw [iteratedDeriv_eq_iteratedFDeriv]
    have h1 : (fun t : ℝ => Φ (t, y')) = (fun p : ℝ × (Fin n → ℝ) => Φ (p + ((0 : ℝ), y'))) ∘ inl := by
      funext t
      show Φ (t, y') = Φ (inl t + ((0 : ℝ), y'))
      simp [inl]
    have hΦt : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => Φ (p + ((0 : ℝ), y'))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right inl hΦt x (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    show (iteratedFDeriv ℝ j Φ (inl x + ((0 : ℝ), y'))) (fun _ => inl 1) = ev (iteratedFDeriv ℝ j Φ (x, y'))
    rw [ContinuousMultilinearMap.apply_apply]
    congr 2 <;> (try funext i) <;> simp [m₀, inl]
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun y' : Fin n → ℝ => ((x, y') : ℝ × (Fin n → ℝ))) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨?_, ?_⟩
  · rw [hslice]
    exact ev.contDiff.comp (hΦ'.comp hA)
  · intro N y
    rw [hslice]
    have hF : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ j Φ ∘ fun y' : Fin n → ℝ => ((x, y') : ℝ × (Fin n → ℝ))) :=
      hΦ'.comp hA
    rw [show ev ∘ iteratedFDeriv ℝ j Φ ∘ (fun y' : Fin n → ℝ => ((x, y') : ℝ × (Fin n → ℝ))) =
        ev ∘ (iteratedFDeriv ℝ j Φ ∘ fun y' : Fin n → ℝ => ((x, y') : ℝ × (Fin n → ℝ))) from rfl]
    rw [ContinuousLinearMap.iteratedFDeriv_comp_left ev (hF.contDiffAt) (by exact_mod_cast le_top)]

    have h2 : (iteratedFDeriv ℝ j Φ ∘ fun y' : Fin n → ℝ => ((x, y') : ℝ × (Fin n → ℝ))) =
        (fun p : ℝ × (Fin n → ℝ) => iteratedFDeriv ℝ j Φ (p + (x, (0 : Fin n → ℝ)))) ∘ inr := by
      funext y'
      show iteratedFDeriv ℝ j Φ (x, y') = iteratedFDeriv ℝ j Φ (inr y' + (x, (0 : Fin n → ℝ)))
      simp [inr]
    have hΦ't : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => iteratedFDeriv ℝ j Φ (p + (x, (0 : Fin n → ℝ)))) :=
      hΦ'.comp (contDiff_id.add contDiff_const)
    rw [h2, ContinuousLinearMap.iteratedFDeriv_comp_right inr hΦ't y (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    have hxy : inr y + (x, (0 : Fin n → ℝ)) = (x, y) := by simp [inr]
    rw [hxy]

    have hev : ‖ev‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun M => ?_
      rw [ContinuousMultilinearMap.apply_apply, one_mul]
      refine (M.le_opNorm m₀).trans ?_
      have : ∏ i : Fin j, ‖m₀ i‖ = 1 := by
        refine Finset.prod_eq_one fun i _ => ?_
        simp [m₀, Prod.norm_def]
      rw [this, mul_one]
    have hinr : ∏ _i : Fin N, ‖inr‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ ℝ (Fin n → ℝ)
    calc ‖ev.compContinuousMultilinearMap
            ((iteratedFDeriv ℝ N (iteratedFDeriv ℝ j Φ) (x, y)).compContinuousLinearMap fun _ => inr)‖
        ≤ ‖ev‖ * ‖(iteratedFDeriv ℝ N (iteratedFDeriv ℝ j Φ) (x, y)).compContinuousLinearMap fun _ => inr‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ 1 * (‖iteratedFDeriv ℝ N (iteratedFDeriv ℝ j Φ) (x, y)‖ * ∏ _i : Fin N, ‖inr‖) := by
          gcongr
          exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ 1 * (‖iteratedFDeriv ℝ N (iteratedFDeriv ℝ j Φ) (x, y)‖ * 1) := by gcongr
      _ = ‖iteratedFDeriv ℝ (N + j) Φ (x, y)‖ := by
          rw [one_mul, mul_one, SliceDeriv.norm_iteratedFDeriv_iteratedFDeriv]

end S_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add
end P2MW
export P2MW.S_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add (solution)
