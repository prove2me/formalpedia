-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:47.597995+00:00
-- url     : https://prove2.me/submissions/6094ece5-edc2-4c4d-b4a7-93404ecdc8bb

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_pr_apply
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_Gr_list
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_Gr_anti
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_Gr_eq_of_pr
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_prod_strict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {a : A →L[ℝ] A}
namespace PositivityTheory.ThKEst.LinDerPf
theorem _root_.solution (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {m : ℕ} (Y : Fin m → A) (hY : ∀ i, a (Y i) = -Y i)
    (c : A →L[ℝ] (Fin m → ℝ)) (hc : ∀ s : Fin m → ℝ, c (∑ i, s i • Y i) = s)
    (hc' : ∀ x y, a x = -x → a y = -y → c x = c y → x = y)
    (e : Fin m → ℝ → A) (he : ∀ i, HasStrictDerivAt (e i) (Y i) 0) (he0 : ∀ i, e i 0 = 1) (heG : ∀ i t, Gr a (e i t))
    (g : ℝ → A) (Z : A) (hg : HasDerivAt g Z 0) (hg0 : g 0 = 1) (hgG : ∀ t, Gr a (g t)) :
    ∃ s : ℝ → Fin m → ℝ, s 0 = 0 ∧ HasDerivAt s (c (pr a Z)) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), g t = (List.ofFn fun i => e i (s t i)).prod := by
  set Φ : (Fin m → ℝ) → A := fun s => (List.ofFn fun i => e i (s i)).prod with hΦ
  have hΦ0 : Φ 0 = 1 := by simp [hΦ, he0]
  have hΦG : ∀ s, Gr a (Φ s) := fun s => Gr.list ha h1 _ fun x hx => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact heG _ _
  have hΦd : HasStrictFDerivAt Φ
      (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Y i)).comp (ContinuousLinearMap.proj i)) 0 :=
    prod_strict m (fun i (s : Fin m → ℝ) => e i (s i)) _ (fun i =>
      HasStrictFDerivAt.comp (0 : Fin m → ℝ) (f := fun s : Fin m → ℝ => s i) (he i).hasStrictFDerivAt
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).hasStrictFDerivAt) he0
  have hΨ : HasStrictFDerivAt (fun s => c (pr a (Φ s)))
      ((ContinuousLinearEquiv.refl ℝ (Fin m → ℝ) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) 0 := by
    have h2 := (c.comp (pr a)).hasStrictFDerivAt.comp 0 hΦd
    refine HasStrictFDerivAt.congr_fderiv h2 (ContinuousLinearMap.ext fun s => ?_)
    have h3 : pr a (∑ i, s i • Y i) = ∑ i, s i • Y i := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, pr_apply, hY, sub_neg_eq_add, ← two_smul ℝ (Y i), smul_smul (1 / 2 : ℝ)]
      norm_num
    have h4 : (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Y i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)) s = ∑ i, s i • Y i := by
      rw [sum_apply]
      rfl
    change c (pr a ((∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Y i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)) s)) = s
    rw [h4, h3, hc]
  set ρ := hΨ.localInverse _ _ _ with hρ
  have hz : c (pr a (Φ 0)) = c (pr a (g 0)) := by rw [hΦ0, hg0]
  have hk : HasDerivAt (fun t => c (pr a (g t))) (c (pr a Z)) 0 :=
    (c.comp (pr a)).hasFDerivAt.comp_hasDerivAt 0 hg
  have hρ0 : ρ (c (pr a (g 0))) = 0 := by
    rw [← hz]
    exact hΨ.localInverse_apply_image
  have hρd := hΨ.to_localInverse.hasFDerivAt
  rw [hz] at hρd
  have hs : HasDerivAt (fun t => ρ (c (pr a (g t)))) (c (pr a Z)) 0 := by
    have h5 := hρd.comp_hasDerivAt 0 hk
    exact h5
  refine ⟨fun t => ρ (c (pr a (g t))), hρ0, hs, ?_⟩
  have hr := hΨ.eventually_right_inverse
  rw [hz] at hr
  have near : ∀ k : ℝ → A, ContinuousAt k 0 → k 0 = 1 → ∀ᶠ t in 𝓝 (0 : ℝ), ‖1 - a (k t)‖ ≤ 1 / 2 := fun k hk hk0 => by
    have h4 : ContinuousAt (fun t => ‖1 - a (k t)‖) 0 :=
      (continuousAt_const.sub (a.continuous.continuousAt.comp hk)).norm
    have h5 := h4.tendsto
    simp only [hk0, h1, sub_self, norm_zero] at h5
    exact h5.eventually (eventually_le_nhds (by norm_num))
  have hΦc : ContinuousAt (fun t => Φ (ρ (c (pr a (g t))))) 0 :=
    ContinuousAt.comp_of_eq (g := Φ) (f := fun t => ρ (c (pr a (g t)))) hΦd.continuousAt hs.continuousAt hρ0
  filter_upwards [hk.continuousAt.tendsto hr, near g hg.continuousAt hg0,
    near _ hΦc (by simp only [hρ0, hΦ0])] with t t1 t2 t3
  exact (hgG t).eq_of_pr (hΦG _) t2 t3
    (hc' _ _ ((hgG t).anti ha h1) ((hΦG _).anti ha h1) (Eq.symm t1))
end PositivityTheory.ThKEst.LinDerPf
