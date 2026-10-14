-- Prove2me | solution 1 for SmaleDiffS4.diffDisk_one_pathConnected
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T04:31:25.067895+00:00
-- url     : https://prove2.me/submissions/81b87ae7-5145-4c9c-b043-4fad93fe4f91

import Mathlib
import Definitions.Def_SmaleDiffS4_Basic
import Theorems.Thm_SmaleDiffS4_continuous_of_smoothIsotopy

set_option autoImplicit false

open SmaleDiffS4
open scoped ContDiff Manifold
open Filter

namespace SmaleDiffS4.S4_C

/-- A smooth self-map of `ℝ` with a two-sided inverse which is the identity outside `(-1,1)`
is strictly monotone. -/
lemma strictMono_of_inv (φ ψ : ℝ → ℝ) (hφ : Continuous φ) (hψφ : ∀ s, ψ (φ s) = s)
    (hfix : ∀ s, 1 ≤ |s| → φ s = s) : StrictMono φ := by
  have hinj : Function.Injective φ := Function.LeftInverse.injective hψφ
  rcases hφ.strictMono_of_inj hinj with h | h
  · exact h
  · exfalso
    have h1 : φ 1 = 1 := hfix 1 (by norm_num)
    have h2 : φ (-1) = -1 := hfix (-1) (by norm_num)
    have := h (show (-1 : ℝ) < 1 by norm_num)
    linarith

lemma deriv_ne_zero_of_inv (φ ψ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ)
    (hψφ : ∀ s, ψ (φ s) = s) (s : ℝ) : deriv φ s ≠ 0 := by
  intro h0
  have h1 : HasDerivAt (ψ ∘ φ) (deriv ψ (φ s) * deriv φ s) s :=
    (hψ (φ s)).hasDerivAt.comp s (hφ s).hasDerivAt
  have hid : ψ ∘ φ = id := funext hψφ
  rw [hid] at h1
  have h2 := h1.unique (hasDerivAt_id s)
  rw [h0, mul_zero] at h2
  exact zero_ne_one h2

/-- The 1-dimensional core: the straight-line interpolation between `id` and a
diffeomorphism `φ` of `ℝ` that fixes the complement of `(-1,1)` is again invertible with a smooth
inverse. -/
lemma exists_smooth_inv (φ ψ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψφ : ∀ s, ψ (φ s) = s) (hfix : ∀ s, 1 ≤ |s| → φ s = s) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ (∀ s, G ((1 - t) * s + t * φ s) = s) ∧
      (∀ u, (1 - t) * G u + t * φ (G u) = u) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hmono : StrictMono φ := strictMono_of_inv φ ψ hφ.continuous hψφ hfix
  have hdpos : ∀ s, 0 < deriv φ s := fun s =>
    lt_of_le_of_ne hmono.monotone.deriv_nonneg (deriv_ne_zero_of_inv φ ψ hφd hψd hψφ s).symm
  set H : ℝ → ℝ := fun s => (1 - t) * s + t * φ s with hH
  have hHc : ContDiff ℝ ∞ H := (contDiff_const.mul contDiff_id).add (contDiff_const.mul hφ)
  have hHmono : StrictMono H := by
    intro a b hab
    have hφab := hmono hab
    simp only [hH]
    rcases eq_or_lt_of_le ht0 with h | h
    · subst h; linarith
    · nlinarith
  have hHfix : ∀ s, 1 ≤ |s| → H s = s := by
    intro s hs
    simp only [hH, hfix s hs]
    ring
  have htop : Tendsto H atTop atTop := by
    refine tendsto_id.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (hHfix s (by rw [abs_of_nonneg (by linarith)]; exact hs)).symm
  have hbot : Tendsto H atBot atBot := by
    refine tendsto_id.congr' ?_
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with s hs
    exact (hHfix s (by rw [abs_of_neg (by linarith)]; linarith)).symm
  have hsurj : Function.Surjective H := hHc.continuous.surjective htop hbot
  let O : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective H hHmono hsurj
  let Hh : ℝ ≃ₜ ℝ := O.toHomeomorph
  have hHh : (Hh : ℝ → ℝ) = H := rfl
  have hderiv : ∀ s, HasDerivAt H ((1 - t) * 1 + t * deriv φ s) s := fun s =>
    ((hasDerivAt_id s).const_mul (1 - t)).add ((hφd s).hasDerivAt.const_mul t)
  have hne : ∀ s, (1 - t) * 1 + t * deriv φ s ≠ 0 := by
    intro s
    have := hdpos s
    rcases eq_or_lt_of_le ht1 with h | h
    · subst h; nlinarith
    · nlinarith
  have hsymm : ContDiff ℝ ∞ (Hh.symm : ℝ → ℝ) :=
    Hh.contDiff_symm_deriv hne (by rw [hHh]; exact hderiv) (by rw [hHh]; exact hHc)
  refine ⟨Hh.symm, hsymm, fun s => ?_, fun u => ?_⟩
  · exact Hh.symm_apply_apply s
  · exact Hh.apply_symm_apply u


/-- The linear isometry `ℝ ≃ E 1`. -/
noncomputable def r : ℝ ≃ₗᵢ[ℝ] E 1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr

lemma diffDisk_ext {n : ℕ} {f g : DiffDisk n} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (Diffeomorph.ext h)

lemma one_apply {n : ℕ} (x : E n) : (1 : DiffDisk n).1 x = x := rfl

lemma contDiff_diffeo {n : ℕ} (f : Diffeomorph 𝓘(ℝ, E n) 𝓘(ℝ, E n) (E n) (E n) ∞) :
    ContDiff ℝ ∞ (f : E n → E n) :=
  contMDiff_iff_contDiff.1 f.contMDiff

/-- The straight-line interpolation `(1 - t) x + t f x` is an element of `Diff(D¹ rel ∂)`. -/
lemma exists_interp (f : DiffDisk 1) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ g : DiffDisk 1, ∀ x, g.1 x = (1 - t) • x + t • f.1 x := by
  obtain ⟨ht0, ht1⟩ := ht
  set φ : ℝ → ℝ := fun s => r.symm (f.1 (r s)) with hφdef
  set ψ : ℝ → ℝ := fun s => r.symm (f.1.symm (r s)) with hψdef
  have hf : ContDiff ℝ ∞ (f.1 : E 1 → E 1) := contDiff_diffeo f.1
  have hfs : ContDiff ℝ ∞ (f.1.symm : E 1 → E 1) := contDiff_diffeo f.1.symm
  have hφ : ContDiff ℝ ∞ φ := r.symm.contDiff.comp (hf.comp r.contDiff)
  have hψ : ContDiff ℝ ∞ ψ := r.symm.contDiff.comp (hfs.comp r.contDiff)
  have hψφ : ∀ s, ψ (φ s) = s := by
    intro s
    simp [hφdef, hψdef]
  have hfix : ∀ s, 1 ≤ |s| → φ s = s := by
    intro s hs
    have hn : 1 ≤ ‖r s‖ := by rw [LinearIsometryEquiv.norm_map, Real.norm_eq_abs]; exact hs
    simp only [hφdef, f.2 _ hn, LinearIsometryEquiv.symm_apply_apply]
  obtain ⟨G, hG, hGl, hGr⟩ := exists_smooth_inv φ ψ hφ hψ hψφ hfix t ht0 ht1
  have hφr : ∀ x : E 1, φ (r.symm x) = r.symm (f.1 x) := by
    intro x; simp [hφdef]
  have key : ∀ x : E 1, r.symm ((1 - t) • x + t • f.1 x) =
      (1 - t) * r.symm x + t * φ (r.symm x) := by
    intro x
    rw [hφr, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  let D : Diffeomorph 𝓘(ℝ, E 1) 𝓘(ℝ, E 1) (E 1) (E 1) ∞ :=
    { toFun := fun x => (1 - t) • x + t • f.1 x
      invFun := fun y => r (G (r.symm y))
      left_inv := by
        intro x
        simp only
        rw [key, hGl, LinearIsometryEquiv.apply_symm_apply]
      right_inv := by
        intro y
        simp only
        apply r.symm.injective
        rw [key, LinearIsometryEquiv.symm_apply_apply, hGr]
      contMDiff_toFun := by
        apply contMDiff_iff_contDiff.2
        show ContDiff ℝ ∞ (fun x : E 1 => (1 - t) • x + t • f.1 x)
        exact ((contDiff_const (c := (1 - t : ℝ))).smul contDiff_id).add
          ((contDiff_const (c := t)).smul hf)
      contMDiff_invFun := by
        apply contMDiff_iff_contDiff.2
        show ContDiff ℝ ∞ (fun y : E 1 => r (G (r.symm y)))
        exact r.contDiff.comp (hG.comp r.symm.contDiff) }
  refine ⟨⟨D, fun x hx => ?_⟩, fun x => rfl⟩
  show (1 - t) • x + t • f.1 x = x
  rw [f.2 x hx, ← add_smul, sub_add_cancel, one_smul]

/-- Every element of `Diff(D¹ rel ∂)` is joined to the identity by a path. -/
lemma joined_one (f : DiffDisk 1) : Joined (1 : DiffDisk 1) f := by
  choose g hg using fun t : Set.Icc (0 : ℝ) 1 => exists_interp f t t.2
  have hF : ContDiff ℝ ∞ (fun p : ℝ × E 1 => (1 - p.1) • p.2 + p.1 • f.1 p.2) :=
    ((contDiff_const.sub contDiff_fst).smul contDiff_snd).add
      (contDiff_fst.smul ((contDiff_diffeo f.1).comp contDiff_snd))
  have hc : Continuous g := continuous_of_smoothIsotopy 1 _ hF g hg
  refine ⟨⟨⟨g, hc⟩, ?_, ?_⟩⟩
  · exact diffDisk_ext fun x => by
      show (g ⟨0, _⟩).1 x = x
      rw [hg]; simp
  · exact diffDisk_ext fun x => by
      show (g ⟨1, _⟩).1 x = f.1 x
      rw [hg]; simp

end SmaleDiffS4.S4_C

theorem solution : PathConnectedSpace (DiffDisk 1) := by
  refine ⟨⟨1⟩, fun f g => ?_⟩
  exact (SmaleDiffS4.S4_C.joined_one f).symm.trans (SmaleDiffS4.S4_C.joined_one g)
