-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.SliceClasses.eig_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:22.542837+00:00
-- url     : https://prove2.me/submissions/6b499982-9075-4578-90ae-9fa2f5e615ef

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_PSliceC
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.SliceClasses
namespace PositivityTheory.Rg.Rs.SliceClasses
theorem _root_.solution {X Y : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W]
    (L : ℝ → (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hL : ∀ s t, ∀ w ∈ W, L s (L t w) = L t (L s w))
    (hW : ∀ t, ∀ w ∈ W, L t w ∈ W) (L' : ℝ → (Y → ℂ) →ₗ[ℂ] (Y → ℂ)) (B : (X → ℂ) → (Y → ℂ))
    (hadd : ∀ v ∈ W, ∀ w ∈ W, B (v + w) = B v + B w) (hsmul : ∀ (a : ℂ), ∀ w ∈ W, B (a • w) = a • B w)
    (c d : ℂ) (hB : ∀ t : ℝ, ∀ w ∈ W, B (L t w) = Complex.exp (d * t) • L' t (B w))
    (w₀ : X → ℂ) (hw₀ : w₀ ∈ W) (hne : B w₀ ≠ 0) (heig : ∀ t : ℝ, L' t (B w₀) = Complex.exp (c * t) • B w₀) :
    ∃ F ∈ W, F ≠ 0 ∧ ∀ t : ℝ, L t F = Complex.exp ((c + d) * t) • F := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, B w₀ y ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  let M : ℝ → Module.End ℂ W := fun t => Complex.exp (-((c + d) * t)) • (L t).restrict (hW t)
  have hMv : ∀ t (w : W), ((M t w : W) : X → ℂ) = Complex.exp (-((c + d) * t)) • L t (w : X → ℂ) := fun _ _ => rfl
  let Φ : W →ₗ[ℂ] ℂ :=
    { toFun := fun w => B (w : X → ℂ) y₀ / B w₀ y₀
      map_add' := fun v w => by
        simp only [Submodule.coe_add]
        rw [hadd _ v.2 _ w.2, Pi.add_apply, add_div]
      map_smul' := fun a w => by
        simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
        rw [hsmul a _ w.2, Pi.smul_apply, smul_eq_mul, mul_div_assoc] }
  have hΦ : ∀ w : W, Φ w = B (w : X → ℂ) y₀ / B w₀ y₀ := fun _ => rfl
  let P : Submodule ℂ W :=
    { carrier := {w | ∃ a : ℂ, B (w : X → ℂ) = a • B w₀}
      add_mem' := fun {v w} hv hw => by
        obtain ⟨a, ha⟩ := hv; obtain ⟨b, hb⟩ := hw
        exact ⟨a + b, by simp only [Submodule.coe_add]; rw [hadd _ v.2 _ w.2, ha, hb, add_smul]⟩
      zero_mem' := ⟨0, by
        have := hsmul 0 w₀ hw₀
        simpa using this⟩
      smul_mem' := fun a w hw => by
        obtain ⟨b, hb⟩ := hw
        exact ⟨a * b, by simp only [Submodule.coe_smul]; rw [hsmul a _ w.2, hb, smul_smul]⟩ }
  have hBM : ∀ t (w : W), B ((M t w : W) : X → ℂ) = Complex.exp (-(c * t)) • L' t (B (w : X → ℂ)) := by
    intro t w
    rw [hMv, hsmul _ _ (hW t _ w.2), hB t _ w.2, smul_smul, ← Complex.exp_add]
    congr 2
    ring
  have hPM : ∀ t (w : W) (a : ℂ), B (w : X → ℂ) = a • B w₀ → B ((M t w : W) : X → ℂ) = a • B w₀ := by
    intro t w a ha
    rw [hBM, ha, map_smul, heig, smul_smul, smul_smul]
    congr 1
    rw [mul_comm _ a, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hc : ∀ s t, Commute (M s) (M t) := by
    intro s t
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp only [Module.End.mul_apply]
    rw [hMv, hMv, hMv, hMv, map_smul, map_smul, hL s t _ w.2, smul_smul, smul_smul, mul_comm]
  obtain ⟨w, -, hw0, hfix⟩ := C_gen M hc Φ _ P rfl
    (fun t w hw => by obtain ⟨a, ha⟩ := hw; exact ⟨a, hPM t w a ha⟩)
    (fun t w hw => by obtain ⟨a, ha⟩ := hw; rw [hΦ, hΦ, hPM t w a ha, ha])
    ⟨⟨w₀, hw₀⟩, ⟨1, by rw [one_smul]⟩, by rw [hΦ]; exact div_ne_zero hy₀ hy₀⟩
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h), fun t => ?_⟩
  have h1 := congrArg Subtype.val (hfix t)
  rw [hMv] at h1
  calc L t (w : X → ℂ) = Complex.exp ((c + d) * t) • (Complex.exp (-((c + d) * t)) • L t (w : X → ℂ)) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp ((c + d) * t) • (w : X → ℂ) := by rw [h1]
end PositivityTheory.Rg.Rs.SliceClasses
