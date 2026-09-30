-- Prove2me | solution 1 for PsiPhi.complex_lift_is_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:31:14.26088+00:00
-- url     : https://prove2.me/submissions/b8ea11f9-351c-4036-bf94-bd68142a7d77

import Theorems.Thm_PsiPhi_psi_phi_roundtrip_and_continuity_v2
set_option autoImplicit false
open PsiPhi

theorem solution (n : ℕ) :
    ∃ (H : {w : ℂ // w.re < (n : ℝ) + 1} ≃ₜ ℂ),
      ∀ z : {w : ℂ // w.re < (n : ℝ) + 1},
        (H z).re = psi n z.1.re ∧ (H z).im = z.1.im := by
  let x₀ : {x : ℝ // x < (n : ℝ) + 1} := ⟨0, by positivity⟩
  have hpsi : ContinuousOn (psi n) (Set.Iio ((n : ℝ) + 1)) :=
    (psi_phi_roundtrip_and_continuity_v2 n x₀ 0).2.2.2.1
  have hphi : Continuous (phi n) :=
    (psi_phi_roundtrip_and_continuity_v2 n x₀ 0).2.2.2.2
  let F : {w : ℂ // w.re < (n : ℝ) + 1} → ℂ :=
    fun z => (psi n z.1.re : ℂ) + (z.1.im : ℂ) * Complex.I
  let G : ℂ → {w : ℂ // w.re < (n : ℝ) + 1} := fun w =>
    ⟨(phi n w.re : ℂ) + (w.im : ℂ) * Complex.I, by
      simpa using (psi_phi_roundtrip_and_continuity_v2 n x₀ w.re).2.2.1⟩
  have hFG : Function.LeftInverse G F := by
    intro z
    apply Subtype.ext
    apply Complex.ext
    · simpa [F, G] using (psi_phi_roundtrip_and_continuity_v2 n ⟨z.1.re,z.2⟩ 0).1
    · simp [F, G]
  have hGF : Function.RightInverse G F := by
    intro w
    apply Complex.ext
    · simpa [F, G] using (psi_phi_roundtrip_and_continuity_v2 n x₀ w.re).2.1
    · simp [F, G]
  have hF : Continuous F := by
    apply Continuous.add
    · exact Complex.continuous_ofReal.comp (hpsi.comp_continuous
        (Complex.continuous_re.comp continuous_subtype_val) (fun z => z.2))
    · exact (Complex.continuous_ofReal.comp
        (Complex.continuous_im.comp continuous_subtype_val)).mul continuous_const
  have hG : Continuous G := by
    apply Continuous.subtype_mk
    exact (Complex.continuous_ofReal.comp (hphi.comp Complex.continuous_re)).add
      ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)
  refine ⟨⟨⟨F, G, hFG, hGF⟩, hF, hG⟩, ?_⟩
  intro z
  simp [F]
