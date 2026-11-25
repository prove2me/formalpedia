-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:30.033797+00:00
-- url     : https://prove2.me/submissions/80af7315-2754-4a56-84df-c17976809ec1

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_eval_eq_zero_of_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    z ∈ conePts P ↔ ∀ h ∈ chartIdeal P p, eval (affCoord p z) h = 0 := by
  have haff : affCoord p z = fun q => (z ⟨q.1, p q.1⟩)⁻¹ * z q := by
    funext q
    show z q / z ⟨q.1, p q.1⟩ = _
    rw [div_eq_inv_mul]
  unfold conePts
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hzP⟩
    have hle : chartIdeal P p ≤ RingHom.ker (eval (affCoord p z)) := by
      refine sup_le ?_ ?_
      · intro f hf
        rw [RingHom.mem_ker, haff]
        exact eval_eq_zero_of_smul hP (fun k => (z ⟨k, p k⟩)⁻¹) z hzP f hf
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_X, map_one]
        show z ⟨k, p k⟩ / z ⟨k, p k⟩ - 1 = 0
        rw [div_self (hz k), sub_self]
    intro h hh
    exact hle hh
  · intro hch
    refine ⟨fun k => ⟨p k, hz k⟩, ?_⟩
    have hzeq : z = fun q => z ⟨q.1, p q.1⟩ * affCoord p z q := by
      funext q
      show z q = z ⟨q.1, p q.1⟩ * (z q / z ⟨q.1, p q.1⟩)
      have := hz q.1
      field_simp
    intro f hf
    rw [hzeq]
    exact eval_eq_zero_of_smul hP (fun k => z ⟨k, p k⟩) (affCoord p z)
      (fun g hg => hch g (Ideal.mem_sup_left hg)) f hf
end ReciprocityTheory.AnForm.R
