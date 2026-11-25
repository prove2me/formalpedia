-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.greenMaDens_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:18.817799+00:00
-- url     : https://prove2.me/submissions/f22e30a7-9a7a-4d16-9ca6-134ed1f82a53

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_R_of_compact
import Theorems.Thm_ReciprocityTheory_AnForm_A_leviOne
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_green_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : GreenMaDensStatement := by
  intro u hu hc
  set v : ℂ → ℝ := fun w => u (fun _ => w) with hv
  have hvc : ContDiff ℝ 2 v := hu.comp (contDiff_pi.2 fun _ => contDiff_id)
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  have hvR : ∀ w, R + 1 ≤ ‖w - 0‖ → v w = 0 := fun w hw => by
    show u (fun _ => w) = 0
    exact image_eq_zero_of_notMem_tsupport fun hm => by
      have := hR _ hm
      have := norm_le_pi_norm (fun _ : Fin 1 => w) 0
      simp only [sub_zero] at hw
      linarith
  obtain ⟨h1, h2⟩ := green_at hvc 0 (by linarith) hvR
  simp only [sub_zero] at h1 h2
  have hd : ∀ z : Fin 1 → ℂ, ReciprocityTheory.AnForm.maDens ![u] z =
      (1 / (2 * Real.pi)) * Δ v (z 0) := by
    intro z
    have hu1 : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
    have hz : z = fun _ => z 0 := funext fun i => by fin_cases i; rfl
    have hl : (ReciprocityTheory.AnForm.hessC u z 0 0).re = ReciprocityTheory.AnForm.levi u z (Pi.single 0 1) := by
      simp [ReciprocityTheory.AnForm.hessC, ReciprocityTheory.AnForm.levi]
    have huv : u = fun w : Fin 1 → ℂ => v (w 0) :=
      funext fun w => congrArg u (funext fun i => by fin_cases i; rfl)
    have hm : ReciprocityTheory.AnForm.maDens ![u] z = (2 / Real.pi) * (ReciprocityTheory.AnForm.hessC u z 0 0).re := by
      simp [ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc, hu1]
    rw [hm, hl, huv, hz, leviOne v (z 0)]
    ring
  have e : (fun z : Fin 1 → ℂ => Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z) =
      (fun w : ℂ => (1 / (2 * Real.pi)) * (Real.log ‖w‖ * Δ v w)) ∘
        (MeasurableEquiv.funUnique (Fin 1) ℂ) := by
    funext z; simp only [Function.comp, hd]; simp; ring
  have mp := volume_preserving_funUnique (Fin 1) ℂ
  have hi := mp.integral_comp (MeasurableEquiv.measurableEmbedding _)
    (fun w : ℂ => (1 / (2 * Real.pi)) * (Real.log ‖w‖ * Δ v w))
  have hv0 : v 0 = u 0 := rfl
  rw [e]
  refine ⟨(mp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 (h1.const_mul _),
    hi.trans ?_⟩
  rw [integral_const_mul, h2, hv0]
  field_simp
end ReciprocityTheory.AnForm.A
