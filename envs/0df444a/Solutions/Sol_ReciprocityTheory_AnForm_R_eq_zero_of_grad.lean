-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.eq_zero_of_grad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:18.939285+00:00
-- url     : https://prove2.me/submissions/cd37ec6b-c651-47ca-95db-73f9f845ca91

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_dualEv_fst
import Theorems.Thm_ReciprocityTheory_AnForm_R_dualEv_snd
import Theorems.Thm_ReciprocityTheory_AnForm_R_eval_eq_zero_of_isLocalRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_dualEv_lift
import Theorems.Thm_ReciprocityTheory_AnForm_R_map_ptIdeal_eq_zero

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
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) {e : ℕ}
    [IsLocalRing (locRing K p)] (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p))
    {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hFK : ∀ i, F i ∈ K)
    (hh : MvPolynomial (Fin n) ℂ) (hhp : eval p hh ≠ 0)
    (hcut : ∀ g ∈ K, hh * g ∈ Ideal.span (Set.range F)) (v : Fin n → ℂ)
    (hvr : ∀ i, ∑ j, eval p (pderiv j (r i)) * v j = 0)
    (hvF : ∀ k, ∑ j, eval p (pderiv j (F k)) * v j = 0) : v = 0 := by
  have heval := eval_eq_zero_of_isLocalRing K p
  have hF : ∀ k, dualEv p v (F k) = 0 := fun k => TrivSqZeroExt.ext
    (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact heval _ (hFK k))
    (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; exact hvF k)
  have hspanF : Ideal.span (Set.range F) ≤ RingHom.ker (dualEv p v).toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hF k
  have hK : ∀ g ∈ K, dualEv p v g = 0 := by
    intro g hg
    have h1 : dualEv p v (hh * g) = 0 := hspanF (hcut g hg)
    rw [map_mul] at h1
    have hu : IsUnit (dualEv p v hh) :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [dualEv_fst]; exact hhp.isUnit)
    exact hu.mul_right_eq_zero.1 h1
  obtain ⟨χ, hχ⟩ := exists_dualEv_lift K p v hK
  obtain ⟨χ0, hχ0⟩ := exists_dualEv_lift K p 0 (fun k hk => TrivSqZeroExt.ext
    (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact heval k hk)
    (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; simp))
  have hle : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p) ≤ RingHom.ker χ0 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hχ0]
    exact TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact RingHom.mem_ker.1 hx)
      (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; simp)
  have hr0 : ∀ i, eval p (r i) = 0 := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p) := by
      rw [← hr]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h1 := RingHom.mem_ker.1 (hle hmem)
    rw [hχ0] at h1
    have h2 := congrArg TrivSqZeroExt.fst h1
    rwa [dualEv_fst, TrivSqZeroExt.fst_zero] at h2
  have hall := map_ptIdeal_eq_zero K p r hr χ (fun i => by
    rw [hχ]
    exact TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact hr0 i)
      (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; exact hvr i))
  funext j
  have hx : (X j - C (p j) : MvPolynomial (Fin n) ℂ) ∈ ptIdeal p := RingHom.mem_ker.2 (by simp)
  have h1 := hall _ hx
  rw [hχ] at h1
  have h2 := congrArg TrivSqZeroExt.snd h1
  rw [dualEv_snd, TrivSqZeroExt.snd_zero] at h2
  simpa [pderiv_X, Pi.single_apply] using h2
end ReciprocityTheory.AnForm.R
