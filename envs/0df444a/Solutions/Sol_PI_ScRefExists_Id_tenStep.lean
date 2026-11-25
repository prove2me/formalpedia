-- Prove2me | solution 1 for PI.ScRefExists.Id.tenStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:26.347548+00:00
-- url     : https://prove2.me/submissions/3f8cf783-a94c-4154-96d3-69c59273e3d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemTen
import Theorems.Thm_PI_ScRefExists_Id_intF
import Theorems.Thm_PI_ScRefExists_Id_iE_alg
import Theorems.Thm_PI_ScRefExists_Id_sig_iA
import Theorems.Thm_PI_ScRefExists_Id_sig_iE
import Theorems.Thm_PI_ScRefExists_Id_iE_mem
import Theorems.Thm_PI_ScRefExists_Id_iA_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.Id
namespace PI.ScRefExists.Id
theorem _root_.solution : TenStep := by
  intro hAd hFix I g θ hg _hsp hθ
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩, ⟨t3, ht3⟩⟩ := hθ
  have hgE : ((g : ℕ) : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs2 : star (t2 : I.E) = t2 := by
    have h1 : star ((θ : I.E) * star (θ : I.E)) = (θ : I.E) * star (θ : I.E) := by
      rw [star_mul, star_star]
    rw [ht2, star_mul, star_natCast, mul_comm] at h1
    exact mul_left_cancel₀ hgE h1
  have hs3 : star (t3 : I.E) = t3 := by
    have h1 : star (1 - (θ : I.E) - star (θ : I.E)) = 1 - (θ : I.E) - star (θ : I.E) := by
      rw [star_sub, star_sub, star_one, star_star]
      ring
    rw [ht3, star_mul, star_natCast, mul_comm] at h1
    exact mul_left_cancel₀ hgE h1
  obtain ⟨a2, ha2⟩ := hFix I t2 hs2
  obtain ⟨a3, ha3⟩ := hFix I t3 hs3
  have hαi : -algebraMap I.F (Af I.F) (a3 : I.F) ∈ Formalism.UG.intAd I.F :=
    (Formalism.UG.intAd I.F).neg_mem (intF a3)
  have hβi : algebraMap I.F (Af I.F) (a2 : I.F) ∈ Formalism.UG.intAd I.F := intF a2
  obtain ⟨C₁, C₂, hC₁, hC₂, hi, hii, hiii⟩ := hAd I.F g _ _ hg hαi hβi
  obtain ⟨W, hWd⟩ : ∃ W : Af I.F, W = 1 + (g : Af I.F) * C₁ := ⟨_, rfl⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : Af I.F, Q = (g : Af I.F) * C₂ := ⟨_, rfl⟩
  obtain ⟨A0, hA0d⟩ : ∃ A0 : Af I.F,
      A0 = 1 + (g : Af I.F) * -algebraMap I.F (Af I.F) (a3 : I.F) := ⟨_, rfl⟩
  obtain ⟨B0, hB0d⟩ : ∃ B0 : Af I.F, B0 = (g : Af I.F) * algebraMap I.F (Af I.F) (a2 : I.F) :=
    ⟨_, rfl⟩
  rw [← hWd, ← hQd, ← hA0d] at hi
  rw [← hWd, ← hQd, ← hB0d] at hii
  rw [← hWd, ← hQd, ← hA0d, ← hB0d] at hiii
  have hi' := congrArg (iA I) hi
  have hii' := congrArg (iA I) hii
  have hiii' := congrArg (iA I) hiii
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat, map_zero] at hi' hii' hiii'
  have hA : iA I A0 = iE I (θ : I.E) + iE I (star (θ : I.E)) := by
    have e1 : A0 = algebraMap I.F (Af I.F) (1 - (g : I.F) * (a3 : I.F)) := by
      rw [hA0d, map_sub, map_one, map_mul, map_natCast]
      ring
    have e2 : algebraMap I.F I.E (1 - (g : I.F) * (a3 : I.F)) = (θ : I.E) + star (θ : I.E) := by
      rw [map_sub, map_one, map_mul, map_natCast, ha3]
      linear_combination ht3
    rw [e1, ← iE_alg, e2, map_add]
  have hB : iA I B0 = iE I (θ : I.E) * iE I (star (θ : I.E)) := by
    have e1 : B0 = algebraMap I.F (Af I.F) ((g : I.F) * (a2 : I.F)) := by
      rw [hB0d, map_mul, map_natCast]
    have e2 : algebraMap I.F I.E ((g : I.F) * (a2 : I.F)) = (θ : I.E) * star (θ : I.E) := by
      rw [map_mul, map_natCast, ha2, ht2]
    rw [e1, ← iE_alg, e2, map_mul]
  rw [hA] at hi' hiii'
  rw [hB] at hii' hiii'
  have hWi : W ∈ Formalism.UG.intAd I.F := by
    rw [hWd]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ g) hC₁)
  have hQi : Q ∈ Formalism.UG.intAd I.F := by
    rw [hQd]
    exact mul_mem (natCast_mem _ g) hC₂
  refine ⟨iE I (θ : I.E) * iA I W - iA I Q, ?_, ?_, ?_, ?_⟩
  · exact sub_mem (mul_mem (iE_mem I θ) (iA_mem I hWi)) (iA_mem I hQi)
  · linear_combination (iE I (θ : I.E)) * hi' + hii'
  · rw [map_sub, map_mul, sig_iE, sig_iA, sig_iA]
    linear_combination hiii'
  · refine ⟨iE I (θ : I.E) * iA I C₁ - iA I C₂,
      sub_mem (mul_mem (iE_mem I θ) (iA_mem I hC₁)) (iA_mem I hC₂), ?_⟩
    have hW' : iA I W = 1 + (g : I.E ⊗[I.F] Af I.F) * iA I C₁ := by
      rw [hWd, map_add, map_one, map_mul, map_natCast]
    have hQ' : iA I Q = (g : I.E ⊗[I.F] Af I.F) * iA I C₂ := by
      rw [hQd, map_mul, map_natCast]
    show iE I (θ : I.E) * iA I W - iA I Q - iE I (θ : I.E) = _
    rw [hW', hQ']
    ring
end PI.ScRefExists.Id
