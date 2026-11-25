-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.mj_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:46:02.818817+00:00
-- url     : https://prove2.me/submissions/5fae87c0-f99f-4266-a746-dbd1b33426b6

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_add_left
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_smul_left
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_add_right
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_smul_right
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_swap
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_self_star
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_tau_real
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_tau_normSq
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_pos
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
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
variable {S}
variable (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) (τ : E →+* ℂ)
  (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
  (hzz : (τ (S.hT z z)).re < 0)
  (hpos : ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
include hstar hPX hzP hzz hpos
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (x y : S.V) (hx : x ∈ P) (hy : y ∈ P) :
    Complex.normSq (τ (mj S z x y)) ≤ (τ (mj S z x x)).re * (τ (mj S z y y)).re := by
  have hnn : ∀ s : E, 0 ≤ (τ (mj S z (s • x + y) (s • x + y))).re := fun s =>
    (mj_pos hstar τ X P hPX z hzP hzz hpos _ (P.add_mem (P.smul_mem s hx) hy)).1
  have hexp : ∀ s : E, mj S z (s • x + y) (s • x + y) =
      star s * s * mj S z x x + star s * mj S z x y + s * star (mj S z x y) + mj S z y y := by
    intro s
    rw [mj_add_left, mj_add_right, mj_add_right, mj_smul_left, mj_smul_left, mj_smul_right,
      mj_smul_right, mj_swap z x y]
    ring
  have hareal := tau_real (hstar τ) (mj_self_star z x)
  have ha0 := (mj_pos hstar τ X P hPX z hzP hzz hpos x hx).1
  rcases ha0.lt_or_eq with hapos | hazero
  · have hane : mj S z x x ≠ 0 := by
      intro h; rw [h, map_zero] at hapos; simp at hapos
    have h := hnn (-(mj S z x y) / mj S z x x)
    rw [hexp] at h
    have hval : star (-(mj S z x y) / mj S z x x) * (-(mj S z x y) / mj S z x x) * mj S z x x +
        star (-(mj S z x y) / mj S z x x) * mj S z x y +
        (-(mj S z x y) / mj S z x x) * star (mj S z x y) + mj S z y y =
        mj S z y y - (star (mj S z x y) * mj S z x y) / mj S z x x := by
      rw [star_div₀, star_neg, mj_self_star]
      field_simp
      ring
    rw [hval, map_sub, map_div₀, tau_normSq (hstar τ), hareal, Complex.sub_re] at h
    rw [← Complex.ofReal_div, Complex.ofReal_re] at h
    rw [sub_nonneg, div_le_iff₀ hapos] at h
    linarith
  · have hτa : τ (mj S z x x) = 0 := by rw [hareal, ← hazero]; simp
    have ha : mj S z x x = 0 := τ.injective (by rw [hτa, map_zero])
    rw [← hazero, zero_mul]
    by_contra hlt
    have hpos' : 0 < Complex.normSq (τ (mj S z x y)) := lt_of_not_ge hlt
    obtain ⟨N, hN⟩ := exists_nat_gt ((τ (mj S z y y)).re / (2 * Complex.normSq (τ (mj S z x y))))
    have h := hnn (-(N : E) * mj S z x y)
    rw [hexp, ha] at h
    have hval : star (-(N : E) * mj S z x y) * (-(N : E) * mj S z x y) * 0 +
        star (-(N : E) * mj S z x y) * mj S z x y +
        (-(N : E) * mj S z x y) * star (mj S z x y) + mj S z y y =
        mj S z y y - (2 * (N : E)) * (star (mj S z x y) * mj S z x y) := by
      rw [star_mul, star_neg, star_natCast]
      ring
    rw [hval, map_sub, map_mul, tau_normSq (hstar τ), Complex.sub_re] at h
    have h2 : (τ (2 * (N : E))) = ((2 * (N : ℝ) : ℝ) : ℂ) := by
      rw [map_mul, map_natCast, map_ofNat]; push_cast; ring
    rw [h2, ← Complex.ofReal_mul, Complex.ofReal_re] at h
    rw [div_lt_iff₀ (by positivity)] at hN
    nlinarith
end PI.AutLzFinite.SlopeTestRemainingChoices
