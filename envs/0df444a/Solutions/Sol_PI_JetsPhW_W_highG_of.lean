-- Prove2me | solution 1 for PI.JetsPhW.W.highG_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:42.399435+00:00
-- url     : https://prove2.me/submissions/64c4d274-0bc0-4532-8dd0-cf81ee8a67c7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_HighGOf
import Theorems.Thm_PI_JetsPhW_W_Dv_add
import Theorems.Thm_PI_JetsPhW_W_Dv_sub
import Theorems.Thm_PI_JetsPhW_W_R_cc_l
import Theorems.Thm_PI_JetsPhW_W_cubeDefectFormula_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.JetsPhW.W
open PI.JetsPhW
section
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
end
private theorem pderiv_lX (hP : PdSelf) (hN : PdNe) {p : ℕ} [Fact p.Prime]
    {σ : Type} [DecidableEq σ] (l : PowerSeries ℂ_[p]) (i j : σ) :
    MvPowerSeries.pderiv ℂ_[p] i (lX l j : MvPowerSeries σ ℂ_[p]) =
      if j = i then PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (PI.JetsPhW.dX l) else 0 := by
  split_ifs with h
  · subst h
    exact hP p σ j l
  · exact hN p σ i j l h
private theorem isIntP_constantCoeff_of_integralMv {p : ℕ} [Fact p.Prime] {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (h : PI.JetsPhW.IntegralMv F) : PI.JetsPhW.IsIntP (MvPowerSeries.constantCoeff F) := by
  have h0 := h 0
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
end PI.JetsPhW.W
end
end

set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW
namespace PI.JetsPhW.W
theorem _root_.solution (hC : DChain) (hS : DSelf) (hN : PdNe) (hP : PdSelf) (hE : Ev0) (hJ : JetD)
    (hL : LogDer) (hI : Dint) : HighG := by
  intro p hp l ex ph hpair hD i hi1 hi2
  have hDdef := cubeDefectFormula_holds p l ex ph hpair
  obtain ⟨hex, hl, v, hvint, hv⟩ := hpair
  obtain ⟨hD0, hDe⟩ := hD
  simp only [sub_zero] at hD0 hDe
  have hl0 : PowerSeries.constantCoeff l = 0 := PI.JetsPhW.W.R.cc_l hex hl
  have hX : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    intro j; simp
  have hLc : ∀ j : Fin 3, MvPowerSeries.constantCoeff (lX l j : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun j => (hE p (Fin 3) _ l (hX j)).trans hl0
  have hpd : ∀ i j : Fin 3, MvPowerSeries.pderiv ℂ_[p] i (lX l j : MvPowerSeries (Fin 3) ℂ_[p]) =
      if j = i then PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) else 0 :=
    fun i j => pderiv_lX hP hN l i j
  have hd : ∀ (i : Fin 3) (S : MvPowerSeries (Fin 3) ℂ_[p]) (c : ℂ_[p]) (g : PowerSeries ℂ_[p]),
      MvPowerSeries.constantCoeff S = 0 →
      MvPowerSeries.pderiv ℂ_[p] i S =
        MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) →
      Dv v i (PowerSeries.subst S g) = MvPowerSeries.C c * PowerSeries.subst S (PI.JetsPhW.dX g) :=
    fun i S c g h1 h2 => hC p (Fin 3) i l v g S c hv h1 h2
  have hXne : ∀ (i j : Fin 3) (g : PowerSeries ℂ_[p]), j ≠ i →
      Dv v i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p]) g) = 0 := by
    intro i j g h
    simp only [Dv]
    rw [hN p (Fin 3) i j g h, mul_zero]
  have hq : ∀ j : Fin 3, (PI.JetsPhW.phAt ph (PI.JetsPhW.Xv j) : MvPowerSeries (Fin 3) ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p]) ph := fun j => rfl
  have c012 : MvPowerSeries.constantCoeff (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add, hLc, add_zero]
  have c01 : MvPowerSeries.constantCoeff (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add, hLc, add_zero]
  have c12 : MvPowerSeries.constantCoeff (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add, hLc, add_zero]
  have c20 : MvPowerSeries.constantCoeff (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add, hLc, add_zero]
  have p0_012 : MvPowerSeries.pderiv ℂ_[p] 0 (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add, hpd]; simp (config := { decide := true })
  have p0_01 : MvPowerSeries.pderiv ℂ_[p] 0 (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add, hpd]; simp (config := { decide := true })
  have p0_12 : MvPowerSeries.pderiv ℂ_[p] 0 (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 0 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add, hpd]; simp (config := { decide := true })
  have p0_20 : MvPowerSeries.pderiv ℂ_[p] 0 (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add, hpd]; simp (config := { decide := true })
  have p1_012 : MvPowerSeries.pderiv ℂ_[p] 1 (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add, hpd]; simp (config := { decide := true })
  have p1_01 : MvPowerSeries.pderiv ℂ_[p] 1 (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add, hpd]; simp (config := { decide := true })
  have p1_20 : MvPowerSeries.pderiv ℂ_[p] 1 (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 0 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add, hpd]; simp (config := { decide := true })
  have p2_012 : MvPowerSeries.pderiv ℂ_[p] 2 (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add, hpd]; simp (config := { decide := true })
  have p2_01 : MvPowerSeries.pderiv ℂ_[p] 2 (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 0 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add, hpd]; simp (config := { decide := true })
  have e1 : Dv v 0 (PI.JetsPhW.cubeE l ex ph) =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (v * PI.JetsPhW.dX ph) := by
    rw [hDdef]
    simp only [Dv_add, Dv_sub, hq]
    rw [hd 0 _ 1 _ c012 p0_012, hd 0 _ 1 _ c01 p0_01, hd 0 _ 0 _ c12 p0_12, hd 0 _ 1 _ c20 p0_20,
      hS p (Fin 3) 0 v ph, hXne 0 1 ph (by decide), hXne 0 2 ph (by decide)]
    simp only [map_one, map_zero, one_mul, zero_mul, sub_zero, add_zero]
  have e2 : Dv v 1
      (PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (v * PI.JetsPhW.dX ph)) =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph))) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph))) := by
    simp only [Dv_add, Dv_sub]
    rw [hd 1 _ 1 _ c012 p1_012, hd 1 _ 1 _ c01 p1_01, hd 1 _ 0 _ c20 p1_20, hXne 1 0 _ (by decide)]
    simp only [map_one, map_zero, one_mul, zero_mul, sub_zero, add_zero]
  have e3 : Dv v 2
      (PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph))) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph)))) =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph)))) := by
    rw [Dv_sub, hd 2 _ 1 _ c012 p2_012, hd 2 _ 0 _ c01 p2_01]
    simp only [map_one, map_zero, one_mul, zero_mul, sub_zero]
  have h1 : PI.JetsPhW.IntegralMv (Dv v 0 (PI.JetsPhW.cubeE l ex ph)) := hL p (Fin 3) 0 v _ hvint hD0 hDe
  rw [e1] at h1
  have h2 := hI p (Fin 3) 1 v _ hvint h1
  rw [e2] at h2
  have h3 := hI p (Fin 3) 2 v _ hvint h2
  rw [e3] at h3
  have hk : ∀ k : ℕ, PI.JetsPhW.IntegralMv (PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
      ((PI.JetsPhW.dX (A := ℂ_[p]))^[k + 3] (psi ex ph))) := by
    intro k
    induction k with
    | zero => exact h3
    | succ k ih =>
      have h4 := hI p (Fin 3) 0 v _ hvint ih
      rw [hd 0 _ 1 _ c012 p0_012, map_one, one_mul] at h4
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, Function.iterate_succ_apply']
      exact h4
  have hψ : PowerSeries.constantCoeff (psi ex ph) = PowerSeries.constantCoeff ph := hE p Unit ex ph hex
  rcases i with _ | _ | _ | k
  ·
    have hph : PowerSeries.constantCoeff ph = 0 := by
      have h0 := hD0
      rw [hDdef] at h0
      simp only [map_add, map_sub, hq] at h0
      rw [hE p (Fin 3) _ _ c012, hE p (Fin 3) _ _ c01, hE p (Fin 3) _ _ c12, hE p (Fin 3) _ _ c20,
        hE p (Fin 3) _ _ (hX 0), hE p (Fin 3) _ _ (hX 1), hE p (Fin 3) _ _ (hX 2), hψ] at h0
      linear_combination h0
    rw [hJ p ex ph]
    show PI.JetsPhW.IsIntP (PowerSeries.constantCoeff (psi ex ph))
    rw [hψ, hph]
    simp [PI.JetsPhW.IsIntP]
  · exact absurd rfl hi1
  · exact absurd rfl hi2
  · have hc := isIntP_constantCoeff_of_integralMv (hk k)
    rw [hE p (Fin 3) _ _ c012] at hc
    rw [hJ p ex ph]
    exact hc
end PI.JetsPhW.W
