-- Prove2me | solution 1 for RetirePartialInfo.Duality.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:41:01.30644+00:00
-- url     : https://prove2.me/submissions/ca5b24c9-7a1b-447b-aefb-11ac3fc732ed

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal
import Definitions.Def_RetirePartialInfo_Duality_Dual
import Theorems.Thm_RetirePartialInfo_Duality_eq_13
import Theorems.Thm_RetirePartialInfo_Duality_eq_16
import Theorems.Thm_RetirePartialInfo_Duality_proof_2_4_value_eq
import Theorems.Thm_RetirePartialInfo_Duality_proof_2_4_feasible
import Theorems.Thm_RetirePartialInfo_Duality_proof_2_4_value_eq_retired
import Theorems.Thm_RetirePartialInfo_Duality_proof_2_4_feasible_retired

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open RetirePartialInfo.Duality

theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (h23 : Assumption23 p st Iθ Zv U1 U2) (hdual : DualIntegrable p st Zv U1 U2) :
    (∀ x : ℝ, b p 0 < x → ∀ ystar : ℝ, 0 < ystar →
      ∀ (τhat : Ω → ℝ≥0) (hτhat : IsRetirementTime p st τhat),
      IsOptimalStop p st Zv U1 U2 ystar τhat hτhat →
      Xcal p st Iθ Zv U1 U2 ystar τhat = ENNReal.ofReal (x - b p 0) →
      ∃ H : ℝ≥0 → Ω → ℝ, (∀ ω, H p.Tn ω = Hstar p Zv U2 ystar ω) ∧
        (⟨cstar p Zv U1 ystar, H, τhat⟩ : Plan Ω) ∈ Bclass p st Iθ U1 U2 x ∧
        IsGreatest (J p st U1 U2 '' Bclass p st Iθ U1 U2 x)
          (J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩) ∧
        V0 p st Iθ U1 U2 x = J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩ ∧
        IsLeast ((fun y => L0 p st Zv U1 U2 y + y * (x - b p 0)) '' Ioi 0)
          (J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩) ∧
        L0 p st Zv U1 U2 ystar + ystar * (x - b p 0) =
          J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩) ∧
    (∀ x : ℝ, 0 < x → ∀ ystar : ℝ, 0 < ystar →
      X12 p st Iθ Zv U1 U2 ystar = ENNReal.ofReal x →
      ∃ H : ℝ≥0 → Ω → ℝ, (∀ ω, H p.Tn ω = Hstar p Zv U2 ystar ω) ∧
        (cstar p Zv U1 ystar, H) ∈ B1class p st Iθ U1 U2 x ∧
        IsGreatest (J1 p st U1 U2 '' B1class p st Iθ U1 U2 x)
          (J1 p st U1 U2 (cstar p Zv U1 ystar, H)) ∧
        V1 p st Iθ U1 U2 x = J1 p st U1 U2 (cstar p Zv U1 ystar, H) ∧
        IsLeast ((fun y => L1 p st Zv U1 U2 y + y * x) '' Ioi 0)
          (J1 p st U1 U2 (cstar p Zv U1 ystar, H)) ∧
        L1 p st Zv U1 U2 ystar + ystar * x = J1 p st U1 U2 (cstar p Zv U1 ystar, H)) := by
  refine ⟨?_, ?_⟩
  · intro x hx ystar hystar τhat hτhat hopt hX
    obtain ⟨H, hHT, hmem⟩ := proof_2_4_feasible p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 h23
      hdual x hx ystar hystar τhat hτhat hX
    have hval := proof_2_4_value_eq p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 h23 hdual x hx
      ystar hystar τhat hτhat hopt hX
    have hJ : J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩ =
        L0 p st Zv U1 U2 ystar + ystar * (x - b p 0) := by
      rw [hval]
      unfold J
      have : H p.Tn = Hstar p Zv U2 ystar := funext hHT
      simp only [this]
    have hG : IsGreatest (J p st U1 U2 '' Bclass p st Iθ U1 U2 x)
        (J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩) := by
      refine ⟨⟨_, hmem, rfl⟩, ?_⟩
      rintro v ⟨q, hq, rfl⟩
      rw [hJ]
      exact eq_16 p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 hdual x ystar hystar q hq
    refine ⟨H, hHT, hmem, hG, hG.csSup_eq, ?_, hJ.symm⟩
    refine ⟨⟨ystar, hystar, hJ.symm⟩, ?_⟩
    rintro v ⟨y, hy, rfl⟩
    exact eq_16 p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 hdual x y hy _ hmem
  · intro x hx ystar hystar hX
    obtain ⟨H, hHT, hmem⟩ := proof_2_4_feasible_retired p st Iθ Zv U1 U2 hst hIto h21 hZv hU1
      hU2 h23 hdual x hx ystar hystar hX
    have hval := proof_2_4_value_eq_retired p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 h23 hdual
      x hx ystar hystar hX
    have hJ : J1 p st U1 U2 (cstar p Zv U1 ystar, H) =
        L1 p st Zv U1 U2 ystar + ystar * x := by
      rw [hval]
      unfold J1
      have : H p.Tn = Hstar p Zv U2 ystar := funext hHT
      simp only [this]
    have hG : IsGreatest (J1 p st U1 U2 '' B1class p st Iθ U1 U2 x)
        (J1 p st U1 U2 (cstar p Zv U1 ystar, H)) := by
      refine ⟨⟨_, hmem, rfl⟩, ?_⟩
      rintro v ⟨q, hq, rfl⟩
      rw [hJ]
      exact eq_13 p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 hdual x ystar hystar q hq
    refine ⟨H, hHT, hmem, hG, hG.csSup_eq, ?_, hJ.symm⟩
    refine ⟨⟨ystar, hystar, hJ.symm⟩, ?_⟩
    rintro v ⟨y, hy, rfl⟩
    exact eq_13 p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 hdual x y hy _ hmem
