-- Prove2me | solution 1 for PI.FockOneDegW.key_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:45:50.339067+00:00
-- url     : https://prove2.me/submissions/5aa380b8-841c-4236-968f-2949cde5e05e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_SameBlockOfPosC
import Theorems.Thm_PI_FockOneDegW_sameBlock_of_posC
import Theorems.Thm_PI_FockOneDegW_isKC_Eab
import Theorems.Thm_PI_FockOneDegW_exists_orth
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_right
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW
namespace PI.FockOneDegW
theorem _root_.solution (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) (hT : HwHarmDeg)
    {p q r s : ℕ} (μ : Ix p q → ℚ) (W : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ W]
    (hWK : KStable (fockAct1 p q r s) W)
    (hWhw : ∀ (ν : Ix p q → ℚ) (w : Pol p q r s), w ∈ W → IsHW (fockAct1 p q r s) ν w → ν = μ)
    (P : Pol p q r s) (hPW : P ∈ W) (hH : Harm2 P) (e : ℕ)
    (he : homogeneousComponent e P ≠ 0) :
    (e : ℚ) = degW (cPair r s) μ := by
  classical
  let V : Submodule ℂ (Pol p q r s) := W ⊓ harmSub hS p q r s
  let N : Submodule ℂ (Pol p q r s) :=
    V ⊓ LinearMap.ker (homogeneousComponent e : Pol p q r s →ₗ[ℂ] Pol p q r s)
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  have hVst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ V, fockAct1 p q r s (Eab a b) u ∈ V := by
    intro a b hab u hu
    exact ⟨hWK _ (isKC_Eab hab) u hu.1, hKh p q r s a b hab u hu.2⟩
  have hNst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ N, fockAct1 p q r s (Eab a b) u ∈ N := by
    intro a b hab u hu
    refine ⟨hVst a b hab u hu.1, ?_⟩
    have h0 : homogeneousComponent e u = 0 := hu.2
    show homogeneousComponent e (fockAct1 p q r s (Eab a b) u) = 0
    rw [hKc p q r s a b hab e u, h0, map_zero]
  let C : Submodule ℂ (Pol p q r s) :=
    { carrier := {c | c ∈ V ∧ ∀ n ∈ N, fockInner n c = 0}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨V.add_mem hx hy, fun n hn => ?_⟩
        rw [fockInner_add_right, hx' n hn, hy' n hn, add_zero]
      zero_mem' := ⟨V.zero_mem, fun n _ => fockInner_zero_right n⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨V.smul_mem c hx, fun n hn => ?_⟩
        rw [fockInner_smul_right, hx' n hn, mul_zero] }
  have hPV : P ∈ V := ⟨hPW, hH⟩
  have hPN : P ∉ N := fun h => he h.2
  have hNV : N < V := lt_of_le_of_ne inf_le_left (fun h => hPN (h ▸ hPV))
  obtain ⟨c0, hc0V, hc0, hc0N⟩ := exists_orth hNV
  have hCne : C ≠ ⊥ := by
    intro h
    have : c0 ∈ C := ⟨hc0V, hc0N⟩
    rw [h, Submodule.mem_bot] at this
    exact hc0 this
  haveI : FiniteDimensional ℂ C :=
    Submodule.finiteDimensional_of_le (show C ≤ V from fun x hx => hx.1)
  have hCst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ C, fockAct1 p q r s (Eab a b) u ∈ C := by
    intro a b hab u hu
    refine ⟨hVst a b hab u hu.1, fun n hn => ?_⟩
    rw [hA p q r s a b hab n u]
    have hba : sameBlock b a := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
    exact hu.2 _ (hNst b a hba n hn)
  obtain ⟨ν, v, hvC, hv0, hvhw⟩ := hE p q r s C inferInstance hCne hCst
  have hνμ : ν = μ := hWhw ν v hvC.1.1 ⟨hv0, hvhw⟩
  subst hνμ

  have hve : homogeneousComponent e v ≠ 0 := by
    intro h
    have hvN : v ∈ N := ⟨hvC.1, h⟩
    have := hvC.2 v hvN
    exact hv0 ((hI _ v v v 0).2.2.2.2.1 this)
  have hwt : ∀ a : Ix p q, fockAct1 p q r s (Eab a a) v = ((ν a : ℚ) : ℂ) • v := by
    intro a
    have := (Submodule.mem_iInf _).mp hvhw.1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  have hraise : ∀ a b : Ix p q, posC a b → fockAct1 p q r s (Eab a b) v = 0 := by
    intro a b hab
    have h1 := (Submodule.mem_iInf _).mp hvhw.2 a
    have h2 := (Submodule.mem_iInf _).mp h1 b
    have h3 := (Submodule.mem_iInf _).mp h2 hab
    exact LinearMap.mem_ker.mp h3
  have hsame : ∀ a : Ix p q, sameBlock a a := by
    intro a; rcases a with a | a <;> simp [sameBlock]
  have hHW : IsHW (fockAct1 p q r s) ν (homogeneousComponent e v) := by
    refine ⟨hve, ?_, ?_⟩
    · refine (Submodule.mem_iInf _).mpr fun a => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, ← hKc p q r s a a (hsame a) e v, hwt a,
        map_smul, LinearMap.smul_apply, LinearMap.id_apply, sub_self]
    · refine (Submodule.mem_iInf _).mpr fun a => (Submodule.mem_iInf _).mpr fun b =>
        (Submodule.mem_iInf _).mpr fun hab => ?_
      rw [LinearMap.mem_ker, ← hKc p q r s a b (sameBlock_of_posC hab) e v, hraise a b hab, map_zero]
  have hhom : homogeneousComponent e v ∈ homog (Ix p q × Ix r s) e :=
    (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e v)
  exact hT p q r s ν e _ hhom hHW (hHc p q r s e v hvC.1.2)
end PI.FockOneDegW
