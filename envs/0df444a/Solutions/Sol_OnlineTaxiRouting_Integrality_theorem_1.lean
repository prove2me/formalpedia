-- Prove2me | solution 1 for OnlineTaxiRouting.Integrality.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:05:51.178194+00:00
-- url     : https://prove2.me/submissions/af6d85ca-4c39-4d4c-b596-a9fde7a6321f

import Mathlib
import Definitions.Def_OnlineTaxiRouting_Integrality_Setting
import Theorems.Thm_OnlineTaxiRouting_Integrality_relax_eq_flow_of_fixed
import Theorems.Thm_OnlineTaxiRouting_Integrality_flowRelax_extreme_zeroOne

open OnlineTaxiRouting.Integrality

theorem solution {C K : Type*} [Fintype C] [Fintype K] (I : Instance C K)
    (hacyc : I.Acyclic) (hfix : ∀ c, I.tmin c = I.tmax c) :
    IsIntegral (relax I) := by
  intro v hv
  have hrel := relax_eq_flow_of_fixed I hfix
  set A : C → C → Prop := fun c' c => I.T c' c ≤ I.tmin c - I.tmin c'
  set B : K → C → Prop := fun k c => I.tinit k + I.Tk k c ≤ I.tmin c
  rw [hrel] at hv
  obtain ⟨⟨hvF, hvt⟩, hext⟩ := mem_extremePoints.1 hv
  have hw : ((v.1, v.2.1, v.2.2.1) : FlowVar C K) ∈ Set.extremePoints ℝ (flowRelax A B) := by
    refine mem_extremePoints.2 ⟨hvF, fun w1 hw1 w2 hw2 hseg => ?_⟩
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hseg
    have h1 : ((w1.1, w1.2.1, w1.2.2, I.tmin) : Var C K) ∈
        {v : Var C K | (v.1, v.2.1, v.2.2.1) ∈ flowRelax A B ∧ v.2.2.2 = I.tmin} :=
      ⟨hw1, rfl⟩
    have h2 : ((w2.1, w2.2.1, w2.2.2, I.tmin) : Var C K) ∈
        {v : Var C K | (v.1, v.2.1, v.2.2.1) ∈ flowRelax A B ∧ v.2.2.2 = I.tmin} :=
      ⟨hw2, rfl⟩
    have hseg' : v ∈ openSegment ℝ ((w1.1, w1.2.1, w1.2.2, I.tmin) : Var C K)
        (w2.1, w2.2.1, w2.2.2, I.tmin) := by
      refine ⟨a, b, ha, hb, hab, ?_⟩
      have e1 := congrArg Prod.fst hcomb
      have e2 := congrArg (fun u => u.2.1) hcomb
      have e3 := congrArg (fun u => u.2.2) hcomb
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at e1 e2 e3
      refine Prod.ext e1 (Prod.ext e2 (Prod.ext e3 ?_))
      simp only [Prod.snd_add, Prod.smul_snd]
      rw [hvt, ← add_smul, hab, one_smul]
    obtain ⟨hv1, hv2⟩ := hext _ h1 _ h2 hseg'
    constructor
    · rw [← hv1]
    · rw [← hv2]
  exact flowRelax_extreme_zeroOne A B _ hw
