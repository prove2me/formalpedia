-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_partition_edge_phase
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:29:40.830446+00:00
-- url     : https://prove2.me/submissions/1d0ed113-8476-49c1-bcdd-f6f4e9890422

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsInduction
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_free_replacement
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_fixed_replacement
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_vertex_recursion
import Theorems.Thm_ZeroFreeRRG_Hardcore_unit_chord_sum_nonzero
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_one_edge_phase_change
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q)
    (V : Type) [Fintype V] (G : SimpleGraph V) (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (S : Finset V) (τ : V → Fin q) (v u : V) (hv : v ∈ S) (he : s(v,u) ∈ G.edgeFinset)
    (hNZ : pottsNonzeroAt q G β S) (hC : pottsCoherentAt q G β S)
    (hNZplus : ∀ T : Finset V, S ⊂ T → pottsNonzeroAt q G β T)
    (W W' : Sym2 V → Fin q → Fin q → ℂ)
    (hW : ∀ e i j, W e i j = W e j i) (hW' : ∀ e i j, W' e i j = W' e j i)
    (hseg : pottsSegmentWeights q G β W) (hseg' : pottsSegmentWeights q G β W')
    (hother : ∀ e ≠ s(v,u), ∀ i j, W' e i j = W e i j) :
    let Z := pottsWeightedPartial q G W hW S τ
    let Z' := pottsWeightedPartial q G W' hW' S τ
    Z' ≠ 0 ∧ ‖Z/(‖Z‖:ℂ)-Z'/(‖Z'‖:ℂ)‖ ≤
      (25/23)*(‖β-1‖/((7/8:ℝ)*(1-‖β-1‖))) := by
  classical
  dsimp only
  let Z := pottsWeightedPartial q G W hW S τ
  let Z' := pottsWeightedPartial q G W' hW' S τ
  have hZ : Z ≠ 0 := hNZ W hW hseg τ
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0:ℝ) < d := by linarith
  have hrad : (0.35:ℝ)/(d:ℝ) < 1 := by apply (div_lt_one₀ hdp).2; linarith
  have hδ : ‖β-1‖ < 1 := hβ.trans hrad
  have hcoeff (c : Fin q) : W s(v,u) (τ v) c ≠ 0 := by
    obtain ⟨t,ht,htW⟩ := hseg s(v,u) he (τ v) c
    have hdis : ‖W s(v,u) (τ v) c - 1‖ < 1 := by
      rw [htW]
      have hh : (1+(t:ℂ)*(β-1))-1 = (t:ℂ)*(β-1) := by ring
      rw [hh,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
      have hm : t*‖β-1‖ ≤ ‖β-1‖ := by
        nlinarith [mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) (norm_nonneg (β-1))]
      exact hm.trans_lt hδ
    intro hz
    rw [hz] at hdis
    norm_num at hdis
  by_cases hu : u ∈ S
  · let z : Unit → ℂ := fun _ => Z
    let a : Unit → ℂ := fun _ => W s(v,u) (τ v) (τ u)
    let b : Unit → ℂ := fun _ => W' s(v,u) (τ v) (τ u)
    have hse : (7/8:ℝ)*(∑ i ∈ (Finset.univ : Finset Unit), ‖z i‖) ≤ ‖∑ i ∈ (Finset.univ : Finset Unit), z i‖ := by
      simp [z]
      nlinarith [norm_nonneg Z]
    have hne : (∑ i ∈ (Finset.univ : Finset Unit), z i) ≠ 0 := by simpa [z] using hZ
    have hh := potts_one_edge_phase_change (Finset.univ : Finset Unit) z a b d hd β hβ
      (fun i hi => hseg s(v,u) he (τ v) (τ u))
      (fun i hi => hseg' s(v,u) he (τ v) (τ u)) hse hne
    have hfixed := potts_edge_fixed_replacement q G W W' hW hW' S τ v u hv hu he hother (hcoeff (τ u))
    simp only [Fintype.sum_unique] at hh
    dsimp [z,a,b] at hh
    change _ ∧ ‖Z/(‖Z‖:ℂ) - ((W' s(v,u) (τ v) (τ u)/W s(v,u) (τ v) (τ u))*Z) /
      (‖(W' s(v,u) (τ v) (τ u)/W s(v,u) (τ v) (τ u))*Z‖:ℂ)‖ ≤ _ at hh
    change Z' = (W' s(v,u) (τ v) (τ u)/W s(v,u) (τ v) (τ u))*Z at hfixed
    rw [←hfixed] at hh
    exact hh
  · let z : Fin q → ℂ := fun c => pottsWeightedPartial q G W hW (insert u S) (Function.update τ u c)
    let a : Fin q → ℂ := fun c => W s(v,u) (τ v) c
    let b : Fin q → ℂ := fun c => W' s(v,u) (τ v) c
    have hsz : S ⊂ insert u S := Finset.ssubset_insert hu
    have hz (c : Fin q) : z c ≠ 0 := (hNZplus _ hsz) W hW hseg (Function.update τ u c)
    obtain ⟨w,hw,hclose⟩ := hC W hW hseg τ u hu
    have hset : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
    have hse := unit_chord_sum_nonzero Finset.univ z w hw hset (fun i _ => hz i) (fun i _ => hclose i)
    have hne : (∑ i ∈ (Finset.univ : Finset (Fin q)), z i) ≠ 0 := hse.2
    have hh := potts_one_edge_phase_change (Finset.univ : Finset (Fin q)) z a b d hd β hβ
      (fun i hi => hseg s(v,u) he (τ v) i)
      (fun i hi => hseg' s(v,u) he (τ v) i) hse.1 hne
    have hold := potts_weighted_vertex_recursion q G W hW S τ u hu
    have hnew := potts_edge_free_replacement q G W W' hW hW' S τ v u hv hu he hother hcoeff
    change Z = ∑ i, z i at hold
    change Z' = ∑ i, (b i/a i)*z i at hnew
    dsimp only at hh
    rw [←hold,←hnew] at hh
    exact hh
