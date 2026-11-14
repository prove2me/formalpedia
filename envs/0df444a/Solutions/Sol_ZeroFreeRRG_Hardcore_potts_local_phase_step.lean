-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_local_phase_step
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:29:25.408045+00:00
-- url     : https://prove2.me/submissions/ff2b7ea9-68e3-4fec-9ef8-0ef8b6f25cdb

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsInduction
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_partition_edge_phase
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_incident_edge_replacement_chain
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_row_replacement_endpoint
import Theorems.Thm_ZeroFreeRRG_Hardcore_sequential_phase_bound
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_discrete_phase_budget
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q)
    (V : Type) [Fintype V] (G : SimpleGraph V) (hG : ∀ v, G.degree v ≤ d)
    (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ)) (S : Finset V)
    (hbig : ∀ T : Finset V, S ⊂ T → pottsNonzeroAt q G β T ∧ pottsCoherentAt q G β T) :
    pottsCoherentAt q G β S := by
  classical
  intro W hW hseg τ v hv
  let a : Fin q := ⟨0, by omega⟩
  let S' := insert v S
  have hss : S ⊂ S' := Finset.ssubset_insert hv
  obtain ⟨hNZ,hC⟩ := hbig S' hss
  have hNZplus : ∀ T : Finset V, S' ⊂ T → pottsNonzeroAt q G β T := by
    intro T hT
    exact (hbig T (hss.trans hT)).1
  let δ := ‖β-1‖
  let r := δ / ((7/8:ℝ)*(1-δ))
  let C := (25/23:ℝ)*r
  have hb := potts_discrete_phase_budget d hd δ (norm_nonneg _) hβ
  have hCnonneg : 0 ≤ C := mul_nonneg (by norm_num) hb.1
  let Za := pottsWeightedPartial q G W hW S' (Function.update τ v a)
  have hZa : Za ≠ 0 := hNZ W hW hseg (Function.update τ v a)
  let center := Za / (‖Za‖ : ℂ)
  have hcenter : ‖center‖ = 1 := by
    dsimp [center]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hZa)
  refine ⟨center,hcenter,?_⟩
  intro b
  obtain ⟨n,Ws,hn,hstart,hend,hprops,hsteps⟩ :=
    potts_incident_edge_replacement_chain q G β W hW hseg v a b
  let f : ℕ → ℂ := fun k => pottsWeightedPartial q G (Ws k) (hprops k).1 S' (Function.update τ v a)
  let phase : ℕ → ℂ := fun k => f k / (‖f k‖ : ℂ)
  have hphase (k : ℕ) (hk : k < n) : ‖phase k - phase (k+1)‖ ≤ C := by
    obtain ⟨e,he,hother,hrow⟩ := hsteps k hk
    have hextract : ∃ u, G.Adj v u ∧ e = s(v,u) := by
      induction e using Sym2.inductionOn with
      | _ x y =>
        rw [G.mem_incidenceFinset, G.mk'_mem_incidenceSet_iff] at he
        rcases he with ⟨hxy, h | h⟩
        · subst x
          exact ⟨y,hxy,rfl⟩
        · subst y
          exact ⟨x,hxy.symm,Sym2.eq_swap⟩
    obtain ⟨u,hu,heq⟩ := hextract
    subst e
    have he' : s(v,u) ∈ G.edgeFinset := G.incidenceFinset_subset v he
    have h := potts_partition_edge_phase d q hd hq V G β hβ S' (Function.update τ v a) v u
      (by simp [S']) he' hNZ hC hNZplus (Ws k) (Ws (k+1)) (hprops k).1 (hprops (k+1)).1
      (hprops k).2 (hprops (k+1)).2 hother
    exact h.2
  have hchain := sequential_phase_bound phase n C hphase
  have hnd : (n:ℝ) ≤ d := by exact_mod_cast (hn ▸ hG v)
  have hless : (n:ℝ)*C < 1/2 := by
    have hle := mul_le_mul_of_nonneg_right hnd hCnonneg
    have hdC : (d:ℝ)*C < 1/2 := by simpa only [C,r,mul_assoc] using hb.2.2
    exact hle.trans_lt hdC
  have hstartf : f 0 = Za := by
    dsimp [f,Za]
    simp only [hstart]
  have hendf : f n = pottsWeightedPartial q G W hW S' (Function.update τ v b) := by
    dsimp [f]
    simpa only [hend] using potts_row_replacement_endpoint q G W hW S τ v hv a b
      (by simpa only [← hend] using (hprops n).1)
  have hh := hchain.trans_lt hless
  dsimp [phase] at hh
  rw [hstartf,hendf] at hh
  exact le_of_lt hh
