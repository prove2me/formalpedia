-- Prove2me | solution 1 for ShortestGCS.MICP.proof_5_7_flow_along_path
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:27:38.554542+00:00
-- url     : https://prove2.me/submissions/7b3ea464-9edd-458d-bba0-75c109e9ece1

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_ShortestGCS_MICP_Setting

set_option autoImplicit false
open Pointwise ShortestGCS.MICP

theorem sgm_persp_eq {n : ℕ} (X : Set (Fin n → ℝ)) (hclosed : IsClosed X)
    (hbdd : Bornology.IsBounded X) :
    perspectiveSet X = {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2 ∧ q.1 ∈ q.2 • X} := by
  unfold perspectiveSet
  apply IsClosed.closure_eq
  apply isClosed_of_closure_subset
  intro q hq
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hq
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hu' : ∀ k, 0 ≤ (u k).2 ∧ ∃ b ∈ X, (u k).2 • b = (u k).1 := by
    intro k
    obtain ⟨h1, h2⟩ := hu k
    exact ⟨h1, by simpa [Set.mem_smul_set] using h2⟩
  have hl : Filter.Tendsto (fun k => (u k).2) Filter.atTop (nhds q.2) :=
    (continuous_snd.tendsto q).comp hlim
  have hx : Filter.Tendsto (fun k => (u k).1) Filter.atTop (nhds q.1) :=
    (continuous_fst.tendsto q).comp hlim
  have hq2 : 0 ≤ q.2 := ge_of_tendsto' hl (fun k => (hu' k).1)
  refine ⟨hq2, ?_⟩
  obtain ⟨b0, hb0, _⟩ := (hu' 0).2
  rcases hq2.eq_or_lt with h0 | hpos
  · -- λ = 0
    have hx0 : q.1 = 0 := by
      have hz : Filter.Tendsto (fun k => (u k).1) Filter.atTop (nhds 0) := by
        apply squeeze_zero_norm (a := fun k => (u k).2 * R)
        · intro k
          obtain ⟨hk, b, hb, hbk⟩ := hu' k
          rw [← hbk, norm_smul, Real.norm_of_nonneg hk]
          exact mul_le_mul_of_nonneg_left (hR b hb) hk
        · have := hl.mul_const R
          rw [← h0] at this
          simpa using this
      exact tendsto_nhds_unique hx hz
    rw [← h0, Set.zero_smul_set ⟨b0, hb0⟩, hx0]
    simp
  · -- λ > 0
    have hev : ∀ᶠ k in Filter.atTop, 0 < (u k).2 := hl.eventually (lt_mem_nhds hpos)
    have hb : Filter.Tendsto (fun k => (u k).2⁻¹ • (u k).1) Filter.atTop (nhds (q.2⁻¹ • q.1)) :=
      (hl.inv₀ hpos.ne').smul hx
    have hmem : q.2⁻¹ • q.1 ∈ X := by
      refine hclosed.mem_of_tendsto hb ?_
      filter_upwards [hev] with k hk
      obtain ⟨_, b, hbX, hbk⟩ := hu' k
      rw [← hbk, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
      exact hbX
    rw [Set.mem_smul_set]
    exact ⟨_, hmem, by rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]⟩

theorem sgm_zero_of_persp {V : Type*} {n : ℕ} (G : GCS V n) (hG : IsGCS G) (v : V)
    (w : Fin n → ℝ) (l : ℝ) (h : (w, l) ∈ perspectiveSet (G.X v)) :
    (l = 0 → w = 0) ∧ (l = 1 → w ∈ G.X v) := by
  rw [sgm_persp_eq (G.X v) (hG.X_compact v).isClosed (hG.X_compact v).isBounded] at h
  obtain ⟨_, hm⟩ := h
  constructor
  · intro h0
    have hm' : w ∈ (0 : ℝ) • G.X v := by simpa [h0] using hm
    rw [Set.zero_smul_set (hG.X_nonempty v)] at hm'
    simpa using hm'
  · intro h1
    have hm' : w ∈ (1 : ℝ) • G.X v := by simpa [h1] using hm
    simpa using hm'

theorem sgm_uniq {α : Type*} [DecidableEq α] (S : Finset α) (y : α → ℝ)
    (hbin : ∀ e ∈ S, y e = 0 ∨ y e = 1) (hle : ∑ e ∈ S, y e ≤ 1) (f : α) (hf : f ∈ S)
    (hyf : y f = 1) (f' : α) (hf' : f' ∈ S) (hne : f' ≠ f) : y f' = 0 := by
  rcases hbin f' hf' with h | h
  · exact h
  · exfalso
    have hsub : ({f, f'} : Finset α) ⊆ S := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := y) (fun a ha _ => by rcases hbin a ha with h | h <;> rw [h] <;> norm_num)
    rw [Finset.sum_pair hne.symm] at h1
    linarith

theorem sgm_path_facts {V : Type*} {n : ℕ} [DecidableEq V] (G : GCS V n) (p : List V)
    (hp : IsPath G p) :
    (∀ k (hk : k + 1 < p.length), (p[k], p[k + 1]) ∈ G.E) ∧
    (∀ k (hk : k + 1 < p.length), (p[k], p[k + 1]) ∈ pathEdges p) ∧
    (∀ h : 0 < p.length, p[0] = G.s) ∧
    (∀ h : 0 < p.length, p[p.length - 1] = G.t) ∧
    (∀ i j (hi : i < p.length) (hj : j < p.length), p[i] = p[j] → i = j) := by
  obtain ⟨hhead, hlast, hnd, hchain⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact List.isChain_iff_getElem.mp hchain k hk
  · intro k hk
    rw [pathEdges, List.mem_iff_getElem]
    refine ⟨k, by simp [List.length_zip]; omega, ?_⟩
    simp [List.getElem_zip, List.getElem_tail]
  · intro h
    have h1 : p[0]? = some G.s := by simpa [List.head?_eq_getElem?] using hhead
    rw [List.getElem?_eq_getElem h] at h1
    exact Option.some.inj h1
  · intro h
    have h1 := hlast
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h1
    exact Option.some.inj h1
  · intro i j hi hj hij
    exact (hnd.getElem_inj_iff).mp hij

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (hG : IsGCS G) (y : V × V → ℝ) (z z' : V × V → Fin n → ℝ) (hfeas : IsMICPFeasible G y z z')
    (p : List V) (hp : IsPath G p) (hpy : ∀ e ∈ pathEdges p, y e = 1) :
    ∀ (k : ℕ) (hk : k + 2 < p.length),
      z' (p[k]'(by omega), p[k + 1]'(by omega)) = z (p[k + 1]'(by omega), p[k + 2]'hk) := by
  intro k hk
  obtain ⟨hE, hPE, hp0, hpl, hinj⟩ := sgm_path_facts G p hp
  have hvs : p[k + 1]'(by omega) ≠ G.s := by
    intro h
    have := hinj (k + 1) 0 (by omega) (by omega) (h.trans (hp0 (by omega)).symm)
    omega
  have hvt : p[k + 1]'(by omega) ≠ G.t := by
    intro h
    have := hinj (k + 1) (p.length - 1) (by omega) (by omega) (h.trans (hpl (by omega)).symm)
    omega
  set v := p[k + 1]'(by omega) with hv
  have he : (p[k]'(by omega), v) ∈ G.E := hE k (by omega)
  have hf : (v, p[k + 2]'hk) ∈ G.E := hE (k + 1) (by omega)
  have hye : y (p[k]'(by omega), v) = 1 := hpy _ (hPE k (by omega))
  have hyf : y (v, p[k + 2]'hk) = 1 := hpy _ (hPE (k + 1) (by omega))
  have hcons := hfeas.conserve_y v hvs hvt
  have hdeg := hfeas.degree v hvs hvt
  have hbinS : ∀ e ∈ G.E, y e = 0 ∨ y e = 1 := hfeas.binary
  have hzero : ∀ e ∈ G.E, y e = 0 → z e = 0 ∧ z' e = 0 := by
    intro e heE hy0
    obtain ⟨h1, h2⟩ := hfeas.persp e heE
    exact ⟨(sgm_zero_of_persp G hG e.1 _ _ h1).1 hy0, (sgm_zero_of_persp G hG e.2 _ _ h2).1 hy0⟩
  have hin : (p[k]'(by omega), v) ∈ inEdges G v := by
    unfold inEdges; exact Finset.mem_filter.mpr ⟨he, rfl⟩
  have hout : (v, p[k + 2]'hk) ∈ outEdges G v := by
    unfold outEdges; exact Finset.mem_filter.mpr ⟨hf, rfl⟩
  have hS1 : ∑ e ∈ inEdges G v, z' e = z' (p[k]'(by omega), v) := by
    apply Finset.sum_eq_single_of_mem _ hin
    intro e' he' hne
    simp only [inEdges, Finset.mem_filter] at he'
    have := sgm_uniq (inEdges G v) y
      (fun e he => hbinS e (Finset.mem_filter.mp he).1) (by rw [hcons]; exact hdeg) _ hin hye e'
      (Finset.mem_filter.mpr he') hne
    exact (hzero e' he'.1 this).2
  have hS2 : ∑ e ∈ outEdges G v, z e = z (v, p[k + 2]'hk) := by
    apply Finset.sum_eq_single_of_mem _ hout
    intro e' he' hne
    simp only [outEdges, Finset.mem_filter] at he'
    have := sgm_uniq (outEdges G v) y
      (fun e he => hbinS e (Finset.mem_filter.mp he).1) hdeg _ hout hyf e'
      (Finset.mem_filter.mpr he') hne
    exact (hzero e' he'.1 this).1
  have := hfeas.conserve_z v hvs hvt
  rw [hS1, hS2] at this
  exact this
