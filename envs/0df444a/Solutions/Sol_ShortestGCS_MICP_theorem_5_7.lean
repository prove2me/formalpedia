-- Prove2me | solution 1 for ShortestGCS.MICP.theorem_5_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:46:26.959347+00:00
-- url     : https://prove2.me/submissions/a75c4d49-f986-4c6b-a667-03e66fc50788

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

theorem sgm_sInf_aux (b : EReal) :
    sInf ((fun σ : ℝ => (σ : EReal)) '' {σ : ℝ | b ≤ (σ : EReal)}) = b := by
  apply le_antisymm
  · induction b using EReal.rec with
    | bot =>
      rw [le_bot_iff, EReal.eq_bot_iff_forall_lt]
      intro r
      exact lt_of_le_of_lt (sInf_le ⟨r - 1, by simp, rfl⟩)
        (EReal.coe_lt_coe_iff.mpr (by linarith))
    | coe r => exact sInf_le ⟨r, by simp, rfl⟩
    | top =>
      have : {σ : ℝ | (⊤ : EReal) ≤ (σ : EReal)} = ∅ := by
        ext σ; simp
      rw [this]; simp
  · exact le_sInf (by rintro _ ⟨σ, hσ, rfl⟩; exact hσ)

theorem sgm_mul_iff (lam : ℝ) (hl : 0 < lam) (a : EReal) (σ : ℝ) :
    a ≤ ((lam⁻¹ * σ : ℝ) : EReal) ↔ (lam : EReal) * a ≤ (σ : EReal) := by
  induction a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hl]
  | top =>
    rw [EReal.coe_mul_top_of_pos hl, top_le_iff, top_le_iff]
    exact ⟨fun h => absurd h (EReal.coe_ne_top _), fun h => absurd h (EReal.coe_ne_top _)⟩
  | coe r =>
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    rw [inv_mul_eq_div, le_div_iff₀ hl]
    constructor <;> intro h <;> linarith [mul_comm r lam]

theorem sgm_part2 {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (f : E → EReal) (x : E) (lam : ℝ) (h : lam < 0) :
    perspectiveFun f x lam = ⊤ := by
  have hs : {σ : ℝ | ((x, σ), lam) ∈ perspectiveSet (epigraph f)} = ∅ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hmem
    unfold perspectiveSet at hmem
    have h0 : ((x, σ), lam) ∈ {q : (E × ℝ) × ℝ | 0 ≤ q.2} :=
      closure_minimal (fun q hq => hq.1) (isClosed_le continuous_const continuous_snd) hmem
    have h1 : 0 ≤ lam := h0
    linarith
  unfold perspectiveFun
  rw [hs]
  simp

theorem sgm_mem_persp_iff {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] (S : Set E) (hS : IsClosed S) (w : E) (lam : ℝ)
    (hl : 0 < lam) :
    (w, lam) ∈ perspectiveSet S ↔ lam⁻¹ • w ∈ S := by
  constructor
  · intro h
    have hU : IsOpen {q : E × ℝ | 0 < q.2} := isOpen_lt continuous_const continuous_snd
    have h1 : (w, lam) ∈ closure ({q : E × ℝ | 0 < q.2} ∩ {q : E × ℝ | 0 ≤ q.2 ∧ q.1 ∈ q.2 • S}) :=
      hU.inter_closure ⟨hl, h⟩
    have hc : ContinuousAt (fun q : E × ℝ => q.2⁻¹ • q.1) (w, lam) :=
      (ContinuousAt.inv₀ continuous_snd.continuousAt hl.ne').smul continuous_fst.continuousAt
    have h2 : (fun q : E × ℝ => q.2⁻¹ • q.1) (w, lam) ∈ closure S := by
      refine hc.continuousWithinAt.mem_closure h1 ?_
      rintro ⟨w', l'⟩ ⟨hl', _, hm⟩
      have hl'' : 0 < l' := hl'
      obtain ⟨s, hs, hse⟩ := hm
      have hse' : l' • s = w' := hse
      show l'⁻¹ • w' ∈ S
      rw [← hse', inv_smul_smul₀ hl''.ne']
      exact hs
    rw [hS.closure_eq] at h2
    exact h2
  · intro h
    apply subset_closure
    refine ⟨hl.le, ?_⟩
    exact ⟨lam⁻¹ • w, h, smul_inv_smul₀ hl.ne' w⟩

theorem sgm_part1 {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    (f : E → EReal) (hcl : IsClosed (epigraph f)) (x : E) (lam : ℝ) (hl : 0 < lam) :
    perspectiveFun f x lam = (lam : EReal) * f (lam⁻¹ • x) := by
  have hset : {σ : ℝ | ((x, σ), lam) ∈ perspectiveSet (epigraph f)} =
      {σ : ℝ | (lam : EReal) * f (lam⁻¹ • x) ≤ (σ : EReal)} := by
    ext σ
    simp only [Set.mem_setOf_eq]
    rw [sgm_mem_persp_iff (epigraph f) hcl (x, σ) lam hl, ← sgm_mul_iff lam hl]
    rfl
  unfold perspectiveFun
  rw [hset]
  exact sgm_sInf_aux _

theorem sgm_part3 {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    (f : E → EReal) (hf : IsProperClosedConvex f) :
    perspectiveFun f 0 0 = 0 := by
  obtain ⟨hconv, hcl, ⟨x0, hx0⟩, hbot⟩ := hf
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x0 = (a : EReal) :=
    ⟨(f x0).toReal, (EReal.coe_toReal hx0 (hbot x0)).symm⟩
  have hxa : (x0, a) ∈ epigraph f := by
    show f x0 ≤ ((a : ℝ) : EReal)
    rw [ha]
  have hset : {σ : ℝ | (((0 : E), σ), (0 : ℝ)) ∈ perspectiveSet (epigraph f)} =
      {σ : ℝ | (0 : EReal) ≤ (σ : EReal)} := by
    ext σ
    simp only [Set.mem_setOf_eq, EReal.coe_nonneg]
    constructor
    · intro h
      have hU : IsOpen {q : (E × ℝ) × ℝ | q.2 < 1} := isOpen_lt continuous_snd continuous_const
      have h1 : (((0 : E), σ), (0 : ℝ)) ∈ closure ({q : (E × ℝ) × ℝ | q.2 < 1} ∩
          {q : (E × ℝ) × ℝ | 0 ≤ q.2 ∧ q.1 ∈ q.2 • epigraph f}) :=
        hU.inter_closure ⟨(by show (0 : ℝ) < 1; norm_num), h⟩
      have hψ : Continuous (fun q : (E × ℝ) × ℝ => q.1 + (1 - q.2) • (x0, a)) :=
        continuous_fst.add ((continuous_const.sub continuous_snd).smul continuous_const)
      have h2 : (fun q : (E × ℝ) × ℝ => q.1 + (1 - q.2) • (x0, a)) (((0 : E), σ), (0 : ℝ))
          ∈ closure (epigraph f) := by
        refine hψ.continuousAt.continuousWithinAt.mem_closure h1 ?_
        rintro ⟨w, l'⟩ ⟨hlt, h0, hm⟩
        obtain ⟨e, he, hwe⟩ := hm
        have hlt' : l' < 1 := hlt
        have h0' : 0 ≤ l' := h0
        show w + (1 - l') • (x0, a) ∈ epigraph f
        have hwe' : l' • e = w := hwe
        rw [← hwe']
        exact hconv he hxa h0' (by linarith) (by ring)
      rw [hcl.closure_eq] at h2
      have e1 : (fun q : (E × ℝ) × ℝ => q.1 + (1 - q.2) • (x0, a)) (((0 : E), σ), (0 : ℝ))
          = (x0, σ + a) := by
        refine Prod.ext (by simp) ?_
        simp [add_comm]
      rw [e1] at h2
      have h3 : f x0 ≤ ((σ + a : ℝ) : EReal) := h2
      rw [ha, EReal.coe_le_coe_iff] at h3
      linarith
    · intro hσ
      let g : ℝ → (E × ℝ) × ℝ := fun ε => ((ε • x0, σ + ε * a), ε)
      have hg : Continuous g := by fun_prop
      have h0 : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by simp [closure_Ioi]
      have h2 : g 0 ∈ closure {q : (E × ℝ) × ℝ | 0 ≤ q.2 ∧ q.1 ∈ q.2 • epigraph f} := by
        refine hg.continuousAt.continuousWithinAt.mem_closure h0 ?_
        intro ε hε
        have hε' : 0 < ε := hε
        refine ⟨hε'.le, ?_⟩
        refine ⟨(x0, σ / ε + a), ?_, ?_⟩
        · show f x0 ≤ ((σ / ε + a : ℝ) : EReal)
          rw [ha, EReal.coe_le_coe_iff]
          have : 0 ≤ σ / ε := div_nonneg hσ hε'.le
          linarith
        · refine Prod.ext rfl ?_
          show ε * (σ / ε + a) = σ + ε * a
          field_simp
      have e : g 0 = (((0 : E), σ), (0 : ℝ)) := by simp [g]
      rw [e] at h2
      exact h2
  unfold perspectiveFun
  rw [hset]
  exact sgm_sInf_aux 0

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

def SgmGood {V : Type*} (F : V → V → Prop) (t : V) (l : List V) : Prop :=
  l.getLast? = some t ∧ l.Nodup ∧ ∀ i (h : i + 1 < l.length), F l[i] l[i + 1]

theorem sgm_build {V : Type*} [Fintype V] [DecidableEq V] (F : V → V → Prop) (s t : V)
    (hout_t : ∀ w, ¬ F t w)
    (hout_uniq : ∀ v a b, F v a → F v b → a = b)
    (hex_t : ∃ u, F u t)
    (hcons : ∀ v, v ≠ s → v ≠ t → ∀ b, F v b → ∃ a, F a v) :
    ∃ l : List V, l.head? = some s ∧ SgmGood F t l := by
  have H : ∀ m : ℕ, ∀ l : List V, Fintype.card V - l.length = m → SgmGood F t l →
      ∃ l' : List V, l'.head? = some s ∧ SgmGood F t l' := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro l hm hg
      rcases l with _ | ⟨h, rest⟩
      · exact absurd hg.1 (by simp)
      by_cases hs : h = s
      · exact ⟨h :: rest, by simp [hs], hg⟩
      have hpred : ∃ w, F w h := by
        by_cases ht : h = t
        · subst ht; exact hex_t
        · rcases rest with _ | ⟨x, rest'⟩
          · exfalso; apply ht; simpa using hg.1
          · exact hcons h hs ht x (by simpa using hg.2.2 0 (by simp))
      obtain ⟨w, hw⟩ := hpred
      have hwn : w ∉ h :: rest := by
        intro hmem
        obtain ⟨i, hi, hwi⟩ := List.mem_iff_getElem.mp hmem
        by_cases hi1 : i + 1 < (h :: rest).length
        · have h1 := hg.2.2 i hi1
          rw [hwi] at h1
          have h2 : (h :: rest)[i + 1] = (h :: rest)[0] := hout_uniq w _ _ h1 hw
          have := (hg.2.1.getElem_inj_iff).mp h2
          omega
        · have h3 : i = (h :: rest).length - 1 := by omega
          have h4 := hg.1
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp)] at h4
          subst h3
          have h5 := Option.some.inj h4
          rw [hwi] at h5
          subst h5
          exact hout_t _ hw
      have hnd : (w :: h :: rest).Nodup := List.nodup_cons.mpr ⟨hwn, hg.2.1⟩
      have hlen := hnd.length_le_card
      refine ih (Fintype.card V - (w :: h :: rest).length) ?_ (w :: h :: rest) rfl
        ⟨?_, hnd, ?_⟩
      · simp only [List.length_cons] at hlen hm ⊢
        omega
      · rw [List.getLast?_cons_cons]; exact hg.1
      · intro i hi
        cases i with
        | zero => exact hw
        | succ j =>
          exact hg.2.2 j (by simp only [List.length_cons] at hi ⊢; omega)
  exact H _ [t] rfl ⟨by simp, by simp, by intro i hi; simp at hi⟩

theorem sgm_mem_pathEdges {V : Type*} (p : List V) (e : V × V) (h : e ∈ pathEdges p) :
    ∃ k, ∃ hk : k + 1 < p.length, e = (p[k], p[k + 1]) := by
  rw [pathEdges, List.mem_iff_getElem] at h
  obtain ⟨i, hi, hie⟩ := h
  have hi' : i + 1 < p.length := by simp [List.length_zip] at hi; omega
  refine ⟨i, hi', ?_⟩
  rw [← hie]
  simp [List.getElem_zip, List.getElem_tail]

theorem sgm_sum_card {α : Type*} [DecidableEq α] (S : Finset α) (y : α → ℝ)
    (hbin : ∀ e ∈ S, y e = 0 ∨ y e = 1) :
    ∑ e ∈ S, y e = ((S.filter fun e => y e = 1).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro e he
  rcases hbin e he with h | h <;> simp [h]

theorem sgm_card_in {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (y : V × V → ℝ) (hbin : ∀ e ∈ G.E, y e = 0 ∨ y e = 1) (v : V) :
    ((G.E.filter fun e => y e = 1 ∧ e.2 = v).card : ℝ) = ∑ e ∈ inEdges G v, y e := by
  rw [sgm_sum_card (inEdges G v) y (fun e he => hbin e (Finset.mem_filter.mp he).1)]
  have : (inEdges G v).filter (fun e => y e = 1) = G.E.filter fun e => y e = 1 ∧ e.2 = v := by
    ext e
    simp only [inEdges, Finset.mem_filter]
    tauto
  rw [this]

theorem sgm_card_out {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (y : V × V → ℝ) (hbin : ∀ e ∈ G.E, y e = 0 ∨ y e = 1) (v : V) :
    ((G.E.filter fun e => y e = 1 ∧ e.1 = v).card : ℝ) = ∑ e ∈ outEdges G v, y e := by
  rw [sgm_sum_card (outEdges G v) y (fun e he => hbin e (Finset.mem_filter.mp he).1)]
  have : (outEdges G v).filter (fun e => y e = 1) = G.E.filter fun e => y e = 1 ∧ e.1 = v := by
    ext e
    simp only [outEdges, Finset.mem_filter]
    tauto
  rw [this]

theorem sgm_path_cycles {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (hst : NoInSNoOutT G) (hne : G.s ≠ G.t) (y : V × V → ℝ)
    (hbin : ∀ e ∈ G.E, y e = 0 ∨ y e = 1)
    (hsource : ∑ e ∈ outEdges G G.s, y e = 1) (htarget : ∑ e ∈ inEdges G G.t, y e = 1)
    (hdeg : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ outEdges G v, y e ≤ 1)
    (hcons : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ inEdges G v, y e = ∑ e ∈ outEdges G v, y e) :
    ∃ p : List V, IsPath G p ∧ (∀ e ∈ pathEdges p, y e = 1) ∧
      (∀ e ∈ G.E, y e = 1 → e ∉ pathEdges p → e.1 ∉ p ∧ e.2 ∉ p) ∧
      ∀ v : V,
        (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.2 = v).card =
            (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v).card ∧
          (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v).card ≤ 1 := by
  have hcin := sgm_card_in G y hbin
  have hcout := sgm_card_out G y hbin
  have hFo_s : (G.E.filter fun e => y e = 1 ∧ e.1 = G.s).card = 1 := by
    have := hcout G.s; rw [hsource] at this; exact_mod_cast this
  have hFi_t : (G.E.filter fun e => y e = 1 ∧ e.2 = G.t).card = 1 := by
    have := hcin G.t; rw [htarget] at this; exact_mod_cast this
  have hFo_le : ∀ v, v ≠ G.s → v ≠ G.t → (G.E.filter fun e => y e = 1 ∧ e.1 = v).card ≤ 1 := by
    intro v hs ht
    have h1 := hcout v
    have h2 := hdeg v hs ht
    rw [← h1] at h2
    exact_mod_cast h2
  have hFeq : ∀ v, v ≠ G.s → v ≠ G.t →
      (G.E.filter fun e => y e = 1 ∧ e.2 = v).card =
        (G.E.filter fun e => y e = 1 ∧ e.1 = v).card := by
    intro v hs ht
    have h1 := hcin v
    have h2 := hcout v
    have h3 := hcons v hs ht
    rw [← h1, ← h2] at h3
    exact_mod_cast h3
  -- F-level facts
  let F : V → V → Prop := fun a b => (a, b) ∈ G.E ∧ y (a, b) = 1
  have memFi : ∀ v a, F a v ↔ (a, v) ∈ (G.E.filter fun e => y e = 1 ∧ e.2 = v) := by
    intro v a
    constructor
    · rintro ⟨h1, h2⟩; exact Finset.mem_filter.mpr ⟨h1, h2, rfl⟩
    · intro h
      obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp h
      exact ⟨h1, h2⟩
  have memFo : ∀ v a, F v a ↔ (v, a) ∈ (G.E.filter fun e => y e = 1 ∧ e.1 = v) := by
    intro v a
    constructor
    · rintro ⟨h1, h2⟩; exact Finset.mem_filter.mpr ⟨h1, h2, rfl⟩
    · intro h
      obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp h
      exact ⟨h1, h2⟩
  have hFi_le : ∀ v, v ≠ G.s → (G.E.filter fun e => y e = 1 ∧ e.2 = v).card ≤ 1 := by
    intro v hs
    by_cases ht : v = G.t
    · subst ht; exact hFi_t.le
    · rw [hFeq v hs ht]; exact hFo_le v hs ht
  have hFo_le' : ∀ v, v ≠ G.t → (G.E.filter fun e => y e = 1 ∧ e.1 = v).card ≤ 1 := by
    intro v ht
    by_cases hs : v = G.s
    · subst hs; exact hFo_s.le
    · exact hFo_le v hs ht
  have hin_uniq : ∀ v a b, F a v → F b v → a = b := by
    intro v a b ha hb
    by_cases hvs : v = G.s
    · exfalso; exact (hst _ ha.1).1 hvs
    · have := Finset.card_le_one.mp (hFi_le v hvs) (a, v) ((memFi v a).mp ha) (b, v)
        ((memFi v b).mp hb)
      exact (Prod.mk.inj this).1
  have hout_uniq : ∀ v a b, F v a → F v b → a = b := by
    intro v a b ha hb
    by_cases hvt : v = G.t
    · exfalso; exact (hst _ ha.1).2 hvt
    · have := Finset.card_le_one.mp (hFo_le' v hvt) (v, a) ((memFo v a).mp ha) (v, b)
        ((memFo v b).mp hb)
      exact (Prod.mk.inj this).2
  have hout_t : ∀ w, ¬ F G.t w := fun w h => (hst _ h.1).2 rfl
  have hnonI : ∀ v, 0 < (G.E.filter fun e => y e = 1 ∧ e.2 = v).card → ∃ a, F a v := by
    intro v h
    obtain ⟨⟨a, b⟩, he⟩ := Finset.card_pos.mp h
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp he
    have h3' : b = v := h3
    subst h3'
    exact ⟨a, h1, h2⟩
  have hex_t : ∃ u, F u G.t := hnonI G.t (by rw [hFi_t]; norm_num)
  have hcons' : ∀ v, v ≠ G.s → v ≠ G.t → ∀ b, F v b → ∃ a, F a v := by
    intro v hs ht b hb
    apply hnonI
    rw [hFeq v hs ht]
    exact Finset.card_pos.mpr ⟨(v, b), (memFo v b).mp hb⟩
  obtain ⟨p, hphead, hgood⟩ := sgm_build F G.s G.t hout_t hout_uniq hex_t hcons'
  have hpath : IsPath G p :=
    ⟨hphead, hgood.1, hgood.2.1, List.isChain_iff_getElem.mpr (fun i h => (hgood.2.2 i h).1)⟩
  obtain ⟨hE, hPE, hp0, hpl, hinj⟩ := sgm_path_facts G p hpath
  have hlen : 0 < p.length := by
    rcases p with _ | ⟨a, r⟩
    · simp at hphead
    · simp
  have hsp : G.s ∈ p := by rw [← hp0 hlen]; exact List.getElem_mem _
  have htp : G.t ∈ p := by rw [← hpl hlen]; exact List.getElem_mem _
  have prop2 : ∀ e ∈ G.E, y e = 1 → e ∉ pathEdges p → e.1 ∉ p ∧ e.2 ∉ p := by
    intro e heE hy hnot
    obtain ⟨u, w⟩ := e
    have hF : F u w := ⟨heE, hy⟩
    constructor
    · intro hu
      obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.mp hu
      by_cases hi1 : i + 1 < p.length
      · have hF2 := hgood.2.2 i hi1
        rw [hiu] at hF2
        have hw := hout_uniq u w _ hF hF2
        apply hnot
        have := hPE i hi1
        rw [hiu, ← hw] at this
        exact this
      · exfalso
        have h3 : i = p.length - 1 := by omega
        subst h3
        have := hpl hlen
        rw [hiu] at this
        exact (hst _ heE).2 this
    · intro hw
      obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hw
      cases i with
      | zero =>
        exfalso
        have := hp0 hlen
        have h5 : w = G.s := hiw.symm.trans this
        exact (hst _ heE).1 h5
      | succ j =>
        have hF2 := hgood.2.2 j (by omega)
        rw [hiw] at hF2
        have hu := hin_uniq w u _ hF hF2
        apply hnot
        have := hPE j (by omega)
        rw [hiw, ← hu] at this
        exact this
  refine ⟨p, hpath, ?_, prop2, ?_⟩
  · intro e he
    obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e he
    exact (hgood.2.2 k hk).2
  · intro v
    by_cases hv : v ∈ p
    · have e1 : (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.2 = v) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (by
          rintro e he ⟨hy, hn, h2⟩
          exact (prop2 e he hy hn).2 (by rw [h2]; exact hv))
      have e2 : (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (by
          rintro e he ⟨hy, hn, h2⟩
          exact (prop2 e he hy hn).1 (by rw [h2]; exact hv))
      rw [e1, e2]; simp
    · have hvs : v ≠ G.s := fun h => hv (h ▸ hsp)
      have hvt : v ≠ G.t := fun h => hv (h ▸ htp)
      have e1 : (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.2 = v) =
          G.E.filter fun e => y e = 1 ∧ e.2 = v := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
        · rintro ⟨h1, h2, h4⟩
          refine ⟨h1, h2, ?_, h4⟩
          intro hmem
          obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e hmem
          exact hv (by rw [← h4]; exact List.getElem_mem _)
      have e2 : (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v) =
          G.E.filter fun e => y e = 1 ∧ e.1 = v := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
        · rintro ⟨h1, h2, h4⟩
          refine ⟨h1, h2, ?_, h4⟩
          intro hmem
          obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e hmem
          exact hv (by rw [← h4]; exact List.getElem_mem _)
      rw [e1, e2]
      exact ⟨hFeq v hvs hvt, hFo_le v hvs hvt⟩

theorem sgm_flow {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
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

theorem sgm_persp_zero {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (X : Set E) (hne : X.Nonempty) (w : E) :
    ((0 : ℝ) • w, (0 : ℝ)) ∈ perspectiveSet X := by
  obtain ⟨x0, hx0⟩ := hne
  apply subset_closure
  refine ⟨le_rfl, ?_⟩
  show (0 : ℝ) • w ∈ (0 : ℝ) • X
  rw [show (0 : ℝ) • w = (0 : ℝ) • x0 by simp]
  exact Set.smul_mem_smul_set hx0

theorem sgm_persp_one {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (X : Set E) (w : E) (hw : w ∈ X) :
    ((1 : ℝ) • w, (1 : ℝ)) ∈ perspectiveSet X := by
  apply subset_closure
  exact ⟨zero_le_one, Set.smul_mem_smul_set hw⟩

theorem sgm_pe_facts {V : Type*} {n : ℕ} [DecidableEq V] (G : GCS V n) (p : List V)
    (hp : IsPath G p) :
    (pathEdges p).Nodup ∧ (∀ e ∈ pathEdges p, e ∈ G.E) ∧
      (∀ e ∈ pathEdges p, e.1 ∈ p ∧ e.2 ∈ p) := by
  obtain ⟨hE, hPE, hp0, hpl, hinj⟩ := sgm_path_facts G p hp
  obtain ⟨_, _, hnd, _⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · apply List.Nodup.of_map Prod.snd
    rw [pathEdges, List.map_snd_zip (by simp)]
    exact hnd.sublist (List.tail_sublist p)
  · intro e he
    obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e he
    exact hE k hk
  · intro e he
    obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e he
    exact ⟨List.getElem_mem _, List.getElem_mem _⟩

theorem sgm_len2 {V : Type*} {n : ℕ} [DecidableEq V] (G : GCS V n) (hne : G.s ≠ G.t)
    (p : List V) (hp : IsPath G p) : 2 ≤ p.length := by
  obtain ⟨hE, hPE, hp0, hpl, hinj⟩ := sgm_path_facts G p hp
  obtain ⟨hhead, _, _, _⟩ := hp
  have hlen : 0 < p.length := by
    rcases p with _ | ⟨a, r⟩
    · simp at hhead
    · simp
  by_contra hlt
  have h0 := hp0 hlen
  have h1 := hpl hlen
  have e : p.length - 1 = 0 := by omega
  have h2 : p[p.length - 1]'(by omega) = p[0]'hlen := by
    congr 1
  exact hne (h0.symm.trans (h2 ▸ h1))

theorem sgm_dirA_core {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (hG : IsGCS G) (p : List V) (hp : IsPath G p) (x : V → Fin n → ℝ)
    (hx : ∀ v ∈ p, x v ∈ G.X v) :
    micpValue G ≤ pathCost G p x := by
  obtain ⟨hE, hPE, hp0, hpl, hinj⟩ := sgm_path_facts G p hp
  obtain ⟨hnodupE, hsubE, hends⟩ := sgm_pe_facts G p hp
  have hlen2 := sgm_len2 G hG.s_ne_t p hp
  have hlen : 0 < p.length := by omega
  have hpl' : ∀ i (hi : i < p.length), i + 1 = p.length → p[i] = G.t := by
    intro i hi h
    have : i = p.length - 1 := by omega
    subst this
    exact hpl hlen
  let y : V × V → ℝ := fun e => if e ∈ pathEdges p then 1 else 0
  have hy1 : ∀ e ∈ pathEdges p, y e = 1 := fun e he => if_pos he
  have hy0 : ∀ e, e ∉ pathEdges p → y e = 0 := fun e he => if_neg he
  have hybin : ∀ e, y e = 0 ∨ y e = 1 := by
    intro e
    by_cases h : e ∈ pathEdges p
    · exact Or.inr (hy1 e h)
    · exact Or.inl (hy0 e h)
  have hout0 : ∀ v, v ∉ p → ∑ e ∈ outEdges G v, y e = 0 := by
    intro v hv
    apply Finset.sum_eq_zero
    intro e he
    simp only [outEdges, Finset.mem_filter] at he
    apply hy0
    intro hmem
    apply hv
    rw [← he.2]
    exact (hends e hmem).1
  have hin0 : ∀ v, v ∉ p → ∑ e ∈ inEdges G v, y e = 0 := by
    intro v hv
    apply Finset.sum_eq_zero
    intro e he
    simp only [inEdges, Finset.mem_filter] at he
    apply hy0
    intro hmem
    apply hv
    rw [← he.2]
    exact (hends e hmem).2
  have hout1 : ∀ j (hj : j + 1 < p.length),
      ∑ e ∈ outEdges G (p[j]'(by omega)), y e = 1 := by
    intro j hj
    have he0 : (p[j]'(by omega), p[j + 1]) ∈ outEdges G (p[j]'(by omega)) := by
      unfold outEdges; exact Finset.mem_filter.mpr ⟨hE j hj, rfl⟩
    rw [Finset.sum_eq_single_of_mem _ he0]
    · exact hy1 _ (hPE j hj)
    · intro e he hne
      simp only [outEdges, Finset.mem_filter] at he
      apply hy0
      intro hmem
      obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e hmem
      apply hne
      have : k = j := hinj k j (by omega) (by omega) he.2
      subst this
      rfl
  have hin1 : ∀ i (hi : i + 1 < p.length),
      ∑ e ∈ inEdges G (p[i + 1]'hi), y e = 1 := by
    intro i hi
    have he0 : (p[i]'(by omega), p[i + 1]'hi) ∈ inEdges G (p[i + 1]'hi) := by
      unfold inEdges; exact Finset.mem_filter.mpr ⟨hE i hi, rfl⟩
    rw [Finset.sum_eq_single_of_mem _ he0]
    · exact hy1 _ (hPE i hi)
    · intro e he hne
      simp only [inEdges, Finset.mem_filter] at he
      apply hy0
      intro hmem
      obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e hmem
      apply hne
      have : k + 1 = i + 1 := hinj (k + 1) (i + 1) (by omega) (by omega) he.2
      have hki : k = i := by omega
      subst hki
      rfl
  have hcons_y : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ inEdges G v, y e = ∑ e ∈ outEdges G v, y e := by
    intro v hs ht
    by_cases hv : v ∈ p
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hs (hp0 hlen)
      have hjl : j + 1 < p.length := by
        by_contra h
        exact ht (hpl' j hj (by omega))
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [hin1 i hj, hout1 (i + 1) hjl]
    · rw [hin0 v hv, hout0 v hv]
  let z : V × V → Fin n → ℝ := fun e => y e • x e.1
  let z' : V × V → Fin n → ℝ := fun e => y e • x e.2
  have hfeas : IsMICPFeasible G y z z' := by
    refine ⟨?_, ?_, ?_, ?_, hcons_y, ?_, ?_⟩
    · have h := hout1 0 (by omega)
      rwa [hp0 hlen] at h
    · have h := hin1 (p.length - 2) (by omega)
      rwa [hpl' (p.length - 2 + 1) (by omega) (by omega)] at h
    · intro v hs ht
      by_cases hv : v ∈ p
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
        have hjl : j + 1 < p.length := by
          by_contra h
          exact ht (hpl' j hj (by omega))
        rw [hout1 j hjl]
      · rw [hout0 v hv]; norm_num
    · intro v hs ht
      have h1 : ∑ e ∈ inEdges G v, z' e = (∑ e ∈ inEdges G v, y e) • x v := by
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro e he
        simp only [inEdges, Finset.mem_filter] at he
        show y e • x e.2 = y e • x v
        rw [he.2]
      have h2 : ∑ e ∈ outEdges G v, z e = (∑ e ∈ outEdges G v, y e) • x v := by
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro e he
        simp only [outEdges, Finset.mem_filter] at he
        show y e • x e.1 = y e • x v
        rw [he.2]
      rw [h1, h2, hcons_y v hs ht]
    · intro e he
      by_cases hm : e ∈ pathEdges p
      · have hye : y e = 1 := hy1 e hm
        refine ⟨?_, ?_⟩
        · show (y e • x e.1, y e) ∈ perspectiveSet (G.X e.1)
          rw [hye]; exact sgm_persp_one _ _ (hx _ (hends e hm).1)
        · show (y e • x e.2, y e) ∈ perspectiveSet (G.X e.2)
          rw [hye]; exact sgm_persp_one _ _ (hx _ (hends e hm).2)
      · have hye : y e = 0 := hy0 e hm
        refine ⟨?_, ?_⟩
        · show (y e • x e.1, y e) ∈ perspectiveSet (G.X e.1)
          rw [hye]; exact sgm_persp_zero _ (hG.X_nonempty _) _
        · show (y e • x e.2, y e) ∈ perspectiveSet (G.X e.2)
          rw [hye]; exact sgm_persp_zero _ (hG.X_nonempty _) _
    · intro e he
      exact hybin e
  have hterm : ∀ e ∈ G.E, perspectiveFun (G.ℓ e) (z e, z' e) (y e) =
      if e ∈ (pathEdges p).toFinset then G.ℓ e (x e.1, x e.2) else 0 := by
    intro e he
    by_cases hm : e ∈ pathEdges p
    · rw [if_pos (List.mem_toFinset.mpr hm)]
      have hye : y e = 1 := hy1 e hm
      show perspectiveFun (G.ℓ e) (y e • x e.1, y e • x e.2) (y e) = _
      rw [hye]
      simp only [one_smul]
      rw [sgm_part1 (G.ℓ e) (hG.ℓ_pcc e he).2.1 _ 1 one_pos]
      simp
    · rw [if_neg (fun h => hm (List.mem_toFinset.mp h))]
      have hye : y e = 0 := hy0 e hm
      show perspectiveFun (G.ℓ e) (y e • x e.1, y e • x e.2) (y e) = _
      rw [hye]
      simp only [zero_smul, Prod.mk_zero_zero]
      exact sgm_part3 (G.ℓ e) (hG.ℓ_pcc e he)
  have hcost : micpCost G y z z' = pathCost G p x := by
    unfold micpCost pathCost
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr (fun e he => hsubE e (List.mem_toFinset.mp he)),
      List.sum_toFinset _ hnodupE]
  rw [← hcost]
  exact iInf_le_of_le y (iInf_le_of_le z (iInf_le_of_le z' (iInf_le_of_le hfeas le_rfl)))

theorem sgm_dirA {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n) (hG : IsGCS G) :
    micpValue G ≤ sppValue G := by
  unfold sppValue
  refine le_iInf fun p => le_iInf fun hp => le_iInf fun x => le_iInf fun hx => ?_
  exact sgm_dirA_core G hG p hp x hx

theorem sgm_dirB_core {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (hG : IsGCS G) (hst : NoInSNoOutT G) (y : V × V → ℝ) (z z' : V × V → Fin n → ℝ)
    (hf : IsMICPFeasible G y z z') : sppValue G ≤ micpCost G y z z' := by
  obtain ⟨p, hpath, hy1, -, -⟩ := sgm_path_cycles G hst hG.s_ne_t y hf.binary hf.source
    hf.target hf.degree hf.conserve_y
  obtain ⟨hE, hPE, hp0, hpl, hinj⟩ := sgm_path_facts G p hpath
  obtain ⟨hnodupE, hsubE, hends⟩ := sgm_pe_facts G p hpath
  have hlen2 := sgm_len2 G hG.s_ne_t p hpath
  have hnd : p.Nodup := by
    obtain ⟨_, _, hnd, _⟩ := hpath
    exact hnd
  have hflow := sgm_flow G hG y z z' hf p hpath hy1
  have hone : ∀ e ∈ G.E, y e = 1 → z e ∈ G.X e.1 ∧ z' e ∈ G.X e.2 := by
    intro e he hy
    obtain ⟨h1, h2⟩ := hf.persp e he
    exact ⟨(sgm_zero_of_persp G hG e.1 _ _ h1).2 hy, (sgm_zero_of_persp G hG e.2 _ _ h2).2 hy⟩
  have hzero : ∀ e ∈ G.E, y e = 0 → z e = 0 ∧ z' e = 0 := by
    intro e he hy
    obtain ⟨h1, h2⟩ := hf.persp e he
    exact ⟨(sgm_zero_of_persp G hG e.1 _ _ h1).1 hy, (sgm_zero_of_persp G hG e.2 _ _ h2).1 hy⟩
  have hterm1 : ∀ e ∈ G.E, y e = 1 →
      perspectiveFun (G.ℓ e) (z e, z' e) (y e) = G.ℓ e (z e, z' e) := by
    intro e he hy
    rw [hy, sgm_part1 (G.ℓ e) (hG.ℓ_pcc e he).2.1 _ 1 one_pos]
    simp
  have hnn : ∀ e ∈ G.E, 0 ≤ perspectiveFun (G.ℓ e) (z e, z' e) (y e) := by
    intro e he
    rcases hf.binary e he with hy | hy
    · obtain ⟨h1, h2⟩ := hzero e he hy
      rw [hy, h1, h2]
      simp only [Prod.mk_zero_zero]
      rw [sgm_part3 (G.ℓ e) (hG.ℓ_pcc e he)]
    · rw [hterm1 e he hy]
      exact hG.ℓ_nonneg e he _
  let a : ℕ → Fin n → ℝ := fun i =>
    if i + 1 < p.length then z (p.getD i G.s, p.getD (i + 1) G.s)
    else z' (p.getD (i - 1) G.s, p.getD i G.s)
  let x : V → Fin n → ℝ := fun v => if v ∈ p then a (p.idxOf v) else 0
  have hxa : ∀ i (hi : i < p.length), x (p[i]) = a i := by
    intro i hi
    have hm : p[i] ∈ p := List.getElem_mem hi
    show (if p[i] ∈ p then a (p.idxOf p[i]) else 0) = a i
    rw [if_pos hm, hnd.idxOf_getElem i hi]
  have hxe : ∀ k (hk : k + 1 < p.length),
      x (p[k]'(by omega)) = z (p[k]'(by omega), p[k + 1]) ∧
        x (p[k + 1]) = z' (p[k]'(by omega), p[k + 1]) := by
    intro k hk
    constructor
    · rw [hxa k (by omega)]
      show (if k + 1 < p.length then _ else _) = _
      rw [if_pos hk, List.getD_eq_getElem (hn := by omega), List.getD_eq_getElem (hn := hk)]
    · rw [hxa (k + 1) hk]
      show (if k + 1 + 1 < p.length then _ else _) = _
      by_cases hk2 : k + 2 < p.length
      · rw [if_pos (by omega), List.getD_eq_getElem (hn := hk), List.getD_eq_getElem (hn := hk2)]
        exact (hflow k hk2).symm
      · rw [if_neg (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [List.getD_eq_getElem (hn := by omega), List.getD_eq_getElem (hn := hk)]
  have hxmem : ∀ v ∈ p, x v ∈ G.X v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    by_cases hi1 : i + 1 < p.length
    · rw [(hxe i hi1).1]
      exact (hone _ (hE i hi1) (hy1 _ (hPE i hi1))).1
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j + 1 < p.length := hi
      rw [(hxe j hj).2]
      exact (hone _ (hE j hj) (hy1 _ (hPE j hj))).2
  calc sppValue G ≤ pathCost G p x :=
        iInf_le_of_le p (iInf_le_of_le hpath (iInf_le_of_le x (iInf_le_of_le hxmem le_rfl)))
    _ ≤ micpCost G y z z' := by
        unfold pathCost micpCost
        rw [← List.sum_toFinset _ hnodupE]
        calc ∑ e ∈ (pathEdges p).toFinset, G.ℓ e (x e.1, x e.2)
            = ∑ e ∈ (pathEdges p).toFinset, perspectiveFun (G.ℓ e) (z e, z' e) (y e) := by
              apply Finset.sum_congr rfl
              intro e he
              have he' : e ∈ pathEdges p := List.mem_toFinset.mp he
              rw [hterm1 e (hsubE e he') (hy1 e he')]
              obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e he'
              show G.ℓ _ (x (p[k]), x (p[k + 1])) = _
              rw [(hxe k hk).1, (hxe k hk).2]
          _ ≤ ∑ e ∈ G.E, perspectiveFun (G.ℓ e) (z e, z' e) (y e) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun e he => hsubE e (List.mem_toFinset.mp he)) (fun e he _ => hnn e he)

theorem sgm_dirB {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n) (hG : IsGCS G)
    (hst : NoInSNoOutT G) : sppValue G ≤ micpValue G := by
  unfold micpValue
  refine le_iInf fun y => le_iInf fun z => le_iInf fun z' => le_iInf fun hf => ?_
  exact sgm_dirB_core G hG hst y z z' hf

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n) (hG : IsGCS G)
    (hst : NoInSNoOutT G) :
    micpValue G = sppValue G :=
  le_antisymm (sgm_dirA G hG) (sgm_dirB G hG hst)
