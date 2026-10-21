-- Prove2me | solution 1 for ShortestGCS.MICP.remark_4_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:23:39.951224+00:00
-- url     : https://prove2.me/submissions/73fc4b59-3fde-47f6-be76-e04a0cb113d9

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun

set_option autoImplicit false
open Pointwise ShortestGCS.MICP

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

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) :
    (IsClosed (epigraph f) →
        ∀ x : E, ∀ lam : ℝ, 0 < lam → perspectiveFun f x lam = (lam : EReal) * f (lam⁻¹ • x)) ∧
      (∀ x : E, ∀ lam : ℝ, lam < 0 → perspectiveFun f x lam = ⊤) ∧
      (IsProperClosedConvex f → perspectiveFun f 0 0 = 0) :=
  ⟨fun h x l hl => sgm_part1 f h x l hl, fun x l hl => sgm_part2 f x l hl, sgm_part3 f⟩
