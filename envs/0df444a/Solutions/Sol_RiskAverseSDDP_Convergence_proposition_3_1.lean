-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:25:22.632817+00:00
-- url     : https://prove2.me/submissions/d8fbab3b-f55e-436f-9802-2e1d8a3fcadb

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model

open RiskAverseSDDP.Convergence
open scoped Topology

section Helpers

/-! ### `Hist.snoc` properties -/

private lemma snoc_continuous {n s : ℕ} :
    Continuous (fun p : Hist n s × EuclideanSpace ℝ (Fin n) => p.1.snoc p.2) := by
  unfold Hist.snoc
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (s + 1) => EuclideanSpace ℝ (Fin n))).comp ?_
  refine continuous_pi fun k => ?_
  refine Fin.lastCases ?_ ?_ k
  · simpa only [Fin.snoc_last] using continuous_snd
  · intro i
    have hcoord : Continuous (fun x : Hist n s => x i) :=
      (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
    simpa only [Fin.snoc_castSucc, Function.comp_def] using hcoord.comp continuous_fst

private lemma snoc_comb {n s : ℕ} (a b : ℝ) (x₁ x₂ : Hist n s)
    (y₁ y₂ : EuclideanSpace ℝ (Fin n)) :
    (a • x₁ + b • x₂).snoc (a • y₁ + b • y₂) = a • (x₁.snoc y₁) + b • (x₂.snoc y₂) := by
  apply PiLp.ext
  intro k
  refine Fin.lastCases ?_ ?_ k
  · simp [Hist.snoc]
  · intro i
    simp [Hist.snoc]

private lemma dist_snoc_snoc {n s : ℕ} (x₁ x₂ : Hist n s) (y : EuclideanSpace ℝ (Fin n)) :
    dist (x₁.snoc y) (x₂.snoc y) = dist x₁ x₂ := by
  rw [dist_eq_norm, dist_eq_norm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [Hist.snoc]

private lemma edist_snoc_snoc {n s : ℕ} (x₁ x₂ : Hist n s) (y : EuclideanSpace ℝ (Fin n)) :
    edist (x₁.snoc y) (x₂.snoc y) = edist x₁ x₂ := by
  rw [edist_dist, edist_dist, dist_snoc_snoc]

private lemma snoc_mem_prodSet {T n M q p : ℕ} (D : Model T n M q p) {s : ℕ}
    {x : Hist n s} {y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ D.prodSet s) (hy : y ∈ D.Xc (s + 1)) :
    x.snoc y ∈ D.prodSet (s + 1) := by
  intro k
  refine Fin.lastCases ?_ ?_ k
  · simpa [Hist.snoc] using hy
  · intro i
    simpa [Hist.snoc] using hx i

private lemma snoc_mem_cthickening_prodSet {T n M q p : ℕ} (D : Model T n M q p) {s : ℕ}
    {ε : ℝ} {x : Hist n s} {y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.cthickening ε (D.prodSet s)) (hy : y ∈ D.Xc (s + 1)) :
    x.snoc y ∈ Metric.cthickening ε (D.prodSet (s + 1)) := by
  rw [Metric.mem_cthickening_iff] at hx ⊢
  refine le_trans ?_ hx
  rw [Metric.le_infEDist]
  intro x₀ hx₀
  calc Metric.infEDist (x.snoc y) (D.prodSet (s + 1))
      ≤ edist (x.snoc y) (x₀.snoc y) :=
        Metric.infEDist_le_edist_of_mem (snoc_mem_prodSet D hx₀ hy)
    _ = edist x x₀ := edist_snoc_snoc x x₀ y

private lemma convex_prodSet {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) {ε : ℝ}
    (hH2 : D.H2 ε) {h : ℕ} (hh : h ≤ T) : Convex ℝ (D.prodSet h) := by
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab i
  have hXc : Convex ℝ (D.Xc (i.val + 1)) := (hH2.2 i.val (lt_of_lt_of_le i.isLt hh)).1.2.1
  exact hXc (hx₁ i) (hx₂ i) ha hb hab

private lemma convex_thickening_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (δ : ℝ) : Convex ℝ (Metric.thickening δ S) := by
  by_cases hδ : 0 < δ
  · intro x₁ hx₁ x₂ hx₂ a b ha hb hab
    rw [Metric.mem_thickening_iff] at hx₁ hx₂ ⊢
    rcases hx₁ with ⟨s₁, hs₁, hd₁⟩
    rcases hx₂ with ⟨s₂, hs₂, hd₂⟩
    refine ⟨a • s₁ + b • s₂, hS hs₁ hs₂ ha hb hab, ?_⟩
    rw [dist_eq_norm] at hd₁ hd₂ ⊢
    have hsub : (a • x₁ + b • x₂) - (a • s₁ + b • s₂) =
        a • (x₁ - s₁) + b • (x₂ - s₂) := by
      simp [smul_sub, add_sub_add_comm]
    rw [hsub]
    have htri : ‖a • (x₁ - s₁) + b • (x₂ - s₂)‖ ≤ a * ‖x₁ - s₁‖ + b * ‖x₂ - s₂‖ := by
      calc ‖a • (x₁ - s₁) + b • (x₂ - s₂)‖
          ≤ ‖a • (x₁ - s₁)‖ + ‖b • (x₂ - s₂)‖ := norm_add_le _ _
        _ = a * ‖x₁ - s₁‖ + b * ‖x₂ - s₂‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; nlinarith
    · nlinarith
  · rw [Metric.thickening_of_nonpos (not_lt.mp hδ)]
    exact convex_empty

/-! ### `EReal` algebraic, convexity, and lower semicontinuity lemmas -/

private lemma ereal_add_ne_bot {u v : EReal} (hu : u ≠ ⊥) (hv : v ≠ ⊥) : u + v ≠ ⊥ := by
  induction u using EReal.rec with
  | bot => exact absurd rfl hu
  | top =>
    rw [EReal.top_add_of_ne_bot hv]
    exact top_ne_bot
  | coe r₁ =>
    induction v using EReal.rec with
    | bot => exact absurd rfl hv
    | top =>
      rw [EReal.coe_add_top]
      exact top_ne_bot
    | coe r₂ =>
      rw [← EReal.coe_add]
      exact EReal.coe_ne_bot _

private lemma ereal_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, ((f i : ℝ) : EReal)) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

private lemma ereal_mul_nonneg_ne_bot {c : ℝ} (hc : 0 ≤ c) {u : EReal} (hu : u ≠ ⊥) :
    (c : EReal) * u ≠ ⊥ := by
  rcases eq_or_lt_of_le hc with rfl | hc'
  · simp
  · induction u using EReal.rec with
    | bot => exact absurd rfl hu
    | top =>
      rw [EReal.coe_mul_top_of_pos hc']
      exact top_ne_bot
    | coe r =>
      rw [← EReal.coe_mul]
      exact EReal.coe_ne_bot _

private lemma ereal_sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ereal_add_ne_bot (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma ereal_le_coe_of_forall_pos {u : EReal} {c : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → u ≤ ((c + δ : ℝ) : EReal)) : u ≤ (c : EReal) := by
  induction u using EReal.rec with
  | bot => exact bot_le
  | top =>
    have h1 := h 1 one_pos
    exact absurd h1 (not_le.mpr (EReal.coe_lt_top _))
  | coe r =>
    rw [EReal.coe_le_coe_iff]
    exact le_of_forall_pos_le_add fun δ hδ => EReal.coe_le_coe_iff.mp (h δ hδ)

private lemma econvex_zero {Z : Type*} [AddCommGroup Z] [Module ℝ Z] :
    EConvex (fun _ : Z => (0 : EReal)) := by
  intro q₁ hq₁ q₂ hq₂ a b ha hb hab
  change (0 : EReal) ≤ (((a • q₁ + b • q₂).2 : ℝ) : EReal)
  have h1 : (0 : ℝ) ≤ q₁.2 := by simpa using hq₁
  have h2 : (0 : ℝ) ≤ q₂.2 := by simpa using hq₂
  have h3 : (0 : ℝ) ≤ a * q₁.2 + b * q₂.2 := by nlinarith
  simpa [smul_eq_mul] using (EReal.coe_le_coe_iff.mpr h3)

private lemma econvex_add {Z : Type*} [AddCommGroup Z] [Module ℝ Z] {f g : Z → EReal}
    (hf : EConvex f) (hg : EConvex g)
    (hf_nbot : ∀ z, f z ≠ ⊥) (hg_nbot : ∀ z, g z ≠ ⊥) :
    EConvex (fun z => f z + g z) := by
  intro q₁ hq₁ q₂ hq₂ a b ha hb hab
  change f (a • q₁.1 + b • q₂.1) + g (a • q₁.1 + b • q₂.1) ≤
    (((a * q₁.2 + b * q₂.2 : ℝ) : EReal))
  have hfinite : ∀ q : Z × ℝ, f q.1 + g q.1 ≤ (q.2 : EReal) →
      f q.1 ≠ ⊤ ∧ g q.1 ≠ ⊤ ∧ (f q.1).toReal + (g q.1).toReal ≤ q.2 := by
    intro q hq
    have hft : f q.1 ≠ ⊤ := by
      intro htop
      rw [htop, EReal.top_add_of_ne_bot (hg_nbot q.1)] at hq
      exact not_le.mpr (EReal.coe_lt_top q.2) hq
    have hgt : g q.1 ≠ ⊤ := by
      intro htop
      rw [htop, EReal.add_top_of_ne_bot (hf_nbot q.1)] at hq
      exact not_le.mpr (EReal.coe_lt_top q.2) hq
    refine ⟨hft, hgt, ?_⟩
    have hf_eq : ((f q.1).toReal : EReal) = f q.1 := EReal.coe_toReal hft (hf_nbot q.1)
    have hg_eq : ((g q.1).toReal : EReal) = g q.1 := EReal.coe_toReal hgt (hg_nbot q.1)
    rw [← hf_eq, ← hg_eq, ← EReal.coe_add, EReal.coe_le_coe_iff] at hq
    exact hq
  obtain ⟨hf1t, hg1t, hsum1⟩ := hfinite q₁ hq₁
  obtain ⟨hf2t, hg2t, hsum2⟩ := hfinite q₂ hq₂
  have hf1_mem : (q₁.1, (f q₁.1).toReal) ∈ {q : Z × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    simp [EReal.coe_toReal hf1t (hf_nbot q₁.1)]
  have hf2_mem : (q₂.1, (f q₂.1).toReal) ∈ {q : Z × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    simp [EReal.coe_toReal hf2t (hf_nbot q₂.1)]
  have hg1_mem : (q₁.1, (g q₁.1).toReal) ∈ {q : Z × ℝ | g q.1 ≤ (q.2 : EReal)} := by
    simp [EReal.coe_toReal hg1t (hg_nbot q₁.1)]
  have hg2_mem : (q₂.1, (g q₂.1).toReal) ∈ {q : Z × ℝ | g q.1 ≤ (q.2 : EReal)} := by
    simp [EReal.coe_toReal hg2t (hg_nbot q₂.1)]
  have hf_comb : f (a • q₁.1 + b • q₂.1) ≤ ((a * (f q₁.1).toReal + b * (f q₂.1).toReal : ℝ) : EReal) :=
    hf hf1_mem hf2_mem ha hb hab
  have hg_comb : g (a • q₁.1 + b • q₂.1) ≤ ((a * (g q₁.1).toReal + b * (g q₂.1).toReal : ℝ) : EReal) :=
    hg hg1_mem hg2_mem ha hb hab
  calc f (a • q₁.1 + b • q₂.1) + g (a • q₁.1 + b • q₂.1)
      ≤ ((a * (f q₁.1).toReal + b * (f q₂.1).toReal : ℝ) : EReal) +
        ((a * (g q₁.1).toReal + b * (g q₂.1).toReal : ℝ) : EReal) :=
          add_le_add hf_comb hg_comb
    _ = (((a * (f q₁.1).toReal + b * (f q₂.1).toReal) +
          (a * (g q₁.1).toReal + b * (g q₂.1).toReal) : ℝ) : EReal) := by
          rw [← EReal.coe_add]
    _ ≤ ((a * q₁.2 + b * q₂.2 : ℝ) : EReal) := by
          rw [EReal.coe_le_coe_iff]
          nlinarith

private lemma econvex_const_mul {Z : Type*} [AddCommGroup Z] [Module ℝ Z] {f : Z → EReal}
    {c : ℝ} (hc : 0 ≤ c) (hf : EConvex f) : EConvex (fun z => (c : EReal) * f z) := by
  rcases eq_or_lt_of_le hc with rfl | hc'
  · simpa using econvex_zero (Z := Z)
  · have hiff : ∀ (u : EReal) (r : ℝ), (c : EReal) * u ≤ (r : EReal) ↔ u ≤ ((r / c : ℝ) : EReal) := by
      intro u r
      induction u using EReal.rec with
      | bot =>
        rw [EReal.coe_mul_bot_of_pos hc']
        simp
      | top =>
        rw [EReal.coe_mul_top_of_pos hc']
        simp
      | coe x =>
        rw [← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, le_div_iff₀' hc']
    intro q₁ hq₁ q₂ hq₂ a b ha hb hab
    change (c : EReal) * f (a • q₁.1 + b • q₂.1) ≤ ((a * q₁.2 + b * q₂.2 : ℝ) : EReal)
    rw [hiff]
    have h1 : (q₁.1, q₁.2 / c) ∈ {q : Z × ℝ | f q.1 ≤ (q.2 : EReal)} := (hiff _ _).mp hq₁
    have h2 : (q₂.1, q₂.2 / c) ∈ {q : Z × ℝ | f q.1 ≤ (q.2 : EReal)} := (hiff _ _).mp hq₂
    have hcomb := hf h1 h2 ha hb hab
    have hrw : a * (q₁.2 / c) + b * (q₂.2 / c) = (a * q₁.2 + b * q₂.2) / c := by ring
    simpa [smul_eq_mul, hrw] using hcomb

private lemma econvex_sum {Z ι : Type*} [AddCommGroup Z] [Module ℝ Z]
    (s : Finset ι) (F : ι → Z → EReal)
    (hconv : ∀ i ∈ s, EConvex (F i)) (hnbot : ∀ i ∈ s, ∀ z, F i z ≠ ⊥) :
    EConvex (fun z => ∑ i ∈ s, F i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using econvex_zero (Z := Z)
  | insert a s ha ih =>
    have heq : (fun z => ∑ i ∈ insert a s, F i z) = fun z => F a z + ∑ i ∈ s, F i z := by
      ext z; exact Finset.sum_insert ha
    rw [heq]
    exact econvex_add
      (hconv a (Finset.mem_insert_self a s))
      (ih (fun i hi => hconv i (Finset.mem_insert_of_mem hi))
          (fun i hi => hnbot i (Finset.mem_insert_of_mem hi)))
      (hnbot a (Finset.mem_insert_self a s))
      (fun z => ereal_sum_ne_bot s (fun i => F i z) fun i hi => hnbot i (Finset.mem_insert_of_mem hi) z)

private lemma econvex_biSup {Z ι : Type*} [AddCommGroup Z] [Module ℝ Z]
    (S : Set ι) (F : ι → Z → EReal) (hconv : ∀ i ∈ S, EConvex (F i)) :
    EConvex (fun z => ⨆ i ∈ S, F i z) := by
  unfold EConvex
  have heq : {q : Z × ℝ | (⨆ i ∈ S, F i q.1) ≤ (q.2 : EReal)} =
      ⋂ i ∈ S, {q : Z × ℝ | F i q.1 ≤ (q.2 : EReal)} := by
    ext q
    simp [iSup_le_iff]
  rw [heq]
  exact convex_iInter fun i => convex_iInter fun hi => hconv i hi

private lemma econvex_toReal_convexOn {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    {f : Z → EReal} {U : Set Z} (hf : EConvex f) (hU : Convex ℝ U)
    (hfin : ∀ x ∈ U, f x ≠ ⊥ ∧ f x ≠ ⊤) :
    ConvexOn ℝ U (fun x => (f x).toReal) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ U := hU hx hy ha hb hab
  have hx_mem : (x, (f x).toReal) ∈ {q : Z × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    simp [EReal.coe_toReal (hfin x hx).2 (hfin x hx).1]
  have hy_mem : (y, (f y).toReal) ∈ {q : Z × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    simp [EReal.coe_toReal (hfin y hy).2 (hfin y hy).1]
  have hcomb : f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) :=
    hf hx_mem hy_mem ha hb hab
  rw [← EReal.coe_toReal (hfin _ hxy).2 (hfin _ hxy).1, EReal.coe_le_coe_iff] at hcomb
  simpa [smul_eq_mul] using hcomb

private lemma lsc_add_ereal {X : Type*} [TopologicalSpace X] {f g : X → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hf_nbot : ∀ x, f x ≠ ⊥) (hg_nbot : ∀ x, g x ≠ ⊥) :
    LowerSemicontinuous (fun x => f x + g x) := by
  intro x₀ a ha
  dsimp only at ha
  have h_exists : ∃ u v : EReal, u < f x₀ ∧ v < g x₀ ∧ a < u + v := by
    have hf0 := hf_nbot x₀
    have hg0 := hg_nbot x₀
    induction hfx : f x₀ using EReal.rec with
    | bot => exact absurd hfx hf0
    | top =>
      induction hgx : g x₀ using EReal.rec with
      | bot => exact absurd hgx hg0
      | top =>
        rw [hfx, hgx] at ha
        obtain ⟨c, hc⟩ : ∃ c : ℝ, a < (c : EReal) := by
          induction a using EReal.rec with
          | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
          | top => exact absurd ha (lt_irrefl _)
          | coe r => exact ⟨r + 1, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
        exact ⟨(c : EReal), (0 : EReal), EReal.coe_lt_top c, EReal.coe_lt_top 0, by simpa using hc⟩
      | coe r₂ =>
        rw [hfx, hgx, EReal.top_add_coe] at ha
        obtain ⟨c, hc⟩ : ∃ c : ℝ, a < (c : EReal) := by
          induction a using EReal.rec with
          | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
          | top => exact absurd ha (lt_irrefl _)
          | coe r => exact ⟨r + 1, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
        refine ⟨((c - r₂ + 1 : ℝ) : EReal), ((r₂ - 1 : ℝ) : EReal),
          EReal.coe_lt_top _, EReal.coe_lt_coe_iff.mpr (by linarith), ?_⟩
        rw [← EReal.coe_add]
        have hEq : (c - r₂ + 1) + (r₂ - 1) = c := by ring
        rwa [hEq]
    | coe r₁ =>
      induction hgx : g x₀ using EReal.rec with
      | bot => exact absurd hgx hg0
      | top =>
        rw [hfx, hgx, EReal.coe_add_top] at ha
        obtain ⟨c, hc⟩ : ∃ c : ℝ, a < (c : EReal) := by
          induction a using EReal.rec with
          | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
          | top => exact absurd ha (lt_irrefl _)
          | coe r => exact ⟨r + 1, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
        refine ⟨((r₁ - 1 : ℝ) : EReal), ((c - r₁ + 1 : ℝ) : EReal),
          EReal.coe_lt_coe_iff.mpr (by linarith), EReal.coe_lt_top _, ?_⟩
        rw [← EReal.coe_add]
        have hEq : (r₁ - 1) + (c - r₁ + 1) = c := by ring
        rwa [hEq]
      | coe r₂ =>
        rw [hfx, hgx, ← EReal.coe_add] at ha
        obtain ⟨c, hac, hcr⟩ : ∃ c : ℝ, a < (c : EReal) ∧ c < r₁ + r₂ := by
          induction a using EReal.rec with
          | bot => exact ⟨r₁ + r₂ - 1, EReal.bot_lt_coe _, by linarith⟩
          | top => exact absurd ha (not_lt.mpr le_top)
          | coe r =>
            have hr : r < r₁ + r₂ := EReal.coe_lt_coe_iff.mp ha
            exact ⟨(r + (r₁ + r₂)) / 2, EReal.coe_lt_coe_iff.mpr (by linarith), by linarith⟩
        set δ := (r₁ + r₂ - c) / 2
        have hδ : 0 < δ := by dsimp [δ]; linarith
        refine ⟨((r₁ - δ : ℝ) : EReal), ((r₂ - δ : ℝ) : EReal),
          EReal.coe_lt_coe_iff.mpr (by linarith), EReal.coe_lt_coe_iff.mpr (by linarith), ?_⟩
        rw [← EReal.coe_add]
        have hEq : (r₁ - δ) + (r₂ - δ) = c := by dsimp [δ]; ring
        rwa [hEq]
  rcases h_exists with ⟨u, v, hu, hv, huv⟩
  filter_upwards [hf x₀ u hu, hg x₀ v hv] with x hfx hgx
  exact lt_of_lt_of_le huv (add_le_add hfx.le hgx.le)

private lemma lsc_const_mul_ereal {X : Type*} [TopologicalSpace X] {f : X → EReal}
    {c : ℝ} (hc : 0 ≤ c) (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun x => (c : EReal) * f x) := by
  rcases eq_or_lt_of_le hc with rfl | hc'
  · simpa using lowerSemicontinuous_const
  · intro x₀ a ha
    dsimp only at ha
    induction a using EReal.rec with
    | bot =>
      change ⊥ < (c : EReal) * f x₀ at ha
      have hfx0 : ⊥ < f x₀ := by
        rw [bot_lt_iff_ne_bot] at ha ⊢
        intro hbot
        rw [hbot, EReal.coe_mul_bot_of_pos hc'] at ha
        exact ha rfl
      filter_upwards [hf x₀ ⊥ hfx0] with x hx
      change ⊥ < f x at hx
      change ⊥ < (c : EReal) * f x
      rw [bot_lt_iff_ne_bot] at hx ⊢
      exact ereal_mul_nonneg_ne_bot hc hx
    | top => exact absurd ha (not_lt.mpr le_top)
    | coe r =>
      have hlt : ∀ u : EReal, (r : EReal) < (c : EReal) * u ↔ ((r / c : ℝ) : EReal) < u := by
        intro u
        induction u using EReal.rec with
        | bot =>
          rw [EReal.coe_mul_bot_of_pos hc']
          simp
        | top =>
          rw [EReal.coe_mul_top_of_pos hc']
          simp
        | coe y =>
          rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff, div_lt_iff₀' hc']
      filter_upwards [hf x₀ ((r / c : ℝ) : EReal) ((hlt _).mp ha)] with x hx
      exact (hlt _).mpr hx

private lemma lsc_sum_ereal {X ι : Type*} [TopologicalSpace X] (s : Finset ι)
    (F : ι → X → EReal)
    (hlsc : ∀ i ∈ s, LowerSemicontinuous (F i))
    (hnbot : ∀ i ∈ s, ∀ x, F i x ≠ ⊥) :
    LowerSemicontinuous (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lowerSemicontinuous_const
  | insert a s ha ih =>
    have heq : (fun x => ∑ i ∈ insert a s, F i x) = fun x => F a x + ∑ i ∈ s, F i x := by
      ext x; exact Finset.sum_insert ha
    rw [heq]
    exact lsc_add_ereal
      (hlsc a (Finset.mem_insert_self a s))
      (ih (fun i hi => hlsc i (Finset.mem_insert_of_mem hi))
          (fun i hi => hnbot i (Finset.mem_insert_of_mem hi)))
      (hnbot a (Finset.mem_insert_self a s))
      (fun x => ereal_sum_ne_bot s (fun i => F i x) fun i hi => hnbot i (Finset.mem_insert_of_mem hi) x)

/-! ### Stage value function and risk measure induction step -/

private lemma stageVal_step {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) {ε : ℝ}
    (hH2 : D.H2 ε) {h : ℕ} (hh : h < T) {j : Fin M} (hj : j ∈ Model.Rlz (M := M) (h + 1))
    {V : Hist n (h + 1) → EReal}
    (hV_conv : EConvex V) (hV_nbot : ∀ z, V z ≠ ⊥) (hV_lsc : LowerSemicontinuous V)
    (hV_ntop : ∀ z ∈ Metric.cthickening ε (D.prodSet (h + 1)), V z ≠ ⊤) :
    let Φ := D.stageVal h j V
    EConvex Φ ∧ (∀ x, Φ x ≠ ⊥) ∧ LowerSemicontinuous Φ ∧
      (∀ x ∈ Metric.cthickening ε (D.prodSet h), Φ x ≠ ⊤) := by
  intro Φ
  obtain ⟨⟨hXc_ne, hXc_conv, hXc_comp⟩, hf_all, hg_all, hf_dom, hfeas_ne, _⟩ := hH2.2 h hh
  obtain ⟨hf_prop, hf_conv, hf_lsc⟩ := hf_all j hj
  have hg_props := hg_all j hj
  let F : Hist n h × EuclideanSpace ℝ (Fin n) → EReal :=
    fun z => D.f (h + 1) j (z.1.snoc z.2) + V (z.1.snoc z.2)
  let Gr : Set (Hist n h × EuclideanSpace ℝ (Fin n)) := {z | z.2 ∈ D.feas h j z.1}
  have hF_nbot : ∀ z, F z ≠ ⊥ := fun z =>
    ereal_add_ne_bot (hf_prop.1 _) (hV_nbot _)
  have hF_conv : EConvex F := by
    have hcomp : ∀ (u : Hist n (h + 1) → EReal), EConvex u →
        EConvex (fun z : Hist n h × EuclideanSpace ℝ (Fin n) => u (z.1.snoc z.2)) := by
      intro u hu q₁ hq₁ q₂ hq₂ a b ha hb hab
      have h1 : (q₁.1.1.snoc q₁.1.2, q₁.2) ∈ {q : Hist n (h + 1) × ℝ | u q.1 ≤ (q.2 : EReal)} := hq₁
      have h2 : (q₂.1.1.snoc q₂.1.2, q₂.2) ∈ {q : Hist n (h + 1) × ℝ | u q.1 ≤ (q.2 : EReal)} := hq₂
      have hcomb := hu h1 h2 ha hb hab
      change u ((a • q₁.1.1 + b • q₂.1.1).snoc (a • q₁.1.2 + b • q₂.1.2)) ≤
        ((a * q₁.2 + b * q₂.2 : ℝ) : EReal)
      rw [snoc_comb]
      simpa [smul_eq_mul] using hcomb
    exact econvex_add (hcomp _ hf_conv) (hcomp _ hV_conv)
      (fun z => hf_prop.1 _) (fun z => hV_nbot _)
  have hF_lsc : LowerSemicontinuous F :=
    lsc_add_ereal (hf_lsc.comp snoc_continuous) (hV_lsc.comp snoc_continuous)
      (fun z => hf_prop.1 _) (fun z => hV_nbot _)
  have hGr_closed : IsClosed Gr := by
    have h1 : IsClosed {z : Hist n h × EuclideanSpace ℝ (Fin n) | z.2 ∈ D.Xc (h + 1)} :=
      hXc_comp.isClosed.preimage continuous_snd
    have h2 : IsClosed {z : Hist n h × EuclideanSpace ℝ (Fin n) |
        ∀ i, D.g (h + 1) j D.x0 (z.1.snoc z.2) i ≤ 0} := by
      have heq : {z : Hist n h × EuclideanSpace ℝ (Fin n) |
          ∀ i, D.g (h + 1) j D.x0 (z.1.snoc z.2) i ≤ 0} =
          ⋂ i, (fun z : Hist n h × EuclideanSpace ℝ (Fin n) =>
            D.g (h + 1) j D.x0 (z.1.snoc z.2) i) ⁻¹' Set.Iic 0 := by
        ext z; simp
      rw [heq]
      exact isClosed_iInter fun i => ((hg_props i).2.comp snoc_continuous).isClosed_preimage 0
    have h3 : IsClosed {z : Hist n h × EuclideanSpace ℝ (Fin n) |
        ∑ τ : Fin (h + 2), D.A (h + 1) j τ
          (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) D.x0
            (fun i => (z.1.snoc z.2) i) τ) = D.b (h + 1) j} := by
      have hcont : Continuous (fun z : Hist n h × EuclideanSpace ℝ (Fin n) =>
          ∑ τ : Fin (h + 2), D.A (h + 1) j τ
            (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) D.x0
              (fun i => (z.1.snoc z.2) i) τ)) := by
        have hrew : (fun z : Hist n h × EuclideanSpace ℝ (Fin n) =>
            ∑ τ : Fin (h + 2), D.A (h + 1) j τ
              (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) D.x0
                (fun i => (z.1.snoc z.2) i) τ)) =
            fun z => D.A (h + 1) j 0 D.x0 +
              ∑ i : Fin (h + 1), D.A (h + 1) j i.succ ((z.1.snoc z.2) i) := by
          ext z
          rw [Fin.sum_univ_succ]
          simp
        rw [hrew]
        refine continuous_const.add (continuous_finsetSum _ fun i _ => ?_)
        have hcoord : Continuous (fun z : Hist n (h + 1) => z i) :=
          (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
        exact (D.A (h + 1) j i.succ).continuous_of_finiteDimensional.comp
          (hcoord.comp snoc_continuous)
      exact isClosed_eq hcont continuous_const
    have hGr_eq : Gr = {z | z.2 ∈ D.Xc (h + 1)} ∩
        ({z | ∀ i, D.g (h + 1) j D.x0 (z.1.snoc z.2) i ≤ 0} ∩
          {z | ∑ τ : Fin (h + 2), D.A (h + 1) j τ
            (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) D.x0
              (fun i => (z.1.snoc z.2) i) τ) = D.b (h + 1) j}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Gr, Model.feas]
    rw [hGr_eq]
    exact h1.inter (h2.inter h3)
  have hGr_conv : Convex ℝ Gr := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    rcases hz₁ with ⟨hy₁, hg₁, hlin₁⟩
    rcases hz₂ with ⟨hy₂, hg₂, hlin₂⟩
    refine ⟨hXc_conv hy₁ hy₂ ha hb hab, ?_, ?_⟩
    · intro i
      have h1 : (z₁.1.snoc z₁.2, (0 : ℝ)) ∈
          {q : Hist n (h + 1) × ℝ | D.g (h + 1) j D.x0 q.1 i ≤ (q.2 : EReal)} := by
        simpa using hg₁ i
      have h2 : (z₂.1.snoc z₂.2, (0 : ℝ)) ∈
          {q : Hist n (h + 1) × ℝ | D.g (h + 1) j D.x0 q.1 i ≤ (q.2 : EReal)} := by
        simpa using hg₂ i
      have hcomb := (hg_props i).1 h1 h2 ha hb hab
      change D.g (h + 1) j D.x0 ((a • z₁.1 + b • z₂.1).snoc (a • z₁.2 + b • z₂.2)) i ≤ 0
      rw [snoc_comb]
      simpa [smul_eq_mul] using hcomb
    · rw [Fin.sum_univ_succ] at hlin₁ hlin₂ ⊢
      simp only [Fin.cons_zero, Fin.cons_succ] at hlin₁ hlin₂ ⊢
      have hsnoc : (a • z₁.1 + b • z₂.1).snoc (a • z₁.2 + b • z₂.2) =
          a • (z₁.1.snoc z₁.2) + b • (z₂.1.snoc z₂.2) := snoc_comb a b z₁.1 z₂.1 z₁.2 z₂.2
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, hsnoc,
        PiLp.add_apply, PiLp.smul_apply, map_add, map_smul, Finset.sum_add_distrib,
        ← Finset.smul_sum]
      calc D.A (h + 1) j 0 D.x0 +
            (a • ∑ i : Fin (h + 1), D.A (h + 1) j i.succ ((z₁.1.snoc z₁.2) i) +
             b • ∑ i : Fin (h + 1), D.A (h + 1) j i.succ ((z₂.1.snoc z₂.2) i))
          = (a + b) • D.A (h + 1) j 0 D.x0 +
            (a • ∑ i : Fin (h + 1), D.A (h + 1) j i.succ ((z₁.1.snoc z₁.2) i) +
             b • ∑ i : Fin (h + 1), D.A (h + 1) j i.succ ((z₂.1.snoc z₂.2) i)) := by
              rw [hab, one_smul]
        _ = a • (D.A (h + 1) j 0 D.x0 +
              ∑ i : Fin (h + 1), D.A (h + 1) j i.succ ((z₁.1.snoc z₁.2) i)) +
            b • (D.A (h + 1) j 0 D.x0 +
              ∑ i : Fin (h + 1), D.A (h + 1) j i.succ ((z₂.1.snoc z₂.2) i)) := by
              rw [add_smul, smul_add, smul_add]; abel
        _ = a • D.b (h + 1) j + b • D.b (h + 1) j := by rw [hlin₁, hlin₂]
        _ = D.b (h + 1) j := by rw [← add_smul, hab, one_smul]
  have hΦ_conv : EConvex Φ := by
    intro q₁ hq₁ q₂ hq₂ a b ha hb hab
    change Φ (a • q₁.1 + b • q₂.1) ≤ ((a * q₁.2 + b * q₂.2 : ℝ) : EReal)
    refine ereal_le_coe_of_forall_pos fun δ hδ => ?_
    have hlt1 : Φ q₁.1 < ((q₁.2 + δ : ℝ) : EReal) :=
      lt_of_le_of_lt hq₁ (EReal.coe_lt_coe_iff.mpr (by linarith))
    have hlt2 : Φ q₂.1 < ((q₂.2 + δ : ℝ) : EReal) :=
      lt_of_le_of_lt hq₂ (EReal.coe_lt_coe_iff.mpr (by linarith))
    simp only [Φ, Model.stageVal, iInf_lt_iff] at hlt1 hlt2
    rcases hlt1 with ⟨y₁, hy₁, hFy₁⟩
    rcases hlt2 with ⟨y₂, hy₂, hFy₂⟩
    have hy_comb : a • y₁ + b • y₂ ∈ D.feas h j (a • q₁.1 + b • q₂.1) :=
      hGr_conv (x := (q₁.1, y₁)) hy₁ (y := (q₂.1, y₂)) hy₂ ha hb hab
    have hF_comb : F (a • q₁.1 + b • q₂.1, a • y₁ + b • y₂) ≤
        ((a * (q₁.2 + δ) + b * (q₂.2 + δ) : ℝ) : EReal) :=
      hF_conv (x := ((q₁.1, y₁), q₁.2 + δ)) hFy₁.le (y := ((q₂.1, y₂), q₂.2 + δ)) hFy₂.le ha hb hab
    have hEq : a * (q₁.2 + δ) + b * (q₂.2 + δ) = a * q₁.2 + b * q₂.2 + δ := by
      calc a * (q₁.2 + δ) + b * (q₂.2 + δ)
          = a * q₁.2 + b * q₂.2 + (a + b) * δ := by ring
        _ = a * q₁.2 + b * q₂.2 + δ := by rw [hab, one_mul]
    rw [hEq] at hF_comb
    exact le_trans (iInf₂_le (a • y₁ + b • y₂) hy_comb) hF_comb
  have hΦ_nbot : ∀ x, Φ x ≠ ⊥ := by
    intro x
    by_cases hne : (D.feas h j x).Nonempty
    · have hclosed_fx : IsClosed (D.feas h j x) :=
        hGr_closed.preimage (continuous_const.prodMk continuous_id)
      have hsub_fx : D.feas h j x ⊆ D.Xc (h + 1) := fun y hy => hy.1
      have hcomp_fx : IsCompact (D.feas h j x) := hXc_comp.of_isClosed_subset hclosed_fx hsub_fx
      have hlsc_y : LowerSemicontinuousOn (fun y => F (x, y)) (D.feas h j x) :=
        (hF_lsc.comp (continuous_const.prodMk continuous_id)).lowerSemicontinuousOn _
      obtain ⟨y₀, hy₀, hmin⟩ := hlsc_y.exists_isMinOn hne hcomp_fx
      have hle : F (x, y₀) ≤ Φ x := le_iInf₂ fun y hy => hmin hy
      intro hbot
      rw [hbot] at hle
      exact hF_nbot (x, y₀) (le_bot_iff.mp hle)
    · have hempty : D.feas h j x = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp [Φ, Model.stageVal, hempty]
  have hΦ_lsc : LowerSemicontinuous Φ := by
    intro x₀ a ha
    obtain ⟨a', haa', ha'Φ⟩ := exists_between ha
    have hloc : ∀ y ∈ D.Xc (h + 1), ∃ U : Set (Hist n h), ∃ W : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x₀ ∈ U ∧ IsOpen W ∧ y ∈ W ∧
        ∀ x ∈ U, ∀ y' ∈ W, (x, y') ∈ Gr → a' < F (x, y') := by
      intro y _
      by_cases hy : (x₀, y) ∈ Gr
      · have hlt : a' < F (x₀, y) := lt_of_lt_of_le ha'Φ (iInf₂_le y hy)
        have hmem : {z | a' < F z} ∈ 𝓝 (x₀, y) := hF_lsc (x₀, y) a' hlt
        rw [nhds_prod_eq, Filter.mem_prod_iff] at hmem
        rcases hmem with ⟨U₀, hU₀, W₀, hW₀, hsub⟩
        rcases mem_nhds_iff.mp hU₀ with ⟨U, hUU₀, hUopen, hx₀U⟩
        rcases mem_nhds_iff.mp hW₀ with ⟨W, hWW₀, hWopen, hyW⟩
        exact ⟨U, W, hUopen, hx₀U, hWopen, hyW, fun x hx y' hy' _ =>
          hsub (Set.mk_mem_prod (hUU₀ hx) (hWW₀ hy'))⟩
      · have hmem : Grᶜ ∈ 𝓝 (x₀, y) := hGr_closed.isOpen_compl.mem_nhds hy
        rw [nhds_prod_eq, Filter.mem_prod_iff] at hmem
        rcases hmem with ⟨U₀, hU₀, W₀, hW₀, hsub⟩
        rcases mem_nhds_iff.mp hU₀ with ⟨U, hUU₀, hUopen, hx₀U⟩
        rcases mem_nhds_iff.mp hW₀ with ⟨W, hWW₀, hWopen, hyW⟩
        exact ⟨U, W, hUopen, hx₀U, hWopen, hyW, fun x hx y' hy' hGr' =>
          absurd hGr' (hsub (Set.mk_mem_prod (hUU₀ hx) (hWW₀ hy')))⟩
    choose U W hUopen hx₀U hWopen hyW hprop using hloc
    have hcover : D.Xc (h + 1) ⊆ ⋃ y : D.Xc (h + 1), W y.1 y.2 :=
      fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyW y hy⟩
    obtain ⟨S, hScover⟩ := hXc_comp.elim_finite_subcover (fun y : D.Xc (h + 1) => W y.1 y.2)
      (fun y => hWopen y.1 y.2) hcover
    let U₀ : Set (Hist n h) := ⋂ y ∈ S, U y.1 y.2
    have hU₀_open : IsOpen U₀ := isOpen_biInter_finset fun y _ => hUopen y.1 y.2
    have hx₀U₀ : x₀ ∈ U₀ := Set.mem_iInter₂.mpr fun y _ => hx₀U y.1 y.2
    filter_upwards [hU₀_open.mem_nhds hx₀U₀] with x hx
    have hle : a' ≤ Φ x := by
      refine le_iInf₂ fun y' hy' => ?_
      have hy'X : y' ∈ D.Xc (h + 1) := hy'.1
      obtain ⟨y, hyS, hy'W⟩ := Set.mem_iUnion₂.mp (hScover hy'X)
      have hxU : x ∈ U y.1 y.2 := Set.mem_iInter₂.mp hx y hyS
      exact (hprop y.1 y.2 x hxU y' hy'W hy').le
    exact lt_of_lt_of_le haa' hle
  have hΦ_ntop : ∀ x ∈ Metric.cthickening ε (D.prodSet h), Φ x ≠ ⊤ := by
    intro x hx
    obtain ⟨y, hy⟩ := hfeas_ne j hj x hx
    have hyX : y ∈ D.Xc (h + 1) := hy.1
    have hsnoc_mem : x.snoc y ∈ Metric.cthickening ε (D.prodSet (h + 1)) :=
      snoc_mem_cthickening_prodSet D hx hyX
    have hflt : D.f (h + 1) j (x.snoc y) < ⊤ := hf_dom j hj x hx y hyX
    have hVlt : V (x.snoc y) < ⊤ := lt_top_iff_ne_top.mpr (hV_ntop _ hsnoc_mem)
    have hFlt : F (x, y) < ⊤ := EReal.add_lt_top hflt.ne hVlt.ne
    exact (lt_of_le_of_lt (iInf₂_le y hy) hFlt).ne
  exact ⟨hΦ_conv, hΦ_nbot, hΦ_lsc, hΦ_ntop⟩

private lemma qaux_invariant {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) {ε : ℝ}
    (hS : D.Standing) (hH2 : D.H2 ε) :
    ∀ r h, 1 ≤ h → h + r = T →
      EConvex (D.Qaux r h) ∧
      (∀ x, D.Qaux r h x ≠ ⊥) ∧
      LowerSemicontinuous (D.Qaux r h) ∧
      (∀ x ∈ Metric.cthickening ε (D.prodSet h), D.Qaux r h x ≠ ⊤) := by
  intro r
  induction r with
  | zero =>
    intro h _ _
    refine ⟨econvex_zero, fun _ => EReal.zero_ne_bot, lowerSemicontinuous_const,
      fun _ _ => EReal.zero_ne_top⟩
  | succ r ih =>
    intro h hh hhr
    have hhT : h < T := by omega
    have hih := ih (h + 1) (by omega) (by omega)
    obtain ⟨hV_conv, hV_nbot, hV_lsc, hV_ntop⟩ := hih
    have hRlz : ∀ j : Fin M, j ∈ Model.Rlz (M := M) (h + 1) := by
      intro j
      simp only [Model.Rlz]
      rw [if_neg (by omega)]
      trivial
    have hstep : ∀ j : Fin M,
        EConvex (D.stageVal h j (D.Qaux r (h + 1))) ∧
        (∀ x, D.stageVal h j (D.Qaux r (h + 1)) x ≠ ⊥) ∧
        LowerSemicontinuous (D.stageVal h j (D.Qaux r (h + 1))) ∧
        (∀ x ∈ Metric.cthickening ε (D.prodSet h),
          D.stageVal h j (D.Qaux r (h + 1)) x ≠ ⊤) :=
      fun j => stageVal_step D hH2 hhT (hRlz j) hV_conv hV_nbot hV_lsc hV_ntop
    obtain ⟨hΦ_pos, _, hPrisk_sub, _, hPrisk_ne⟩ := hS (h + 1) (by omega) (by omega)
    have hw_nonneg : ∀ π ∈ D.Prisk (h + 1), ∀ j : Fin M, 0 ≤ π j * D.Φ (h + 1) j := by
      intro π hπ j
      exact mul_nonneg ((hPrisk_sub hπ).1 j) (hΦ_pos j).le
    have hQeq : D.Qaux (r + 1) h = fun x =>
        ⨆ π ∈ D.Prisk (h + 1),
          ∑ j : Fin M, ((π j * D.Φ (h + 1) j : ℝ) : EReal) *
            D.stageVal h j (D.Qaux r (h + 1)) x := by
      ext x; rfl
    rw [hQeq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine econvex_biSup (D.Prisk (h + 1)) _ fun π hπ => ?_
      refine econvex_sum Finset.univ _ (fun j _ => ?_) (fun j _ x => ?_)
      · exact econvex_const_mul (hw_nonneg π hπ j) (hstep j).1
      · exact ereal_mul_nonneg_ne_bot (hw_nonneg π hπ j) ((hstep j).2.1 x)
    · intro x
      obtain ⟨π₀, hπ₀⟩ := hPrisk_ne
      have hsum_nbot : (∑ j : Fin M, ((π₀ j * D.Φ (h + 1) j : ℝ) : EReal) *
          D.stageVal h j (D.Qaux r (h + 1)) x) ≠ ⊥ :=
        ereal_sum_ne_bot Finset.univ _ fun j _ =>
          ereal_mul_nonneg_ne_bot (hw_nonneg π₀ hπ₀ j) ((hstep j).2.1 x)
      have hle : (∑ j : Fin M, ((π₀ j * D.Φ (h + 1) j : ℝ) : EReal) *
          D.stageVal h j (D.Qaux r (h + 1)) x) ≤
          ⨆ π ∈ D.Prisk (h + 1), ∑ j : Fin M, ((π j * D.Φ (h + 1) j : ℝ) : EReal) *
            D.stageVal h j (D.Qaux r (h + 1)) x :=
        le_biSup (fun π => ∑ j : Fin M, ((π j * D.Φ (h + 1) j : ℝ) : EReal) *
          D.stageVal h j (D.Qaux r (h + 1)) x) hπ₀
      intro hbot
      dsimp only at hbot
      rw [hbot] at hle
      exact hsum_nbot (le_bot_iff.mp hle)
    · intro x₀
      refine lowerSemicontinuousAt_iSup fun π => lowerSemicontinuousAt_iSup fun hπ => ?_
      exact (lsc_sum_ereal Finset.univ _
        (fun j _ => lsc_const_mul_ereal (hw_nonneg π hπ j) (hstep j).2.2.1)
        (fun j _ x => ereal_mul_nonneg_ne_bot (hw_nonneg π hπ j) ((hstep j).2.1 x))) x₀
    · intro x hx
      let C : ℝ := Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin M => (D.stageVal h j (D.Qaux r (h + 1)) x).toReal)
      have hleC : (⨆ π ∈ D.Prisk (h + 1),
          ∑ j : Fin M, ((π j * D.Φ (h + 1) j : ℝ) : EReal) *
            D.stageVal h j (D.Qaux r (h + 1)) x) ≤ (C : EReal) := by
        refine iSup₂_le fun π hπ => ?_
        have hsum_one : ∑ j : Fin M, π j * D.Φ (h + 1) j = 1 := (hPrisk_sub hπ).2
        have hterm : ∀ j : Fin M,
            ((π j * D.Φ (h + 1) j : ℝ) : EReal) * D.stageVal h j (D.Qaux r (h + 1)) x ≤
              (((π j * D.Φ (h + 1) j) * C : ℝ) : EReal) := by
          intro j
          have hfin_j : ((D.stageVal h j (D.Qaux r (h + 1)) x).toReal : EReal) =
              D.stageVal h j (D.Qaux r (h + 1)) x :=
            EReal.coe_toReal ((hstep j).2.2.2 x hx) ((hstep j).2.1 x)
          rw [← hfin_j, ← EReal.coe_mul, EReal.coe_le_coe_iff]
          exact mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun j : Fin M => (D.stageVal h j (D.Qaux r (h + 1)) x).toReal)
              (Finset.mem_univ j))
            (hw_nonneg π hπ j)
        calc ∑ j : Fin M, ((π j * D.Φ (h + 1) j : ℝ) : EReal) *
              D.stageVal h j (D.Qaux r (h + 1)) x
            ≤ ∑ j : Fin M, (((π j * D.Φ (h + 1) j) * C : ℝ) : EReal) :=
              Finset.sum_le_sum fun j _ => hterm j
          _ = ((∑ j : Fin M, (π j * D.Φ (h + 1) j) * C : ℝ) : EReal) := by
              rw [ereal_coe_sum]
          _ = (((∑ j : Fin M, π j * D.Φ (h + 1) j) * C : ℝ) : EReal) := by
              rw [Finset.sum_mul]
          _ = (C : EReal) := by rw [hsum_one, one_mul]
      exact (lt_of_le_of_lt hleC (EReal.coe_lt_top C)).ne

end Helpers

theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) :
    ∀ h, 1 ≤ h → h ≤ T → ∀ ε', 0 < ε' → ε' < ε →
      EConvex (D.Q h) ∧
      (∀ x ∈ Metric.cthickening ε' (D.prodSet h), D.Q h x ≠ ⊥ ∧ D.Q h x ≠ ⊤) ∧
      ContinuousOn (fun x => (D.Q h x).toReal) (Metric.cthickening ε' (D.prodSet h)) := by
  intro h hh1 hhT ε' hε'0 hε'ε
  obtain ⟨hconv, hnbot, _, hntop⟩ :=
    qaux_invariant D hS hH2 (T - h) h hh1 (by omega)
  change EConvex (D.Q h) at hconv
  change ∀ x, D.Q h x ≠ ⊥ at hnbot
  change ∀ x ∈ Metric.cthickening ε (D.prodSet h), D.Q h x ≠ ⊤ at hntop
  refine ⟨hconv, ?_, ?_⟩
  · intro x hx
    exact ⟨hnbot x, hntop x (Metric.cthickening_mono hε'ε.le (D.prodSet h) hx)⟩
  · let U := Metric.thickening ε (D.prodSet h)
    have hU_open : IsOpen U := Metric.isOpen_thickening
    have hU_conv : Convex ℝ U := convex_thickening_of_convex (convex_prodSet D hH2 hhT) ε
    have hU_sub : U ⊆ Metric.cthickening ε (D.prodSet h) :=
      Metric.thickening_subset_cthickening ε (D.prodSet h)
    have hConvOn : ConvexOn ℝ U (fun x => (D.Q h x).toReal) :=
      econvex_toReal_convexOn hconv hU_conv fun x hx => ⟨hnbot x, hntop x (hU_sub hx)⟩
    have hContU : ContinuousOn (fun x => (D.Q h x).toReal) U := hConvOn.continuousOn hU_open
    exact hContU.mono (Metric.cthickening_subset_thickening' hH2.1 hε'ε (D.prodSet h))
